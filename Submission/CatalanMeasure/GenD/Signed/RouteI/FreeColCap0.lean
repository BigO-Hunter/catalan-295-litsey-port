module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.MarkedPilot

@[expose] public section
set_option autoImplicit false
set_option Elab.async false

/-!
# C12 `FreeColCap0`: generic interval consumer for the anchor-0 free column cap

Target (T4 `hC` input): `capSource.FreeColCap 0 (-2946610/1000000)`, i.e.
`colField 0 s <= -2.94661` for `0 < s < 1`, `s` exact integer data of `CapSourceData.capSource`.

* `unit_real`: for `s` in `[alpha, beta]` with `alpha < m < beta`, all column cells except the one
  containing `[alpha, beta]` are tangent-bounded at `m` (concavity of the cell potential outside the
  cell, pointwise `log x <= log x0 + x/x0 - 1`), the containing cell and the row potential are
  chord-bounded (convexity of `x log x`, concavity of `log`), the two logarithms are tangent-bounded.
* Exact closed form `pot_closed`: `c.pot y = w/(hi-lo) * (Fv (hi-y) - Fv (lo-y))`, `Fv u = u log u - u`.
* Numerics: `lgv` fixed-point logarithm (`MarkedPilot.logFx`, 2^-64 scale, error `lgErr`), `evUp/evLo`
  enclosures of one cell, `sUp/sLo` list sums, `unitLite` + chunked `decide +kernel` certificates.
* `L_cert`: `Lq <= physL (refRow 0) log|.|` with `Lq = -0.6905432` from the antiderivative
  `Phi Y = Y log u(Y) - sqrt(Y^2-4)` of `log u(Y)`, `u = (Y + sqrt(Y^2-4))/2`.
* `unit300`: ONE real unit, `[667727272727, 667960227272]/10^12` inside column cell 300.
* `chain_sound`, `freeColCap0_of_cover`: any chain of certified units (cover of `[a,b]`) plus the two
  end ranges `(0,a]` and `[b,1)` give `FreeColCap 0 (-2946610/1000000)`. The cover and the ends are NOT
  supplied here; only the consumer and the one unit are.

kcost: each `decide +kernel` below is a chunk of at most 200 cells (about 2 fixed-point logarithms per
cell, 2.5 ms each); measured kernel 0.7 to 1.6 s per chunk, 28 s for the whole certificate section
(unit about 17.7 s, `L_cert` about 10.4 s). Chunks stay below 200 cells because a single sum over 500
or more cells ran out of memory in the kernel.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

open Real Set intervalIntegral MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.MarkedPilot (logFx logFx_spec lnormOK lnorm lnormAux atanhV ln2_enc)

noncomputable section

def Fv (u : ℝ) : ℝ := u * Real.log u - u

theorem Fv_neg (u : ℝ) : Fv (-u) = - Fv u := by
  unfold Fv; rw [Real.log_neg_eq_log]; ring

theorem int_log_shift (l h y : ℝ) :
    ∫ t in l..h, Real.log |y - t| = Fv (h - y) - Fv (l - y) := by
  have e : ∀ t : ℝ, Real.log |y - t| = Real.log (t - y) := by
    intro t; rw [Real.log_abs, ← Real.log_neg_eq_log (y - t)]; congr 1; ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_right (fun t => Real.log t) y, integral_log]
  unfold Fv; ring

theorem pot_closed (c : YCell) (y : ℝ) :
    c.pot y = c.w / (c.hi - c.lo) * (Fv (c.hi - y) - Fv (c.lo - y)) := by
  unfold YCell.pot YCell.avg
  rw [int_log_shift]

/-- derivative of the cell potential at `m` (two logs). -/
def dpot (c : YCell) (m : ℝ) : ℝ :=
  c.w / (c.hi - c.lo) * (Real.log (c.lo - m) - Real.log (c.hi - m))

theorem ii_log (l h y : ℝ) : IntervalIntegrable (fun t : ℝ => Real.log |y - t|) volume l h := by
  have e : ∀ t : ℝ, Real.log |y - t| = Real.log (t - y) := by
    intro t; rw [Real.log_abs, ← Real.log_neg_eq_log (y - t)]; congr 1; ring
  simp_rw [e]
  have := (intervalIntegrable_log' (a := l - y) (b := h - y)).comp_sub_right y
  simpa using this

/-- Tangent bound for a cell to the right of both points. -/
theorem pot_tangent_right (c : YCell) {s m : ℝ} (hs : s ≤ c.lo) (hm : m < c.lo) :
    c.pot s ≤ c.pot m + dpot c m * (s - m) := by
  have hlh := c.lo_lt
  have hρ : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg (by linarith)
  have hm' : m < c.hi := by linarith
  have key : ∫ t in c.lo..c.hi, Real.log |s - t| ≤
      (∫ t in c.lo..c.hi, Real.log |m - t|) +
        (m - s) * (Real.log (c.hi - m) - Real.log (c.lo - m)) := by
    have hI : ∫ t in c.lo..c.hi, (t - m)⁻¹ = Real.log (c.hi - m) - Real.log (c.lo - m) := by
      rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => t⁻¹) m,
        integral_inv_of_pos (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)]
    have hi1 : IntervalIntegrable (fun t : ℝ => (m - s) * (t - m)⁻¹) volume c.lo c.hi := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      linarith [ht.1]
    calc ∫ t in c.lo..c.hi, Real.log |s - t|
        ≤ ∫ t in c.lo..c.hi, (Real.log |m - t| + (m - s) * (t - m)⁻¹) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hlh.le (ii_log _ _ _)
            ((ii_log _ _ _).add hi1)
          intro t ht
          have h1 : 0 < t - m := by linarith [ht.1]
          have h2 : 0 < t - s := by linarith [ht.1]
          rw [abs_sub_comm s t, abs_sub_comm m t, abs_of_pos h2, abs_of_pos h1]
          have := Real.log_le_sub_one_of_pos (div_pos h2 h1)
          rw [Real.log_div h2.ne' h1.ne'] at this
          have e : (t - s) / (t - m) - 1 = (m - s) * (t - m)⁻¹ := by field_simp; ring
          linarith
      _ = (∫ t in c.lo..c.hi, Real.log |m - t|) + (m - s) * ∫ t in c.lo..c.hi, (t - m)⁻¹ := by
          rw [intervalIntegral.integral_add (ii_log _ _ _) hi1, intervalIntegral.integral_const_mul]
      _ = _ := by rw [hI]
  unfold YCell.pot YCell.avg dpot
  have := mul_le_mul_of_nonneg_left key hρ
  have e : c.w / (c.hi - c.lo) * (Real.log (c.lo - m) - Real.log (c.hi - m)) * (s - m) =
      c.w / (c.hi - c.lo) * ((m - s) * (Real.log (c.hi - m) - Real.log (c.lo - m))) := by ring
  rw [e]; nlinarith [this]

def negc (c : YCell) : YCell := ⟨-c.hi, -c.lo, c.w, by linarith [c.lo_lt], c.w_nonneg⟩

theorem pot_negc (c : YCell) (y : ℝ) : (negc c).pot (-y) = c.pot y := by
  rw [pot_closed, pot_closed]
  have e1 : (negc c).hi - (negc c).lo = c.hi - c.lo := by simp [negc]; ring
  have e2 : (negc c).hi - -y = -(c.lo - y) := by simp [negc]; ring
  have e3 : (negc c).lo - -y = -(c.hi - y) := by simp [negc]; ring
  rw [e1, e2, e3, Fv_neg, Fv_neg]
  show c.w / (c.hi - c.lo) * (-Fv (c.lo - y) - -Fv (c.hi - y)) = _
  ring

theorem dpot_negc (c : YCell) (m : ℝ) : dpot (negc c) (-m) = - dpot c m := by
  unfold dpot
  have e1 : (negc c).hi - (negc c).lo = c.hi - c.lo := by simp [negc]; ring
  have e2 : (negc c).lo - -m = -(c.hi - m) := by simp [negc]; ring
  have e3 : (negc c).hi - -m = -(c.lo - m) := by simp [negc]; ring
  rw [e1, e2, e3, Real.log_neg_eq_log, Real.log_neg_eq_log]
  show c.w / (c.hi - c.lo) * (Real.log (c.hi - m) - Real.log (c.lo - m)) = _
  ring

theorem pot_tangent_left (c : YCell) {s m : ℝ} (hs : c.hi ≤ s) (hm : c.hi < m) :
    c.pot s ≤ c.pot m + dpot c m * (s - m) := by
  have h := pot_tangent_right (negc c) (s := -s) (m := -m) (by simp [negc]; linarith) (by simp [negc]; linarith)
  rw [pot_negc, pot_negc, dpot_negc] at h
  linarith

/-- inside cell closed form -/
theorem pot_inside (c : YCell) {y : ℝ} (h1 : c.lo ≤ y) (h2 : y ≤ c.hi) :
    c.pot y = c.w / (c.hi - c.lo) *
      ((c.hi - y) * Real.log (c.hi - y) + (y - c.lo) * Real.log (y - c.lo) - (c.hi - c.lo)) := by
  rw [pot_closed]
  have : Fv (c.lo - y) = - Fv (y - c.lo) := by rw [← Fv_neg]; congr 1; ring
  rw [this]; unfold Fv; congr 1; ring

theorem pot_chord_inside (c : YCell) {α β s a b : ℝ} (hα : c.lo ≤ α) (hβ : β ≤ c.hi) (hαβ : α ≤ β)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : s = a * α + b * β) :
    c.pot s ≤ a * c.pot α + b * c.pot β := by
  have hlh := c.lo_lt
  have hρ : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg (by linarith)
  have hh : ∀ x : ℝ, a * x + b * x = x := fun x => by rw [← add_mul, hab, one_mul]
  have hsl : c.lo ≤ s := by
    rw [hs]; nlinarith [mul_nonneg ha (sub_nonneg.2 hα), mul_nonneg hb (sub_nonneg.2 (hα.trans hαβ)),
      hh c.lo]
  have hsh : s ≤ c.hi := by
    rw [hs]; nlinarith [mul_nonneg ha (sub_nonneg.2 (hαβ.trans hβ)), mul_nonneg hb (sub_nonneg.2 hβ),
      hh c.hi]
  rw [pot_inside c hsl hsh, pot_inside c hα (by linarith), pot_inside c (by linarith) hβ]
  have cv := convexOn_mul_log
  have k1 : (c.hi - s) * Real.log (c.hi - s) ≤ a * ((c.hi - α) * Real.log (c.hi - α)) +
      b * ((c.hi - β) * Real.log (c.hi - β)) := by
    have := cv.2 (show c.hi - α ∈ Set.Ici (0:ℝ) from by simp; linarith)
      (show c.hi - β ∈ Set.Ici (0:ℝ) from by simp; linarith) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (c.hi - α) + b * (c.hi - β) = c.hi - s := by rw [hs]; linear_combination c.hi * hab
    rw [e] at this; exact this
  have k2 : (s - c.lo) * Real.log (s - c.lo) ≤ a * ((α - c.lo) * Real.log (α - c.lo)) +
      b * ((β - c.lo) * Real.log (β - c.lo)) := by
    have := cv.2 (show α - c.lo ∈ Set.Ici (0:ℝ) from by simp; linarith)
      (show β - c.lo ∈ Set.Ici (0:ℝ) from by simp; linarith) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (α - c.lo) + b * (β - c.lo) = s - c.lo := by rw [hs]; linear_combination (-c.lo) * hab
    rw [e] at this; exact this
  have e3 : c.hi - c.lo = a * (c.hi - c.lo) + b * (c.hi - c.lo) := by linear_combination (-(c.hi - c.lo)) * hab
  have : c.w / (c.hi - c.lo) * ((c.hi - s) * Real.log (c.hi - s) + (s - c.lo) * Real.log (s - c.lo) - (c.hi - c.lo)) ≤
      c.w / (c.hi - c.lo) * (a * ((c.hi - α) * Real.log (c.hi - α) + (α - c.lo) * Real.log (α - c.lo) - (c.hi - c.lo)) +
        b * ((c.hi - β) * Real.log (c.hi - β) + (β - c.lo) * Real.log (β - c.lo) - (c.hi - c.lo))) := by
    apply mul_le_mul_of_nonneg_left _ hρ
    nlinarith [k1, k2, e3]
  linarith [this]

/-- concavity chord for a cell to the right of both points. -/
theorem pot_chord_right (c : YCell) {y1 y2 y a b : ℝ} (h1 : y1 ≤ c.lo) (h2 : y2 ≤ c.lo)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hy : y = a * y1 + b * y2) :
    a * c.pot y1 + b * c.pot y2 ≤ c.pot y := by
  have hlh := c.lo_lt
  have hρ : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg (by linarith)
  have hh : ∀ x : ℝ, a * x + b * x = x := fun x => by rw [← add_mul, hab, one_mul]
  have key : a * (∫ t in c.lo..c.hi, Real.log |y1 - t|) + b * (∫ t in c.lo..c.hi, Real.log |y2 - t|)
      ≤ ∫ t in c.lo..c.hi, Real.log |y - t| := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((ii_log _ _ _).const_mul a) ((ii_log _ _ _).const_mul b)]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hlh.le
      (((ii_log _ _ _).const_mul a).add ((ii_log _ _ _).const_mul b)) (ii_log _ _ _)
    intro t ht
    have p1 : 0 < t - y1 := by linarith [ht.1]
    have p2 : 0 < t - y2 := by linarith [ht.1]
    have hyl : y ≤ c.lo := by
      rw [hy]; nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2),
        hh c.lo]
    have p : 0 < t - y := by linarith [ht.1]
    rw [abs_sub_comm y1 t, abs_sub_comm y2 t, abs_sub_comm y t, abs_of_pos p1, abs_of_pos p2, abs_of_pos p]
    have := strictConcaveOn_log_Ioi.concaveOn.2 (show t - y1 ∈ Set.Ioi (0:ℝ) from p1)
      (show t - y2 ∈ Set.Ioi (0:ℝ) from p2) ha hb hab
    simp only [smul_eq_mul] at this
    have e : a * (t - y1) + b * (t - y2) = t - y := by rw [hy]; linear_combination t * hab
    rw [e] at this; exact this
  unfold YCell.pot YCell.avg
  have := mul_le_mul_of_nonneg_left key hρ
  nlinarith [this]

theorem pot_chord_left (c : YCell) {y1 y2 y a b : ℝ} (h1 : c.hi ≤ y1) (h2 : c.hi ≤ y2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hy : y = a * y1 + b * y2) :
    a * c.pot y1 + b * c.pot y2 ≤ c.pot y := by
  have h := pot_chord_right (negc c) (y1 := -y1) (y2 := -y2) (y := -y)
    (by simp [negc]; linarith) (by simp [negc]; linarith) ha hb hab (by rw [hy]; ring)
  rw [pot_negc, pot_negc, pot_negc] at h
  exact h

/-! ### List level -/

def dpotL (l : List YCell) (m : ℝ) : ℝ := (l.map fun c => dpot c m).sum

theorem potL_tangent (l : List YCell) {s m α β : ℝ} (hf : ∀ c ∈ l, c.hi ≤ α ∨ β ≤ c.lo)
    (hαm : α < m) (hmβ : m < β) (hs1 : α ≤ s) (hs2 : s ≤ β) :
    potL l s ≤ potL l m + dpotL l m * (s - m) := by
  induction l with
  | nil => simp [potL, dpotL]
  | cons c l ih =>
    have h1 : potL l s ≤ potL l m + dpotL l m * (s - m) := ih fun d hd => hf d (by simp [hd])
    have h2 : c.pot s ≤ c.pot m + dpot c m * (s - m) := by
      rcases hf c (by simp) with h | h
      · exact pot_tangent_left c (by linarith) (by linarith)
      · exact pot_tangent_right c (by linarith) (by linarith)
    simp only [potL, dpotL, List.map_cons, List.sum_cons] at h1 h2 ⊢
    nlinarith

theorem potL_chord (R : List YCell) {α β s a b : ℝ} (hf : ∀ c ∈ R, 2 * β ≤ c.lo ∨ c.hi ≤ 2 * α)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : s = a * α + b * β) (hαβ : α ≤ β) :
    a * potL R (2 * α) + b * potL R (2 * β) ≤ potL R (2 * s) := by
  induction R with
  | nil => simp [potL]
  | cons c R ih =>
    have h1 := ih fun d hd => hf d (by simp [hd])
    have hy : 2 * s = a * (2 * α) + b * (2 * β) := by rw [hs]; ring
    have h2 : a * c.pot (2 * α) + b * c.pot (2 * β) ≤ c.pot (2 * s) := by
      rcases hf c (by simp) with h | h
      · exact pot_chord_right c (by linarith) h ha hb hab hy
      · exact pot_chord_left c h (by linarith) ha hb hab hy
    simp only [potL, List.map_cons, List.sum_cons] at h1 h2 ⊢
    nlinarith

/-- The affine bound at an endpoint. -/
def Eend (F : List YCell) (I : YCell) (R : List YCell) (m x : ℝ) : ℝ :=
  2 * (potL F m + dpotL F m * (x - m)) + 2 * I.pot x +
    (9 / 58 * (Real.log m + (x - m) / m) + 3 / 58 * (Real.log (1 - m) - (x - m) / (1 - m))) -
    potL R (2 * x)

theorem unit_real (Lc Rc : List YCell) (I : YCell) (R : List YCell) {α β m : ℝ}
    (hαβ : α < β) (hα0 : 0 < α) (hβ1 : β < 1) (hαm : α < m) (hmβ : m < β)
    (hLc : ∀ c ∈ Lc, c.hi ≤ α) (hRc : ∀ c ∈ Rc, β ≤ c.lo) (hI1 : I.lo ≤ α) (hI2 : β ≤ I.hi)
    (hR : ∀ c ∈ R, 2 * β ≤ c.lo ∨ c.hi ≤ 2 * α) (K : ℝ)
    (hEα : Eend (Lc ++ Rc) I R m α ≤ K) (hEβ : Eend (Lc ++ Rc) I R m β ≤ K)
    {s : ℝ} (hs1 : α ≤ s) (hs2 : s ≤ β) :
    2 * potL (Lc ++ I :: Rc) s - potL R (2 * s) + 9 / 58 * Real.log s + 3 / 58 * Real.log (1 - s) ≤ K := by
  have hd : 0 < β - α := by linarith
  obtain ⟨a, b, ha, hb, hab, hsab⟩ : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ s = a * α + b * β := by
    refine ⟨(β - s) / (β - α), (s - α) / (β - α), div_nonneg (by linarith) hd.le,
      div_nonneg (by linarith) hd.le, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring
  have hm0 : m ≠ 0 := by intro h; linarith
  have hm1 : 1 - m ≠ 0 := by intro h; linarith
  have hF : ∀ c ∈ Lc ++ Rc, c.hi ≤ α ∨ β ≤ c.lo := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact Or.inl (hLc c h)
    · exact Or.inr (hRc c h)
  have t1 := potL_tangent (Lc ++ Rc) hF hαm hmβ hs1 hs2
  have t2 := pot_chord_inside I hI1 hI2 hαβ.le ha hb hab hsab
  have t3 := potL_chord R hR ha hb hab hsab hαβ.le
  have hsm : s - m = a * (α - m) + b * (β - m) := by rw [hsab]; linear_combination m * hab
  have lg1 : Real.log s ≤ Real.log m + (s - m) / m := by
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < s) (by linarith : 0 < m))
    rw [Real.log_div (by linarith) (by linarith)] at this
    have e : s / m - 1 = (s - m) / m := by field_simp
    linarith
  have lg2 : Real.log (1 - s) ≤ Real.log (1 - m) - (s - m) / (1 - m) := by
    have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < 1 - s) (by linarith : 0 < 1 - m))
    rw [Real.log_div (by linarith) (by linarith)] at this
    have e : (1 - s) / (1 - m) - 1 = -((s - m) / (1 - m)) := by field_simp; ring
    linarith
  have hpl : potL (Lc ++ I :: Rc) s = potL (Lc ++ Rc) s + I.pot s := by
    simp [potL, List.map_append, List.sum_append]; ring
  rw [hpl]
  -- the affine identity
  have key : a * Eend (Lc ++ Rc) I R m α + b * Eend (Lc ++ Rc) I R m β =
      2 * (potL (Lc ++ Rc) m + dpotL (Lc ++ Rc) m * (s - m)) +
      2 * (a * I.pot α + b * I.pot β) +
      (9 / 58 * (Real.log m + (s - m) / m) + 3 / 58 * (Real.log (1 - m) - (s - m) / (1 - m))) -
      (a * potL R (2 * α) + b * potL R (2 * β)) := by
    unfold Eend
    have e1 : (s - m) / m = a * ((α - m) / m) + b * ((β - m) / m) := by
      rw [hsm]; field_simp
    have e2 : (s - m) / (1 - m) = a * ((α - m) / (1 - m)) + b * ((β - m) / (1 - m)) := by
      rw [hsm]; field_simp
    rw [e1, e2, hsm]
    have hh : ∀ x : ℝ, a * x + b * x = x := fun x => by rw [← add_mul, hab, one_mul]
    have := hh (2 * potL (Lc ++ Rc) m) 
    have := hh (2 * Real.log m)
    nlinarith [hh (2 * potL (Lc ++ Rc) m), hh (9 / 58 * Real.log m), hh (3 / 58 * Real.log (1 - m))]
  have hmax : a * Eend (Lc ++ Rc) I R m α + b * Eend (Lc ++ Rc) I R m β ≤ K := by
    have hK : a * K + b * K = K := by rw [← add_mul, hab, one_mul]
    linarith [mul_le_mul_of_nonneg_left hEα ha, mul_le_mul_of_nonneg_left hEβ hb]
  nlinarith [key, hmax, t1, t2, t3, lg1, lg2]

def lgv (P : ℕ) : ℤ := if P = 0 then 0 else logFx 64 10 20 P (10 ^ 12)
def lgErr : ℕ := 46 * (6 * 20 + (3 * 2 ^ 64 + 3 ^ 41 - 1) / 3 ^ 41) + 6 * 10 +
  (5 * 2 ^ 64 + 2 * 5 ^ 21 - 1) / (2 * 5 ^ 21) + 1

theorem lnorm_fst_le (P : ℕ) (hP : P < 2 ^ 45) : |((lnorm P (10 ^ 12)).1 : ℝ)| ≤ 46 := by
  have hq : (10 ^ 12 : ℕ).log2 = 39 := by decide
  have h1 : P.log2 ≤ 44 := by
    by_cases h0 : P = 0
    · simp [h0]
    · have := (Nat.log2_lt h0).2 hP
      omega
  unfold lnorm
  rw [hq]
  have hm : ∀ m0 P0 Q0, m0 ≤ 6 → -39 ≤ m0 → |((lnormAux m0 P0 Q0).1 : ℝ)| ≤ 46 := by
    intro m0 P0 Q0 h1 h2
    unfold lnormAux
    split_ifs <;> simp only [abs_le] <;> constructor <;> push_cast <;> norm_cast <;> omega
  exact hm _ _ _ (by omega) (by omega)

theorem lg_enc (P : ℕ) (hP : P < 2 ^ 45) (hok : P = 0 ∨ lnormOK P (10 ^ 12) = true) :
    |Real.log ((P : ℝ) / 1000000000000) - (lgv P : ℝ) / 2 ^ 64| ≤ (lgErr : ℝ) / 2 ^ 64 := by
  by_cases h0 : P = 0
  · subst h0; simp [lgv]; positivity
  · have hP' : 0 < P := Nat.pos_of_ne_zero h0
    have h := logFx_spec (F := 64) (n := 10) (n2 := 20) hP' (by norm_num : 0 < 10 ^ 12) (hok.resolve_left h0)
    have hm := lnorm_fst_le P hP
    simp only [lgv, h0, if_false]
    push_cast at h
    norm_num at h ⊢
    refine h.trans ?_
    have hc : (0:ℝ) ≤ 6 * 20 / 2 ^ 64 + 3 * (1 / 3) ^ 41 := by positivity
    have := mul_le_mul_of_nonneg_right hm hc
    have e : (46 : ℝ) * (6 * 20 / 2 ^ 64 + 3 * (1 / 3) ^ 41) + (6 * 10 / 2 ^ 64 + 5 / 2 * (1 / 5) ^ 21) ≤
        (lgErr : ℝ) / 2 ^ 64 := by
      unfold lgErr; norm_num
    norm_num at this ⊢
    linarith

theorem prod_up {κ k K Z Zu : ℝ} (hK : 0 < K) (hk0 : 0 ≤ k) (h1 : k / K ≤ κ) (h2 : κ ≤ (k + 1) / K)
    (hZ : Z ≤ Zu) : κ * Z ≤ (k * Zu + |Zu|) / K := by
  have hκ : 0 ≤ κ := le_trans (div_nonneg hk0 hK.le) h1
  have hd0 : 0 ≤ κ - k / K := by linarith
  have hd1 : κ - k / K ≤ 1 / K := by
    have : (k + 1) / K = k / K + 1 / K := by ring
    linarith
  have a1 : κ * Z ≤ κ * Zu := mul_le_mul_of_nonneg_left hZ hκ
  have a2 : (κ - k / K) * Zu ≤ (κ - k / K) * |Zu| := mul_le_mul_of_nonneg_left (le_abs_self _) hd0
  have a3 : (κ - k / K) * |Zu| ≤ (1 / K) * |Zu| := mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)
  have e : (k * Zu + |Zu|) / K = k / K * Zu + 1 / K * |Zu| := by ring
  rw [e]; nlinarith

theorem prod_lo {κ k K Z Zl : ℝ} (hK : 0 < K) (hk0 : 0 ≤ k) (h1 : k / K ≤ κ) (h2 : κ ≤ (k + 1) / K)
    (hZ : Zl ≤ Z) : (k * Zl - |Zl|) / K ≤ κ * Z := by
  have hκ : 0 ≤ κ := le_trans (div_nonneg hk0 hK.le) h1
  have hd0 : 0 ≤ κ - k / K := by linarith
  have hd1 : κ - k / K ≤ 1 / K := by
    have : (k + 1) / K = k / K + 1 / K := by ring
    linarith
  have a1 : κ * Zl ≤ κ * Z := mul_le_mul_of_nonneg_left hZ hκ
  have a2 : -(κ - k / K) * |Zl| ≤ (κ - k / K) * Zl := by
    have := neg_abs_le Zl
    nlinarith
  have a3 : (κ - k / K) * |Zl| ≤ (1 / K) * |Zl| := mul_le_mul_of_nonneg_right hd1 (abs_nonneg _)
  have e : (k * Zl - |Zl|) / K = k / K * Zl - 1 / K * |Zl| := by ring
  rw [e]; nlinarith

def KB : ℕ := 128
def kk (T : ℤ) (t : Tr) : ℤ := (t.2.2 * 2 ^ KB) / (T * (t.2.1 - t.1))
def zBase (t : Tr) (M X : ℤ) : ℤ :=
  (t.2.1 - X) * lgv (t.2.1 - M).natAbs - (t.1 - X) * lgv (t.1 - M).natAbs - (t.2.1 - t.1) * 2 ^ 64
def zErr (t : Tr) (X : ℤ) : ℤ := (((t.2.1 - X).natAbs + (t.1 - X).natAbs : ℕ) : ℤ) * (lgErr : ℤ)
def zUp (t : Tr) (M X : ℤ) : ℤ := zBase t M X + zErr t X
def zLo (t : Tr) (M X : ℤ) : ℤ := zBase t M X - zErr t X
def evUp (T : ℤ) (t : Tr) (M X : ℤ) : ℤ := kk T t * zUp t M X + |zUp t M X|
def evLo (T : ℤ) (t : Tr) (M X : ℤ) : ℤ := kk T t * zLo t M X - |zLo t M X|

/-- real value of tangent line evaluation of a cell -/
def tv (c : YCell) (m x : ℝ) : ℝ := c.pot m + dpot c m * (x - m)

theorem kk_bounds (T : ℤ) (t : Tr) (hT : 0 < T) (hv : t.1 < t.2.1) :
    (kk T t : ℝ) ≤ (t.2.2 : ℝ) * 2 ^ KB / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) ∧
    (t.2.2 : ℝ) * 2 ^ KB / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) ≤ ((kk T t : ℝ) + 1) := by
  have hb : 0 < T * (t.2.1 - t.1) := mul_pos hT (by omega)
  have hbr : (0 : ℝ) < (T : ℝ) * ((t.2.1 : ℝ) - t.1) := by exact_mod_cast hb
  have h1 := Int.ediv_mul_le (t.2.2 * 2 ^ KB) hb.ne'
  have h2 := Int.lt_ediv_add_one_mul_self (t.2.2 * 2 ^ KB) hb
  unfold kk
  constructor
  · rw [le_div_iff₀ hbr]; exact_mod_cast h1
  · rw [div_le_iff₀ hbr]; push_cast; exact_mod_cast h2.le

theorem tv_closed (t : Tr) (T : ℤ) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) (hT : 0 < T) (M X : ℤ) :
    tv (mkCell 1 T t) ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) =
      ((t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1))) *
        (((t.2.1 : ℝ) - X) * Real.log (((t.2.1 : ℝ) - M) / 1000000000000) -
          ((t.1 : ℝ) - X) * Real.log (((t.1 : ℝ) - M) / 1000000000000) - ((t.2.1 : ℝ) - t.1)) := by
  obtain ⟨hl, hh, hw⟩ := mkCell_eq hv (by omega : (0 : ℤ) ≤ T) (by norm_num : (0 : ℝ) ≤ 1)
  have e1 : (mkCell 1 T t).hi - (M : ℝ) / 10 ^ 12 = ((t.2.1 : ℝ) - M) / 1000000000000 := by rw [hh]; ring
  have e2 : (mkCell 1 T t).lo - (M : ℝ) / 10 ^ 12 = ((t.1 : ℝ) - M) / 1000000000000 := by rw [hl]; ring
  unfold tv dpot
  rw [pot_closed]
  unfold Fv
  rw [e1, e2, hw, hl, hh]
  generalize Real.log (((t.2.1 : ℝ) - M) / 1000000000000) = la
  generalize Real.log (((t.1 : ℝ) - M) / 1000000000000) = lb
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hHL : (t.2.1 : ℝ) - t.1 ≠ 0 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  field_simp
  ring

theorem lg_int (a : ℤ) (h : a.natAbs < 2 ^ 45) (hok : a.natAbs = 0 ∨ lnormOK a.natAbs (10 ^ 12) = true) :
    |Real.log ((a : ℝ) / 1000000000000) - (lgv a.natAbs : ℝ) / 2 ^ 64| ≤ (lgErr : ℝ) / 2 ^ 64 := by
  have := lg_enc a.natAbs h hok
  have e : Real.log ((a : ℝ) / 1000000000000) = Real.log (((a.natAbs : ℕ) : ℝ) / 1000000000000) := by
    rw [← Real.log_abs, abs_div]
    congr 2
    · rw [Nat.cast_natAbs]; simp
    · norm_num
  rw [e]; exact this

theorem mul_enc {u la l e : ℝ} (h : |la - l| ≤ e) :
    u * la ≤ u * l + |u| * e ∧ u * l - |u| * e ≤ u * la := by
  have : |u * (la - l)| ≤ |u| * e := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  rw [abs_le] at this
  constructor <;> nlinarith [this.1, this.2]

theorem ev_enc (t : Tr) (T : ℤ) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) (hT : 0 < T) (M X : ℤ)
    (h1 : (t.2.1 - M).natAbs < 2 ^ 45) (h2 : (t.1 - M).natAbs < 2 ^ 45)
    (o1 : (t.2.1 - M).natAbs = 0 ∨ lnormOK (t.2.1 - M).natAbs (10 ^ 12) = true)
    (o2 : (t.1 - M).natAbs = 0 ∨ lnormOK (t.1 - M).natAbs (10 ^ 12) = true) :
    (evLo T t M X : ℝ) / 2 ^ (KB + 64) ≤ tv (mkCell 1 T t) ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) ∧
    tv (mkCell 1 T t) ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) ≤ (evUp T t M X : ℝ) / 2 ^ (KB + 64) := by
  rw [tv_closed t T hv hT]
  have la := lg_int (t.2.1 - M) h1 o1
  have lb := lg_int (t.1 - M) h2 o2
  push_cast at la lb
  have ma := mul_enc (u := (t.2.1 : ℝ) - X) la
  have mb := mul_enc (u := (t.1 : ℝ) - X) lb
  have hk := kk_bounds T t hT hv.1
  have hK : (0 : ℝ) < 2 ^ KB := by positivity
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hHL : (0 : ℝ) < (t.2.1 : ℝ) - t.1 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  have hk0 : (0 : ℝ) ≤ (kk T t : ℝ) := by
    have : 0 ≤ kk T t := Int.ediv_nonneg (mul_nonneg hv.2 (by positivity)) (mul_pos hT (show 0 < t.2.1 - t.1 by omega)).le
    exact_mod_cast this
  set κ : ℝ := (t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) with hκ
  have hk1 : (kk T t : ℝ) / 2 ^ KB ≤ κ := by
    rw [div_le_iff₀ hK]
    have := hk.2
    rw [hκ]
    calc (kk T t : ℝ) ≤ _ := hk.1
      _ = _ := by field_simp
  have hk2 : κ ≤ ((kk T t : ℝ) + 1) / 2 ^ KB := by
    rw [le_div_iff₀ hK]
    rw [hκ]
    calc _ = (t.2.2 : ℝ) * 2 ^ KB / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) := by field_simp
      _ ≤ _ := hk.2
  have e64 : (0 : ℝ) < 2 ^ 64 := by positivity
  set Z : ℝ := ((t.2.1 : ℝ) - X) * Real.log (((t.2.1 : ℝ) - M) / 1000000000000) -
          ((t.1 : ℝ) - X) * Real.log (((t.1 : ℝ) - M) / 1000000000000) - ((t.2.1 : ℝ) - t.1) with hZ
  have hzup : Z ≤ (zUp t M X : ℝ) / 2 ^ 64 := by
    unfold zUp zBase zErr; push_cast
    rw [hZ]
    have := ma.1; have := mb.2
    calc _ ≤ ((t.2.1 : ℝ) - X) * ((lgv (t.2.1 - M).natAbs : ℝ) / 2 ^ 64) +
          |(t.2.1 : ℝ) - X| * ((lgErr : ℝ) / 2 ^ 64) -
          (((t.1 : ℝ) - X) * ((lgv (t.1 - M).natAbs : ℝ) / 2 ^ 64) -
          |(t.1 : ℝ) - X| * ((lgErr : ℝ) / 2 ^ 64)) - ((t.2.1 : ℝ) - t.1) := by linarith
      _ = _ := by ring
  have hzlo : (zLo t M X : ℝ) / 2 ^ 64 ≤ Z := by
    unfold zLo zBase zErr; push_cast
    rw [hZ]
    have := ma.2; have := mb.1
    calc _ = ((t.2.1 : ℝ) - X) * ((lgv (t.2.1 - M).natAbs : ℝ) / 2 ^ 64) -
          |(t.2.1 : ℝ) - X| * ((lgErr : ℝ) / 2 ^ 64) -
          (((t.1 : ℝ) - X) * ((lgv (t.1 - M).natAbs : ℝ) / 2 ^ 64) +
          |(t.1 : ℝ) - X| * ((lgErr : ℝ) / 2 ^ 64)) - ((t.2.1 : ℝ) - t.1) := by ring
      _ ≤ _ := by linarith
  have hS : (2 : ℝ) ^ (KB + 64) = 2 ^ KB * 2 ^ 64 := pow_add _ _ _
  constructor
  · have := prod_lo (κ := κ) (k := (kk T t : ℝ)) (K := 2 ^ KB) hK hk0 hk1 hk2 hzlo
    refine le_trans (le_of_eq ?_) this
    unfold evLo; push_cast
    rw [hS, abs_div, abs_of_pos e64]
    field_simp
  · have := prod_up (κ := κ) (k := (kk T t : ℝ)) (K := 2 ^ KB) hK hk0 hk1 hk2 hzup
    refine le_trans this (le_of_eq ?_)
    unfold evUp; push_cast
    rw [hS, abs_div, abs_of_pos e64]
    field_simp

def tangL (l : List YCell) (m x : ℝ) : ℝ := potL l m + dpotL l m * (x - m)

theorem tangL_cons (c : YCell) (l : List YCell) (m x : ℝ) :
    tangL (c :: l) m x = tv c m x + tangL l m x := by
  simp only [tangL, tv, potL, dpotL, List.map_cons, List.sum_cons]; ring

theorem tangL_nil (m x : ℝ) : tangL [] m x = 0 := by simp [tangL, potL, dpotL]

def sUp (T : ℤ) (l : List Tr) (M X : ℤ) : ℤ := (l.map fun t => evUp T t M X).sum
def sLo (T : ℤ) (l : List Tr) (M X : ℤ) : ℤ := (l.map fun t => evLo T t M X).sum

def lnOK (P : ℕ) : Bool := decide (P = 0) || lnormOK P (10 ^ 12)

def okT (t : Tr) (M : ℤ) : Bool :=
  decide ((t.2.1 - M).natAbs < 2 ^ 45) && decide ((t.1 - M).natAbs < 2 ^ 45) &&
    lnOK (t.2.1 - M).natAbs && lnOK (t.1 - M).natAbs
def okL (l : List Tr) (M : ℤ) : Bool := l.all fun t => okT t M

theorem okT_spec {t : Tr} {M : ℤ} (h : okT t M = true) :
    (t.2.1 - M).natAbs < 2 ^ 45 ∧ (t.1 - M).natAbs < 2 ^ 45 ∧
      ((t.2.1 - M).natAbs = 0 ∨ lnormOK (t.2.1 - M).natAbs (10 ^ 12) = true) ∧
      ((t.1 - M).natAbs = 0 ∨ lnormOK (t.1 - M).natAbs (10 ^ 12) = true) := by
  simp only [okT, lnOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem tangL_enc (T : ℤ) (hT : 0 < T) (M X : ℤ) :
    ∀ l : List Tr, (∀ t ∈ l, t.1 < t.2.1 ∧ 0 ≤ t.2.2) → okL l M = true →
      (sLo T l M X : ℝ) / 2 ^ (KB + 64) ≤ tangL (l.map (mkCell 1 T)) ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) ∧
      tangL (l.map (mkCell 1 T)) ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) ≤ (sUp T l M X : ℝ) / 2 ^ (KB + 64)
  | [], _, _ => by simp [tangL_nil, sLo, sUp]
  | t :: l, hv, hok => by
    have ih := tangL_enc T hT M X l (fun s hs => hv s (List.mem_cons_of_mem _ hs))
      (by simp only [okL, List.all_cons, Bool.and_eq_true] at hok; exact hok.2)
    have h1 := okT_spec (by simp only [okL, List.all_cons, Bool.and_eq_true] at hok; exact hok.1)
    have e := ev_enc t T (hv t List.mem_cons_self) hT M X h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
    simp only [List.map_cons, tangL_cons, sLo, sUp, List.sum_cons] at ih ⊢
    simp only [Int.cast_add, add_div]
    constructor <;> linarith [ih.1, ih.2, e.1, e.2]

def Tc : ℤ := sumP col0
def Trw : ℤ := sumP row0
def Lq : ℚ := -6905432 / 10 ^ 7
def cq : ℚ := -2946610 / 10 ^ 6

def okLog (M : ℤ) : Bool :=
  decide (M.natAbs < 2 ^ 45) && lnOK M.natAbs &&
    decide ((10 ^ 12 - M).natAbs < 2 ^ 45) && lnOK (10 ^ 12 - M).natAbs

def eUpOf (sU iU rL M X : ℤ) : ℚ :=
  ((2 * (sU + iU) - rL : ℤ) : ℚ) / 2 ^ (KB + 64) +
    9 / 58 * (((lgv M.natAbs + lgErr : ℤ) : ℚ) / 2 ^ 64 + ((X - M : ℤ) : ℚ) / (M : ℚ)) +
    3 / 58 * (((lgv (10 ^ 12 - M).natAbs + lgErr : ℤ) : ℚ) / 2 ^ 64 -
      ((X - M : ℤ) : ℚ) / ((10 ^ 12 - M : ℤ) : ℚ))

def eUp (Lt Rt : List Tr) (It : Tr) (M X : ℤ) : ℚ :=
  eUpOf (sUp Tc (Lt ++ Rt) M X) (evUp Tc It X X) (sLo Trw row0 (2 * X) (2 * X)) M X

def Vt (t : Tr) : Prop := t.1 < t.2.1 ∧ 0 ≤ t.2.2

theorem eend_le (Lt Rt : List Tr) (It : Tr) (M X : ℤ)
    (hvL : ∀ t ∈ Lt ++ Rt, Vt t) (hvI : Vt It) (hvR : ∀ t ∈ row0, Vt t)
    (hM0 : 0 < M) (hM1 : M < 10 ^ 12) (hT : 0 < Tc) (hTr : 0 < Trw)
    (o1 : okL (Lt ++ Rt) M = true) (o2 : okT It X = true) (o3 : okL row0 (2 * X) = true)
    (o4 : okLog M = true) :
    Eend ((Lt ++ Rt).map (mkCell 1 Tc)) (mkCell 1 Tc It) (row0.map (mkCell 1 Trw))
      ((M : ℝ) / 10 ^ 12) ((X : ℝ) / 10 ^ 12) ≤ ((eUp Lt Rt It M X : ℚ) : ℝ) := by
  have e1 := (tangL_enc Tc hT M X (Lt ++ Rt) hvL o1).2
  have e2 := (ev_enc It Tc hvI hT X X (okT_spec o2).1 (okT_spec o2).2.1 (okT_spec o2).2.2.1
    (okT_spec o2).2.2.2).2
  have e3 := (tangL_enc Trw hTr (2 * X) (2 * X) row0 hvR o3).1
  have hy : ((2 * X : ℤ) : ℝ) / 10 ^ 12 = 2 * ((X : ℝ) / 10 ^ 12) := by push_cast; ring
  rw [hy] at e3
  simp only [tangL, sub_self, mul_zero, add_zero] at e3
  simp only [tv, sub_self, mul_zero, add_zero] at e2
  simp only [okLog, lnOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at o4
  have l1 := lg_int M o4.1.1.1 o4.1.1.2
  have l2 := lg_int (10 ^ 12 - M) o4.1.2 o4.2
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hM1r : (M : ℝ) < 10 ^ 12 := by exact_mod_cast hM1
  have hq1 : ((X : ℝ) / 10 ^ 12 - (M : ℝ) / 10 ^ 12) / ((M : ℝ) / 10 ^ 12) = ((X : ℝ) - M) / M := by
    field_simp
  have hq2 : (1 - (M : ℝ) / 10 ^ 12) = (((10 ^ 12 - M : ℤ)) : ℝ) / 1000000000000 := by
    push_cast; ring
  have hq3 : ((X : ℝ) / 10 ^ 12 - (M : ℝ) / 10 ^ 12) / (1 - (M : ℝ) / 10 ^ 12) =
      ((X : ℝ) - M) / (((10 ^ 12 - M : ℤ)) : ℝ) := by
    have : ((10 ^ 12 - M : ℤ) : ℝ) ≠ 0 := by push_cast; linarith
    rw [hq2]; field_simp; ring
  rw [abs_le] at l1 l2
  unfold Eend
  unfold tangL at e1
  rw [hq1, hq3, hq2]
  push_cast [eUp, eUpOf]
  push_cast at l1 l2
  have c1 := l1.2; have c2 := l2.2
  simp only [show (1000000000000 : ℝ) = 10 ^ 12 by norm_num] at c1 c2 ⊢
  have hdiv : ∀ a b : ℝ, a / 2 ^ (KB + 64) + b / 2 ^ (KB + 64) = (a + b) / 2 ^ (KB + 64) := fun a b => by ring
  have hs : (2 * (((sUp Tc (Lt ++ Rt) M X : ℤ) : ℝ) + ((evUp Tc It X X : ℤ) : ℝ)) -
      ((sLo Trw row0 (2 * X) (2 * X) : ℤ) : ℝ)) / 2 ^ (KB + 64) =
      2 * (((sUp Tc (Lt ++ Rt) M X : ℤ) : ℝ) / 2 ^ (KB + 64)) +
      2 * (((evUp Tc It X X : ℤ) : ℝ) / 2 ^ (KB + 64)) -
      ((sLo Trw row0 (2 * X) (2 * X) : ℤ) : ℝ) / 2 ^ (KB + 64) := by ring
  rw [hs]
  have hl1 : (((lgv M.natAbs : ℤ) : ℝ) + (lgErr : ℝ)) / 2 ^ 64 = ((lgv M.natAbs : ℤ) : ℝ) / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64 := by ring
  have hl2 : (((lgv (1000000000000 - M).natAbs : ℤ) : ℝ) + (lgErr : ℝ)) / 2 ^ 64 = ((lgv (1000000000000 - M).natAbs : ℤ) : ℝ) / 2 ^ 64 + (lgErr : ℝ) / 2 ^ 64 := by ring
  rw [hl1, hl2]
  linarith [e1, e2, e3, c1, c2]

def unitLite (k : ℕ) (It : Tr) (Rt : List Tr) (α β M v1 v2 v3 v4 v5 v6 : ℤ) : Bool :=
  decide (0 < α ∧ α < M ∧ M < β ∧ β < 10 ^ 12) && decide (It.1 ≤ α ∧ β ≤ It.2.1) &&
  (col0.take k).all (fun t => decide (t.2.1 ≤ α)) && Rt.all (fun t => decide (β ≤ t.1)) &&
  row0.all (fun t => decide (2 * β ≤ t.1 ∨ t.2.1 ≤ 2 * α)) &&
  okLog M && decide (eUpOf v1 v3 v5 M α ≤ cq + Lq) && decide (eUpOf v2 v4 v6 M β ≤ cq + Lq)

theorem refCol0 : capSource.refCol 0 = col0.map (mkCell 1 Tc) := by
  simp [capSource, refColF, Tc]

theorem refRow0 : capSource.refRow 0 = row0.map (mkCell 1 Trw) := by
  simp [capSource, refRowF, Trw]

theorem lo_eq {t : Tr} {T : ℤ} (hv : Vt t) (hT : 0 < T) :
    (mkCell 1 T t).lo = (t.1 : ℝ) / 10 ^ 12 := (mkCell_eq hv hT.le (by norm_num)).1
theorem hi_eq {t : Tr} {T : ℤ} (hv : Vt t) (hT : 0 < T) :
    (mkCell 1 T t).hi = (t.2.1 : ℝ) / 10 ^ 12 := (mkCell_eq hv hT.le (by norm_num)).2.1

theorem Tc_pos : 0 < Tc := col0_tot
theorem Trw_pos : 0 < Trw := row0_tot

theorem unit_cap (hLq : ((Lq : ℚ) : ℝ) ≤ physL (capSource.refRow 0) (fun u => Real.log |u|))
    {k : ℕ} {α β M : ℤ} {It : Tr} {Rt : List Tr} (hd : col0.drop k = It :: Rt)
    {v1 v2 v3 v4 v5 v6 : ℤ}
    (hv1 : sUp Tc (col0.take k ++ Rt) M α = v1) (hv2 : sUp Tc (col0.take k ++ Rt) M β = v2)
    (hv3 : evUp Tc It α α = v3) (hv4 : evUp Tc It β β = v4)
    (hv5 : sLo Trw row0 (2 * α) (2 * α) = v5) (hv6 : sLo Trw row0 (2 * β) (2 * β) = v6)
    (o1 : okL (col0.take k ++ Rt) M = true) (o2 : okT It α = true) (o3 : okT It β = true)
    (o4 : okL row0 (2 * α) = true) (o5 : okL row0 (2 * β) = true)
    (h : unitLite k It Rt α β M v1 v2 v3 v4 v5 v6 = true) {s : ℝ}
    (h1 : (α : ℝ) / 10 ^ 12 ≤ s) (h2 : s ≤ (β : ℝ) / 10 ^ 12) :
    capSource.colField 0 s ≤ ((cq : ℚ) : ℝ) := by
  unfold unitLite at h
  obtain ⟨Lt, hLt⟩ : ∃ Lt, Lt = col0.take k := ⟨_, rfl⟩
  rw [← hLt] at h o1 hv1 hv2
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨hα0, hαM, hMβ, hβ1, hI1, hI2, hLc, hRc, hRow, o6, e1, e2⟩ := h
  have e1 : eUp Lt Rt It M α ≤ cq + Lq := by unfold eUp; rw [hv1, hv3, hv5]; exact e1
  have e2 : eUp Lt Rt It M β ≤ cq + Lq := by unfold eUp; rw [hv2, hv4, hv6]; exact e2
  have hsplit : col0 = Lt ++ It :: Rt := by
    have := List.take_append_drop k col0
    rw [hd, ← hLt] at this
    exact this.symm
  have hvc : ∀ t ∈ col0, Vt t := col0_ok
  have hvr : ∀ t ∈ row0, Vt t := row0_ok
  have mL : ∀ t ∈ Lt, t ∈ col0 := fun t ht => by rw [hsplit]; exact List.mem_append_left _ ht
  have mR : ∀ t ∈ Rt, t ∈ col0 := fun t ht => by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
  have mI : It ∈ col0 := by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self
  have hC : capSource.refCol 0 = Lt.map (mkCell 1 Tc) ++ mkCell 1 Tc It :: Rt.map (mkCell 1 Tc) := by
    rw [refCol0]; conv_lhs => rw [hsplit]
    simp
  have hvL : ∀ t ∈ Lt ++ Rt, Vt t := by
    intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact hvc t (mL t h)
    · exact hvc t (mR t h)
  have hvI : Vt It := hvc It mI
  have hT := Tc_pos
  have hTr := Trw_pos
  have hM0 : 0 < M := by omega
  have hM1 : M < 10 ^ 12 := by omega
  have hmk : ∀ x : ℤ, (0 : ℝ) < 10 ^ 12 := fun _ => by positivity
  have hαβ : (α : ℝ) / 10 ^ 12 < (β : ℝ) / 10 ^ 12 := by
    apply div_lt_div_of_pos_right _ (by positivity); exact_mod_cast (by omega : α < β)
  have hα0' : 0 < (α : ℝ) / 10 ^ 12 := by
    apply div_pos _ (by positivity); exact_mod_cast hα0
  have hβ1' : (β : ℝ) / 10 ^ 12 < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast hβ1
  have hαm : (α : ℝ) / 10 ^ 12 < (M : ℝ) / 10 ^ 12 := by
    apply div_lt_div_of_pos_right _ (by positivity); exact_mod_cast hαM
  have hmβ : (M : ℝ) / 10 ^ 12 < (β : ℝ) / 10 ^ 12 := by
    apply div_lt_div_of_pos_right _ (by positivity); exact_mod_cast hMβ
  have hLc' : ∀ c ∈ Lt.map (mkCell 1 Tc), c.hi ≤ (α : ℝ) / 10 ^ 12 := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    rw [hi_eq (hvc t (mL t ht)) hT]
    apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast hLc t ht
  have hRc' : ∀ c ∈ Rt.map (mkCell 1 Tc), (β : ℝ) / 10 ^ 12 ≤ c.lo := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    rw [lo_eq (hvc t (mR t ht)) hT]
    apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast hRc t ht
  have hI1' : (mkCell 1 Tc It).lo ≤ (α : ℝ) / 10 ^ 12 := by
    rw [lo_eq hvI hT]; apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast hI1
  have hI2' : (β : ℝ) / 10 ^ 12 ≤ (mkCell 1 Tc It).hi := by
    rw [hi_eq hvI hT]; apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast hI2
  have hR' : ∀ c ∈ row0.map (mkCell 1 Trw), 2 * ((β : ℝ) / 10 ^ 12) ≤ c.lo ∨ c.hi ≤ 2 * ((α : ℝ) / 10 ^ 12) := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    rcases hRow t ht with h | h
    · left
      rw [lo_eq (hvr t ht) hTr, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast h
    · right
      rw [hi_eq (hvr t ht) hTr, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity); exact_mod_cast h
  have hK1 : Eend (Lt.map (mkCell 1 Tc) ++ Rt.map (mkCell 1 Tc)) (mkCell 1 Tc It) (row0.map (mkCell 1 Trw))
      ((M : ℝ) / 10 ^ 12) ((α : ℝ) / 10 ^ 12) ≤ ((cq : ℚ) : ℝ) + ((Lq : ℚ) : ℝ) := by
    rw [← List.map_append]
    have := eend_le Lt Rt It M α hvL hvI hvr hM0 hM1 hT hTr o1 o2 o4 o6
    refine this.trans ?_
    exact_mod_cast (show eUp Lt Rt It M α ≤ cq + Lq from e1)
  have hK2 : Eend (Lt.map (mkCell 1 Tc) ++ Rt.map (mkCell 1 Tc)) (mkCell 1 Tc It) (row0.map (mkCell 1 Trw))
      ((M : ℝ) / 10 ^ 12) ((β : ℝ) / 10 ^ 12) ≤ ((cq : ℚ) : ℝ) + ((Lq : ℚ) : ℝ) := by
    rw [← List.map_append]
    have := eend_le Lt Rt It M β hvL hvI hvr hM0 hM1 hT hTr o1 o3 o5 o6
    refine this.trans ?_
    exact_mod_cast (show eUp Lt Rt It M β ≤ cq + Lq from e2)
  have key := unit_real (Lt.map (mkCell 1 Tc)) (Rt.map (mkCell 1 Tc)) (mkCell 1 Tc It)
    (row0.map (mkCell 1 Trw)) hαβ hα0' hβ1' hαm hmβ hLc' hRc' hI1' hI2' hR'
    (((cq : ℚ) : ℝ) + ((Lq : ℚ) : ℝ)) hK1 hK2 h1 h2
  unfold CapSource.colField
  rw [hC, refRow0]
  rw [refRow0] at hLq
  linarith [key, hLq]

def sq (Y : ℝ) : ℝ := Real.sqrt (Y ^ 2 - 4)
def uu (Y : ℝ) : ℝ := (Y + sq Y) / 2
def Phi (Y : ℝ) : ℝ := Y * Real.log (uu Y) - sq Y

theorem uu_pos {Y : ℝ} (h : 2 ≤ Y) : 1 ≤ uu Y := by
  unfold uu sq; have := Real.sqrt_nonneg (Y ^ 2 - 4); linarith

theorem phi_deriv {Y : ℝ} (h : 2 < Y) : HasDerivAt Phi (Real.log (uu Y)) Y := by
  have h4 : 0 < Y ^ 2 - 4 := by nlinarith
  have hs : 0 < sq Y := Real.sqrt_pos.2 h4
  have hsq : sq Y ^ 2 = Y ^ 2 - 4 := Real.sq_sqrt h4.le
  have d1 : HasDerivAt (fun Y : ℝ => Y ^ 2 - 4) (2 * Y) Y := by
    simpa using ((hasDerivAt_pow 2 Y).sub_const 4)
  have d2 : HasDerivAt sq (Y / sq Y) Y := by
    have := d1.sqrt h4.ne'
    convert this using 1
    · rfl
    · show Y / sq Y = _
      unfold sq; field_simp
  have d3 : HasDerivAt uu ((1 + Y / sq Y) / 2) Y := by
    unfold uu; exact ((hasDerivAt_id Y).add d2).div_const 2
  have hu : 0 < uu Y := by have := uu_pos h.le; linarith
  have d4 := d3.log hu.ne'
  have d5 := ((hasDerivAt_id Y).mul d4).sub d2
  convert d5 using 1
  · funext x; simp [Phi]
  · have : (1 + Y / sq Y) / 2 / uu Y = 1 / sq Y := by
      unfold uu; field_simp; nlinarith [hsq]
    simp only [id]
    rw [this]; field_simp; ring

theorem phi_cont : ContinuousOn Phi (Ici 2) := by
  have h1 : ContinuousOn sq (Ici 2) := by
    unfold sq; exact (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
  have h2 : ContinuousOn uu (Ici 2) := by unfold uu; exact (continuousOn_id.add h1).div_const 2
  unfold Phi
  refine (continuousOn_id.mul (ContinuousOn.log h2 fun x hx => ?_)).sub h1
  have := uu_pos hx; linarith

theorem int_loguu {l h : ℝ} (hl : 2 ≤ l) (hlh : l ≤ h) :
    ∫ Y in l..h, Real.log (uu Y) = Phi h - Phi l := by
  apply integral_eq_sub_of_hasDerivAt_of_le hlh (phi_cont.mono (fun x hx => by simp at hx ⊢; linarith [hx.1]))
  · intro x hx; exact phi_deriv (by linarith [hx.1])
  · apply ContinuousOn.intervalIntegrable
    have h1 : ContinuousOn sq (Ici 2) := by
      unfold sq; exact (Real.continuous_sqrt.comp_continuousOn (by fun_prop))
    have h2 : ContinuousOn uu (Ici 2) := by unfold uu; exact (continuousOn_id.add h1).div_const 2
    rw [uIcc_of_le hlh]
    refine (ContinuousOn.log h2 fun x hx => ?_).mono (fun x hx => by simp at hx ⊢; linarith [hx.1])
    have := uu_pos hx; linarith

theorem log_physX_pos {Y : ℝ} (h : 2 ≤ Y) : Real.log |YCell.physX Y| = - Real.log (uu Y) := by
  have hs0 := Real.sqrt_nonneg (Y ^ 2 - 4)
  have hu := uu_pos h
  unfold YCell.physX
  rw [if_pos (by linarith)]
  have : 2 / (Y + √(Y ^ 2 - 4)) = (uu Y)⁻¹ := by
    unfold uu sq; field_simp
  rw [this, abs_of_pos (by positivity), Real.log_inv]

theorem log_physX_neg {Y : ℝ} (h : Y ≤ -2) : Real.log |YCell.physX Y| = - Real.log (uu (-Y)) := by
  have hs0 := Real.sqrt_nonneg (Y ^ 2 - 4)
  have hu := uu_pos (show 2 ≤ -Y by linarith)
  unfold YCell.physX
  rw [if_neg (by linarith)]
  have : 2 / (-Y + √(Y ^ 2 - 4)) = (uu (-Y))⁻¹ := by
    unfold uu sq; field_simp
  rw [abs_neg, this, abs_of_pos (by positivity), Real.log_inv]

/-- positive cell: phys log = -(rho)(Phi h - Phi l) -/
theorem phys_log_pos (c : YCell) (h : 2 ≤ c.lo) :
    c.phys (fun u => Real.log |u|) = - (c.w / (c.hi - c.lo) * (Phi c.hi - Phi c.lo)) := by
  unfold YCell.phys YCell.avg
  have : ∫ Y in c.lo..c.hi, Real.log |YCell.physX Y| = - (Phi c.hi - Phi c.lo) := by
    rw [← int_loguu h c.lo_lt.le, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro Y hY
    rw [uIcc_of_le c.lo_lt.le] at hY
    exact log_physX_pos (by linarith [hY.1])
  rw [this]; ring

/-- negative cell -/
theorem phys_log_neg (c : YCell) (h : c.hi ≤ -2) :
    c.phys (fun u => Real.log |u|) = - (c.w / (c.hi - c.lo) * (Phi (-c.lo) - Phi (-c.hi))) := by
  unfold YCell.phys YCell.avg
  have hlh := c.lo_lt
  have : ∫ Y in c.lo..c.hi, Real.log |YCell.physX Y| = - (Phi (-c.lo) - Phi (-c.hi)) := by
    have e : ∫ Y in c.lo..c.hi, Real.log |YCell.physX Y| = ∫ Y in c.lo..c.hi, - Real.log (uu (-Y)) := by
      apply intervalIntegral.integral_congr
      intro Y hY
      rw [uIcc_of_le hlh.le] at hY
      exact log_physX_neg (by linarith [hY.2])
    rw [e, intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg (fun Y => Real.log (uu Y)),
      int_loguu (by linarith) (by linarith)]
  rw [this]; ring

def LN2 : ℤ := (atanhV 64 20 1 3 : ℕ)
def ln2Err : ℤ := 6 * 20 + (3 * 2 ^ 64 + 3 ^ 41 - 1) / 3 ^ 41
def rr (Yn : ℕ) : ℕ := Nat.sqrt (Yn ^ 2 - 4 * 10 ^ 24)
def phiUpZ (Yn : ℕ) : ℤ :=
  (Yn : ℤ) * (lgv (Yn + rr Yn) + lgErr - LN2 + ln2Err) - (rr Yn : ℤ) * 2 ^ 64
def phiLoZ (Yn : ℕ) : ℤ :=
  (Yn : ℤ) * (lgv (Yn + rr Yn + 1) - lgErr - LN2 - ln2Err) - ((rr Yn : ℤ) + 1) * 2 ^ 64

def Fs (Y s : ℝ) : ℝ := Y * Real.log ((Y + s) / 2) - s

theorem Fs_anti {Y s1 s2 : ℝ} (hY : 0 < Y) (h1 : 0 ≤ s1) (h12 : s1 ≤ s2) : Fs Y s2 ≤ Fs Y s1 := by
  unfold Fs
  have hp1 : 0 < Y + s1 := by linarith
  have hp2 : 0 < Y + s2 := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hp2 hp1)
  rw [Real.log_div hp2.ne' hp1.ne'] at hl
  have e : (Y + s2) / 2 = (Y + s2) / 2 := rfl
  have hlg : Real.log ((Y + s2) / 2) - Real.log ((Y + s1) / 2) = Real.log (Y + s2) - Real.log (Y + s1) := by
    rw [Real.log_div hp2.ne' (by norm_num), Real.log_div hp1.ne' (by norm_num)]; ring
  have h3 : (Y + s2) / (Y + s1) - 1 = (s2 - s1) / (Y + s1) := by field_simp; ring
  have h4 : Y * ((s2 - s1) / (Y + s1)) ≤ s2 - s1 := by
    rw [← mul_div_assoc, div_le_iff₀ hp1]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left (show Real.log ((Y + s2) / 2) - Real.log ((Y + s1) / 2) ≤ (s2 - s1) / (Y + s1) by linarith) hY.le]

theorem sq_bounds (Yn : ℕ) (h : 2 * 10 ^ 12 ≤ Yn) :
    ((rr Yn : ℝ) / 10 ^ 12 ≤ sq ((Yn : ℝ) / 10 ^ 12)) ∧ sq ((Yn : ℝ) / 10 ^ 12) ≤ ((rr Yn : ℝ) + 1) / 10 ^ 12 := by
  have h4 : 4 * 10 ^ 24 ≤ Yn ^ 2 := by nlinarith
  have hr1 : rr Yn ^ 2 ≤ Yn ^ 2 - 4 * 10 ^ 24 := Nat.sqrt_le' _
  have hr2 : Yn ^ 2 - 4 * 10 ^ 24 < (rr Yn + 1) ^ 2 := Nat.lt_succ_sqrt' _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 4 * 10 ^ 24 := ⟨_, rfl⟩
  rw [← hK] at h4 hr1 hr2
  have hKr : (K : ℝ) = 4 * 10 ^ 24 := by rw [hK]; norm_num
  have hc : ((Yn ^ 2 - K : ℕ) : ℝ) = (Yn : ℝ) ^ 2 - K := by
    rw [Nat.cast_sub h4]; push_cast; ring
  have a1 : ((rr Yn : ℝ)) ^ 2 ≤ (Yn : ℝ) ^ 2 - 4 * 10 ^ 24 := by
    rw [← hKr, ← hc]; exact_mod_cast hr1
  have a2 : (Yn : ℝ) ^ 2 - 4 * 10 ^ 24 < ((rr Yn : ℝ) + 1) ^ 2 := by
    rw [← hKr, ← hc]; exact_mod_cast hr2
  have e : ((Yn : ℝ) / 10 ^ 12) ^ 2 - 4 = ((Yn : ℝ) ^ 2 - 4 * 10 ^ 24) / (10 ^ 12) ^ 2 := by
    field_simp
  unfold sq
  rw [e]
  have hpos : (0 : ℝ) < 10 ^ 12 := by positivity
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    exact div_le_div_of_nonneg_right a1 (by positivity)
  · apply Real.sqrt_le_iff.2
    constructor
    · exact div_nonneg (by linarith [(Nat.cast_nonneg (rr Yn) : (0 : ℝ) ≤ rr Yn)]) (by norm_num)
    · rw [div_pow]
      exact div_le_div_of_nonneg_right a2.le (by positivity)

theorem ln2_bound : |Real.log 2 - (LN2 : ℝ) / 2 ^ 64| ≤ (ln2Err : ℝ) / 2 ^ 64 := by
  have h := ln2_enc 64 20
  unfold LN2
  refine h.trans ?_
  have : (6 * (20 : ℝ) / 2 ^ 64 + 3 * (1 / 3) ^ (2 * 20 + 1)) ≤ (ln2Err : ℝ) / 2 ^ 64 := by
    unfold ln2Err; push_cast; norm_num
  push_cast at h ⊢
  convert this using 2 <;> norm_num

theorem phi_enc (Yn : ℕ) (h : 2 * 10 ^ 12 ≤ Yn)
    (hb : Yn + rr Yn + 1 < 2 ^ 45)
    (o1 : Yn + rr Yn = 0 ∨ lnormOK (Yn + rr Yn) (10 ^ 12) = true)
    (o2 : Yn + rr Yn + 1 = 0 ∨ lnormOK (Yn + rr Yn + 1) (10 ^ 12) = true) :
    (phiLoZ Yn : ℝ) / (2 ^ 64 * 10 ^ 12) ≤ Phi ((Yn : ℝ) / 10 ^ 12) ∧
    Phi ((Yn : ℝ) / 10 ^ 12) ≤ (phiUpZ Yn : ℝ) / (2 ^ 64 * 10 ^ 12) := by
  have hYn : (2 * 10 ^ 12 : ℝ) ≤ Yn := by exact_mod_cast h
  have hY : 0 < (Yn : ℝ) / 10 ^ 12 := by apply div_pos _ (by norm_num); linarith
  obtain ⟨hs1, hs2⟩ := sq_bounds Yn h
  have hr0 : (0 : ℝ) ≤ rr Yn := Nat.cast_nonneg _
  have hs0 : 0 ≤ (rr Yn : ℝ) / 10 ^ 12 := div_nonneg hr0 (by norm_num)
  have hPhi : Phi ((Yn : ℝ) / 10 ^ 12) = Fs ((Yn : ℝ) / 10 ^ 12) (sq ((Yn : ℝ) / 10 ^ 12)) := rfl
  have l2 := ln2_bound
  rw [abs_le] at l2
  have e2 : (0 : ℝ) < 2 ^ 64 := by positivity
  have h64 : (2 : ℝ) ^ 64 = 18446744073709551616 := by norm_num
  constructor
  · -- lower bound
    have a := Fs_anti hY (le_trans hs0 hs1) hs2
    rw [hPhi]
    refine le_trans ?_ a
    have lg := lg_enc (Yn + rr Yn + 1) (by omega) o2
    rw [abs_le] at lg
    have hP : ((Yn : ℝ) / 10 ^ 12 + ((rr Yn : ℝ) + 1) / 10 ^ 12) / 2 = (((Yn + rr Yn + 1 : ℕ) : ℝ) / 1000000000000) / 2 := by
      push_cast; ring
    have hPpos : (0 : ℝ) < ((Yn + rr Yn + 1 : ℕ) : ℝ) / 1000000000000 := by
      apply div_pos _ (by norm_num); exact Nat.cast_pos.2 (Nat.succ_pos _)
    unfold Fs
    rw [hP, Real.log_div hPpos.ne' (by norm_num)]
    have hlog : ((lgv (Yn + rr Yn + 1) : ℝ) - lgErr - LN2 - ln2Err) / 2 ^ 64 ≤
        Real.log (((Yn + rr Yn + 1 : ℕ) : ℝ) / 1000000000000) - Real.log 2 := by
      have := lg.1; have := l2.2
      have e : ((lgv (Yn + rr Yn + 1) : ℝ) - lgErr - LN2 - ln2Err) / 2 ^ 64 =
          ((lgv (Yn + rr Yn + 1) : ℝ) / 2 ^ 64 - lgErr / 2 ^ 64) - ((LN2 : ℝ) / 2 ^ 64 + ln2Err / 2 ^ 64) := by ring
      rw [e]; linarith
    have e : (phiLoZ Yn : ℝ) / (2 ^ 64 * 10 ^ 12) =
        ((Yn : ℝ) / 10 ^ 12) * (((lgv (Yn + rr Yn + 1) : ℝ) - lgErr - LN2 - ln2Err) / 2 ^ 64) -
          ((rr Yn : ℝ) + 1) / 10 ^ 12 := by
      unfold phiLoZ; push_cast; field_simp; rw [h64]
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hlog hY.le]
  · -- upper bound
    have a := Fs_anti hY hs0 hs1
    rw [hPhi]
    refine le_trans a ?_
    have lg := lg_enc (Yn + rr Yn) (by omega) o1
    rw [abs_le] at lg
    have hP : ((Yn : ℝ) / 10 ^ 12 + (rr Yn : ℝ) / 10 ^ 12) / 2 = (((Yn + rr Yn : ℕ) : ℝ) / 1000000000000) / 2 := by
      push_cast; ring
    have hPpos : (0 : ℝ) < ((Yn + rr Yn : ℕ) : ℝ) / 1000000000000 := by
      apply div_pos _ (by norm_num); exact Nat.cast_pos.2 (by omega)
    unfold Fs
    rw [hP, Real.log_div hPpos.ne' (by norm_num)]
    have hlog : Real.log (((Yn + rr Yn : ℕ) : ℝ) / 1000000000000) - Real.log 2 ≤
        ((lgv (Yn + rr Yn) : ℝ) + lgErr - LN2 + ln2Err) / 2 ^ 64 := by
      have := lg.2; have := l2.1
      have e : ((lgv (Yn + rr Yn) : ℝ) + lgErr - LN2 + ln2Err) / 2 ^ 64 =
          ((lgv (Yn + rr Yn) : ℝ) / 2 ^ 64 + lgErr / 2 ^ 64) - ((LN2 : ℝ) / 2 ^ 64 - ln2Err / 2 ^ 64) := by ring
      rw [e]; linarith
    have e : (phiUpZ Yn : ℝ) / (2 ^ 64 * 10 ^ 12) =
        ((Yn : ℝ) / 10 ^ 12) * (((lgv (Yn + rr Yn) : ℝ) + lgErr - LN2 + ln2Err) / 2 ^ 64) -
          (rr Yn : ℝ) / 10 ^ 12 := by
      unfold phiUpZ; push_cast; field_simp; rw [h64]
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hlog hY.le]

def normT (t : Tr) : ℕ × ℕ :=
  if 0 ≤ t.1 then (t.1.toNat, t.2.1.toNat) else ((-t.2.1).toNat, (-t.1).toNat)

def zL (t : Tr) : ℤ := phiUpZ (normT t).2 - phiLoZ (normT t).1
def evL (T : ℤ) (t : Tr) : ℤ := kk T t * zL t + |zL t|
def sL (T : ℤ) (l : List Tr) : ℤ := (l.map fun t => evL T t).sum

def okPhi (Yn : ℕ) : Bool :=
  decide (2 * 10 ^ 12 ≤ Yn) && decide (Yn + rr Yn + 1 < 2 ^ 45) && lnOK (Yn + rr Yn) && lnOK (Yn + rr Yn + 1)
def okLT (t : Tr) : Bool := okPhi (normT t).1 && okPhi (normT t).2
def okLL (l : List Tr) : Bool := l.all okLT

theorem okPhi_spec {Yn : ℕ} (h : okPhi Yn = true) :
    2 * 10 ^ 12 ≤ Yn ∧ Yn + rr Yn + 1 < 2 ^ 45 ∧ (Yn + rr Yn = 0 ∨ lnormOK (Yn + rr Yn) (10 ^ 12) = true) ∧
      (Yn + rr Yn + 1 = 0 ∨ lnormOK (Yn + rr Yn + 1) (10 ^ 12) = true) := by
  simp only [okPhi, lnOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem kappa_bd (T : ℤ) (t : Tr) (hT : 0 < T) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (kk T t : ℝ) / 2 ^ KB ≤ (t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) ∧
    (t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) ≤ ((kk T t : ℝ) + 1) / 2 ^ KB := by
  have hk := kk_bounds T t hT hv.1
  have hK : (0 : ℝ) < 2 ^ KB := by positivity
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hHL : (0 : ℝ) < (t.2.1 : ℝ) - t.1 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  constructor
  · rw [div_le_iff₀ hK]
    calc (kk T t : ℝ) ≤ _ := hk.1
      _ = _ := by field_simp
  · rw [le_div_iff₀ hK]
    calc _ = (t.2.2 : ℝ) * 2 ^ KB / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) := by field_simp
      _ ≤ _ := hk.2

theorem rho_eq (t : Tr) (T : ℤ) (hT : 0 < T) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) :
    (mkCell 1 T t).w / ((mkCell 1 T t).hi - (mkCell 1 T t).lo) =
      (t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) * 10 ^ 12 := by
  obtain ⟨hl, hh, hw⟩ := mkCell_eq hv hT.le (by norm_num : (0 : ℝ) ≤ 1)
  rw [hw, hl, hh]
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hHL : (t.2.1 : ℝ) - t.1 ≠ 0 := by
    have : (t.1 : ℝ) < t.2.1 := by exact_mod_cast hv.1
    linarith
  field_simp

theorem cell_L (t : Tr) (T : ℤ) (hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2) (hT : 0 < T)
    (haw : (0 ≤ t.1 → 2000000000000 ≤ t.1) ∧ (t.1 < 0 → t.2.1 ≤ -2000000000000))
    (o : okLT t = true) :
    -(evL T t : ℝ) / 2 ^ (KB + 64) ≤ (mkCell 1 T t).phys (fun u => Real.log |u|) := by
  unfold okLT at o
  simp only [Bool.and_eq_true] at o
  obtain ⟨oa, ob⟩ := o
  have pa := okPhi_spec oa
  have pb := okPhi_spec ob
  have ea := phi_enc _ pa.1 pa.2.1 pa.2.2.1 pa.2.2.2
  have eb := phi_enc _ pb.1 pb.2.1 pb.2.2.1 pb.2.2.2
  have rho := rho_eq t T hT hv
  have kb := kappa_bd T t hT hv
  have hK : (0 : ℝ) < 2 ^ KB := by positivity
  have hk0 : (0 : ℝ) ≤ (kk T t : ℝ) := by
    have : 0 ≤ kk T t := Int.ediv_nonneg (mul_nonneg hv.2 (by positivity)) (mul_pos hT (show 0 < t.2.1 - t.1 by omega)).le
    exact_mod_cast this
  -- Z bound
  have hZ : (phiUpZ (normT t).2 : ℝ) / (2 ^ 64 * 10 ^ 12) - (phiLoZ (normT t).1 : ℝ) / (2 ^ 64 * 10 ^ 12) ≥
      Phi (((normT t).2 : ℝ) / 10 ^ 12) - Phi (((normT t).1 : ℝ) / 10 ^ 12) := by linarith [ea.1, eb.2]
  have cast_toNat : ∀ z : ℤ, 0 ≤ z → (((z.toNat : ℕ) : ℝ)) = (z : ℝ) := fun z hz => by
    have := Int.toNat_of_nonneg hz; exact_mod_cast this
  have hph : (mkCell 1 T t).phys (fun u => Real.log |u|) =
      -((t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) * 10 ^ 12 *
        (Phi (((normT t).2 : ℝ) / 10 ^ 12) - Phi (((normT t).1 : ℝ) / 10 ^ 12))) := by
    by_cases h0 : 0 ≤ t.1
    · have hlo : 2 ≤ (mkCell 1 T t).lo := by
        rw [lo_eq hv hT]
        have : (2000000000000 : ℝ) ≤ t.1 := by exact_mod_cast haw.1 h0
        rw [le_div_iff₀ (by norm_num)]; linarith
      rw [phys_log_pos _ hlo, rho_eq t T hT hv, hi_eq hv hT, lo_eq hv hT]
      simp only [normT, if_pos h0]
      rw [cast_toNat _ h0, cast_toNat _ (by omega)]
    · have h1 : t.1 < 0 := not_le.1 h0
      have hhi : (mkCell 1 T t).hi ≤ -2 := by
        rw [hi_eq hv hT]
        have : (t.2.1 : ℝ) ≤ -2000000000000 := by exact_mod_cast haw.2 h1
        rw [div_le_iff₀ (by norm_num)]; linarith
      rw [phys_log_neg _ hhi, rho_eq t T hT hv, hi_eq hv hT, lo_eq hv hT]
      simp only [normT, if_neg h0]
      have e1 : (((-t.2.1).toNat : ℕ) : ℝ) = -(t.2.1 : ℝ) := by
        have := cast_toNat (-t.2.1) (by have := haw.2 h1; omega); push_cast at this; exact this
      have e2 : (((-t.1).toNat : ℕ) : ℝ) = -(t.1 : ℝ) := by
        have := cast_toNat (-t.1) (by omega); push_cast at this; exact this
      rw [e1, e2]
      have : (-(t.2.1 : ℝ)) / 10 ^ 12 = -((t.2.1 : ℝ) / 10 ^ 12) := by ring
      have : (-(t.1 : ℝ)) / 10 ^ 12 = -((t.1 : ℝ) / 10 ^ 12) := by ring
      simp only [*]
  rw [hph]
  set κ : ℝ := (t.2.2 : ℝ) / ((T : ℝ) * ((t.2.1 : ℝ) - t.1)) with hκ
  have hκ0 : 0 ≤ κ := le_trans (div_nonneg hk0 hK.le) kb.1
  have hS : (2 : ℝ) ^ (KB + 64) = 2 ^ KB * 2 ^ 64 := pow_add _ _ _
  have e64 : (0 : ℝ) < 2 ^ 64 := by positivity
  have hD : 10 ^ 12 * (Phi (((normT t).2 : ℝ) / 10 ^ 12) - Phi (((normT t).1 : ℝ) / 10 ^ 12)) ≤ (zL t : ℝ) / 2 ^ 64 := by
    unfold zL; push_cast
    have : (phiUpZ (normT t).2 : ℝ) / (2 ^ 64 * 10 ^ 12) - (phiLoZ (normT t).1 : ℝ) / (2 ^ 64 * 10 ^ 12) =
        ((phiUpZ (normT t).2 : ℝ) - phiLoZ (normT t).1) / 2 ^ 64 / 10 ^ 12 := by ring
    rw [this] at hZ
    have h12 : (0 : ℝ) < 10 ^ 12 := by norm_num
    rw [ge_iff_le, le_div_iff₀ h12] at hZ
    linarith
  have hup := prod_up (κ := κ) (k := (kk T t : ℝ)) (K := 2 ^ KB) hK hk0 kb.1 kb.2 hD
  have hmul : κ * 10 ^ 12 * (Phi (((normT t).2 : ℝ) / 10 ^ 12) - Phi (((normT t).1 : ℝ) / 10 ^ 12)) ≤
      κ * ((zL t : ℝ) / 2 ^ 64) := by
    have := mul_le_mul_of_nonneg_left hD hκ0
    nlinarith
  have hfin : (evL T t : ℝ) / 2 ^ (KB + 64) = ((kk T t : ℝ) * ((zL t : ℝ) / 2 ^ 64) + |(zL t : ℝ) / 2 ^ 64|) / 2 ^ KB := by
    unfold evL; push_cast
    rw [hS, abs_div, abs_of_pos e64]; field_simp
  have : -(evL T t : ℝ) / 2 ^ (KB + 64) = -((evL T t : ℝ) / 2 ^ (KB + 64)) := by ring
  rw [this, hfin]
  linarith

theorem L_lower (T : ℤ) (hT : 0 < T) : ∀ l : List Tr,
    (∀ t ∈ l, (t.1 < t.2.1 ∧ 0 ≤ t.2.2) ∧
      ((0 ≤ t.1 → 2000000000000 ≤ t.1) ∧ (t.1 < 0 → t.2.1 ≤ -2000000000000))) →
    okLL l = true →
    -(sL T l : ℝ) / 2 ^ (KB + 64) ≤ physL (l.map (mkCell 1 T)) (fun u => Real.log |u|)
  | [], _, _ => by simp [sL, physL]
  | t :: l, hv, ho => by
    have ih := L_lower T hT l (fun s hs => hv s (List.mem_cons_of_mem _ hs))
      (by simp only [okLL, List.all_cons, Bool.and_eq_true] at ho; exact ho.2)
    have h1 := cell_L t T (hv t List.mem_cons_self).1 hT (hv t List.mem_cons_self).2
      (by simp only [okLL, List.all_cons, Bool.and_eq_true] at ho; exact ho.1)
    simp only [List.map_cons, physL, sL, List.sum_cons] at ih ⊢
    simp only [Int.cast_add, neg_add, add_div]
    linarith

theorem Lq_proved (hok : okLL row0 = true) (hq : Lq ≤ -(sL Trw row0 : ℚ) / 2 ^ (KB + 64)) :
    ((Lq : ℚ) : ℝ) ≤ physL (capSource.refRow 0) (fun u => Real.log |u|) := by
  rw [refRow0]
  have h := L_lower Trw Trw_pos row0 (fun t ht => ⟨row0_ok t ht, row0_away t ht⟩) hok
  refine le_trans ?_ h
  have : ((Lq : ℚ) : ℝ) ≤ ((-(sL Trw row0 : ℚ) / 2 ^ (KB + 64) : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at this
  linarith

/-! ### Certificates: one real unit and the constant `L_cert` -/

def ch (l : List Tr) (a b : ℕ) : List Tr := (l.drop a).take b

theorem sUp_append (T : ℤ) (l1 l2 : List Tr) (M X : ℤ) :
    sUp T (l1 ++ l2) M X = sUp T l1 M X + sUp T l2 M X := by
  simp [sUp, List.map_append, List.sum_append]
theorem sLo_append (T : ℤ) (l1 l2 : List Tr) (M X : ℤ) :
    sLo T (l1 ++ l2) M X = sLo T l1 M X + sLo T l2 M X := by
  simp [sLo, List.map_append, List.sum_append]
theorem sL_append (T : ℤ) (l1 l2 : List Tr) : sL T (l1 ++ l2) = sL T l1 + sL T l2 := by
  simp [sL, List.map_append, List.sum_append]
theorem okL_append (l1 l2 : List Tr) (M : ℤ) : okL (l1 ++ l2) M = (okL l1 M && okL l2 M) := by
  simp [okL, List.all_append]
theorem okLL_append (l1 l2 : List Tr) : okLL (l1 ++ l2) = (okLL l1 && okLL l2) := by
  simp [okLL, List.all_append]

theorem colsplit : col0.take 300 ++ col0.drop 301 =
    ch col0 0 150 ++ ch col0 150 150 ++ ch col0 301 164 ++ ch col0 465 163 := by
  -- kcost: list equality, 627 triples compared
  decide +kernel
theorem rowsplit : row0 = ch row0 0 176 ++ ch row0 176 176 ++ ch row0 352 176 ++ ch row0 528 176 := by
  -- kcost: list equality, 704 triples compared
  decide +kernel
theorem hd300 : col0.drop 300 = (667727272727, (671454545455, 2460244217)) :: col0.drop 301 := by
  -- kcost: structural
  decide +kernel

theorem c_sUp_a0 : sUp Tc (ch col0 0 150) 667843749999 667727272727 = -406497307776972592694189886602402564083167128193442565662 := by
  -- kcost: sUp over 150 cells, ~300 logs, measured below
  decide +kernel
theorem c_sUp_a1 : sUp Tc (ch col0 150 150) 667843749999 667727272727 = -3552598058962604302455348208884893843138839209129003714666 := by
  -- kcost: sUp over 150 cells, ~300 logs, measured below
  decide +kernel
theorem c_sUp_a2 : sUp Tc (ch col0 301 164) 667843749999 667727272727 = -3430288477802714669348516605485415570912081249413271258466 := by
  -- kcost: sUp over 164 cells, ~328 logs, measured below
  decide +kernel
theorem c_sUp_a3 : sUp Tc (ch col0 465 163) 667843749999 667727272727 = -1576389960918743263757240692660005420171297400664231374876 := by
  -- kcost: sUp over 163 cells, ~326 logs, measured below
  decide +kernel
theorem c_iUp_a : evUp Tc (667727272727, (671454545455, 2460244217)) 667727272727 667727272727 = -101802808447062735321393942787542833178947780216814192544 := by
  -- kcost: one cell
  decide +kernel
theorem c_sLo_a0 : sLo Trw (ch row0 0 176) (2 * 667727272727) (2 * 667727272727) = 2590966977715443414172945350225242787673208235791253041078 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_a1 : sLo Trw (ch row0 176 176) (2 * 667727272727) (2 * 667727272727) = 634106733260049955044642459785298154254902387970646378946 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_a2 : sLo Trw (ch row0 352 176) (2 * 667727272727) (2 * 667727272727) = -504854609442543847680669252102602030624914636197468200846 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_a3 : sLo Trw (ch row0 528 176) (2 * 667727272727) (2 * 667727272727) = 1225066252673673575455262835878707124431786145571625093160 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sUp_b0 : sUp Tc (ch col0 0 150) 667843749999 667960227272 = -406180336105870095690463068746996517378503924195684490112 := by
  -- kcost: sUp over 150 cells, ~300 logs, measured below
  decide +kernel
theorem c_sUp_b1 : sUp Tc (ch col0 150 150) 667843749999 667960227272 = -3544565225039473773594847476797066708272384604254923567696 := by
  -- kcost: sUp over 150 cells, ~300 logs, measured below
  decide +kernel
theorem c_sUp_b2 : sUp Tc (ch col0 301 164) 667843749999 667960227272 = -3435186887290403871321947154429603925025567965196352592796 := by
  -- kcost: sUp over 164 cells, ~328 logs, measured below
  decide +kernel
theorem c_sUp_b3 : sUp Tc (ch col0 465 163) 667843749999 667960227272 = -1577398466184899883674729340770620127661885575521910571616 := by
  -- kcost: sUp over 163 cells, ~326 logs, measured below
  decide +kernel
theorem c_iUp_b : evUp Tc (667727272727, (671454545455, 2460244217)) 667960227272 667960227272 = -105413300565052394322343382698397232667939200369022370680 := by
  -- kcost: one cell
  decide +kernel
theorem c_sLo_b0 : sLo Trw (ch row0 0 176) (2 * 667960227272) (2 * 667960227272) = 2591137283620261714911335473810585049068496157356783847066 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_b1 : sLo Trw (ch row0 176 176) (2 * 667960227272) (2 * 667960227272) = 633975837491670366741388792866809474904388742194663481912 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_b2 : sLo Trw (ch row0 352 176) (2 * 667960227272) (2 * 667960227272) = -505816340867971434377552550496105402182865510450178132316 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sLo_b3 : sLo Trw (ch row0 528 176) (2 * 667960227272) (2 * 667960227272) = 1224369498548980034446782214303153744478846293402839855472 := by
  -- kcost: sLo over 176 cells
  decide +kernel
theorem c_sL_0 : sL Trw (ch row0 0 176) = 1739341987427607037067100715833820508898249716350086096022 := by
  -- kcost: sL over 176 cells
  decide +kernel
theorem c_okLL_0 : okLL (ch row0 0 176) = true := by
  -- kcost: okLL over 176 cells
  decide +kernel
theorem c_sL_1 : sL Trw (ch row0 176 176) = 120301312286119766523795040376001875305005252623785486682 := by
  -- kcost: sL over 176 cells
  decide +kernel
theorem c_okLL_1 : okLL (ch row0 176 176) = true := by
  -- kcost: okLL over 176 cells
  decide +kernel
theorem c_sL_2 : sL Trw (ch row0 352 176) = 267679755982707922111157431480564392359800071669330595582 := by
  -- kcost: sL over 176 cells
  decide +kernel
theorem c_okLL_2 : okLL (ch row0 352 176) = true := by
  -- kcost: okLL over 176 cells
  decide +kernel
theorem c_sL_3 : sL Trw (ch row0 528 176) = 2207286762198052940717377138686859364704037843356638257364 := by
  -- kcost: sL over 176 cells
  decide +kernel
theorem c_okLL_3 : okLL (ch row0 528 176) = true := by
  -- kcost: okLL over 176 cells
  decide +kernel
theorem c_okc_0 : okL (ch col0 0 150) 667843749999 = true := by
  -- kcost: okL over 150 cells
  decide +kernel
theorem c_okc_1 : okL (ch col0 150 150) 667843749999 = true := by
  -- kcost: okL over 150 cells
  decide +kernel
theorem c_okc_2 : okL (ch col0 301 164) 667843749999 = true := by
  -- kcost: okL over 164 cells
  decide +kernel
theorem c_okc_3 : okL (ch col0 465 163) 667843749999 = true := by
  -- kcost: okL over 163 cells
  decide +kernel
theorem c_okr_a0 : okL (ch row0 0 176) (2 * 667727272727) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_a1 : okL (ch row0 176 176) (2 * 667727272727) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_a2 : okL (ch row0 352 176) (2 * 667727272727) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_a3 : okL (ch row0 528 176) (2 * 667727272727) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_b0 : okL (ch row0 0 176) (2 * 667960227272) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_b1 : okL (ch row0 176 176) (2 * 667960227272) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_b2 : okL (ch row0 352 176) (2 * 667960227272) = true := by
  -- kcost: okL over 176 cells
  decide +kernel
theorem c_okr_b3 : okL (ch row0 528 176) (2 * 667960227272) = true := by
  -- kcost: okL over 176 cells
  decide +kernel

theorem hv1 : sUp Tc (col0.take 300 ++ col0.drop 301) 667843749999 667727272727 = -8965773805461034828255295393632717398305384987399948913670 := by
  rw [colsplit]; simp only [sUp_append]; rw [c_sUp_a0, c_sUp_a1, c_sUp_a2, c_sUp_a3]; norm_num
theorem hv2 : sUp Tc (col0.take 300 ++ col0.drop 301) 667843749999 667960227272 = -8963330914620647624281987040744287278338342069168871222220 := by
  rw [colsplit]; simp only [sUp_append]; rw [c_sUp_b0, c_sUp_b1, c_sUp_b2, c_sUp_b3]; norm_num
theorem hv5 : sLo Trw row0 (2 * 667727272727) (2 * 667727272727) = 3945285354206623096992181393786646035734982133136056312338 := by
  rw [rowsplit]; simp only [sLo_append]; rw [c_sLo_a0, c_sLo_a1, c_sLo_a2, c_sLo_a3]; norm_num
theorem hv6 : sLo Trw row0 (2 * 667960227272) (2 * 667960227272) = 3943666278792940681721953930484442866268865682504109052134 := by
  rw [rowsplit]; simp only [sLo_append]; rw [c_sLo_b0, c_sLo_b1, c_sLo_b2, c_sLo_b3]; norm_num
theorem o1 : okL (col0.take 300 ++ col0.drop 301) 667843749999 = true := by
  rw [colsplit]; simp only [okL_append, c_okc_0, c_okc_1, c_okc_2, c_okc_3]; rfl
theorem o4 : okL row0 (2 * 667727272727) = true := by
  rw [rowsplit]; simp only [okL_append, c_okr_a0, c_okr_a1, c_okr_a2, c_okr_a3]; rfl
theorem o5 : okL row0 (2 * 667960227272) = true := by
  rw [rowsplit]; simp only [okL_append, c_okr_b0, c_okr_b1, c_okr_b2, c_okr_b3]; rfl
theorem okLLrow : okLL row0 = true := by
  rw [rowsplit]; simp only [okLL_append, c_okLL_0, c_okLL_1, c_okLL_2, c_okLL_3]; rfl
theorem sLrow : sL Trw row0 = 4334609817894487666419430326377246141267092883999840435650 := by
  rw [rowsplit]; simp only [sL_append]; rw [c_sL_0, c_sL_1, c_sL_2, c_sL_3]; norm_num
theorem L_cert : ((Lq : ℚ) : ℝ) ≤ physL (capSource.refRow 0) (fun u => Real.log |u|) :=
  Lq_proved okLLrow (by rw [sLrow]; norm_num [Lq, KB])
theorem lite300 : unitLite 300 (667727272727, (671454545455, 2460244217)) (col0.drop 301) 667727272727 667960227272 667843749999
    (-8965773805461034828255295393632717398305384987399948913670) (-8963330914620647624281987040744287278338342069168871222220) (-101802808447062735321393942787542833178947780216814192544) (-105413300565052394322343382698397232667939200369022370680) (3945285354206623096992181393786646035734982133136056312338) (3943666278792940681721953930484442866268865682504109052134) = true := by
  -- kcost: structural list checks over 627 and 704 cells plus two rational comparisons
  decide +kernel
theorem o2 : okT (667727272727, (671454545455, 2460244217)) 667727272727 = true := by
  -- kcost: one cell, two logs
  decide +kernel
theorem o3 : okT (667727272727, (671454545455, 2460244217)) 667960227272 = true := by
  -- kcost: one cell, two logs
  decide +kernel
theorem unit300 : ∀ s : ℝ, ((667727272727 : ℤ) : ℝ) / 10 ^ 12 ≤ s → s ≤ ((667960227272 : ℤ) : ℝ) / 10 ^ 12 →
    capSource.colField 0 s ≤ ((cq : ℚ) : ℝ) := fun s h1 h2 =>
  unit_cap L_cert hd300 hv1 hv2 c_iUp_a c_iUp_b hv5 hv6 o1 o2 o3 o4 o5 lite300 h1 h2



/-! ### Cover consumer -/

def UnitCap (u : ℤ × ℤ) : Prop :=
  ∀ s : ℝ, (u.1 : ℝ) / 10 ^ 12 ≤ s → s ≤ (u.2 : ℝ) / 10 ^ 12 →
    capSource.colField 0 s ≤ ((cq : ℚ) : ℝ)

/-- `chain a us b`: the unit intervals `[u.1, u.2]` tile `[a, b]` without gaps. -/
def chain : ℤ → List (ℤ × ℤ) → ℤ → Bool
  | _, [], _ => false
  | a, [u], b => decide (u.1 = a ∧ u.2 = b)
  | a, u :: v :: us, b => decide (u.1 = a) && chain u.2 (v :: us) b

theorem chain_sound : ∀ (us : List (ℤ × ℤ)) (a b : ℤ), chain a us b = true →
    (∀ u ∈ us, UnitCap u) → ∀ s : ℝ, (a : ℝ) / 10 ^ 12 ≤ s → s ≤ (b : ℝ) / 10 ^ 12 →
      capSource.colField 0 s ≤ ((cq : ℚ) : ℝ)
  | [], a, b, h, _, s, _, _ => by simp [chain] at h
  | [u], a, b, h, hu, s, h1, h2 => by
    simp only [chain, decide_eq_true_eq] at h
    exact hu u (by simp) s (by rw [h.1]; exact h1) (by rw [h.2]; exact h2)
  | u :: v :: us, a, b, h, hu, s, h1, h2 => by
    simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hs : s ≤ (u.2 : ℝ) / 10 ^ 12
    · exact hu u (by simp) s (by rw [h.1]; exact h1) hs
    · exact chain_sound (v :: us) u.2 b h.2 (fun w hw => hu w (List.mem_cons_of_mem _ hw)) s
        (le_of_lt (not_le.1 hs)) h2

theorem cq_eq : ((cq : ℚ) : ℝ) = -2946610 / 1000000 := by norm_num [cq]

/-- **Generic consumer.** A chain of certified units tiling `[a,b]`, and the two end ranges, give the
`hC` input of T4 for the anchor-0 free column. -/
theorem freeColCap0_of_cover (a b : ℤ) (us : List (ℤ × ℤ)) (hch : chain a us b = true)
    (hu : ∀ u ∈ us, UnitCap u)
    (hLeft : ∀ s : ℝ, 0 < s → s ≤ (a : ℝ) / 10 ^ 12 → capSource.colField 0 s ≤ ((cq : ℚ) : ℝ))
    (hRight : ∀ s : ℝ, (b : ℝ) / 10 ^ 12 ≤ s → s < 1 → capSource.colField 0 s ≤ ((cq : ℚ) : ℝ)) :
    capSource.FreeColCap 0 (-2946610 / 1000000) := by
  intro s hs
  rw [← cq_eq]
  by_cases h1 : s ≤ (a : ℝ) / 10 ^ 12
  · exact hLeft s hs.1 h1
  by_cases h2 : (b : ℝ) / 10 ^ 12 ≤ s
  · exact hRight s h2 hs.2
  exact chain_sound us a b hch hu s (le_of_lt (not_le.1 h1)) (le_of_lt (not_le.1 h2))

theorem unit300_cap : UnitCap (667727272727, 667960227272) := unit300

#print axioms unit300_cap
#print axioms L_cert
#print axioms freeColCap0_of_cover

end

end CatalanMeasure.GenD.Signed.RouteI.FreeColCap0

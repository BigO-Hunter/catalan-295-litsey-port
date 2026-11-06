module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Algebra.Field.GeomSum
public import CatalanMeasure.GenD.Signed.RouteI.CapFields

@[expose] public section
set_option Elab.async false

/-!
# Route I `MomentSource` (plan row C8): exact positive-bin source primitives and the Jensen gas bound

Data-free theorem side, stated over the `CapFields` source record.

* `vY` is the smaller root of `x^2 - Y x + 1`; `CapFields.YCell.physX` equals `vY` on `Y >= 2`
  (`physX_pos`) and `-vY (-Y)` on `Y <= -2` (`physX_neg`).
* `integral_vY`, `integral_vY_sq`, `phys_one`, `phys_id`, `phys_sq`: exact primitives
  `H1 = log x - x^2/2`, `H2 = x - x^3/3` of the mass and first two physical moments of a uniform
  `Y`-cell (the generic source identity of `C8-MOMENT-SOURCE-IDENTITY.md`, no change of variables).
* `CellCut`, `Partitioned`: finite additivity over cuts of source cells and regrouping into bins.
* `bin_cone`: strict moment cone `A^2 < m B` of a nonempty bin of positive-mass cells.
* `logPoly_nonpos`: for odd `n` and `z < 1`, `log (1 - z) <= -sum_{k<=n} z^k/k`.
* `intervalIntegrable_logQ`: `log (a - 2 b u x + c x^2)` is integrable along a cell, including the
  logarithmic singularity at `u = +-1`.
* `bin_jensen`, `gas_bins_jensen`: tangent (Jensen) bound of a bin and its sum over a partition.
* `gasPart_pos_le`, `gasPart_neg_le`: the bound for the gas part (`gasPart`) of `CapSource.angular`
  (direct term; for the negative species also the mirror term, through `reflectL`).
* `alpha_perturb`, `binAlpha_mem`, `H1_approx`, `H2_approx`, `cell_A_err`, `cell_B_err`,
  `bin_moment_err`: the input-error consumer (primitive evaluation, moment and alpha perturbation).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MomentSource


open Real Set intervalIntegral MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CapFields
noncomputable section

/-- smaller root `v(Y) = (Y - sqrt(Y^2-4))/2` of `x^2 - Y x + 1`. -/
def vY (Y : ℝ) : ℝ := (Y - √(Y ^ 2 - 4)) / 2

@[fun_prop] lemma vY_continuous : Continuous vY := by
  unfold vY; fun_prop

lemma sq_sqrt_aux {Y : ℝ} (hY : 2 ≤ Y) : √(Y ^ 2 - 4) ^ 2 = Y ^ 2 - 4 :=
  Real.sq_sqrt (by nlinarith)

lemma sqrt_lt_aux {Y : ℝ} (hY : 2 ≤ Y) : √(Y ^ 2 - 4) < Y := by
  rw [Real.sqrt_lt' (by linarith)]; nlinarith

lemma vY_pos {Y : ℝ} (hY : 2 ≤ Y) : 0 < vY Y := by
  unfold vY; linarith [sqrt_lt_aux hY]

lemma vY_le_one {Y : ℝ} (hY : 2 ≤ Y) : vY Y ≤ 1 := by
  have h0 := Real.sqrt_nonneg (Y ^ 2 - 4)
  have h2 := sq_sqrt_aux hY
  have hv := vY_pos hY
  -- v = 2/(Y+s) <= 1
  have : vY Y * (Y + √(Y ^ 2 - 4)) = 2 := by unfold vY; nlinarith
  nlinarith

/-- `v + 1/v = Y`. -/
lemma vY_add_inv {Y : ℝ} (hY : 2 ≤ Y) : vY Y + (vY Y)⁻¹ = Y := by
  have hv := vY_pos hY
  have h2 := sq_sqrt_aux hY
  field_simp
  unfold vY; nlinarith

lemma vY_mul {Y : ℝ} (hY : 2 ≤ Y) : vY Y * (Y + √(Y ^ 2 - 4)) = 2 := by
  unfold vY; nlinarith [sq_sqrt_aux hY]

lemma physX_pos {Y : ℝ} (hY : 2 ≤ Y) : YCell.physX Y = vY Y := by
  unfold YCell.physX
  have h0 : (0:ℝ) ≤ Y := by linarith
  simp only [h0, ↓reduceIte]
  have h := vY_mul hY
  have hs := Real.sqrt_nonneg (Y ^ 2 - 4)
  have : 0 < Y + √(Y ^ 2 - 4) := by linarith
  field_simp
  linarith

lemma physX_neg {Y : ℝ} (hY : Y ≤ -2) : YCell.physX Y = -vY (-Y) := by
  unfold YCell.physX
  have h0 : ¬ (0:ℝ) ≤ Y := by linarith
  simp only [h0, ↓reduceIte]
  have h := vY_mul (Y := -Y) (by linarith)
  have hs := Real.sqrt_nonneg (Y ^ 2 - 4)
  have e : (-Y) ^ 2 - 4 = Y ^ 2 - 4 := by ring
  rw [e] at h
  have : 0 < -Y + √(Y ^ 2 - 4) := by linarith
  field_simp
  linarith

/-- derivative of `v` at `Y > 2`. -/
lemma vY_hasDerivAt {Y : ℝ} (hY : 2 < Y) :
    HasDerivAt vY (-(vY Y) / √(Y ^ 2 - 4)) Y := by
  have hpos : 0 < Y ^ 2 - 4 := by nlinarith
  have hs : 0 < √(Y ^ 2 - 4) := Real.sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 4) (2 * Y) Y := by
    simpa using ((hasDerivAt_pow 2 Y).sub_const 4)
  have h2 := h1.sqrt hpos.ne'
  have h3 : HasDerivAt vY ((1 - 2 * Y / (2 * √(Y ^ 2 - 4))) / 2) Y :=
    ((hasDerivAt_id Y).sub h2).div_const 2
  refine h3.congr_deriv ?_
  unfold vY
  field_simp
  ring

def H1 (x : ℝ) : ℝ := Real.log x - x ^ 2 / 2
def H2 (x : ℝ) : ℝ := x - x ^ 3 / 3

lemma vY_quad {Y : ℝ} (hY : 2 ≤ Y) : vY Y ^ 2 = Y * vY Y - 1 := by
  have h := vY_add_inv hY
  have hv := vY_pos hY
  field_simp at h
  nlinarith

lemma vY_sqrt_eq {Y : ℝ} (hY : 2 ≤ Y) : vY Y * √(Y ^ 2 - 4) = 2 - Y * vY Y := by
  have h := vY_mul hY
  nlinarith

lemma H1_comp_hasDerivAt {Y : ℝ} (hY : 2 < Y) :
    HasDerivAt (fun y => H1 (vY y)) (-(vY Y)) Y := by
  have hv := vY_pos hY.le
  have hs : 0 < √(Y ^ 2 - 4) := Real.sqrt_pos.2 (by nlinarith)
  have h := (vY_hasDerivAt hY)
  have h2 := (h.log hv.ne').sub ((h.pow 2).div_const 2)
  refine h2.congr_deriv ?_
  have q := vY_quad hY.le
  have e := vY_sqrt_eq hY.le
  norm_num
  field_simp
  nlinarith

lemma H2_comp_hasDerivAt {Y : ℝ} (hY : 2 < Y) :
    HasDerivAt (fun y => H2 (vY y)) (-(vY Y ^ 2)) Y := by
  have hv := vY_pos hY.le
  have hs : 0 < √(Y ^ 2 - 4) := Real.sqrt_pos.2 (by nlinarith)
  have h := (vY_hasDerivAt hY)
  have h2 := h.sub ((h.pow 3).div_const 3)
  refine h2.congr_deriv ?_
  have q := vY_quad hY.le
  have e := vY_sqrt_eq hY.le
  norm_num
  field_simp
  nlinarith

lemma vY_contOn {a b : ℝ} (ha : 2 ≤ a) : ContinuousOn vY (Icc a b) := vY_continuous.continuousOn

lemma integral_vY {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ Y in a..b, vY Y = H1 (vY a) - H1 (vY b) := by
  have hc : ContinuousOn (fun y => H1 (vY y)) (Icc a b) := by
    intro y hy
    have hv := vY_pos (le_trans ha hy.1)
    unfold H1
    exact ((vY_continuous.continuousAt.log hv.ne').sub
      ((vY_continuous.continuousAt.pow 2).div_const 2)).continuousWithinAt
  have hd : ∀ y ∈ Ioo a b, HasDerivAt (fun y => H1 (vY y)) (-(vY y)) y :=
    fun y hy => H1_comp_hasDerivAt (lt_of_le_of_lt ha hy.1)
  have := integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    (vY_continuous.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at this
  linarith

lemma integral_vY_sq {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ Y in a..b, vY Y ^ 2 = H2 (vY a) - H2 (vY b) := by
  have hc : ContinuousOn (fun y => H2 (vY y)) (Icc a b) := by
    unfold H2
    exact (vY_continuous.sub ((vY_continuous.pow 3).div_const 3)).continuousOn
  have hd : ∀ y ∈ Ioo a b, HasDerivAt (fun y => H2 (vY y)) (-(vY y ^ 2)) y :=
    fun y hy => H2_comp_hasDerivAt (lt_of_le_of_lt ha hy.1)
  have := integral_eq_sub_of_hasDerivAt_of_le hab hc hd
    ((vY_continuous.pow 2).neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at this
  linarith

lemma vY_injOn : InjOn vY (Ici 2) := by
  intro x hx y hy h
  have a := vY_add_inv (Y := x) hx
  have b := vY_add_inv (Y := y) hy
  rw [← a, ← b, h]

/-- cell integral in the `v` coordinate (positive cells). -/
lemma phys_pos {c : YCell} (h : 2 ≤ c.lo) (f : ℝ → ℝ) :
    c.phys f = c.w / (c.hi - c.lo) * ∫ Y in c.lo..c.hi, f (vY Y) := by
  unfold YCell.phys YCell.avg
  congr 1
  apply intervalIntegral.integral_congr
  intro Y hY
  rw [uIcc_of_le c.lo_lt.le] at hY
  simp only [physX_pos (le_trans h hY.1)]

lemma phys_one {c : YCell} : c.phys (fun _ => 1) = c.w := by
  unfold YCell.phys YCell.avg
  have : c.hi - c.lo ≠ 0 := by linarith [c.lo_lt]
  simp [this]

lemma phys_id {c : YCell} (h : 2 ≤ c.lo) :
    c.phys id = c.w / (c.hi - c.lo) * (H1 (vY c.lo) - H1 (vY c.hi)) := by
  rw [phys_pos h]; simp only [id]; rw [integral_vY h c.lo_lt.le]

lemma phys_sq {c : YCell} (h : 2 ≤ c.lo) :
    c.phys (fun x => x ^ 2) = c.w / (c.hi - c.lo) * (H2 (vY c.lo) - H2 (vY c.hi)) := by
  rw [phys_pos h]; rw [integral_vY_sq h c.lo_lt.le]

/-- reflection of a negative cell. -/
def _root_.CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell.reflect (c : YCell) : YCell :=
  ⟨-c.hi, -c.lo, c.w, by linarith [c.lo_lt], c.w_nonneg⟩

lemma phys_reflect {c : YCell} (h : c.hi ≤ -2) (f : ℝ → ℝ) :
    c.phys f = c.reflect.phys (fun x => f (-x)) := by
  unfold YCell.phys YCell.avg YCell.reflect
  have e : -c.lo - -c.hi = c.hi - c.lo := by ring
  simp only [e]
  congr 1
  have h1 : ∫ Y in c.lo..c.hi, f (YCell.physX Y) = ∫ Y in c.lo..c.hi, f (-vY (-Y)) := by
    apply intervalIntegral.integral_congr
    intro Y hY
    rw [uIcc_of_le c.lo_lt.le] at hY
    simp only [physX_neg (le_trans hY.2 h)]
  have h2 := intervalIntegral.integral_comp_neg (a := c.lo) (b := c.hi) (fun Y => f (-vY Y))
  have h3 : ∫ Y in -c.hi..-c.lo, f (-YCell.physX Y) = ∫ Y in -c.hi..-c.lo, f (-vY Y) := by
    apply intervalIntegral.integral_congr
    intro Y hY
    rw [uIcc_of_le (by linarith [c.lo_lt])] at hY
    simp only [physX_pos (le_trans (by linarith) hY.1)]
  rw [h1, h3, ← h2]

/-- the quadratic `a - 2 b u x + c x^2` whose logarithm is integrated. -/
def Qf (a b c u x : ℝ) : ℝ := a - 2 * b * u * x + c * x ^ 2

lemma Qf_nonneg {a b c u : ℝ} (hc : 0 < c) (hb : b ^ 2 * u ^ 2 ≤ a * c) (x : ℝ) :
    0 ≤ Qf a b c u x := by
  unfold Qf
  have : 0 ≤ (c * x - b * u) ^ 2 + (a * c - b ^ 2 * u ^ 2) := by nlinarith [sq_nonneg (c * x - b * u)]
  have h2 : c * (a - 2 * b * u * x + c * x ^ 2) = (c * x - b * u) ^ 2 + (a * c - b ^ 2 * u ^ 2) := by ring
  by_contra hneg
  push_neg at hneg
  nlinarith

lemma Qf_eq_zero {a b c u x : ℝ} (hc : 0 < c) (hb : b ^ 2 * u ^ 2 ≤ a * c)
    (h : Qf a b c u x = 0) : c * x = b * u := by
  unfold Qf at h
  have h2 : c * (a - 2 * b * u * x + c * x ^ 2) = (c * x - b * u) ^ 2 + (a * c - b ^ 2 * u ^ 2) := by ring
  rw [h] at h2
  have : (c * x - b * u) ^ 2 = 0 := by nlinarith [sq_nonneg (c * x - b * u)]
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

lemma phys_quad {cl : YCell} (h : 2 ≤ cl.lo) (a b c u : ℝ) :
    cl.phys (Qf a b c u) = a * cl.w - 2 * b * u * cl.phys id + c * cl.phys (fun x => x ^ 2) := by
  have hne : cl.hi - cl.lo ≠ 0 := by linarith [cl.lo_lt]
  have i1 : IntervalIntegrable (fun Y => vY Y) volume cl.lo cl.hi := vY_continuous.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun Y => vY Y ^ 2) volume cl.lo cl.hi :=
    (vY_continuous.pow 2).intervalIntegrable _ _
  have i0 : IntervalIntegrable (fun _ : ℝ => a) volume cl.lo cl.hi := intervalIntegrable_const
  have e : ∫ Y in cl.lo..cl.hi, Qf a b c u (vY Y) =
      a * (cl.hi - cl.lo) - 2 * b * u * (∫ Y in cl.lo..cl.hi, vY Y) +
        c * (∫ Y in cl.lo..cl.hi, vY Y ^ 2) := by
    have : (fun Y => Qf a b c u (vY Y)) = fun Y => (a - (2 * b * u) * vY Y) + c * vY Y ^ 2 := by
      funext Y; unfold Qf; ring
    rw [this, intervalIntegral.integral_add (i0.sub (i1.const_mul _)) (i2.const_mul _),
      intervalIntegral.integral_sub i0 (i1.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    simp
    ring
  rw [phys_pos h, e, phys_pos h, phys_pos h]
  simp only [id]
  field_simp

/-- cell Jensen (tangent) inequality. -/
lemma cell_tangent {cl : YCell} (h : 2 ≤ cl.lo) {a b c u t : ℝ} (hc : 0 < c)
    (hb : b ^ 2 * u ^ 2 ≤ a * c) (ht : 0 < t)
    (hint : IntervalIntegrable (fun Y => Real.log (Qf a b c u (vY Y))) volume cl.lo cl.hi) :
    cl.phys (fun x => Real.log (Qf a b c u x)) ≤
      cl.w * Real.log t + cl.phys (Qf a b c u) / t - cl.w := by
  have hne : cl.hi - cl.lo ≠ 0 := by linarith [cl.lo_lt]
  have hpos : 0 < cl.hi - cl.lo := by linarith [cl.lo_lt]
  have iQ : IntervalIntegrable (fun Y => Qf a b c u (vY Y)) volume cl.lo cl.hi := by
    have : Continuous fun Y => Qf a b c u (vY Y) := by unfold Qf; fun_prop
    exact this.intervalIntegrable _ _
  have iR : IntervalIntegrable (fun Y => Real.log t + Qf a b c u (vY Y) / t - 1) volume cl.lo cl.hi :=
    ((intervalIntegrable_const.add (iQ.div_const t)).sub intervalIntegrable_const)
  have hmono : ∫ Y in cl.lo..cl.hi, Real.log (Qf a b c u (vY Y)) ≤
      ∫ Y in cl.lo..cl.hi, (Real.log t + Qf a b c u (vY Y) / t - 1) := by
    apply intervalIntegral.integral_mono_ae_restrict cl.lo_lt.le hint iR
    -- exceptional set is a single point
    have hZ : {Y : ℝ | 2 ≤ Y ∧ Qf a b c u (vY Y) = 0}.Subsingleton := by
      intro Y1 h1 Y2 h2
      have e1 := Qf_eq_zero hc hb h1.2
      have e2 := Qf_eq_zero hc hb h2.2
      exact vY_injOn (mem_Ici.2 h1.1) (mem_Ici.2 h2.1) (by
        have : c * vY Y1 = c * vY Y2 := by rw [e1, e2]
        exact mul_left_cancel₀ hc.ne' this)
    have hnull : volume {Y : ℝ | 2 ≤ Y ∧ Qf a b c u (vY Y) = 0} = 0 := hZ.measure_zero volume
    have hae : ∀ᵐ Y ∂(volume.restrict (Icc cl.lo cl.hi)), ¬ (2 ≤ Y ∧ Qf a b c u (vY Y) = 0) := by
      apply ae_restrict_of_ae
      exact (MeasureTheory.measure_eq_zero_iff_ae_notMem).1 hnull
    have hmem : ∀ᵐ Y ∂(volume.restrict (Icc cl.lo cl.hi)), Y ∈ Icc cl.lo cl.hi :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hae, hmem] with Y hY hm
    have h2 : 2 ≤ Y := le_trans h hm.1
    have hq : Qf a b c u (vY Y) ≠ 0 := fun hz => hY ⟨h2, hz⟩
    have hq' : 0 < Qf a b c u (vY Y) := lt_of_le_of_ne (Qf_nonneg hc hb _) (Ne.symm hq)
    have := Real.log_le_sub_one_of_pos (div_pos hq' ht)
    rw [Real.log_div hq'.ne' ht.ne'] at this
    show Real.log (Qf a b c u (vY Y)) ≤ Real.log t + Qf a b c u (vY Y) / t - 1
    linarith
  have hR : ∫ Y in cl.lo..cl.hi, (Real.log t + Qf a b c u (vY Y) / t - 1) =
      (Real.log t - 1) * (cl.hi - cl.lo) + (∫ Y in cl.lo..cl.hi, Qf a b c u (vY Y)) / t := by
    have : (fun Y => Real.log t + Qf a b c u (vY Y) / t - 1) =
        fun Y => (Real.log t - 1) + (1 / t) * Qf a b c u (vY Y) := by
      funext Y; field_simp; ring
    rw [this, intervalIntegral.integral_add intervalIntegrable_const (iQ.const_mul _),
      intervalIntegral.integral_const_mul]
    simp; field_simp
  rw [phys_pos h, phys_pos h]
  rw [hR] at hmono
  have hw := cl.w_nonneg
  have key : cl.w / (cl.hi - cl.lo) * ∫ Y in cl.lo..cl.hi, Real.log (Qf a b c u (vY Y)) ≤
      cl.w / (cl.hi - cl.lo) * ((Real.log t - 1) * (cl.hi - cl.lo) +
        (∫ Y in cl.lo..cl.hi, Qf a b c u (vY Y)) / t) :=
    mul_le_mul_of_nonneg_left hmono (div_nonneg hw hpos.le)
  have : cl.w / (cl.hi - cl.lo) * ((Real.log t - 1) * (cl.hi - cl.lo) +
        (∫ Y in cl.lo..cl.hi, Qf a b c u (vY Y)) / t) =
      cl.w * Real.log t + cl.w / (cl.hi - cl.lo) * (∫ Y in cl.lo..cl.hi, Qf a b c u (vY Y)) / t - cl.w := by
    field_simp
    ring
  linarith
def logPoly (n : ℕ) (z : ℝ) : ℝ := ∑ k ∈ Finset.range n, z ^ (k + 1) / ((k : ℝ) + 1) + Real.log (1 - z)

lemma logPoly_hasDerivAt (n : ℕ) {z : ℝ} (hz : z < 1) :
    HasDerivAt (logPoly n) (-(z ^ n) / (1 - z)) z := by
  have ht : ∀ k ∈ Finset.range n, HasDerivAt (fun y : ℝ => y ^ (k + 1) / ((k : ℝ) + 1)) (z ^ k) z := by
    intro k _
    have h := ((hasDerivAt_pow (k + 1) z).div_const ((k : ℝ) + 1))
    convert h using 1
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]; push_cast; field_simp
  have hs : HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range n, y ^ (k + 1) / ((k : ℝ) + 1))
      (∑ k ∈ Finset.range n, z ^ k) z := HasDerivAt.fun_sum ht
  have hl : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - z)) z := by
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
    have := h1.log (by linarith : (1 - z) ≠ 0)
    simpa using this
  have := hs.add hl
  refine this.congr_deriv ?_
  have h1z : (1 - z) ≠ 0 := by linarith
  have g : ∑ k ∈ Finset.range n, z ^ k = (1 - z ^ n) / (1 - z) := by
    have := geom_sum_eq (x := z) (by linarith : z ≠ 1) n
    rw [this, div_eq_div_iff (by linarith : z - 1 ≠ 0) h1z]; ring
  rw [g]; field_simp; ring

lemma logPoly_nonpos {n : ℕ} (hn : Odd n) {z : ℝ} (hz : z < 1) : logPoly n z ≤ 0 := by
  have h0 : logPoly n 0 = 0 := by simp [logPoly]
  have hcont : ∀ y, y < 1 → ContinuousAt (logPoly n) y := fun y hy =>
    (logPoly_hasDerivAt n hy).continuousAt
  rcases le_total 0 z with hz0 | hz0
  · -- antitone on Ico 0 1
    have hanti : AntitoneOn (logPoly n) (Ico 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ico 0 1)
      · intro y hy; exact (hcont y hy.2).continuousWithinAt
      · intro y hy
        rw [interior_Ico] at hy
        exact (logPoly_hasDerivAt n hy.2).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ico] at hy
        rw [(logPoly_hasDerivAt n hy.2).deriv]
        have : 0 ≤ y ^ n := pow_nonneg hy.1.le n
        have : 0 < 1 - y := by linarith [hy.2]
        have : 0 ≤ y ^ n / (1 - y) := by positivity
        rw [neg_div]; linarith
    have := hanti (a := 0) (b := z) ⟨le_refl _, by norm_num⟩ ⟨hz0, hz⟩ hz0
    linarith
  · have hmono : MonotoneOn (logPoly n) (Iic 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
      · intro y hy; exact (hcont y (by have := hy; simp at this; linarith)).continuousWithinAt
      · intro y hy
        rw [interior_Iic] at hy
        exact (logPoly_hasDerivAt n (by simp at hy; linarith)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Iic] at hy
        have hy' : y < 0 := hy
        rw [(logPoly_hasDerivAt n (by linarith)).deriv]
        have : y ^ n ≤ 0 := Odd.pow_nonpos hn hy'.le
        have : 0 < 1 - y := by linarith
        have : 0 ≤ -(y ^ n) / (1 - y) := by apply div_nonneg <;> linarith
        exact this
    have := hmono (a := z) (b := 0) hz0 (by simp) hz0
    linarith

/-! ### Lists of cells -/

def PosL (l : List YCell) : Prop := ∀ c ∈ l, 2 ≤ c.lo

lemma physL_cons (c : YCell) (l : List YCell) (f : ℝ → ℝ) :
    physL (c :: l) f = c.phys f + physL l f := by simp [physL]
lemma massL_cons (c : YCell) (l : List YCell) : massL (c :: l) = c.w + massL l := by simp [massL]

lemma massL_nonneg (l : List YCell) : 0 ≤ massL l := by
  induction l with
  | nil => simp [massL]
  | cons c l ih => rw [massL_cons]; linarith [c.w_nonneg]

lemma physL_quad {l : List YCell} (hl : PosL l) (a b c u : ℝ) :
    physL l (Qf a b c u) = a * massL l - 2 * b * u * physL l id + c * physL l (fun x => x ^ 2) := by
  induction l with
  | nil => simp [physL, massL]
  | cons cl l ih =>
    have hc : 2 ≤ cl.lo := hl cl (by simp)
    rw [physL_cons, physL_cons, physL_cons, massL_cons, phys_quad hc, ih (fun d hd => hl d (by simp [hd]))]
    ring

lemma list_tangent {l : List YCell} (hl : PosL l) {a b c u t : ℝ} (hc : 0 < c)
    (hb : b ^ 2 * u ^ 2 ≤ a * c) (ht : 0 < t)
    (hint : ∀ cl ∈ l, IntervalIntegrable (fun Y => Real.log (Qf a b c u (vY Y))) volume cl.lo cl.hi) :
    physL l (fun x => Real.log (Qf a b c u x)) ≤
      massL l * Real.log t + physL l (Qf a b c u) / t - massL l := by
  induction l with
  | nil => simp [physL, massL]
  | cons cl l ih =>
    have h1 := cell_tangent (hl cl (by simp)) hc hb ht (hint cl (by simp))
    have h2 := ih (fun d hd => hl d (by simp [hd])) (fun d hd => hint d (by simp [hd]))
    rw [physL_cons, physL_cons, massL_cons]
    linarith [add_div (cl.phys (Qf a b c u)) (physL l (Qf a b c u)) t]

/-- Jensen for a positive bin with explicit mean parameters: with `m,A,B` the mass and first two
moments, `t = (a m - 2 b u A + c B)/m`, `D = a + c B / m`, `alpha = 2 b A/(m D)`. -/
theorem bin_jensen {l : List YCell} (hl : PosL l) {a b c u : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : b ^ 2 ≤ a * c) (hu : |u| ≤ 1) {n : ℕ} (hn : Odd n)
    (hm : 0 < massL l)
    (hcone : (physL l id) ^ 2 < massL l * physL l (fun x => x ^ 2))
    (hint : ∀ cl ∈ l, IntervalIntegrable (fun Y => Real.log (Qf a b c u (vY Y))) volume cl.lo cl.hi) :
    physL l (fun x => Real.log (Qf a b c u x)) ≤
      massL l * (Real.log (a + c * physL l (fun x => x ^ 2) / massL l) -
        ∑ k ∈ Finset.range n, (2 * b * physL l id / (massL l * (a + c * physL l (fun x => x ^ 2) / massL l)) * u) ^ (k + 1) / ((k : ℝ) + 1)) := by
  set m := massL l with hmdef
  set A := physL l id with hA
  set B := physL l (fun x => x ^ 2) with hB
  have hb2 : b ^ 2 * u ^ 2 ≤ a * c := by
    have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    nlinarith [sq_nonneg b]
  set D := a + c * B / m with hD
  -- positivity of the mean
  have hBm : (A / m) ^ 2 < B / m := by
    rw [div_pow, div_lt_div_iff₀ (by positivity) hm]; nlinarith
  have hDpos : 0 < D := by
    have : 0 ≤ B / m := le_trans (sq_nonneg _) hBm.le
    rw [hD]; have := mul_nonneg hc.le this; nlinarith [mul_div_assoc c B m]
  set t := (a * m - 2 * b * u * A + c * B) / m with ht
  have htD : t = D * (1 - 2 * b * A / (m * D) * u) := by
    have hD0 : D ≠ 0 := hDpos.ne'
    have hm0 : m ≠ 0 := hm.ne'
    have e1 : D * (1 - 2 * b * A / (m * D) * u) = D - 2 * b * A * u / m := by field_simp
    rw [e1, ht, hD]; field_simp; ring
  have htpos : 0 < t := by
    have e : t = a - 2 * b * u * (A / m) + c * (B / m) := by rw [ht]; field_simp
    have h1 : 0 ≤ c * (A / m - b * u / c) ^ 2 + (a - b ^ 2 * u ^ 2 / c) := by
      have : 0 ≤ a - b ^ 2 * u ^ 2 / c := by
        rw [sub_nonneg, div_le_iff₀ hc]; linarith
      positivity
    have h2 : c * (A / m - b * u / c) ^ 2 + (a - b ^ 2 * u ^ 2 / c) = a - 2 * b * u * (A / m) + c * (A / m) ^ 2 := by
      field_simp; ring
    rw [e]
    nlinarith [mul_lt_mul_of_pos_left hBm hc]
  have key := list_tangent hl hc hb2 htpos hint
  rw [physL_quad hl] at key
  have hq : a * m - 2 * b * u * A + c * B = t * m := by rw [ht]; field_simp
  have e2 : (a * massL l - 2 * b * u * physL l id + c * physL l (fun x => x ^ 2)) / t = m := by
    rw [← hmdef, ← hA, ← hB, hq]; field_simp
  rw [e2] at key
  -- log t <= log D - poly
  have hz : 2 * b * A / (m * D) * u < 1 := by
    have : 0 < 1 - 2 * b * A / (m * D) * u := by
      by_contra hneg; push_neg at hneg
      have h1 : 0 < D * (1 - 2 * b * A / (m * D) * u) := htD ▸ htpos
      have h2 := mul_nonpos_of_nonneg_of_nonpos hDpos.le (show 1 - 2 * b * A / (m * D) * u ≤ 0 by linarith)
      linarith
    linarith
  have hnp := logPoly_nonpos hn hz
  unfold logPoly at hnp
  have hlogt : Real.log t = Real.log D + Real.log (1 - 2 * b * A / (m * D) * u) := by
    rw [htD, Real.log_mul hDpos.ne' (by linarith)]
  have hlt : Real.log t ≤ Real.log D - ∑ k ∈ Finset.range n,
      (2 * b * A / (m * D) * u) ^ (k + 1) / ((k : ℝ) + 1) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlt hm.le
  rw [← hmdef] at key
  linarith

/-! ### Integrability of `log Q` along a cell (including the logarithmic singularity) -/

lemma vY_ge_inv {Y : ℝ} (hY : 2 ≤ Y) : 1 / Y ≤ vY Y := by
  have hv := vY_pos hY
  have h := vY_add_inv hY
  have : (vY Y)⁻¹ ≤ Y := by linarith
  rw [div_le_iff₀ (by linarith)]
  have := (inv_mul_cancel₀ hv.ne')
  nlinarith [inv_pos.2 hv]

/-- distance identity `(Y - Y0) v x0 = (v - x0)(v x0 - 1)` when `Y0 = x0 + 1/x0`. -/
lemma dist_identity {Y x0 : ℝ} (hY : 2 ≤ Y) (hx : 0 < x0) :
    (Y - (x0 + 1 / x0)) * vY Y * x0 = (vY Y - x0) * (vY Y * x0 - 1) := by
  have hv := vY_pos hY
  have h := vY_add_inv hY
  have key : ∀ v : ℝ, 0 < v → ((v + v⁻¹) - (x0 + 1 / x0)) * v * x0 = (v - x0) * (v * x0 - 1) := by
    intro v hv; field_simp; ring
  have := key (vY Y) hv
  rwa [h] at this

lemma intervalIntegrable_log_sq_sing {lo hi x0 : ℝ} (hlo : 2 ≤ lo) (hlh : lo ≤ hi)
    (hx0 : 0 < x0) (hx1 : x0 ≤ 1) :
    IntervalIntegrable (fun Y => Real.log ((vY Y - x0) ^ 2)) volume lo hi := by
  set Y0 := x0 + 1 / x0 with hY0
  have hG : IntervalIntegrable (fun Y => 2 * |Real.log (Y - Y0)| + 2 * Real.log (hi / x0)) volume lo hi := by
    have h1 : IntervalIntegrable (fun Y => Real.log (Y - Y0)) volume lo hi := by
      have := (intervalIntegrable_log' (a := lo - Y0) (b := hi - Y0)).comp_sub_right Y0
      simpa using this
    exact (h1.abs.const_mul 2).add intervalIntegrable_const
  have hmeas : AEStronglyMeasurable (fun Y => Real.log ((vY Y - x0) ^ 2)) (volume.restrict (uIoc lo hi)) := by
    have : Measurable (fun Y => Real.log ((vY Y - x0) ^ 2)) :=
      Real.measurable_log.comp (((vY_continuous.sub continuous_const).pow 2).measurable)
    exact this.aestronglyMeasurable
  refine hG.mono_fun' hmeas ?_
  have hne : ∀ᵐ Y ∂(volume.restrict (uIoc lo hi)), Y ∉ ({Y0} : Set ℝ) := by
    apply ae_restrict_of_ae
    exact (MeasureTheory.measure_eq_zero_iff_ae_notMem).1 (measure_singleton Y0)
  have hmem : ∀ᵐ Y ∂(volume.restrict (uIoc lo hi)), Y ∈ uIoc lo hi := ae_restrict_mem measurableSet_uIoc
  filter_upwards [hne, hmem] with Y hY hm
  rw [uIoc_of_le hlh] at hm
  have hY2 : 2 ≤ Y := le_trans hlo hm.1.le
  have hYne : Y ≠ Y0 := by simpa using hY
  have hv := vY_pos hY2
  have hv1 := vY_le_one hY2
  have hid := dist_identity (x0 := x0) hY2 hx0
  rw [← hY0] at hid
  have hvx : 0 < vY Y * x0 := mul_pos hv hx0
  have hvx1 : vY Y * x0 ≤ 1 := by nlinarith
  have hYd : 0 < |Y - Y0| := abs_pos.2 (sub_ne_zero.2 hYne)
  have hd : |Y - Y0| * (vY Y * x0) = |vY Y - x0| * (1 - vY Y * x0) := by
    have := congrArg abs hid
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hv, abs_of_pos hx0,
      abs_of_nonpos (by linarith : vY Y * x0 - 1 ≤ 0)] at this
    linarith [this]
  set d := |vY Y - x0| with hd0
  have hdpos : 0 < d := by
    by_contra hneg
    have : d = 0 := le_antisymm (not_lt.1 hneg) (abs_nonneg _)
    rw [this] at hd
    have : 0 < |Y - Y0| * (vY Y * x0) := mul_pos hYd hvx
    linarith
  have hd1 : d ≤ 1 := by
    rw [hd0, abs_le]; constructor <;> linarith
  have hlow : |Y - Y0| * (vY Y * x0) ≤ d := by rw [hd]; nlinarith
  have hlogd : Real.log (|Y - Y0| * (vY Y * x0)) ≤ Real.log d := Real.log_le_log (mul_pos hYd hvx) hlow
  rw [Real.log_mul hYd.ne' hvx.ne'] at hlogd
  have hlogd0 : Real.log d ≤ 0 := Real.log_nonpos hdpos.le hd1
  have hsq : Real.log ((vY Y - x0) ^ 2) = 2 * Real.log d := by
    have e : (vY Y - x0) ^ 2 = d ^ 2 := (sq_abs _).symm
    rw [e, Real.log_pow]; norm_num
  have hhi : 0 < hi := by linarith [hm.2, hm.1, hlo]
  have hvlow : x0 / hi ≤ vY Y * x0 := by
    have h1 := vY_ge_inv hY2
    have hh : 0 < Y := by linarith
    have h2 : 1 / hi ≤ vY Y := le_trans (one_div_le_one_div_of_le hh hm.2) h1
    calc x0 / hi = (1 / hi) * x0 := by ring
      _ ≤ vY Y * x0 := by nlinarith
  have hlogv : Real.log (x0 / hi) ≤ Real.log (vY Y * x0) :=
    Real.log_le_log (div_pos hx0 hhi) hvlow
  have hlogq : Real.log (hi / x0) = - Real.log (x0 / hi) := by
    rw [← Real.log_inv, inv_div]
  have hl : Real.log |Y - Y0| = Real.log (Y - Y0) := Real.log_abs _
  have hneg := neg_abs_le (Real.log (Y - Y0))
  simp only [Real.norm_eq_abs]
  rw [hsq, abs_of_nonpos (by linarith)]
  linarith

lemma intervalIntegrable_logQ {lo hi a b c u : ℝ} (hlo : 2 ≤ lo) (hlh : lo ≤ hi)
    (hc : 0 < c) (hb : b ^ 2 * u ^ 2 ≤ a * c) :
    IntervalIntegrable (fun Y => Real.log (Qf a b c u (vY Y))) volume lo hi := by
  by_cases hpos : ∀ Y ∈ Icc lo hi, Qf a b c u (vY Y) ≠ 0
  · have hcont : ContinuousOn (fun Y => Real.log (Qf a b c u (vY Y))) (uIcc lo hi) := by
      rw [uIcc_of_le hlh]
      have : Continuous fun Y => Qf a b c u (vY Y) := by unfold Qf; fun_prop
      exact this.continuousOn.log hpos
    exact hcont.intervalIntegrable
  · push_neg at hpos
    obtain ⟨Y0, hY0, hz⟩ := hpos
    have hY02 : 2 ≤ Y0 := le_trans hlo hY0.1
    set x0 := vY Y0 with hx0d
    have hx0 : 0 < x0 := vY_pos hY02
    have hx1 : x0 ≤ 1 := vY_le_one hY02
    have e1 := Qf_eq_zero hc hb hz
    have hQ : ∀ x, Qf a b c u x = c * (x - x0) ^ 2 := by
      intro x
      have hz' : a - 2 * b * u * x0 + c * x0 ^ 2 = 0 := hz
      unfold Qf
      have : a = c * x0 ^ 2 := by nlinarith
      nlinarith
    have hS := intervalIntegrable_log_sq_sing (x0 := x0) hlo hlh hx0 hx1
    have hG : IntervalIntegrable (fun Y => |Real.log c| + |Real.log ((vY Y - x0) ^ 2)|) volume lo hi :=
      intervalIntegrable_const.add hS.abs
    have hmeas : AEStronglyMeasurable (fun Y => Real.log (Qf a b c u (vY Y))) (volume.restrict (uIoc lo hi)) := by
      have : Measurable (fun Y => Real.log (Qf a b c u (vY Y))) := by
        apply Real.measurable_log.comp
        have : Continuous fun Y => Qf a b c u (vY Y) := by unfold Qf; fun_prop
        exact this.measurable
      exact this.aestronglyMeasurable
    refine hG.mono_fun' hmeas (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Real.norm_eq_abs, hQ]
    by_cases h0 : (vY Y - x0) ^ 2 = 0
    · rw [h0]; simp
    · rw [Real.log_mul hc.ne' h0]
      exact abs_add_le _ _

/-! ### Strict variance (moment cone) -/

lemma cell_var_pos {cl : YCell} (h : 2 ≤ cl.lo) (hw : 0 < cl.w) (xb : ℝ) :
    0 < cl.phys (Qf (xb ^ 2) xb 1 1) := by
  have hq : ∀ x, Qf (xb ^ 2) xb 1 1 x = (x - xb) ^ 2 := by intro x; unfold Qf; ring
  rw [phys_pos h]
  have hpos : 0 < cl.hi - cl.lo := by linarith [cl.lo_lt]
  apply mul_pos (div_pos hw hpos)
  have hI : 0 < ∫ Y in cl.lo..cl.hi, Qf (xb ^ 2) xb 1 1 (vY Y) := by
    apply intervalIntegral.integral_pos cl.lo_lt
    · have : Continuous fun Y => Qf (xb ^ 2) xb 1 1 (vY Y) := by unfold Qf; fun_prop
      exact this.continuousOn
    · intro Y _; simp only [hq]; positivity
    · by_cases h1 : vY cl.lo = xb
      · refine ⟨cl.hi, ⟨cl.lo_lt.le, le_refl _⟩, ?_⟩
        simp only [hq]
        have : vY cl.hi ≠ xb := by
          intro h2
          have := vY_injOn (mem_Ici.2 h) (mem_Ici.2 (by linarith [cl.lo_lt] : 2 ≤ cl.hi)) (h1.trans h2.symm)
          linarith [cl.lo_lt]
        positivity
      · refine ⟨cl.lo, ⟨le_refl _, cl.lo_lt.le⟩, ?_⟩
        simp only [hq]
        have : vY cl.lo - xb ≠ 0 := sub_ne_zero.2 h1
        positivity
  exact hI

lemma physL_var_nonneg {l : List YCell} (hl : PosL l) (hw : ∀ c ∈ l, 0 < c.w) (xb : ℝ) :
    0 ≤ physL l (Qf (xb ^ 2) xb 1 1) := by
  induction l with
  | nil => simp [physL]
  | cons c l' ih =>
    rw [physL_cons]
    have h1 := cell_var_pos (hl c (by simp)) (hw c (by simp)) xb
    have h2 := ih (fun d hd => hl d (by simp [hd])) (fun d hd => hw d (by simp [hd]))
    linarith

lemma bin_cone {l : List YCell} (hl : PosL l) (hne : l ≠ []) (hw : ∀ c ∈ l, 0 < c.w) :
    (physL l id) ^ 2 < massL l * physL l (fun x => x ^ 2) := by
  have hm : 0 < massL l := by
    cases l with
    | nil => exact absurd rfl hne
    | cons c l' => rw [massL_cons]; linarith [hw c (by simp), massL_nonneg l']
  set xb := physL l id / massL l with hxb
  have hsum : 0 < physL l (Qf (xb ^ 2) xb 1 1) := by
    cases l with
    | nil => exact absurd rfl hne
    | cons c l' =>
      rw [physL_cons]
      have h1 := cell_var_pos (hl c (by simp)) (hw c (by simp)) xb
      have h2 := physL_var_nonneg (l := l') (fun d hd => hl d (by simp [hd])) (fun d hd => hw d (by simp [hd])) xb
      linarith
  rw [physL_quad hl] at hsum
  have : xb * massL l = physL l id := by rw [hxb]; field_simp
  nlinarith

/-! ### Cutting cells into bins -/

def _root_.CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell.left (c : YCell) (m : ℝ) (h1 : c.lo < m) (_h2 : m < c.hi) : YCell :=
  ⟨c.lo, m, c.w * (m - c.lo) / (c.hi - c.lo), h1,
    div_nonneg (mul_nonneg c.w_nonneg (by linarith)) (by linarith [c.lo_lt])⟩

def _root_.CatalanMeasure.GenD.Signed.RouteI.CapFields.YCell.right (c : YCell) (m : ℝ) (_h1 : c.lo < m) (h2 : m < c.hi) : YCell :=
  ⟨m, c.hi, c.w * (c.hi - m) / (c.hi - c.lo), h2,
    div_nonneg (mul_nonneg c.w_nonneg (by linarith)) (by linarith [c.lo_lt])⟩

/-- `L` is the list of pieces obtained from `c` by successive cuts (mass proportional to width). -/
inductive CellCut : YCell → List YCell → Prop
  | refl (c : YCell) : CellCut c [c]
  | split (c : YCell) (m : ℝ) (h1 : c.lo < m) (h2 : m < c.hi) {L1 L2 : List YCell} :
      CellCut (c.left m h1 h2) L1 → CellCut (c.right m h1 h2) L2 → CellCut c (L1 ++ L2)

lemma CellCut.bounds {c : YCell} {L : List YCell} (h : CellCut c L) :
    ∀ d ∈ L, c.lo ≤ d.lo ∧ d.hi ≤ c.hi := by
  induction h with
  | refl c => intro d hd; simp at hd; subst hd; exact ⟨le_refl _, le_refl _⟩
  | split c m h1 h2 _ _ ih1 ih2 =>
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · have := ih1 d hd; simp [YCell.left] at this; constructor <;> linarith [this.1, this.2]
    · have := ih2 d hd; simp [YCell.right] at this; constructor <;> linarith [this.1, this.2]

lemma CellCut.wpos {c : YCell} {L : List YCell} (h : CellCut c L) (hw : 0 < c.w) :
    ∀ d ∈ L, 0 < d.w := by
  induction h with
  | refl c => intro d hd; simp at hd; subst hd; exact hw
  | split c m h1 h2 _ _ ih1 ih2 =>
    have hpos : 0 < c.hi - c.lo := by linarith [c.lo_lt]
    intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact ih1 (by simp [YCell.left]; exact div_pos (mul_pos hw (by linarith)) hpos) d hd
    · exact ih2 (by simp [YCell.right]; exact div_pos (mul_pos hw (by linarith)) hpos) d hd

lemma phys_split {c : YCell} (h : 2 ≤ c.lo) {m : ℝ} (h1 : c.lo < m) (h2 : m < c.hi) (f : ℝ → ℝ)
    (hint : IntervalIntegrable (fun Y => f (vY Y)) volume c.lo c.hi) :
    c.phys f = (c.left m h1 h2).phys f + (c.right m h1 h2).phys f := by
  have hpos : 0 < c.hi - c.lo := by linarith [c.lo_lt]
  have iL : IntervalIntegrable (fun Y => f (vY Y)) volume c.lo m :=
    hint.mono_set (by rw [uIcc_of_le h1.le, uIcc_of_le c.lo_lt.le]; exact Icc_subset_Icc le_rfl h2.le)
  have iR : IntervalIntegrable (fun Y => f (vY Y)) volume m c.hi :=
    hint.mono_set (by rw [uIcc_of_le h2.le, uIcc_of_le c.lo_lt.le]; exact Icc_subset_Icc h1.le le_rfl)
  rw [phys_pos h, phys_pos (c := c.left m h1 h2) h, phys_pos (c := c.right m h1 h2) (by simpa [YCell.right] using (by linarith : 2 ≤ m))]
  simp only [YCell.left, YCell.right]
  rw [← integral_add_adjacent_intervals iL iR]
  have e1 : c.hi - c.lo ≠ 0 := hpos.ne'
  have e2 : m - c.lo ≠ 0 := by linarith
  have e3 : c.hi - m ≠ 0 := by linarith
  field_simp

lemma phys_cut {c : YCell} {L : List YCell} (h : CellCut c L) (hlo : 2 ≤ c.lo) (f : ℝ → ℝ)
    (hint : IntervalIntegrable (fun Y => f (vY Y)) volume c.lo c.hi) :
    c.phys f = physL L f := by
  induction h with
  | refl c => simp [physL]
  | split c m h1 h2 hL hR ih1 ih2 =>
    rw [phys_split hlo h1 h2 f hint]
    have iL : IntervalIntegrable (fun Y => f (vY Y)) volume c.lo m :=
      hint.mono_set (by rw [uIcc_of_le h1.le, uIcc_of_le c.lo_lt.le]; exact Icc_subset_Icc le_rfl h2.le)
    have iR : IntervalIntegrable (fun Y => f (vY Y)) volume m c.hi :=
      hint.mono_set (by rw [uIcc_of_le h2.le, uIcc_of_le c.lo_lt.le]; exact Icc_subset_Icc h1.le le_rfl)
    have a1 := ih1 hlo iL
    have a2 := ih2 (by simpa [YCell.right] using (by linarith : 2 ≤ m)) iR
    rw [a1, a2]
    simp [physL, List.map_append, List.sum_append]

/-! ### Partitions of a cell list into bins -/

lemma physL_append (l1 l2 : List YCell) (f : ℝ → ℝ) : physL (l1 ++ l2) f = physL l1 f + physL l2 f := by
  simp [physL, List.map_append, List.sum_append]

lemma physL_flatten (L : List (List YCell)) (f : ℝ → ℝ) :
    physL L.flatten f = (L.map fun b => physL b f).sum := by
  induction L with
  | nil => simp [physL]
  | cons b L ih => simp [List.flatten_cons, physL_append, ih]

lemma physL_perm {l1 l2 : List YCell} (h : l1.Perm l2) (f : ℝ → ℝ) : physL l1 f = physL l2 f := by
  unfold physL; exact (h.map _).sum_eq

/-- `bins` re-groups the pieces obtained by cutting the cells of `gas`. -/
def Partitioned (gas : List YCell) (bins : List (List YCell)) : Prop :=
  ∃ pieces : List (List YCell), List.Forall₂ CellCut gas pieces ∧ (pieces.flatten).Perm bins.flatten

lemma forall₂_physL {gas : List YCell} {pieces : List (List YCell)}
    (hF : List.Forall₂ CellCut gas pieces) (f : ℝ → ℝ) :
    PosL gas → (∀ c ∈ gas, IntervalIntegrable (fun Y => f (vY Y)) volume c.lo c.hi) →
    physL gas f = physL pieces.flatten f := by
  induction hF with
  | nil => intro _ _; simp [physL]
  | @cons c p gs ps hcut _ ih =>
    intro hg hint
    rw [physL_cons, List.flatten_cons, physL_append,
      phys_cut hcut (hg c (by simp)) f (hint c (by simp)),
      ih (fun d hd => hg d (by simp [hd])) (fun d hd => hint d (by simp [hd]))]

lemma forall₂_cut {gas : List YCell} {pieces : List (List YCell)}
    (hF : List.Forall₂ CellCut gas pieces) : ∀ p ∈ pieces, ∃ c ∈ gas, CellCut c p := by
  induction hF with
  | nil => intro p hp; simp at hp
  | @cons c p gs ps hcut _ ih =>
    intro p hp
    rcases List.mem_cons.1 hp with h | h
    · exact ⟨c, by simp, h ▸ hcut⟩
    · obtain ⟨c', hc', hc''⟩ := ih p h
      exact ⟨c', by simp [hc'], hc''⟩

lemma Partitioned.physL_eq {gas : List YCell} {bins : List (List YCell)} (hp : Partitioned gas bins)
    (hg : PosL gas) (f : ℝ → ℝ)
    (hint : ∀ c ∈ gas, IntervalIntegrable (fun Y => f (vY Y)) volume c.lo c.hi) :
    physL gas f = (bins.map fun b => physL b f).sum := by
  obtain ⟨pieces, hF, hperm⟩ := hp
  rw [forall₂_physL hF f hg hint, physL_perm hperm, physL_flatten]

lemma Partitioned.cells {gas : List YCell} {bins : List (List YCell)} (hp : Partitioned gas bins)
    (hg : PosL gas) (hw : ∀ c ∈ gas, 0 < c.w) :
    ∀ b ∈ bins, ∀ d ∈ b, 2 ≤ d.lo ∧ 0 < d.w := by
  obtain ⟨pieces, hF, hperm⟩ := hp
  intro b hb d hd
  have hd' : d ∈ pieces.flatten := hperm.mem_iff.2 (List.mem_flatten.2 ⟨b, hb, hd⟩)
  obtain ⟨p, hp, hdp⟩ := List.mem_flatten.1 hd'
  obtain ⟨c, hc, hcut⟩ := forall₂_cut hF p hp
  exact ⟨le_trans (hg c hc) (hcut.bounds d hdp).1, hcut.wpos (hw c hc) d hdp⟩

/-- normalized base `D = a + c B/m` of a bin (moments `m, A, B` of the bin). -/
def binD (a c : ℝ) (l : List YCell) : ℝ := a + c * physL l (fun x => x ^ 2) / massL l

/-- `alpha = 2 b A/(m D)` of a bin. -/
def binAlpha (a b c : ℝ) (l : List YCell) : ℝ := 2 * b * physL l id / (massL l * binD a c l)

/-- The Jensen bound of one bin: `m (log D - sum_{k<=n} (alpha u)^k / k)`. -/
def binTerm (a b c u : ℝ) (n : ℕ) (l : List YCell) : ℝ :=
  massL l * (Real.log (binD a c l) -
    ∑ k ∈ Finset.range n, (binAlpha a b c l * u) ^ (k + 1) / ((k : ℝ) + 1))
lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem gas_bins_jensen {gas : List YCell} {bins : List (List YCell)} (hp : Partitioned gas bins)
    (hg : PosL gas) (hw : ∀ c ∈ gas, 0 < c.w) {a b c u : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hb : b ^ 2 ≤ a * c) (hu : |u| ≤ 1) {n : ℕ} (hn : Odd n) :
    physL gas (fun x => Real.log (Qf a b c u x)) ≤ (bins.map (binTerm a b c u n)).sum := by
  have hb2 : b ^ 2 * u ^ 2 ≤ a * c := by
    have : u ^ 2 ≤ 1 := by nlinarith [abs_nonneg u, sq_abs u]
    nlinarith [sq_nonneg b]
  rw [hp.physL_eq hg _ (fun c' hc' => intervalIntegrable_logQ (hg c' hc') c'.lo_lt.le hc hb2)]
  apply list_sum_map_le
  intro l hl
  by_cases hnil : l = []
  · subst hnil; simp [physL, binTerm, massL]
  · have hcells := hp.cells hg hw l hl
    have hlpos : PosL l := fun d hd => (hcells d hd).1
    have hlw : ∀ d ∈ l, 0 < d.w := fun d hd => (hcells d hd).2
    have hm : 0 < massL l := by
      cases l with
      | nil => exact absurd rfl hnil
      | cons d l' => rw [massL_cons]; linarith [hlw d (by simp), massL_nonneg l']
    exact bin_jensen hlpos ha hc hb hu hn hm (bin_cone hlpos hnil hlw)
      (fun cl hcl => intervalIntegrable_logQ (hlpos cl hcl) cl.lo_lt.le hc hb2)

/-! ### Matching the gas part of `CapFields.angular` -/

lemma phys_const_mul (c : YCell) (k : ℝ) (f : ℝ → ℝ) : c.phys (fun x => k * f x) = k * c.phys f := by
  unfold YCell.phys YCell.avg
  rw [intervalIntegral.integral_const_mul]; ring

lemma physL_const_mul (l : List YCell) (k : ℝ) (f : ℝ → ℝ) :
    physL l (fun x => k * f x) = k * physL l f := by
  induction l with
  | nil => simp [physL]
  | cons c l ih => rw [physL_cons, physL_cons, phys_const_mul, ih]; ring

def reflectL (l : List YCell) : List YCell := l.map YCell.reflect

lemma physL_reflect {l : List YCell} (h : ∀ c ∈ l, c.hi ≤ -2) (f : ℝ → ℝ) :
    physL l f = physL (reflectL l) (fun x => f (-x)) := by
  induction l with
  | nil => simp [physL, reflectL]
  | cons c l ih =>
    have := ih (fun d hd => h d (by simp [hd]))
    simp only [reflectL, List.map_cons] at this ⊢
    rw [physL_cons, physL_cons, phys_reflect (h c (by simp)) f, this]

lemma posL_reflect {l : List YCell} (h : ∀ c ∈ l, c.hi ≤ -2) : PosL (reflectL l) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  have := h c hc
  simp [YCell.reflect]; linarith

lemma reflectL_w {l : List YCell} (hw : ∀ c ∈ l, 0 < c.w) : ∀ d ∈ reflectL l, 0 < d.w := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  exact hw c hc

/-- gas part of the angular field (direct term, plus mirror term for the negative species). -/
def gasPart (S : CapSource) (σ : Sign) (i : ℕ) (θ : ℝ) : ℝ :=
  physL (S.gas σ) (fun x => (1 / 2) * Real.log ((S.rad i) ^ 2 - 2 * S.rad i * x * Real.cos θ + x ^ 2)) +
  (if σ = Sign.neg then
    physL (S.gas σ) (fun x =>
      (1 / 2) * Real.log (1 - 2 * S.rad i * x * Real.cos θ + (S.rad i) ^ 2 * x ^ 2))
   else 0)

lemma angular_eq (S : CapSource) (t : Trunc) (σ : Sign) (i : ℕ) (θ : ℝ) :
    S.angular t σ i θ = gasPart S σ i θ +
      (((S.aux σ).map fun e =>
        e.w * (-S.sigma (min i e.rad) +
          t.sum (fun k => S.coef k *
            ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
              (if σ = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) *
            Real.cos (k * e.phase) * Real.cos (k * θ)))).sum +
      (53 * S.sigma i - S.radial i / 2) / 58 + S.auxTail t σ) := by
  unfold CapSource.angular gasPart; ring

theorem gasPart_pos_le (S : CapSource) {bins : List (List YCell)} (i : ℕ) (θ : ℝ)
    (hp : Partitioned (S.gas Sign.pos) bins) (hg : PosL (S.gas Sign.pos))
    (hw : ∀ c ∈ S.gas Sign.pos, 0 < c.w) {n : ℕ} (hn : Odd n) :
    gasPart S Sign.pos i θ ≤
      (1 / 2) * (bins.map (binTerm ((S.rad i) ^ 2) (S.rad i) 1 (Real.cos θ) n)).sum := by
  have hr : 0 < S.rad i := Real.exp_pos _
  have h := gas_bins_jensen hp hg hw (a := (S.rad i) ^ 2) (b := S.rad i) (c := 1) (u := Real.cos θ)
    (by positivity) one_pos (by nlinarith) (Real.abs_cos_le_one θ) hn
  have e : (fun x => (1 / 2) * Real.log ((S.rad i) ^ 2 - 2 * S.rad i * x * Real.cos θ + x ^ 2)) =
      fun x => (1 / 2) * Real.log (Qf ((S.rad i) ^ 2) (S.rad i) 1 (Real.cos θ) x) := by
    funext x; unfold Qf; congr 2; ring
  unfold gasPart
  simp only [Sign.pos, reduceCtorEq, if_false, add_zero]
  rw [e, physL_const_mul]
  linarith

theorem gasPart_neg_le (S : CapSource) {bins : List (List YCell)} (i : ℕ) (θ : ℝ)
    (hp : Partitioned (reflectL (S.gas Sign.neg)) bins) (hg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2)
    (hw : ∀ c ∈ S.gas Sign.neg, 0 < c.w) {n : ℕ} (hn : Odd n) :
    gasPart S Sign.neg i θ ≤
      (1 / 2) * (bins.map (binTerm ((S.rad i) ^ 2) (S.rad i) 1 (-Real.cos θ) n)).sum +
      (1 / 2) * (bins.map (binTerm 1 (S.rad i) ((S.rad i) ^ 2) (-Real.cos θ) n)).sum := by
  have hr : 0 < S.rad i := Real.exp_pos _
  have hu : |(-Real.cos θ)| ≤ 1 := by rw [abs_neg]; exact Real.abs_cos_le_one θ
  have hPos := posL_reflect hg
  have hW := reflectL_w hw
  have h1 := gas_bins_jensen hp hPos hW (a := (S.rad i) ^ 2) (b := S.rad i) (c := 1) (u := -Real.cos θ)
    (by positivity) one_pos (by nlinarith) hu hn
  have h2 := gas_bins_jensen hp hPos hW (a := 1) (b := S.rad i) (c := (S.rad i) ^ 2) (u := -Real.cos θ)
    one_pos (by positivity) (by nlinarith) hu hn
  have k1 : physL (S.gas Sign.neg) (fun x => (1 / 2) * Real.log ((S.rad i) ^ 2 - 2 * S.rad i * x * Real.cos θ + x ^ 2)) =
      (1 / 2) * physL (reflectL (S.gas Sign.neg)) (fun x => Real.log (Qf ((S.rad i) ^ 2) (S.rad i) 1 (-Real.cos θ) x)) := by
    rw [physL_reflect hg, ← physL_const_mul]
    congr 1; funext x; unfold Qf; congr 2; ring
  have k2 : physL (S.gas Sign.neg) (fun x => (1 / 2) * Real.log (1 - 2 * S.rad i * x * Real.cos θ + (S.rad i) ^ 2 * x ^ 2)) =
      (1 / 2) * physL (reflectL (S.gas Sign.neg)) (fun x => Real.log (Qf 1 (S.rad i) ((S.rad i) ^ 2) (-Real.cos θ) x)) := by
    rw [physL_reflect hg, ← physL_const_mul]
    congr 1; funext x; unfold Qf; congr 2; ring
  unfold gasPart
  simp only [if_true]
  rw [k1, k2]
  linarith

lemma list_abs_sum_le {α : Type*} (l : List α) (f g h : α → ℝ) (H : ∀ x ∈ l, |f x - g x| ≤ h x) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map h).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := ih (fun y hy => H y (by simp [hy]))
    have h1 := H x (by simp)
    calc |f x + (l.map f).sum - (g x + (l.map g).sum)|
        = |(f x - g x) + ((l.map f).sum - (l.map g).sum)| := by ring_nf
      _ ≤ |f x - g x| + |(l.map f).sum - (l.map g).sum| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 this



/-! ### Input-error consumer: alpha perturbation and `alpha in [0,1]` -/

lemma phys_id_nonneg {cl : YCell} (h : 2 ≤ cl.lo) : 0 ≤ cl.phys id := by
  rw [phys_pos h]
  apply mul_nonneg (div_nonneg cl.w_nonneg (by linarith [cl.lo_lt]))
  apply intervalIntegral.integral_nonneg cl.lo_lt.le
  intro Y hY; exact (vY_pos (le_trans h hY.1)).le

lemma physL_id_nonneg {l : List YCell} (hl : PosL l) : 0 ≤ physL l id := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    rw [physL_cons]
    exact add_nonneg (phys_id_nonneg (hl c (by simp))) (ih (fun d hd => hl d (by simp [hd])))

lemma phys_sq_nonneg {cl : YCell} : 0 ≤ cl.phys (fun x => x ^ 2) := by
  unfold YCell.phys YCell.avg
  apply mul_nonneg (div_nonneg cl.w_nonneg (by linarith [cl.lo_lt]))
  apply intervalIntegral.integral_nonneg cl.lo_lt.le
  intro Y _; positivity

lemma physL_sq_nonneg (l : List YCell) : 0 ≤ physL l (fun x => x ^ 2) := by
  induction l with
  | nil => simp [physL]
  | cons c l ih => rw [physL_cons]; exact add_nonneg phys_sq_nonneg ih

/-- `0 <= alpha <= 1` for a nonempty positive bin. -/
lemma binAlpha_mem {l : List YCell} (hl : PosL l) (hne : l ≠ []) (hw : ∀ c ∈ l, 0 < c.w)
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hbac : b ^ 2 ≤ a * c) :
    0 ≤ binAlpha a b c l ∧ binAlpha a b c l ≤ 1 := by
  have hm : 0 < massL l := by
    cases l with
    | nil => exact absurd rfl hne
    | cons d l' => rw [massL_cons]; linarith [hw d (by simp), massL_nonneg l']
  have hcone := bin_cone hl hne hw
  have hA := physL_id_nonneg hl
  have hB := physL_sq_nonneg l
  set A := physL l id
  set B := physL l (fun x => x ^ 2)
  set m := massL l
  have hD : 0 < m * binD a c l := by
    unfold binD; rw [mul_add, mul_div_cancel₀ _ hm.ne']; positivity
  have e : m * binD a c l = m * a + c * B := by unfold binD; rw [mul_add, mul_div_cancel₀ _ hm.ne']
  constructor
  · unfold binAlpha; positivity
  · unfold binAlpha
    rw [div_le_one hD, e]
    by_contra hneg
    push_neg at hneg
    have h1 : (m * a + c * B) ^ 2 < (2 * b * A) ^ 2 := by
      apply pow_lt_pow_left₀ hneg (by positivity) (by norm_num)
    nlinarith [sq_nonneg (m * a - c * B), mul_nonneg hA hA, mul_pos ha hc, mul_pos hm (mul_pos ha hc),
      mul_le_mul_of_nonneg_left hbac (sq_nonneg A), mul_le_mul_of_nonneg_left hcone.le (mul_pos ha hc).le]


lemma massL_pos {l : List YCell} (hne : l ≠ []) (hw : ∀ c ∈ l, 0 < c.w) : 0 < massL l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons d l' => rw [massL_cons]; linarith [hw d (by simp), massL_nonneg l']

/-- alpha perturbation: `alpha = 2 b A / D0`, prepared `alpha~ = 2 b' A' / D0'`. -/
lemma alpha_perturb {A A' b b' D0 D0' : ℝ} (hb' : 0 < b') (hD : 0 < D0) (hD' : 0 < D0')
    (hA' : 0 ≤ A') (hα' : 2 * b' * A' / D0' ≤ 1) (hb : 0 ≤ b) :
    |2 * b * A / D0 - 2 * b' * A' / D0'| ≤
      2 * b * |A - A'| / D0 + |b - b'| * D0' / (b' * D0) + |D0 - D0'| / D0 := by
  have h1 : 2 * b * A / D0 - 2 * b' * A' / D0' =
      (2 * b * (A - A') + 2 * (b - b') * A') / D0 + (2 * b' * A' / D0') * ((D0' - D0) / D0) := by
    field_simp; ring
  rw [h1]
  have hα0 : 0 ≤ 2 * b' * A' / D0' := by positivity
  have hA'le : 2 * A' ≤ D0' / b' := by
    rw [le_div_iff₀ hb']; rw [div_le_one hD'] at hα'; nlinarith
  calc _ ≤ |(2 * b * (A - A') + 2 * (b - b') * A') / D0| + |(2 * b' * A' / D0') * ((D0' - D0) / D0)| :=
        abs_add_le _ _
    _ ≤ (2 * b * |A - A'| + |b - b'| * (D0' / b')) / D0 + |(D0' - D0) / D0| := by
        apply add_le_add
        · rw [abs_div, abs_of_pos hD]
          apply div_le_div_of_nonneg_right _ hD.le
          calc |2 * b * (A - A') + 2 * (b - b') * A'| ≤ |2 * b * (A - A')| + |2 * (b - b') * A'| := abs_add_le _ _
            _ = 2 * b * |A - A'| + |b - b'| * (2 * A') := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA', abs_of_nonneg hb]; norm_num; ring
            _ ≤ 2 * b * |A - A'| + |b - b'| * (D0' / b') := by
                gcongr
        · rw [abs_mul, abs_of_nonneg hα0]
          calc _ ≤ 1 * |(D0' - D0) / D0| := mul_le_mul_of_nonneg_right hα' (abs_nonneg _)
            _ = _ := one_mul _
    _ = 2 * b * |A - A'| / D0 + |b - b'| * D0' / (b' * D0) + |D0 - D0'| / D0 := by
        rw [abs_div, abs_of_pos hD, abs_sub_comm D0' D0]
        field_simp

lemma binAlpha_eq {l : List YCell} (hm : 0 < massL l) (a b c : ℝ) :
    binAlpha a b c l = 2 * b * physL l id / (massL l * a + c * physL l (fun x => x ^ 2)) := by
  unfold binAlpha binD
  rw [mul_add, mul_div_cancel₀ _ hm.ne']


/-! ### Primitive evaluation errors and the constant coefficient -/

lemma abs_log_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / min x y := by
  have hm : 0 < min x y := lt_min hx hy
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne'] at h1
  rw [Real.log_div hy.ne' hx.ne'] at h2
  have e1 : x / y - 1 = (x - y) / y := by field_simp
  have e2 : y / x - 1 = (y - x) / x := by field_simp
  rw [abs_le]
  have a1 : (x - y) / y ≤ |x - y| / min x y := by
    calc (x - y) / y ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy.le
      _ ≤ |x - y| / min x y := div_le_div_of_nonneg_left (abs_nonneg _) hm (min_le_right _ _)
  have a2 : (y - x) / x ≤ |x - y| / min x y := by
    calc (y - x) / x ≤ |x - y| / x := div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) hx.le
      _ ≤ |x - y| / min x y := div_le_div_of_nonneg_left (abs_nonneg _) hm (min_le_left _ _)
  constructor <;> linarith

/-- First primitive `H1 = log x - x^2/2` at a root `x` approximated by `x'` with a log enclosure. -/
lemma H1_approx {x x' L' δ η xm : ℝ} (hxm : 0 < xm) (hx : xm ≤ x) (hx' : xm ≤ x')
    (hx1 : x ≤ 1) (hx1' : x' ≤ 1 + δ) (hδ : 0 ≤ δ) (hd : |x - x'| ≤ δ)
    (hL : |L' - Real.log x'| ≤ η) :
    |(L' - x' ^ 2 / 2) - H1 x| ≤ η + (1 / xm + (2 + δ) / 2) * δ := by
  unfold H1
  have hx0 : 0 < x := lt_of_lt_of_le hxm hx
  have hx0' : 0 < x' := lt_of_lt_of_le hxm hx'
  have h1 := abs_log_sub_le hx0 hx0'
  have hmin : xm ≤ min x x' := le_min hx hx'
  have h1' : |Real.log x - Real.log x'| ≤ δ / xm := by
    calc _ ≤ |x - x'| / min x x' := h1
      _ ≤ δ / min x x' := div_le_div_of_nonneg_right hd (lt_min hx0 hx0').le
      _ ≤ δ / xm := div_le_div_of_nonneg_left hδ hxm hmin
  have h2 : |x' ^ 2 / 2 - x ^ 2 / 2| ≤ (2 + δ) / 2 * δ := by
    have : x' ^ 2 / 2 - x ^ 2 / 2 = (x' - x) * (x' + x) / 2 := by ring
    rw [this, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hs : |x' + x| ≤ 2 + δ := by rw [abs_of_pos (by linarith)]; linarith
    have hd' : |x' - x| ≤ δ := by rw [abs_sub_comm]; exact hd
    calc |x' - x| * |x' + x| / 2 ≤ δ * (2 + δ) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hd' hs (abs_nonneg _) hδ
      _ = (2 + δ) / 2 * δ := by ring
  have e : (L' - x' ^ 2 / 2) - (Real.log x - x ^ 2 / 2) =
      (L' - Real.log x') + (Real.log x' - Real.log x) - (x' ^ 2 / 2 - x ^ 2 / 2) := by ring
  rw [e]
  have t1 := abs_sub ((L' - Real.log x') + (Real.log x' - Real.log x)) (x' ^ 2 / 2 - x ^ 2 / 2)
  have t2 := abs_add_le (L' - Real.log x') (Real.log x' - Real.log x)
  have t3 : |Real.log x' - Real.log x| ≤ δ / xm := by rw [abs_sub_comm]; exact h1'
  have t4 : δ / xm = 1 / xm * δ := by ring
  have t5 : (1 / xm + (2 + δ) / 2) * δ = 1 / xm * δ + (2 + δ) / 2 * δ := by ring
  linarith

/-- Second primitive `H2 = x - x^3/3`. -/
lemma H2_approx {x x' δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hx0' : 0 ≤ x') (hx1' : x' ≤ 1 + δ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : |x - x'| ≤ δ) :
    |(x' - x' ^ 3 / 3) - H2 x| ≤ 4 * δ := by
  unfold H2
  have e : (x' - x' ^ 3 / 3) - (x - x ^ 3 / 3) = (x' - x) * (1 - (x' ^ 2 + x' * x + x ^ 2) / 3) := by ring
  rw [e, abs_mul]
  have hd' : |x' - x| ≤ δ := by rw [abs_sub_comm]; exact hd
  have hb : |1 - (x' ^ 2 + x' * x + x ^ 2) / 3| ≤ 4 := by
    have h1 : x' ^ 2 ≤ 4 := by nlinarith
    have h2 : x' * x ≤ 2 := by nlinarith
    have h3 : x ^ 2 ≤ 1 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg x', sq_nonneg x, mul_nonneg hx0' hx0]
  calc _ ≤ δ * 4 := mul_le_mul hd' hb (abs_nonneg _) hδ
    _ = 4 * δ := by ring


/-! ### Bin moments from cell primitives, and the gas bounds -/

lemma cell_A_err {cl : YCell} (h : 2 ≤ cl.lo) {Hl Hh e : ℝ}
    (hl : |Hl - H1 (vY cl.lo)| ≤ e) (hh : |Hh - H1 (vY cl.hi)| ≤ e) :
    |cl.w / (cl.hi - cl.lo) * (Hl - Hh) - cl.phys id| ≤ 2 * (cl.w / (cl.hi - cl.lo)) * e := by
  rw [phys_id h]
  have hρ : 0 ≤ cl.w / (cl.hi - cl.lo) := div_nonneg cl.w_nonneg (by linarith [cl.lo_lt])
  rw [← mul_sub, abs_mul, abs_of_nonneg hρ]
  have : |(Hl - Hh) - (H1 (vY cl.lo) - H1 (vY cl.hi))| ≤ 2 * e := by
    have := abs_sub (Hl - H1 (vY cl.lo)) (Hh - H1 (vY cl.hi))
    have e2 : (Hl - Hh) - (H1 (vY cl.lo) - H1 (vY cl.hi)) = (Hl - H1 (vY cl.lo)) - (Hh - H1 (vY cl.hi)) := by ring
    rw [e2]; linarith
  calc _ ≤ cl.w / (cl.hi - cl.lo) * (2 * e) := mul_le_mul_of_nonneg_left this hρ
    _ = _ := by ring

lemma cell_B_err {cl : YCell} (h : 2 ≤ cl.lo) {Hl Hh e : ℝ}
    (hl : |Hl - H2 (vY cl.lo)| ≤ e) (hh : |Hh - H2 (vY cl.hi)| ≤ e) :
    |cl.w / (cl.hi - cl.lo) * (Hl - Hh) - cl.phys (fun x => x ^ 2)| ≤ 2 * (cl.w / (cl.hi - cl.lo)) * e := by
  rw [phys_sq h]
  have hρ : 0 ≤ cl.w / (cl.hi - cl.lo) := div_nonneg cl.w_nonneg (by linarith [cl.lo_lt])
  rw [← mul_sub, abs_mul, abs_of_nonneg hρ]
  have : |(Hl - Hh) - (H2 (vY cl.lo) - H2 (vY cl.hi))| ≤ 2 * e := by
    have := abs_sub (Hl - H2 (vY cl.lo)) (Hh - H2 (vY cl.hi))
    have e2 : (Hl - Hh) - (H2 (vY cl.lo) - H2 (vY cl.hi)) = (Hl - H2 (vY cl.lo)) - (Hh - H2 (vY cl.hi)) := by ring
    rw [e2]; linarith
  calc _ ≤ cl.w / (cl.hi - cl.lo) * (2 * e) := mul_le_mul_of_nonneg_left this hρ
    _ = _ := by ring

/-- Summing per-cell approximations of a moment gives the bin moment with the summed error. -/
lemma bin_moment_err (l : List YCell) (f : ℝ → ℝ) (Ah E : YCell → ℝ)
    (h : ∀ c ∈ l, |Ah c - c.phys f| ≤ E c) :
    |(l.map Ah).sum - physL l f| ≤ (l.map E).sum := by
  have := list_abs_sum_le l Ah (fun c => c.phys f) E h
  simpa [physL] using this


end
end CatalanMeasure.GenD.Signed.RouteI.MomentSource

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPiece
public import CatalanMeasure.GenD.Signed.FieldForm
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! # Laurent Taylor-merged Chebyshev pieces

Canonical CHEBENGINE module, approved by CHEBENGINE-REVIEW.md (b60cdc6a).
The Laurent coefficients/log enclosures are the existing TaylorCell/Core machinery.
The R/J majorants close the infinite remainder; no fixed cutoff discards a tail.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open scoped BigOperators

/-- Field addition before normalization of equal sites/poles. -/
abbrev fqAdd := CatalanMeasure.Signed.FieldForm.fqAdd

theorem fieldTower_add (a b : FieldQ) (x : ℝ) :
    fieldTower (fqAdd a b) (poleF (fqAdd a b).poles) 0 x =
      fieldTower a (poleF a.poles) 0 x + fieldTower b (poleF b.poles) 0 x := by
  have hF : poleF (fqAdd a b).poles = fun y => poleF a.poles y + poleF b.poles y := by
    funext y
    simp [fqAdd, CatalanMeasure.Signed.FieldForm.fqAdd, poleF]
  rw [hF]
  exact CatalanMeasure.Signed.FieldForm.fieldTower_add a b (poleF a.poles) (poleF b.poles) x

theorem lfieldTower_add (a b : List LTerm) (x : ℝ) :
    lfieldTower (a ++ b) 0 x = lfieldTower a 0 x + lfieldTower b 0 x := by
  simp only [lfieldTower, List.map_append, List.sum_append]

/-- The negative-binomial coefficient, including the constant inverse-power case. -/
def invBinom : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | s + 1, k => (k + s).choose s

theorem invBinom_nonneg (s k : ℕ) : (0 : ℝ) ≤ invBinom s k := Nat.cast_nonneg _

/-- The inverse-power series; this is Mathlib's binomial geometric series,
with the s=0 constant handled explicitly. -/
theorem invPowerSeries (s : ℕ) (u : ℝ) (hu : |u| < 1) :
    HasSum (fun k : ℕ => (invBinom s k : ℝ) * u ^ k) (1 / (1-u)^s) := by
  cases s with
  | zero =>
      have hf : (fun k : ℕ => (invBinom 0 k : ℝ)*u^k) =
          (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
        funext k
        by_cases hk : k = 0 <;> simp [invBinom, hk]
      rw [hf]
      simpa using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  | succ s =>
      simpa [invBinom, Nat.add_comm] using
        (hasSum_choose_mul_geometric_of_norm_lt_one s (show ‖u‖ < 1 by simpa using hu))

/-- Finite prefix and total expression for the nonnegative negative-binomial tail. -/
def invTailQ (s K : ℕ) (q : ℚ) : ℚ :=
  1 / (1-q)^s - ∑ k ∈ Finset.range (K+1), (invBinom s k : ℚ)*q^k

/-- Its semantic interpretation, including every omitted coefficient. -/
theorem invTailQ_spec (s K : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' k : ℕ, (invBinom s (k+(K+1)) : ℝ) * (q : ℝ)^(k+(K+1)) =
      (invTailQ s K q : ℝ) := by
  have hq : |(q : ℝ)| < 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hq0)]
    exact_mod_cast hq1
  have h := invPowerSeries s (q : ℝ) hq
  have hd := h.summable.sum_add_tsum_nat_add (K+1)
  rw [h.tsum_eq] at hd
  unfold invTailQ
  push_cast
  linarith

theorem invTailQ_nonneg (s K : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ invTailQ s K q := by
  have ht := invTailQ_spec s K q hq0 hq1
  have hp : (0 : ℝ) ≤ ∑' k : ℕ,
      (invBinom s (k+(K+1)) : ℝ) * (q : ℝ)^(k+(K+1)) :=
    tsum_nonneg (fun k => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by exact_mod_cast hq0) _))
  rw [ht] at hp
  exact_mod_cast hp

/-- Mean-value bound using only interior derivatives of the regular part. -/
theorem endLip (lo hi e G0 Γ TR : ℚ) (g dg : ℝ → ℝ)
    (he : (e : ℝ) ∈ Icc (lo : ℝ) (hi : ℝ))
    (hc : ContinuousOn g (Icc (lo : ℝ) (hi : ℝ)))
    (hd : ∀ x ∈ Ioo (lo : ℝ) (hi : ℝ), HasDerivAt g (dg x) x)
    (hb : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), |dg x| ≤ (Γ : ℝ))
    (h0 : g (e : ℝ) ≤ (G0 : ℝ)) (hΓ : 0 ≤ Γ)
    (hT : G0 + Γ * max (e-lo) (hi-e) ≤ TR) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), g x ≤ (TR : ℝ) := by
  have hΓ' : (0 : ℝ) ≤ Γ := by exact_mod_cast hΓ
  have hT' : (G0 : ℝ) + (Γ : ℝ) * max ((e : ℝ)-lo) ((hi : ℝ)-e) ≤ TR := by
    exact_mod_cast hT
  intro x hx
  rcases lt_trichotomy x (e : ℝ) with hxe | hxe | hex
  · obtain ⟨z, hz, hs⟩ := exists_hasDerivAt_eq_slope g dg hxe
        (hc.mono (fun y hy => ⟨hx.1.trans hy.1, hy.2.trans he.2⟩))
        (fun y hy => hd y ⟨lt_of_le_of_lt hx.1 hy.1, lt_of_lt_of_le hy.2 he.2⟩)
    have hz' : z ∈ Icc (lo : ℝ) (hi : ℝ) :=
      ⟨le_trans hx.1 hz.1.le, le_trans hz.2.le he.2⟩
    have hb' := (abs_le.mp (hb z hz')).1
    have hs' : dg z * ((e : ℝ)-x) = g (e : ℝ)-g x :=
      (eq_div_iff (sub_ne_zero.mpr hxe.ne')).mp hs
    have hm := mul_le_mul_of_nonneg_left
      (show (e : ℝ)-x ≤ max ((e : ℝ)-lo) ((hi : ℝ)-e) from
        le_trans (by linarith [hx.1]) (le_max_left _ _)) hΓ'
    nlinarith [mul_le_mul_of_nonneg_right hb' (sub_nonneg.mpr hxe.le)]
  · subst x
    exact h0.trans (by nlinarith [mul_nonneg hΓ' (show (0 : ℝ) ≤ max ((e : ℝ)-lo) ((hi : ℝ)-e) from
      (sub_nonneg.mpr he.1).trans (le_max_left _ _))])
  · obtain ⟨z, hz, hs⟩ := exists_hasDerivAt_eq_slope g dg hex
        (hc.mono (fun y hy => ⟨he.1.trans hy.1, hy.2.trans hx.2⟩))
        (fun y hy => hd y ⟨lt_of_le_of_lt he.1 hy.1, lt_of_lt_of_le hy.2 hx.2⟩)
    have hz' : z ∈ Icc (lo : ℝ) (hi : ℝ) :=
      ⟨le_trans he.1 hz.1.le, le_trans hz.2.le hx.2⟩
    have hb' := (abs_le.mp (hb z hz')).2
    have hs' : dg z * (x-(e : ℝ)) = g x-g (e : ℝ) :=
      (eq_div_iff (sub_ne_zero.mpr hex.ne')).mp hs
    have hm := mul_le_mul_of_nonneg_left
      (show x-(e : ℝ) ≤ max ((e : ℝ)-lo) ((hi : ℝ)-e) from
        le_trans (by linarith [hx.2]) (le_max_right _ _)) hΓ'
    nlinarith [mul_le_mul_of_nonneg_right hb' (sub_nonneg.mpr hex.le)]

/-- A checked regular-part estimate discharges the existing end-window hypothesis. -/
theorem endULip_sound (fq : FieldQ) (ts : List LTerm) (e lo hi : ℚ)
    (k kR : ℕ) (U TR T G0 Γ : ℚ) (dg : ℝ → ℝ)
    (hchk : endUOK fq ts e lo hi k kR U TR T = true)
    (he : (e : ℝ) ∈ Icc (lo : ℝ) (hi : ℝ))
    (hc : ContinuousOn (fun x => fieldTower (regQ fq e) (poleF (regQ fq e).poles) 0 x +
      lfieldTower (regL ts e) 0 x) (Icc (lo : ℝ) (hi : ℝ)))
    (hd : ∀ x ∈ Ioo (lo : ℝ) (hi : ℝ), HasDerivAt
      (fun x => fieldTower (regQ fq e) (poleF (regQ fq e).poles) 0 x +
        lfieldTower (regL ts e) 0 x) (dg x) x)
    (hb : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), |dg x| ≤ (Γ : ℝ))
    (h0 : fieldTower (regQ fq e) (poleF (regQ fq e).poles) 0 (e : ℝ) +
      lfieldTower (regL ts e) 0 (e : ℝ) ≤ (G0 : ℝ))
    (hΓ : 0 ≤ Γ) (hT : G0 + Γ * max (e-lo) (hi-e) ≤ TR) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ≠ (e : ℝ) →
      fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x ≤ (T : ℝ) :=
  endUOK_sound fq ts e lo hi k kR U TR T hchk
    (endLip lo hi e G0 Γ TR _ dg he hc hd hb h0 hΓ hT)

/-- A list of adjacent intervals covers [lo,hi]; all geometry is rational. -/
def pieceCover (hi : ℚ) : ℚ → List (ℚ × ℚ) → Bool
  | lo, [] => decide (lo = hi)
  | lo, (a,b) :: ps => decide (a = lo ∧ a ≤ b) && pieceCover hi b ps

theorem pieceCover_sound (hi : ℚ) : ∀ (lo : ℚ) (ps : List (ℚ × ℚ)),
    pieceCover hi lo ps = true → ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      x = (hi : ℝ) ∨ ∃ p ∈ ps, x ∈ Icc (p.1 : ℝ) (p.2 : ℝ) := by
  intro lo ps
  induction ps generalizing lo with
  | nil =>
      intro h x hx
      simp only [pieceCover, decide_eq_true_eq] at h
      subst lo
      exact Or.inl (le_antisymm hx.2 hx.1)
  | cons p ps ih =>
      intro h x hx
      rcases p with ⟨a,b⟩
      simp only [pieceCover, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hab⟩, hr⟩ := h
      by_cases hxb : x ≤ (b : ℝ)
      · exact Or.inr ⟨(a,b), by simp, hx.1, hxb⟩
      · rcases ih b hr x ⟨(lt_of_not_ge hxb).le, hx.2⟩ with hxhi | ⟨p,hp,hxp⟩
        · exact Or.inl hxhi
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hxp⟩

#print axioms fieldTower_add
#print axioms lfieldTower_add
#print axioms invPowerSeries
#print axioms invTailQ_spec
#print axioms invTailQ_nonneg
#print axioms endLip
#print axioms endULip_sound
#print axioms pieceCover_sound

end CatalanMeasure.GenD.Signed.Data.Cells

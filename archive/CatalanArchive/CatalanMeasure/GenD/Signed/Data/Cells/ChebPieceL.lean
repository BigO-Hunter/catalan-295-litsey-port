module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPiece
public import CatalanMeasure.GenD.Signed.FieldForm
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Data.List.Sort

@[expose] public section

/-! # Laurent Taylor-merged Chebyshev pieces

Canonical CHEBENGINE module, approved by CHEBENGINE-REVIEW.md (b60cdc6a).
The Laurent coefficients/log enclosures are the existing TaylorCell/Core machinery.
The R/J majorants close the infinite remainder; no fixed cutoff discards a tail.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval
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

/-! ## Finite R/J evaluation and the generic analytic remainder bridge -/

@[simp] theorem invBinom_at_zero (s : ℕ) : invBinom s 0 = 1 := by
  cases s <;> simp [invBinom]

theorem invBinom_step (s k : ℕ) :
    invBinom (s+1) (k+1) = invBinom (s+1) k + invBinom s (k+1) := by
  cases s with
  | zero => simp [invBinom]
  | succ s =>
      simpa [invBinom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (Nat.choose_succ_succ (k+s+1) s)

theorem invBinom_asc (s k : ℕ) :
    (invBinom s k : ℚ) = (s.ascFactorial k : ℚ) / (k.factorial : ℚ) := by
  cases s with
  | zero => cases k <;> simp [invBinom, Nat.zero_ascFactorial]
  | succ s =>
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
      have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      simp only [invBinom, Nat.cast_mul]
      rw [mul_div_cancel_left₀ _ hf]
      congr 1
      simpa [Nat.add_comm] using (Nat.choose_symm_add (a := s) (b := k))

/-- Exact finite-prefix telescoping, used to prove the positive recurrence. -/
theorem invPrefix_step (s K : ℕ) (q : ℚ) :
    (1-q) * (∑ k ∈ Finset.range (K+1), (invBinom (s+1) k : ℚ)*q^k) =
      (∑ k ∈ Finset.range (K+1), (invBinom s k : ℚ)*q^k) -
        (invBinom (s+1) K : ℚ)*q^(K+1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ (fun k => (invBinom (s+1) k : ℚ)*q^k) (K+1),
        Finset.sum_range_succ (fun k => (invBinom s k : ℚ)*q^k) (K+1)]
      have he : (invBinom (s+1) (K+1) : ℚ) =
          (invBinom (s+1) K : ℚ) + (invBinom s (K+1) : ℚ) := by
        exact_mod_cast invBinom_step s K
      rw [he, pow_succ q (K+1)]
      linear_combination ih

theorem invTailQ_step (s K : ℕ) (q : ℚ) (hq : q ≠ 1) :
    (1-q) * invTailQ (s+1) K q =
      invTailQ s K q + (invBinom (s+1) K : ℚ)*q^(K+1) := by
  have hq' : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hp := invPrefix_step s K q
  have hi : (1-q) * (1 / (1-q)^(s+1)) = 1 / (1-q)^s := by
    rw [pow_succ]
    field_simp
  unfold invTailQ
  rw [mul_sub, hi]
  linarith [hp]

/-- Positive evaluator for R_s(K,q), structurally recursive in s. -/
def invTailPosQ (K : ℕ) (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | s+1 => (invTailPosQ K q s + (invBinom (s+1) K : ℚ)*q^(K+1))/(1-q)

theorem invTailPosQ_eq (K : ℕ) (q : ℚ) (hq : q ≠ 1) :
    ∀ s : ℕ, invTailPosQ K q s = invTailQ s K q := by
  intro s
  induction s with
  | zero =>
      simp [invTailPosQ, invTailQ, invBinom, Finset.sum_ite_eq', Finset.mem_range]
  | succ s ih =>
      rw [invTailPosQ, ih]
      symm
      apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hq))).mpr
      have h := invTailQ_step s K q hq
      linarith

/-- J_s(K,q): the tail of q*z*(1-q*z)^(-(s+1)) at z=1. -/
def logInvTailQ (s K : ℕ) (q : ℚ) : ℚ :=
  q * (invTailPosQ K q (s+1) + (invBinom (s+1) K : ℚ)*q^K)

theorem logInvTailQ_nonneg (s K : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ logInvTailQ s K q := by
  unfold logInvTailQ
  rw [invTailPosQ_eq K q (ne_of_lt hq1)]
  exact mul_nonneg hq0 (add_nonneg (invTailQ_nonneg (s+1) K q hq0 hq1)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _)))

/-- A known convergent majorant controls every term past a finite prefix.
This is the generic bridge used for the Laurent R/J tails. -/
theorem series_tail_error (f d : ℕ → ℝ) (F D : ℝ) (N : ℕ)
    (hf : HasSum f F) (hd : HasSum d D) (hb : ∀ k, |f k| ≤ d k) :
    |F - ∑ k ∈ Finset.range N, f k| ≤ D - ∑ k ∈ Finset.range N, d k := by
  have hf' := hf.summable.sum_add_tsum_nat_add N
  have hd' := hd.summable.sum_add_tsum_nat_add N
  rw [hf.tsum_eq] at hf'
  rw [hd.tsum_eq] at hd'
  have hdt : HasSum (fun k => d (k+N)) (D - ∑ k ∈ Finset.range N, d k) := by
    convert ((summable_nat_add_iff N).2 hd.summable).hasSum using 1
    linarith
  have hbound := tsum_of_norm_bounded hdt (f := fun k => f (k+N))
    (fun k => by simpa only [Real.norm_eq_abs] using hb (k+N))
  have he : F - ∑ k ∈ Finset.range N, f k = ∑' k, f (k+N) := by linarith
  rw [he]
  simpa only [Real.norm_eq_abs] using hbound

/-- Precise coefficients through K, a closed majorant only beyond K. -/
theorem series_refined_tail_error (f c d : ℕ → ℝ) (F D : ℝ) (M K : ℕ)
    (hMK : M ≤ K) (hf : HasSum f F) (hd : HasSum d D)
    (hc : ∀ k, |f k| ≤ c k) (hb : ∀ k, |f k| ≤ d k) :
    |F - ∑ k ∈ Finset.range (M+1), f k| ≤
      (∑ k ∈ Finset.Ico (M+1) (K+1), c k) +
        (D - ∑ k ∈ Finset.range (K+1), d k) := by
  have ht := series_tail_error f d F D (K+1) hf hd hb
  have hp := Finset.sum_range_add_sum_Ico f (Nat.add_le_add_right hMK 1)
  have hbfin : |∑ k ∈ Finset.Ico (M+1) (K+1), f k| ≤
      ∑ k ∈ Finset.Ico (M+1) (K+1), c k := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => hc k))
  have he : F - ∑ k ∈ Finset.range (M+1), f k =
      (∑ k ∈ Finset.Ico (M+1) (K+1), f k) + (F - ∑ k ∈ Finset.range (K+1), f k) := by
    linarith
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hbfin ht)

/-! ## Laurent analytic identity at a nonzero centre -/

/-- Rescaling the already-defined normalized inverse-power coefficient. -/
theorem monoInv_scaled_eq (s k : ℕ) (c : ℚ) (hc : c ≠ 0) (y : ℝ) :
    monoInv s k (c : ℝ)/(k.factorial : ℝ)*y^k =
      (invBinom s k : ℝ)/(c : ℝ)^s * (-y/(c : ℝ))^k := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hb : (invBinom s k : ℝ) = (s.ascFactorial k : ℝ)/(k.factorial : ℝ) := by
    have h := congrArg (fun v : ℚ => (v : ℝ)) (invBinom_asc s k)
    push_cast at h
    exact h
  have hpow : (-y/(c : ℝ))^k = (-1 : ℝ)^k*y^k/(c : ℝ)^k := by
    rw [div_pow, neg_pow]
  rw [hb, hpow]
  simp only [monoInv, pow_add]
  field_simp [hc']
  <;> ring

theorem monoInvSeries (s : ℕ) (c : ℚ) (hc : c ≠ 0) (y : ℝ)
    (hy : |y| < |(c : ℝ)|) :
    HasSum (fun k : ℕ => monoInv s k (c : ℝ) / (k.factorial : ℝ) * y^k)
      (monoInv s 0 ((c : ℝ)+y)) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcy : (c : ℝ)+y ≠ 0 := by
    intro h
    have he : y = -(c : ℝ) := by linarith
    rw [he, abs_neg] at hy
    exact (lt_irrefl _) hy
  have hu : |-y/(c : ℝ)| < 1 := by
    rw [abs_div, abs_neg]
    exact (div_lt_one (abs_pos.mpr hc')).mpr hy
  have hs := (invPowerSeries s (-y/(c : ℝ)) hu).mul_left (1/(c : ℝ)^s)
  convert hs using 1
  · funext k
    rw [monoInv_scaled_eq s k c hc y]
    ring
  · have he : 1-(-y/(c : ℝ)) = ((c : ℝ)+y)/(c : ℝ) := by
      field_simp
      <;> ring
    simp only [monoInv, pow_zero, Nat.ascFactorial_zero, Nat.cast_one, one_mul, Nat.add_zero]
    rw [he, div_pow]
    field_simp
    <;> ring

theorem zTowAuxSeries (c : ℚ) (hc : c ≠ 0) (y : ℝ) (hy : |y| < |(c : ℝ)|) :
    ∀ (a : List ℚ) (s : ℕ),
      HasSum (fun k : ℕ => zTowAux s a k (c : ℝ) / (k.factorial : ℝ) * y^k)
        (zTowAux s a 0 ((c : ℝ)+y)) := by
  intro a
  induction a with
  | nil => intro s; simpa [zTowAux] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons a as ih =>
      intro s
      convert ((monoInvSeries s c hc y hy).mul_left (a : ℝ)).add (ih (s+1)) using 1
      · funext k
        simp only [zTowAux]
        ring
      · rfl

theorem lfTowerSeries (o : Option (ℚ × ℚ)) (c : ℚ) (y : ℝ)
    (hne : ∀ ab, o = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0)
    (hy : ∀ ab, o = some ab → |-(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| < 1) :
    HasSum (fun k : ℕ => lfTower o k (c : ℝ) / (k.factorial : ℝ) * y^k)
      (lfTower o 0 ((c : ℝ)+y)) := by
  cases o with
  | none =>
      have he : (fun k : ℕ => lfTower none k (c : ℝ) / (k.factorial : ℝ) * y^k) =
          (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) := by
        funext k
        cases k <;> simp [lfTower, oneTower]
      rw [he]
      simpa [lfTower, oneTower] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  | some ab =>
      let a : ℝ := ab.1
      let b : ℝ := ab.2
      let d : ℝ := a*(c : ℝ)-b
      let u : ℝ := -a*y/d
      have hd : d ≠ 0 := hne ab rfl
      have hd' : a*(c : ℝ)-b ≠ 0 := hd
      have hu : |u| < 1 := hy ab rfl
      let f : ℕ → ℝ := fun k => linLogTower a b k (c : ℝ)/(k.factorial : ℝ)*y^k
      have hs : HasSum (fun n => f (n+1)) (Real.log (1-u)) := by
        have h := (Real.hasSum_pow_div_log_of_abs_lt_one hu).neg
        convert h using 1
        · funext n
          dsimp [f, u, d, linLogTower]
          rw [Nat.factorial_succ]
          push_cast
          have hn : (n.factorial : ℝ) ≠ 0 := by positivity
          have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
          have hpow : (-a*y/(a*(c : ℝ)-b))^(n+1) =
              (-1 : ℝ)^(n+1)*a^(n+1)*y^(n+1)/(a*(c : ℝ)-b)^(n+1) := by
            rw [div_pow, mul_pow, neg_pow]
          rw [hpow, pow_succ (-1 : ℝ) n]
          field_simp [hd']
          <;> ring
        · ring
      have hf := (hasSum_nat_add_iff (f := f) 1).mp hs
      have hp : 0 < 1-u := by linarith [(le_abs_self u).trans_lt hu]
      have he : a*((c : ℝ)+y)-b = d*(1-u) := by
        dsimp [d, u]
        field_simp [hd']
        <;> ring
      change HasSum f (linLogTower a b 0 ((c : ℝ)+y))
      convert hf using 1
      simp only [Finset.sum_range_one, f, linLogTower, Nat.factorial_zero, Nat.cast_one,
        div_one, pow_zero, mul_one]
      rw [Real.log_abs, he, Real.log_mul hd hp.ne', Real.log_abs]
      dsimp [d]
      ring

theorem laurentTaylor_ident (t : LTerm) (c : ℚ) (hc : c ≠ 0) (y : ℝ)
    (hy0 : |y| < |(c : ℝ)|)
    (hne : ∀ ab, t.2 = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0)
    (hyL : ∀ ab, t.2 = some ab → |-(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| < 1) :
    HasSum (fun k : ℕ => mulTower (zTow t.1) (lfTower t.2) k (c : ℝ) /
      (k.factorial : ℝ)*y^k) (mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y)) := by
  have hz := zTowAuxSeries c hc y hy0 t.1 0
  have hl := lfTowerSeries t.2 c y hne hyL
  have hz' : Summable (fun k : ℕ => ‖zTow t.1 k (c : ℝ)/(k.factorial : ℝ)*y^k‖) := by
    simpa only [Real.norm_eq_abs, zTow] using hz.summable.abs
  have hl' : Summable (fun k : ℕ => ‖lfTower t.2 k (c : ℝ)/(k.factorial : ℝ)*y^k‖) := by
    simpa only [Real.norm_eq_abs] using hl.summable.abs
  have hm := hasSum_sum_range_mul_of_summable_norm hz' hl'
  have hzt : ∑' k : ℕ, zTow t.1 k (c : ℝ)/(k.factorial : ℝ)*y^k =
      zTow t.1 0 ((c : ℝ)+y) := hz.tsum_eq
  rw [hzt, hl.tsum_eq] at hm
  convert hm using 1
  · funext k
    rw [mulTower_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (zTow t.1 i (c : ℝ)/(i.factorial : ℝ))*
        (lfTower t.2 j (c : ℝ)/(j.factorial : ℝ))), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hp : y^i * y^(k-i) = y^k := by rw [← pow_add, Nat.add_sub_of_le hik]
    rw [← hp]
    ring
  · rw [mulTower_zero]

/-! ## The inverse-polynomial majorant U_k and its exact finite remainder -/

def invMajAux (c q : ℚ) : ℕ → List ℚ → ℕ → ℚ
  | _, [], _ => 0
  | s, a :: as, k => qabs' a / (qabs' c)^s * (invBinom s k : ℚ) * q^k +
      invMajAux c q (s+1) as k

def invMajTotal (c q : ℚ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a / (qabs' c)^s / (1-q)^s + invMajTotal c q (s+1) as

def invMajTail (c q : ℚ) (K : ℕ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a / (qabs' c)^s * invTailPosQ K q s + invMajTail c q K (s+1) as

theorem monoInv_scaled_bound (s k : ℕ) (c q : ℚ) (hc : c ≠ 0) (hq : 0 ≤ q) (y : ℝ)
    (hy : |y| ≤ (q : ℝ)*|(c : ℝ)|) :
    |monoInv s k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
      (invBinom s k : ℝ)/|(c : ℝ)|^s*(q : ℝ)^k := by
  rw [monoInv_scaled_eq s k c hc y]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcp : 0 < |(c : ℝ)| := abs_pos.mpr hc'
  have hb : (0 : ℝ) ≤ invBinom s k := Nat.cast_nonneg _
  simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hb]
  have hp := pow_le_pow_left₀ (div_nonneg (abs_nonneg y) hcp.le)
    ((div_le_iff₀ hcp).mpr hy) k
  exact mul_le_mul_of_nonneg_left hp (div_nonneg hb (pow_nonneg hcp.le _))

theorem invMajAux_bound (c q : ℚ) (hc : c ≠ 0) (hq : 0 ≤ q) (y : ℝ)
    (hy : |y| ≤ (q : ℝ)*|(c : ℝ)|) : ∀ (a : List ℚ) (s k : ℕ),
    |zTowAux s a k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤ (invMajAux c q s a k : ℝ) := by
  intro a
  induction a with
  | nil => intro s k; simp [zTowAux, invMajAux]
  | cons a as ih =>
      intro s k
      have ht := monoInv_scaled_bound s k c q hc hq y hy
      have hr := ih (s+1) k
      have he : zTowAux s (a :: as) k (c : ℝ)/(k.factorial : ℝ)*y^k =
          (a : ℝ)*(monoInv s k (c : ℝ)/(k.factorial : ℝ)*y^k) +
            zTowAux (s+1) as k (c : ℝ)/(k.factorial : ℝ)*y^k := by
        simp only [zTowAux]
        ring
      rw [he]
      have hm : |(a : ℝ)*(monoInv s k (c : ℝ)/(k.factorial : ℝ)*y^k)| ≤
          |(a : ℝ)| *((invBinom s k : ℝ)/|(c : ℝ)|^s*(q : ℝ)^k) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ht (abs_nonneg (a : ℝ))
      have hs : |(a : ℝ)*(monoInv s k (c : ℝ)/(k.factorial : ℝ)*y^k) +
          zTowAux (s+1) as k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
          |(a : ℝ)| *((invBinom s k : ℝ)/|(c : ℝ)|^s*(q : ℝ)^k) +
            (invMajAux c q (s+1) as k : ℝ) :=
        (abs_add_le _ _).trans (add_le_add hm hr)
      simp only [invMajAux, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
        qabs'_cast]
      convert hs using 1 <;> ring

theorem invMajAux_nonneg (c q : ℚ) (hq : 0 ≤ q) : ∀ (a : List ℚ) (s k : ℕ),
    0 ≤ invMajAux c q s a k := by
  intro a
  induction a with
  | nil => intro s k; simp [invMajAux]
  | cons a as ih =>
      intro s k
      simp only [invMajAux]
      exact add_nonneg (mul_nonneg (mul_nonneg (div_nonneg (show 0 ≤ qabs' a by rw [qabs'_eq_abs]; exact abs_nonneg _) (pow_nonneg (show 0 ≤ qabs' c by rw [qabs'_eq_abs]; exact abs_nonneg _) _))
        (Nat.cast_nonneg _)) (pow_nonneg hq _)) (ih (s+1) k)

theorem invMajAuxSeries (c q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : ∀ (a : List ℚ) (s : ℕ),
    HasSum (fun k : ℕ => (invMajAux c q s a k : ℝ)) (invMajTotal c q s a : ℝ) := by
  have hq : |(q : ℝ)| < 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hq0)]
    exact_mod_cast hq1
  intro a
  induction a with
  | nil => intro s; simpa [invMajAux, invMajTotal] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons a as ih =>
      intro s
      have ht := (invPowerSeries s (q : ℝ) hq).mul_left ((qabs' a / (qabs' c)^s : ℚ) : ℝ)
      convert ht.add (ih (s+1)) using 1
      · funext k
        simp only [invMajAux]
        push_cast <;> ring
      · simp only [invMajTotal]
        push_cast <;> ring

theorem invMajTail_eq (c q : ℚ) (K : ℕ) (hq : q ≠ 1) : ∀ (a : List ℚ) (s : ℕ),
    invMajTotal c q s a - (∑ k ∈ Finset.range (K+1), invMajAux c q s a k) =
      invMajTail c q K s a := by
  intro a
  induction a with
  | nil => intro s; simp [invMajTotal, invMajAux, invMajTail]
  | cons a as ih =>
      intro s
      have hp : (∑ k ∈ Finset.range (K+1), invMajAux c q s (a :: as) k) =
          qabs' a/(qabs' c)^s * (∑ k ∈ Finset.range (K+1), (invBinom s k : ℚ)*q^k) +
            ∑ k ∈ Finset.range (K+1), invMajAux c q (s+1) as k := by
        simp only [invMajAux, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hp, invMajTotal, invMajTail, invTailPosQ_eq K q hq]
      unfold invTailQ
      linear_combination ih (s+1)

/-! ## Log-factor and product coefficient majorants -/

def lfMaj (o : Option (ℚ × ℚ)) (L q : ℚ) : ℕ → ℚ
  | 0 => match o with | none => 1 | some _ => L
  | k+1 => match o with
    | none => 0
    | some ab => if ab.1 = 0 then 0 else q^(k+1)/((k : ℚ)+1)

def lfCoarse (o : Option (ℚ × ℚ)) (L q : ℚ) : ℕ → ℚ
  | 0 => match o with | none => 1 | some _ => L
  | k+1 => match o with
    | none => 0
    | some ab => if ab.1 = 0 then 0 else q^(k+1)

theorem lf_scaled_eq (ab : ℚ × ℚ) (c : ℚ) (k : ℕ) (y : ℝ)
    (hd : (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0) :
    lfTower (some ab) (k+1) (c : ℝ)/((k+1).factorial : ℝ)*y^(k+1) =
      (-1 : ℝ)^k * ((ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2))^(k+1)/((k : ℝ)+1) := by
  simp only [lfTower, linLogTower, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ)+1 ≠ 0 := by positivity
  rw [div_pow, mul_pow]
  field_simp [hd]
  <;> ring

theorem lfMaj_nonneg (o : Option (ℚ × ℚ)) (L q : ℚ) (hL : 0 ≤ L) (hq : 0 ≤ q) (k : ℕ) :
    0 ≤ lfMaj o L q k := by
  cases o with
  | none => cases k <;> simp [lfMaj]
  | some ab =>
      cases k with
      | zero => exact hL
      | succ k =>
          simp only [lfMaj]
          split_ifs <;> positivity

theorem lfMaj_le_coarse (o : Option (ℚ × ℚ)) (L q : ℚ) (hq : 0 ≤ q) (k : ℕ) :
    lfMaj o L q k ≤ lfCoarse o L q k := by
  cases o with
  | none => cases k <;> simp [lfMaj, lfCoarse]
  | some ab =>
      cases k with
      | zero => exact le_refl _
      | succ k =>
          simp only [lfMaj, lfCoarse]
          split_ifs with ha
          · exact le_refl _
          · have hk : (0 : ℚ) < (k : ℚ)+1 := by positivity
            apply (div_le_iff₀ hk).mpr
            nlinarith [mul_nonneg (pow_nonneg hq (k+1)) (Nat.cast_nonneg k : (0 : ℚ) ≤ k)]

theorem lfMaj_bound (o : Option (ℚ × ℚ)) (c L q : ℚ) (y : ℝ) (hq : 0 ≤ q)
    (hne : ∀ ab, o = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0)
    (hL : ∀ ab, o = some ab → |Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (L : ℝ))
    (hR : ∀ ab, o = some ab → |(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| ≤ (q : ℝ))
    (k : ℕ) :
    |lfTower o k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤ (lfMaj o L q k : ℝ) := by
  cases o with
  | none => cases k <;> simp [lfTower, oneTower, lfMaj]
  | some ab =>
      cases k with
      | zero => simpa [lfTower, linLogTower, lfMaj] using hL ab rfl
      | succ k =>
          by_cases ha : ab.1 = 0
          · simp [lfTower, linLogTower, lfMaj, ha]
          · rw [lf_scaled_eq ab c k y (hne ab rfl)]
            have hk : (0 : ℝ) < (k : ℝ)+1 := by positivity
            have hp := pow_le_pow_left₀ (abs_nonneg ((ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)))
              (hR ab rfl) (k+1)
            have hd := div_le_div_of_nonneg_right hp hk.le
            simpa only [lfMaj, if_neg ha, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
              Rat.cast_one, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_pos hk] using hd

/-- The normalized product coefficient is the finite convolution of normalized factors. -/
theorem mulTower_scaled (z l : ℕ → ℝ → ℝ) (c y : ℝ) (k : ℕ) :
    mulTower z l k c/(k.factorial : ℝ)*y^k =
      ∑ i ∈ Finset.range (k+1),
        (z i c/(i.factorial : ℝ)*y^i)*(l (k-i) c/((k-i).factorial : ℝ)*y^(k-i)) := by
  rw [mulTower_div, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (z i c/(i.factorial : ℝ))*(l j c/(j.factorial : ℝ))), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hp : y^i*y^(k-i) = y^k := by rw [← pow_add, Nat.add_sub_of_le hik]
  rw [← hp]
  ring

theorem mulTower_scaled_bound (z l : ℕ → ℝ → ℝ) (c y : ℝ) (U V : ℕ → ℚ)
    (hU : ∀ k, |z k c/(k.factorial : ℝ)*y^k| ≤ (U k : ℝ))
    (hV : ∀ k, |l k c/(k.factorial : ℝ)*y^k| ≤ (V k : ℝ)) (k : ℕ) :
    |mulTower z l k c/(k.factorial : ℝ)*y^k| ≤ (convQ U V k (k+1) : ℝ) := by
  rw [mulTower_scaled, convQ_cast]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul (hU i) (hV (k-i)) (abs_nonneg _)
    ((abs_nonneg _).trans (hU i))

/-! ## The J-series and scalar coarse product -/

def logInvCoef (s : ℕ) (q : ℚ) : ℕ → ℚ
  | 0 => 0
  | k+1 => (invBinom (s+1) k : ℚ)*q^(k+1)

def geoInvCoef (s : ℕ) (L q : ℚ) (k : ℕ) : ℚ :=
  L*(invBinom s k : ℚ)*q^k + logInvCoef s q k

def geoInvTotal (s : ℕ) (L q : ℚ) : ℚ := L/(1-q)^s + q/(1-q)^(s+1)

def geoInvTail (s K : ℕ) (L q : ℚ) : ℚ :=
  L*invTailPosQ K q s + logInvTailQ s K q

theorem invBinom_sum (s k : ℕ) :
    ∑ i ∈ Finset.range (k+1), (invBinom s i : ℚ) = (invBinom (s+1) k : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      exact_mod_cast (invBinom_step s k).symm

theorem logInvCoefSeries (s : ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => (logInvCoef s q k : ℝ)) ((q/(1-q)^(s+1) : ℚ) : ℝ) := by
  have hq : |(q : ℝ)| < 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hq0)]
    exact_mod_cast hq1
  have hp : HasSum (fun k : ℕ => (logInvCoef s q (k+1) : ℝ))
      ((q/(1-q)^(s+1) : ℚ) : ℝ) := by
    convert (invPowerSeries (s+1) (q : ℝ) hq).mul_left (q : ℝ) using 1
    · funext k
      simp only [logInvCoef, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, pow_succ]
      ring
    · push_cast <;> ring
  have hfull := (hasSum_nat_add_iff
    (f := fun k : ℕ => (logInvCoef s q k : ℝ)) 1).mp hp
  simpa [logInvCoef] using hfull

theorem logInvTailQ_eq (s K : ℕ) (q : ℚ) (hq : q ≠ 1) :
    q/(1-q)^(s+1) - (∑ k ∈ Finset.range (K+1), logInvCoef s q k) = logInvTailQ s K q := by
  have hp : (∑ k ∈ Finset.range K, logInvCoef s q (k+1)) =
      q*(∑ k ∈ Finset.range K, (invBinom (s+1) k : ℚ)*q^k) := by
    simp only [logInvCoef]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [Finset.sum_range_succ' (fun k => logInvCoef s q k) K, hp]
  simp only [logInvCoef, add_zero]
  unfold logInvTailQ
  rw [invTailPosQ_eq K q hq]
  unfold invTailQ
  rw [Finset.sum_range_succ (fun k => (invBinom (s+1) k : ℚ)*q^k) K]
  ring

theorem geoInvCoefSeries (s : ℕ) (L q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => (geoInvCoef s L q k : ℝ)) (geoInvTotal s L q : ℝ) := by
  have hq : |(q : ℝ)| < 1 := by
    rw [abs_of_nonneg (by exact_mod_cast hq0)]
    exact_mod_cast hq1
  have h := ((invPowerSeries s (q : ℝ) hq).mul_left (L : ℝ)).add
    (logInvCoefSeries s q hq0 hq1)
  convert h using 1
  · funext k
    simp only [geoInvCoef]
    push_cast <;> ring
  · simp only [geoInvTotal]
    push_cast <;> ring

theorem geoInvTail_eq (s K : ℕ) (L q : ℚ) (hq : q ≠ 1) :
    geoInvTotal s L q - (∑ k ∈ Finset.range (K+1), geoInvCoef s L q k) =
      geoInvTail s K L q := by
  have hp : (∑ k ∈ Finset.range (K+1), geoInvCoef s L q k) =
      L*(∑ k ∈ Finset.range (K+1), (invBinom s k : ℚ)*q^k) +
        ∑ k ∈ Finset.range (K+1), logInvCoef s q k := by
    simp only [geoInvCoef, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hj := logInvTailQ_eq s K q hq
  rw [hp]
  unfold geoInvTail geoInvTotal
  rw [invTailPosQ_eq K q hq]
  unfold invTailQ
  linear_combination hj

theorem convQ_fin (U V : ℕ → ℚ) (k n : ℕ) :
    convQ U V k n = ∑ i ∈ Finset.range n, U i*V (k-i) := by
  induction n with
  | zero => simp [convQ]
  | succ n ih => rw [convQ, Finset.sum_range_succ, ih]

theorem invGeo_conv (s k : ℕ) (q L : ℚ) (ab : ℚ × ℚ) (ha : ab.1 ≠ 0) :
    convQ (fun i => (invBinom s i : ℚ)*q^i) (lfCoarse (some ab) L q) k (k+1) =
      geoInvCoef s L q k := by
  cases k with
  | zero => simp [convQ, lfCoarse, geoInvCoef, logInvCoef]
  | succ k =>
      have hp : convQ (fun i => (invBinom s i : ℚ)*q^i)
          (lfCoarse (some ab) L q) (k+1) (k+1) =
            (invBinom (s+1) k : ℚ)*q^(k+1) := by
        rw [convQ_fin]
        calc
          (∑ i ∈ Finset.range (k+1), (invBinom s i : ℚ)*q^i*lfCoarse (some ab) L q (k+1-i)) =
              ∑ i ∈ Finset.range (k+1), (invBinom s i : ℚ)*q^(k+1) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hik : i < k+1 := Finset.mem_range.mp hi
                obtain ⟨m, hm⟩ : ∃ m, k+1-i = m+1 := ⟨k-i, by omega⟩
                rw [hm, lfCoarse, if_neg ha]
                have he : i+(m+1) = k+1 := by omega
                rw [mul_assoc, ← pow_add, he]
          _ = (invBinom (s+1) k : ℚ)*q^(k+1) := by
                rw [← Finset.sum_mul, invBinom_sum]
      rw [convQ, hp]
      simp only [Nat.sub_self, lfCoarse, geoInvCoef, logInvCoef]
      ring

/-! ## Summing the scalar R/J formulas over a Laurent polynomial -/

def geoMajAux (c q L : ℚ) : ℕ → List ℚ → ℕ → ℚ
  | _, [], _ => 0
  | s, a :: as, k => qabs' a/(qabs' c)^s*geoInvCoef s L q k + geoMajAux c q L (s+1) as k

def geoMajTotal (c q L : ℚ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a/(qabs' c)^s*geoInvTotal s L q + geoMajTotal c q L (s+1) as

def geoMajTail (c q L : ℚ) (K : ℕ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | s, a :: as => qabs' a/(qabs' c)^s*geoInvTail s K L q + geoMajTail c q L K (s+1) as

theorem geoMajAuxSeries (c q L : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) : ∀ (a : List ℚ) (s : ℕ),
    HasSum (fun k : ℕ => (geoMajAux c q L s a k : ℝ)) (geoMajTotal c q L s a : ℝ) := by
  intro a
  induction a with
  | nil => intro s; simpa [geoMajAux, geoMajTotal] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons a as ih =>
      intro s
      have ht := (geoInvCoefSeries s L q hq0 hq1).mul_left ((qabs' a/(qabs' c)^s : ℚ) : ℝ)
      convert ht.add (ih (s+1)) using 1
      · funext k
        simp only [geoMajAux]
        push_cast <;> ring
      · simp only [geoMajTotal]
        push_cast <;> ring

theorem geoMajTail_eq (c q L : ℚ) (K : ℕ) (hq : q ≠ 1) : ∀ (a : List ℚ) (s : ℕ),
    geoMajTotal c q L s a - (∑ k ∈ Finset.range (K+1), geoMajAux c q L s a k) =
      geoMajTail c q L K s a := by
  intro a
  induction a with
  | nil => intro s; simp [geoMajTotal, geoMajAux, geoMajTail]
  | cons a as ih =>
      intro s
      have hp : (∑ k ∈ Finset.range (K+1), geoMajAux c q L s (a :: as) k) =
          qabs' a/(qabs' c)^s*(∑ k ∈ Finset.range (K+1), geoInvCoef s L q k) +
            ∑ k ∈ Finset.range (K+1), geoMajAux c q L (s+1) as k := by
        simp only [geoMajAux, Finset.sum_add_distrib, Finset.mul_sum]
      rw [hp, geoMajTotal, geoMajTail]
      linear_combination (qabs' a/(qabs' c)^s) * (geoInvTail_eq s K L q hq) + ih (s+1)

theorem convQ_add_left (U W V : ℕ → ℚ) (k : ℕ) : ∀ n : ℕ,
    convQ (fun i => U i+W i) V k n = convQ U V k n + convQ W V k n := by
  intro n
  induction n with
  | zero => simp [convQ]
  | succ n ih => simp only [convQ, ih]; ring

theorem convQ_scale_left (U V : ℕ → ℚ) (b : ℚ) (k : ℕ) : ∀ n : ℕ,
    convQ (fun i => b*U i) V k n = b*convQ U V k n := by
  intro n
  induction n with
  | zero => simp [convQ]
  | succ n ih => simp only [convQ, ih]; ring

theorem invMajAux_conv (c q L : ℚ) (ab : ℚ × ℚ) (ha : ab.1 ≠ 0) :
    ∀ (a : List ℚ) (s k : ℕ),
    convQ (invMajAux c q s a) (lfCoarse (some ab) L q) k (k+1) = geoMajAux c q L s a k := by
  intro a
  induction a with
  | nil => intro s k; simp [convQ_fin, invMajAux, geoMajAux]
  | cons a as ih =>
      intro s k
      have he : invMajAux c q s (a :: as) = fun i =>
          qabs' a/(qabs' c)^s*((invBinom s i : ℚ)*q^i) + invMajAux c q (s+1) as i := by
        funext i
        simp only [invMajAux]
        ring
      rw [he, convQ_add_left, convQ_scale_left, invGeo_conv s k q L ab ha, ih (s+1) k]
      rfl

theorem convQ_delta_right (U : ℕ → ℚ) (L : ℚ) (k : ℕ) :
    convQ U (fun j => if j = 0 then L else 0) k (k+1) = U k*L := by
  rw [convQ_fin]
  calc
    (∑ i ∈ Finset.range (k+1), U i*(if k-i = 0 then L else 0)) =
        U k*(if k-k = 0 then L else 0) := by
      apply Finset.sum_eq_single k
      · intro i hi hik
        have hi' : i < k := by have := Finset.mem_range.mp hi; omega
        have hs : k-i ≠ 0 := by omega
        simp [hs]
      · intro hk
        exact (hk (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim
    _ = U k*L := by simp

/-! ## One coarse Laurent majorant, with the exact constant-factor cases -/

def laurentCoarseCoef (c q L : ℚ) (t : LTerm) (k : ℕ) : ℚ :=
  convQ (invMajAux c q 0 t.1) (lfCoarse t.2 L q) k (k+1)

def laurentCoarseTotal (c q L : ℚ) (t : LTerm) : ℚ :=
  match t.2 with
  | none => invMajTotal c q 0 t.1
  | some ab => if ab.1 = 0 then L*invMajTotal c q 0 t.1 else geoMajTotal c q L 0 t.1

def laurentCoarseTail (c q L : ℚ) (K : ℕ) (t : LTerm) : ℚ :=
  match t.2 with
  | none => invMajTail c q K 0 t.1
  | some ab => if ab.1 = 0 then L*invMajTail c q K 0 t.1 else geoMajTail c q L K 0 t.1

theorem laurentCoarseCoefSeries (c q L : ℚ) (t : LTerm) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => (laurentCoarseCoef c q L t k : ℝ)) (laurentCoarseTotal c q L t : ℝ) := by
  rcases t with ⟨a,o⟩
  cases o with
  | none =>
      have he : lfCoarse none L q = fun k => if k = 0 then (1 : ℚ) else 0 := by
        funext k
        cases k <;> simp [lfCoarse]
      simp only [laurentCoarseCoef, he, convQ_delta_right, mul_one, laurentCoarseTotal]
      exact invMajAuxSeries c q hq0 hq1 a 0
  | some ab =>
      by_cases ha : ab.1 = 0
      · have he : lfCoarse (some ab) L q = fun k => if k = 0 then L else 0 := by
          funext k
          cases k <;> simp [lfCoarse, ha]
        have h := (invMajAuxSeries c q hq0 hq1 a 0).mul_right (L : ℝ)
        convert h using 1
        · funext k
          simp only [laurentCoarseCoef, he, convQ_delta_right, Rat.cast_mul]
        · simp only [laurentCoarseTotal, if_pos ha]
          push_cast <;> ring
      · simp only [laurentCoarseCoef, laurentCoarseTotal, if_neg ha]
        simp_rw [invMajAux_conv c q L ab ha a 0]
        exact geoMajAuxSeries c q L hq0 hq1 a 0

theorem laurentCoarseTail_eq (c q L : ℚ) (K : ℕ) (t : LTerm) (hq : q ≠ 1) :
    laurentCoarseTotal c q L t - (∑ k ∈ Finset.range (K+1), laurentCoarseCoef c q L t k) =
      laurentCoarseTail c q L K t := by
  rcases t with ⟨a,o⟩
  cases o with
  | none =>
      have he : lfCoarse none L q = fun k => if k = 0 then (1 : ℚ) else 0 := by
        funext k
        cases k <;> simp [lfCoarse]
      simp only [laurentCoarseCoef, he, convQ_delta_right, mul_one, laurentCoarseTotal, laurentCoarseTail]
      exact invMajTail_eq c q K hq a 0
  | some ab =>
      by_cases ha : ab.1 = 0
      · have he : lfCoarse (some ab) L q = fun k => if k = 0 then L else 0 := by
          funext k
          cases k <;> simp [lfCoarse, ha]
        simp only [laurentCoarseCoef, he, convQ_delta_right, laurentCoarseTotal, laurentCoarseTail, if_pos ha]
        rw [← Finset.sum_mul]
        linear_combination L * (invMajTail_eq c q K hq a 0)
      · simp only [laurentCoarseCoef, laurentCoarseTotal, laurentCoarseTail, if_neg ha]
        simp_rw [invMajAux_conv c q L ab ha a 0]
        exact geoMajTail_eq c q L K hq a 0

def laurentFineCoef (c q0 qL L : ℚ) (t : LTerm) (k : ℕ) : ℚ :=
  convQ (invMajAux c q0 0 t.1) (lfMaj t.2 L qL) k (k+1)

/-- The section-7.1 tail: precise convolution up to K, plus the full R/J remainder. -/
def laurentTail (c q0 qL L : ℚ) (M K : ℕ) (t : LTerm) : ℚ :=
  (∑ k ∈ Finset.Ico (M+1) (K+1), laurentFineCoef c q0 qL L t k) +
    laurentCoarseTail c (max q0 qL) L K t

theorem laurentMajorant_tail (t : LTerm) (c q0 qL L : ℚ) (M K : ℕ) (y : ℝ)
    (hc : c ≠ 0) (hq0 : 0 ≤ q0) (hq0' : q0 ≤ 1/2) (hqL : 0 ≤ qL) (hqL' : qL ≤ 1/2)
    (hMK : M ≤ K) (hy : |y| ≤ (q0 : ℝ)*|(c : ℝ)|)
    (hne : ∀ ab, t.2 = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0)
    (hL : ∀ ab, t.2 = some ab → |Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (L : ℝ))
    (hR : ∀ ab, t.2 = some ab → |(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| ≤ (qL : ℝ)) :
    |mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
      ∑ k ∈ Finset.range (M+1),
        mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
      (laurentTail c q0 qL L M K t : ℝ) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hy0 : |y| < |(c : ℝ)| := by
    have hq : (q0 : ℝ) ≤ 1/2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hq0'
      push_cast at h
      exact h
    have hm := mul_le_mul_of_nonneg_right hq (abs_nonneg (c : ℝ))
    have hp : (1/2 : ℝ)*|(c : ℝ)| < |(c : ℝ)| := by linarith [abs_pos.mpr hc']
    exact (hy.trans hm).trans_lt hp
  have hyL : ∀ ab, t.2 = some ab → |-(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| < 1 := by
    intro ab hab
    have hq : (qL : ℝ) ≤ 1/2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr hqL'
      push_cast at h
      exact h
    have hr := hR ab hab
    have he : -(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2) =
        -((ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)) := by ring
    rw [he, abs_neg]
    linarith
  have hf := laurentTaylor_ident t c hc y hy0 hne hyL
  have hq : 0 ≤ max q0 qL := hq0.trans (le_max_left _ _)
  have hq1 : max q0 qL < 1 := (max_le hq0' hqL').trans_lt (by norm_num)
  have hyq : |y| ≤ ((max q0 qL : ℚ) : ℝ)*|(c : ℝ)| := by
    have hh : (q0 : ℝ) ≤ ((max q0 qL : ℚ) : ℝ) := by exact_mod_cast le_max_left q0 qL
    exact hy.trans (mul_le_mul_of_nonneg_right hh (abs_nonneg _))
  have hRq : ∀ ab, t.2 = some ab → |(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| ≤
      ((max q0 qL : ℚ) : ℝ) := by
    intro ab hab
    have hh : (qL : ℝ) ≤ ((max q0 qL : ℚ) : ℝ) := by exact_mod_cast le_max_right q0 qL
    exact (hR ab hab).trans hh
  have hU := invMajAux_bound c q0 hc hq0 y hy t.1 0
  have hV := lfMaj_bound t.2 c L qL y hqL hne hL hR
  have hC : ∀ k, |mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
      (laurentFineCoef c q0 qL L t k : ℝ) := by
    intro k
    exact mulTower_scaled_bound (zTow t.1) (lfTower t.2) (c : ℝ) y (invMajAux c q0 0 t.1) (lfMaj t.2 L qL) hU hV k
  have hUq := invMajAux_bound c (max q0 qL) hc hq y hyq t.1 0
  have hVq : ∀ k, |lfTower t.2 k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
      (lfCoarse t.2 L (max q0 qL) k : ℝ) := by
    intro k
    have h := lfMaj_bound t.2 c L (max q0 qL) y hq hne hL hRq k
    have he : (lfMaj t.2 L (max q0 qL) k : ℝ) ≤ (lfCoarse t.2 L (max q0 qL) k : ℝ) := by
      exact_mod_cast lfMaj_le_coarse t.2 L (max q0 qL) hq k
    exact h.trans he
  have hD : ∀ k, |mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k| ≤
      (laurentCoarseCoef c (max q0 qL) L t k : ℝ) := by
    intro k
    exact mulTower_scaled_bound (zTow t.1) (lfTower t.2) (c : ℝ) y (invMajAux c (max q0 qL) 0 t.1) (lfCoarse t.2 L (max q0 qL)) hUq hVq k
  have hd := laurentCoarseCoefSeries c (max q0 qL) L t hq hq1
  have ht := series_refined_tail_error _ _ _ _ _ M K hMK hf hd hC hD
  have he := congrArg (fun v : ℚ => (v : ℝ)) (laurentCoarseTail_eq c (max q0 qL) L K t (ne_of_lt hq1))
  push_cast at he
  unfold laurentTail
  push_cast
  linarith [ht]

/-! ## Finite coefficient enclosure, reusing lTerm_approx -/

def laurentPoly (t : LTerm) (c L : ℚ) (M P : ℕ) : List ℚ :=
  (List.range (M+1)).map (fun k => dyRound P (lTermCoef t c L k))

def laurentCoeffErr (t : LTerm) (c L ε r : ℚ) (M P : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (M+1),
    (lEps t.2 ε*qabs' (zHat t.1 c k) + qabs' (lTermCoef t c L k-dyRound P (lTermCoef t c L k)))*r^k

theorem polyApprox_error (f : ℕ → ℝ) (C E : ℕ → ℚ) (M : ℕ) (r y : ℝ)
    (hy : |y| ≤ r) (hC : ∀ k, |f k-(C k : ℝ)| ≤ (E k : ℝ)) :
    |(∑ k ∈ Finset.range (M+1), f k*y^k) -
      polyTow ((List.range (M+1)).map C) 0 y| ≤
        ∑ k ∈ Finset.range (M+1), (E k : ℝ)*r^k := by
  rw [polyTow_mapRange]
  have he : (∑ k ∈ Finset.range (M+1), f k*y^k) -
      (∑ k ∈ Finset.range (M+1), (C k : ℝ)*y^k) =
        ∑ k ∈ Finset.range (M+1), (f k-(C k : ℝ))*y^k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact mul_le_mul (hC k) (pow_le_pow_left₀ (abs_nonneg y) hy k) (pow_nonneg (abs_nonneg y) _)
    ((abs_nonneg _).trans (hC k))

theorem laurentCoeffErr_spec (t : LTerm) (c L ε r : ℚ) (M P : ℕ) (hc : c ≠ 0) (y : ℝ)
    (hy : |y| ≤ (r : ℝ))
    (hne : ∀ ab, t.2 = some ab → ab.1*c-ab.2 ≠ 0)
    (hL : ∀ ab, t.2 = some ab → |(L : ℝ)-Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (ε : ℝ)) :
    |(∑ k ∈ Finset.range (M+1),
        mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k) -
      polyTow (laurentPoly t c L M P) 0 y| ≤ (laurentCoeffErr t c L ε r M P : ℝ) := by
  have hcoeff : ∀ k : ℕ,
      |mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ) -
        (dyRound P (lTermCoef t c L k) : ℝ)| ≤
      ((lEps t.2 ε*qabs' (zHat t.1 c k) +
        qabs' (lTermCoef t c L k-dyRound P (lTermCoef t c L k)) : ℚ) : ℝ) := by
    intro k
    have h := lTerm_approx t c hc L ε hne hL k
    have he : mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ) -
        (dyRound P (lTermCoef t c L k) : ℝ) =
      (mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ) - (lTermCoef t c L k : ℝ)) +
        ((lTermCoef t c L k : ℝ) - (dyRound P (lTermCoef t c L k) : ℝ)) := by ring
    rw [he]
    have hb := (abs_add_le _ _).trans (add_le_add h
      (le_refl |(lTermCoef t c L k : ℝ)-(dyRound P (lTermCoef t c L k) : ℝ)|))
    simp only [Rat.cast_add, qabs'_cast, Rat.cast_sub]
    exact hb
  have h := polyApprox_error
    (fun k => mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ))
    (fun k => dyRound P (lTermCoef t c L k))
    (fun k => lEps t.2 ε*qabs' (zHat t.1 c k) +
      qabs' (lTermCoef t c L k-dyRound P (lTermCoef t c L k))) M (r : ℝ) y hy hcoeff
  unfold laurentPoly laurentCoeffErr
  push_cast at h ⊢
  exact h

/-! ## The untrusted Laurent piece data and Boolean approximation checker -/

structure LaurentPieceData where
  q0 : ℚ
  qL : ℚ
  L : ℚ
  eps : ℚ
  K : ℕ

/-- Ignore the supplied log ratio for constant factors. -/
def laurentQL (t : LTerm) (d : LaurentPieceData) : ℚ :=
  match t.2 with
  | none => 0
  | some ab => if ab.1 = 0 then 0 else d.qL

def laurentGeom (c r : ℚ) (M : ℕ) (t : LTerm) (d : LaurentPieceData) : Bool :=
  decide (0 ≤ r ∧ c ≠ 0 ∧ 0 ≤ d.q0 ∧ d.q0 ≤ 1/2 ∧ r ≤ d.q0*qabs' c ∧
    0 ≤ laurentQL t d ∧ laurentQL t d ≤ 1/2 ∧ M ≤ d.K ∧ 0 ≤ d.eps) &&
  match t.2 with
  | none => true
  | some ab => decide (ab.1*c-ab.2 ≠ 0 ∧
      qabs' ab.1*r ≤ laurentQL t d*qabs' (ab.1*c-ab.2))

def laurentApx (nL M P : ℕ) (c r : ℚ) (t : LTerm) (d : LaurentPieceData) : Option (List ℚ × ℚ) :=
  if laurentGeom c r M t d && llogsCheck nL c [t] [(d.L,d.eps)] then
    some (laurentPoly t c d.L M P,
      laurentCoeffErr t c d.L d.eps r M P +
        laurentTail c d.q0 (laurentQL t d) (qabs' d.L+d.eps) M d.K t)
  else none

theorem laurentApx_spec {nL M P : ℕ} {c r : ℚ} {t : LTerm} {d : LaurentPieceData}
    {A : List ℚ} {E : ℚ}
    (h : laurentApx nL M P c r t d = some (A,E)) (y : ℝ) (hy : |y| ≤ (r : ℝ)) :
    |mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) - polyTow A 0 y| ≤ (E : ℝ) := by
  unfold laurentApx at h
  split_ifs at h with hchk
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨hg,hl⟩ := hchk
    simp only [laurentGeom, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hr,hc,hq0,hq0',hry,hqL,hqL',hMK,hε⟩,haff⟩ := hg
    have hguard : ∀ ab, t.2 = some ab → ab.1*c-ab.2 ≠ 0 ∧
        qabs' ab.1*r ≤ laurentQL t d*qabs' (ab.1*c-ab.2) := by
      intro ab hab
      rw [hab] at haff
      exact of_decide_eq_true haff
    have hneQ : ∀ ab, t.2 = some ab → ab.1*c-ab.2 ≠ 0 := fun ab hab => (hguard ab hab).1
    have hne : ∀ ab, t.2 = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0 := by
      intro ab hab
      have hn := hneQ ab hab
      exact_mod_cast hn
    have hLv := llogsCheck_spec nL c [t] [(d.L,d.eps)] hl
    have hL : ∀ ab, t.2 = some ab →
        |(d.L : ℝ)-Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (d.eps : ℝ) := hLv.1
    have hLB : ∀ ab, t.2 = some ab →
        |Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ ((qabs' d.L+d.eps : ℚ) : ℝ) := by
      intro ab hab
      have he := abs_le.mp (hL ab hab)
      rw [Rat.cast_add, qabs'_cast, abs_le]
      constructor <;> linarith [he.1, he.2, le_abs_self (d.L : ℝ), neg_abs_le (d.L : ℝ)]
    have hy0 : |y| ≤ (d.q0 : ℝ)*|(c : ℝ)| := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hry
      simp only [Rat.cast_mul, qabs'_cast] at hh
      exact hy.trans hh
    have hR : ∀ ab, t.2 = some ab →
        |(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| ≤ (laurentQL t d : ℝ) := by
      intro ab hab
      have hh := (Rat.cast_le (K := ℝ)).mpr (hguard ab hab).2
      simp only [Rat.cast_mul, qabs'_cast] at hh
      push_cast at hh
      rw [abs_div, abs_mul]
      apply (div_le_iff₀ (abs_pos.mpr (hne ab hab))).mpr
      exact (mul_le_mul_of_nonneg_left hy (abs_nonneg (ab.1 : ℝ))).trans hh
    have ht := laurentMajorant_tail t c d.q0 (laurentQL t d) (qabs' d.L+d.eps) M d.K y
      hc hq0 hq0' hqL hqL' hMK hy0 hne hLB hR
    have hp := laurentCoeffErr_spec t c d.L d.eps r M P hc y hy hneQ hL
    have he : mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
        polyTow (laurentPoly t c d.L M P) 0 y =
      (mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
        ∑ k ∈ Finset.range (M+1), mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k) +
      ((∑ k ∈ Finset.range (M+1), mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k) -
        polyTow (laurentPoly t c d.L M P) 0 y) := by ring
    rw [he, Rat.cast_add]
    have hb := (abs_add_le _ _).trans (add_le_add ht hp)
    linarith

/-! ## Laurent list fold and the merged Chebyshev field checker -/

def laurentM (nL M P : ℕ) (lo hi : ℚ) :
    List LTerm → List LaurentPieceData → Option (List ℚ × ℚ)
  | [], [] => some ([],0)
  | t :: ts, d :: ds =>
      match laurentApx nL M P ((lo+hi)/2) ((hi-lo)/2) t d, laurentM nL M P lo hi ts ds with
      | some a, some b => some (vecAdd a.1 b.1, a.2+b.2)
      | _, _ => none
  | _, _ => none

theorem laurentM_bnd {nL M P : ℕ} {lo hi : ℚ} :
    ∀ (ts : List LTerm) (ds : List LaurentPieceData) (A : List ℚ) (B : ℚ),
      laurentM nL M P lo hi ts ds = some (A,B) →
        Bnd lo hi (fun x => lfieldTower ts 0 x) A B := by
  intro ts
  induction ts with
  | nil =>
      intro ds A B h
      cases ds with
      | nil =>
          simp only [laurentM, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          simpa only [lfieldTower_nil_zero] using Bnd.zero lo hi
      | cons d ds => simp [laurentM] at h
  | cons t ts ih =>
      intro ds A B h
      cases ds with
      | nil => simp [laurentM] at h
      | cons d ds =>
          unfold laurentM at h
          split at h
          · rename_i a b ha hb
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            have ht : Bnd lo hi (fun x => mulTower (zTow t.1) (lfTower t.2) 0 x) a.1 a.2 := by
              intro x hx
              have hA := laurentApx_spec ha (x-(((lo+hi)/2 : ℚ) : ℝ)) (hx_abs lo hi x hx)
              have he : (((lo+hi)/2 : ℚ) : ℝ)+(x-(((lo+hi)/2 : ℚ) : ℝ)) = x := by ring
              rw [he] at hA
              have hu := (abs_le.mp hA).2
              linarith
            have hs := ht.add (ih ds b.1 b.2 hb)
            intro x hx
            simpa only [lfieldTower, List.map_cons, List.sum_cons] using hs x hx
          · simp at h

def mergeUBL (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) : Option ℚ :=
  if lo < hi then
    match plogsM nL nA Ml P lo hi (mergeSites fq.plogs) pd,
      polesM nL nA Mp P lo hi fq.poles qd, laurentM nL ML P lo hi ts ld with
    | some a, some b, some l =>
        some (chebPolyUB (sclPow ((hi-lo)/2) 0
          (vecAdd (shiftLK ((lo+hi)/2) fq.poly.length fq.poly) (vecAdd a.1 (vecAdd b.1 l.1)))) γ +
          a.2+b.2+l.2)
    | _, _, _ => none
  else none

def chebMergePieceL (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (T : ℚ) : Bool :=
  match mergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ with
  | some v => decide (v ≤ T)
  | none => false

theorem mergeUBL_spec (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (v : ℚ) (hv : mergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ = some v) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (v : ℝ) := by
  unfold mergeUBL at hv
  split_ifs at hv with hlo
  · split at hv
    · rename_i a b l ha hb hl
      simp only [Option.some.injEq] at hv
      subst v
      intro x hx
      have hr : (0 : ℝ) < (((hi-lo)/2 : ℚ) : ℝ) := by
        have hh : (lo : ℝ) < (hi : ℝ) := (Rat.cast_lt (K := ℝ)).mpr hlo
        push_cast
        linarith
      have hxc := hx_abs lo hi x hx
      have hp := plogsM_bnd hlo (mergeSites fq.plogs) pd a.1 a.2 ha x hx
      beta_reduce at hp
      rw [mergeSites_eq] at hp
      have hq := polesM_bnd hlo fq.poles qd b.1 b.2 hb x hx
      beta_reduce at hq
      have hL := laurentM_bnd ts ld l.1 l.2 hl x hx
      have hpoly : polyTow fq.poly 0 x =
          polyTow (shiftLK ((lo+hi)/2) fq.poly.length fq.poly) 0 (x-(((lo+hi)/2 : ℚ) : ℝ)) := by
        rw [shiftLK_eq', polyTow_shiftL, sub_add_cancel]
      have hcheb := polyTow_le_cheb
        (vecAdd (shiftLK ((lo+hi)/2) fq.poly.length fq.poly) (vecAdd a.1 (vecAdd b.1 l.1))) γ
        ((lo+hi)/2) ((hi-lo)/2) hr x hxc
      rw [polyTow_vecAdd, polyTow_vecAdd, polyTow_vecAdd] at hcheb
      rw [fieldTower_zero, hpoly]
      simp only [Rat.cast_add]
      beta_reduce at hL
      linarith
    · simp at hv

theorem chebMergePieceL_sound (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (T : ℚ)
    (hchk : chebMergePieceL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ T = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (T : ℝ) := by
  unfold chebMergePieceL at hchk
  split at hchk
  · rename_i v hv
    simp only [decide_eq_true_eq] at hchk
    intro x hx
    exact (mergeUBL_spec fq ts nL nA Mp Ml ML P lo hi pd qd ld γ v hv x hx).trans
      ((Rat.cast_le (K := ℝ)).mpr hchk)
  · simp at hchk

/-- Reconstruct the exact checker from separately checked shifts and term-list results. -/
theorem mergeUBL_of_parts (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ S Ap Aq Al : List ℚ) (Ep Eq El : ℚ) (hlo : lo < hi)
    (hs : shiftLK ((lo+hi)/2) fq.poly.length fq.poly = S)
    (hp : plogsM nL nA Ml P lo hi (mergeSites fq.plogs) pd = some (Ap,Ep))
    (hq : polesM nL nA Mp P lo hi fq.poles qd = some (Aq,Eq))
    (hl : laurentM nL ML P lo hi ts ld = some (Al,El)) :
    mergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ =
      some (chebPolyUB (sclPow ((hi-lo)/2) 0 (vecAdd S (vecAdd Ap (vecAdd Aq Al)))) γ+Ep+Eq+El) := by
  simp only [mergeUBL, if_pos hlo, hp, hq, hl, hs]

/-! ## Exact normal forms for checked trial differences -/

def trimPoly : List ℚ → List ℚ
  | [] => []
  | a :: as => let t := trimPoly as; if t = [] ∧ a = 0 then [] else a :: t

theorem trimPoly_sound (a : List ℚ) (x : ℝ) : polyTow (trimPoly a) 0 x = polyTow a 0 x := by
  induction a with
  | nil => rfl
  | cons a as ih =>
      simp only [trimPoly]
      split_ifs with h
      · have hz : polyTow as 0 x = 0 := by rw [← ih, h.1]; rfl
        simp [polyTow, h.2, hz]
      · simp only [polyTow, ih]

theorem map_sum_mergeSort {α : Type} (l : List α) (r : α → α → Bool) (f : α → ℝ) :
    ((l.mergeSort r).map f).sum = (l.map f).sum :=
  ((List.mergeSort_perm l r).map f).sum_eq

def siteClean : List (List ℚ × ℚ) → List (List ℚ × ℚ)
  | [] => []
  | t :: ts => if trimPoly t.1 = [] then siteClean ts else (trimPoly t.1,t.2) :: siteClean ts

theorem siteClean_sound (ts : List (List ℚ × ℚ)) (x : ℝ) :
    ((siteClean ts).map (fun t => polyTow t.1 0 x*Real.log |x-(t.2 : ℝ)|)).sum =
      (ts.map (fun t => polyTow t.1 0 x*Real.log |x-(t.2 : ℝ)|)).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rcases t with ⟨P,e⟩
      simp only [siteClean]
      split_ifs with h
      · have hz : polyTow P 0 x = 0 := by rw [← trimPoly_sound P x, h]; rfl
        simp only [List.map_cons, List.sum_cons, ih, hz, zero_mul, zero_add]
      · simp only [List.map_cons, List.sum_cons, trimPoly_sound, ih]


/-- Structural insertion/sort is deliberately kernel-reducible across module boundaries. -/
def insertKernel {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if le a b then a :: b :: bs else b :: insertKernel le a bs

def sortKernel {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: as => insertKernel le a (sortKernel le as)

theorem map_sum_insertKernel {α : Type} (le : α → α → Bool) (f : α → ℝ) (a : α) :
    ∀ l : List α, ((insertKernel le a l).map f).sum = f a+(l.map f).sum := by
  intro l
  induction l with
  | nil => simp [insertKernel]
  | cons b bs ih =>
      simp only [insertKernel]
      split_ifs
      · simp
      · simp only [List.map_cons,List.sum_cons,ih]
        ring

theorem map_sum_sortKernel {α : Type} (le : α → α → Bool) (f : α → ℝ) (l : List α) :
    ((sortKernel le l).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [sortKernel,map_sum_insertKernel,ih,List.map_cons,List.sum_cons]

#print axioms map_sum_insertKernel
#print axioms map_sum_sortKernel

def siteNF (ts : List (List ℚ × ℚ)) : List (List ℚ × ℚ) :=
  sortKernel (fun a b => decide (a.2 ≤ b.2)) (siteClean (mergeSites ts))

theorem siteNF_sound (ts : List (List ℚ × ℚ)) (x : ℝ) :
    ((siteNF ts).map (fun t => polyTow t.1 0 x*Real.log |x-(t.2 : ℝ)|)).sum =
      (ts.map (fun t => polyTow t.1 0 x*Real.log |x-(t.2 : ℝ)|)).sum := by
  unfold siteNF
  rw [map_sum_sortKernel, siteClean_sound, mergeSites_eq]

def ratPairLE (a b : ℚ × ℚ) : Bool := decide (a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2)

def lFactorLE : Option (ℚ × ℚ) → Option (ℚ × ℚ) → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => ratPairLE a b

def lfClean : List LTerm → List LTerm
  | [] => []
  | t :: ts => if trimPoly t.1 = [] then lfClean ts else (trimPoly t.1,t.2) :: lfClean ts

theorem lfClean_sound (ts : List LTerm) (x : ℝ) :
    lfieldTower (lfClean ts) 0 x = lfieldTower ts 0 x := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rcases t with ⟨P,o⟩
      simp only [lfClean]
      split_ifs with h
      · have hz : polyTow P 0 x⁻¹ = 0 := by rw [← trimPoly_sound P x⁻¹, h]; rfl
        rw [lf_cons, ih, hz]
        ring
      · simp only [lf_cons, trimPoly_sound, ih]

def laurentNF (ts : List LTerm) : List LTerm :=
  sortKernel (fun a b => lFactorLE a.2 b.2) (lfClean (mergeL ts))

theorem laurentNF_sound (ts : List LTerm) (x : ℝ) :
    lfieldTower (laurentNF ts) 0 x = lfieldTower ts 0 x := by
  unfold laurentNF lfieldTower
  rw [map_sum_sortKernel]
  change lfieldTower (lfClean (mergeL ts)) 0 x = lfieldTower ts 0 x
  rw [lfClean_sound, lfieldTower_mergeL]

theorem laurent_eq_of_nf (a b : List LTerm) (h : laurentNF a = laurentNF b) (x : ℝ) :
    lfieldTower a 0 x = lfieldTower b 0 x := by
  rw [← laurentNF_sound a x, h, laurentNF_sound b x]

/-! ## Checked order-one regular bounds for existing end windows -/

structure EndLipData where
  nLc : ℕ
  Pc : ℕ
  nLp : ℕ
  nAp : ℕ
  Pp : ℕ
  nLL : ℕ
  AQ : ℚ
  BQ : ℚ
  BL : ℚ
  G0 : ℚ
  Gamma : ℚ
  CbP : List ℚ
  pb : List PlogBlk
  ks : List ℕ
  mx : ℚ
  bs : List LBlk
  lks : List ℕ
  Lv : List (ℚ × ℚ)

def endLipCheck (fq : FieldQ) (ts : List LTerm) (e lo hi TR : ℚ) (d : EndLipData) : Bool :=
  decide (lo ≤ e ∧ e ≤ hi ∧ 0 ≤ d.BQ ∧ 0 ≤ d.BL ∧ 0 ≤ d.Gamma ∧
    (ts = [] ∨ e ≠ 0) ∧
    d.AQ+lCoef ts d.Lv e 0+lErr ts d.Lv e 0 ≤ d.G0 ∧
    d.BQ+d.BL ≤ d.Gamma ∧ d.G0+d.Gamma*max (e-lo) (hi-e) ≤ TR) &&
  decide (anchorUB2 d.nLc d.Pc d.nLp d.nAp d.Pp fq e = some d.AQ) &&
  blockOK3 fq ((lo+hi)/2) lo hi 1 d.CbP d.pb d.ks d.BQ &&
  llogsCheck d.nLL e ts d.Lv &&
  if ts = [] then decide (d.BL = 0) else lBlockOK ts lo hi d.mx 1 d.bs d.lks d.BL

theorem endLipCheck_sound (fq : FieldQ) (ts : List LTerm) (e lo hi TR : ℚ) (d : EndLipData)
    (hchk : endLipCheck fq ts e lo hi TR d = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (TR : ℝ) := by
  simp only [endLipCheck, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨hmain,ha⟩,hb⟩,hlogs⟩,hLaur⟩ := hchk
  obtain ⟨heLo,heHi,hBQ,hBL,hGamma,he0,hG0,hB,hT⟩ := hmain
  have he : (e : ℝ) ∈ Icc (lo : ℝ) (hi : ℝ) :=
    ⟨(Rat.cast_le (K := ℝ)).mpr heLo,(Rat.cast_le (K := ℝ)).mpr heHi⟩
  have hlow : (((lo+hi)/2 : ℚ) : ℝ)-(((hi-lo)/2 : ℚ) : ℝ) = (lo : ℝ) := by push_cast; ring
  have hhigh : (((lo+hi)/2 : ℚ) : ℝ)+(((hi-lo)/2 : ℚ) : ℝ) = (hi : ℝ) := by push_cast; ring
  have hbf := blockFacts_of_ok3 fq ((lo+hi)/2) lo hi 1 d.CbP d.pb d.ks d.BQ hb
  have hTq := isTower_fieldTower fq (poleF fq.poles)
    (((lo+hi)/2 : ℚ) : ℝ) (((hi-lo)/2 : ℚ) : ℝ) 1
    (fun t ht x hx => hbf.plog t ht x (by simpa only [hlow,hhigh] using hx))
    (fun x hx q hq => hbf.pole q hq x (by simpa only [hlow,hhigh] using hx))
    (fun x hx => hbf.deriv x (by simpa only [hlow,hhigh] using hx))
  have hLT : IsTower (lfieldTower ts) (((lo+hi)/2 : ℚ) : ℝ) (((hi-lo)/2 : ℚ) : ℝ) 1 ∧
      (∀ x ∈ Icc (lo : ℝ) (hi : ℝ), |lfieldTower ts 1 x| ≤ (d.BL : ℝ)) ∧
      (lfieldTower ts 0 (e : ℝ) ≤ ((lCoef ts d.Lv e 0+lErr ts d.Lv e 0 : ℚ) : ℝ)) := by
    by_cases hn : ts = []
    · have hz : lfieldTower ts = fun (_ : ℕ) (_ : ℝ) => 0 := by
        subst ts
        funext j x
        simp [lfieldTower]
      rw [hz]
      refine ⟨⟨fun _ _ => continuousOn_const,fun _ _ x _ => hasDerivAt_const x 0⟩,?_,?_⟩
      · intro x hx
        simpa using (Rat.cast_le (K := ℝ)).mpr hBL
      · subst ts
        simp [lCoef,lErr]
    · have hLb : lBlockOK ts lo hi d.mx 1 d.bs d.lks d.BL = true := by
        simpa only [if_neg hn] using hLaur
      have hlf := lBlockFacts_of_ok ts lo hi d.mx 1 d.bs d.lks d.BL hLb
      have hTL := isTower_lfieldTower ts (((lo+hi)/2 : ℚ) : ℝ) (((hi-lo)/2 : ℚ) : ℝ) 1
        (fun x hx => hlf.avoid0 x (by simpa only [hlow,hhigh] using hx))
        (fun t ht ab hab x hx => hlf.avoidL t ht ab hab x (by simpa only [hlow,hhigh] using hx))
      have hne : ∀ t ∈ ts, ∀ ab, t.2 = some ab → ab.1*e-ab.2 ≠ 0 := by
        intro t ht ab hab
        have h := hlf.avoidL t ht ab hab (e : ℝ) he
        exact_mod_cast h
      have hc : e ≠ 0 := he0.resolve_left hn
      have hp := lfield_approx e hc ts d.Lv (llogsCheck_spec d.nLL e ts d.Lv hlogs) hne 0
      simp only [Nat.factorial_zero,Nat.cast_one,div_one] at hp
      have hupper : lfieldTower ts 0 (e : ℝ) ≤ ((lCoef ts d.Lv e 0+lErr ts d.Lv e 0 : ℚ) : ℝ) := by
        rw [Rat.cast_add]
        linarith [(abs_le.mp hp).2]
      refine ⟨hTL,?_,hupper⟩
      intro x hx
      simpa using hlf.tail x hx
  have hAQ := anchorUB2_spec d.nLc d.Pc d.nLp d.nAp d.Pp fq e d.AQ ha
  have hpoint : fieldTower fq (poleF fq.poles) 0 (e : ℝ)+lfieldTower ts 0 (e : ℝ) ≤ (d.G0 : ℝ) := by
    have hG := (Rat.cast_le (K := ℝ)).mpr hG0
    push_cast at hG
    have hp := hLT.2.2
    rw [Rat.cast_add] at hp
    linarith
  apply endLip lo hi e d.G0 d.Gamma TR
    (fun x => fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x)
    (fun x => fieldTower fq (poleF fq.poles) 1 x+lfieldTower ts 1 x) he
  · have hq := hTq.cont 0 (by decide)
    have hl := hLT.1.cont 0 (by decide)
    have hsum := hq.add hl
    rw [hlow,hhigh] at hsum
    convert hsum using 1 <;> (funext x; simp only [Pi.add_apply])
  · intro x hx
    have hx' : x ∈ Ioo
        ((((lo+hi)/2 : ℚ) : ℝ)-(((hi-lo)/2 : ℚ) : ℝ))
        ((((lo+hi)/2 : ℚ) : ℝ)+(((hi-lo)/2 : ℚ) : ℝ)) := by
      simpa only [hlow,hhigh] using hx
    exact (hTq.der 0 (by decide) x hx').add (hLT.1.der 0 (by decide) x hx')
  · intro x hx
    have hq : |fieldTower fq (poleF fq.poles) 1 x| ≤ (d.BQ : ℝ) := by simpa using hbf.tail x hx
    have hl := hLT.2.1 x hx
    have hsum := (abs_add_le _ _).trans (add_le_add hq hl)
    have hB' := (Rat.cast_le (K := ℝ)).mpr hB
    rw [Rat.cast_add] at hB'
    exact hsum.trans hB'
  · exact hpoint
  · exact hGamma
  · exact hT

theorem endULipChecked_sound (fq : FieldQ) (ts : List LTerm) (e lo hi : ℚ)
    (k kR : ℕ) (U TR T : ℚ) (d : EndLipData)
    (he : endUOK fq ts e lo hi k kR U TR T = true)
    (hr : endLipCheck (regQ fq e) (regL ts e) e lo hi TR d = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ≠ (e : ℝ) →
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (T : ℝ) :=
  endUOK_sound fq ts e lo hi k kR U TR T he
    (endLipCheck_sound (regQ fq e) (regL ts e) e lo hi TR d hr)

theorem endL0LipChecked_sound (fq : FieldQ) (ts : List LTerm) (hi : ℚ) (k n : ℕ) (U TR : ℚ)
    (d : EndLipData) (he : endL0OK fq ts hi k n U = true)
    (hr : endLipCheck (regQ fq 0) [] 0 0 hi TR d = true) :
    ∀ x ∈ Ioc (0 : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤
      (TR : ℝ)+(U : ℝ)+(l0Const ts hi n : ℝ)+
        ((endC fq [] 0+l0C ts : ℚ) : ℝ)*Real.log |x| := by
  apply endL0_sound fq ts hi k n U TR he
  have h := endLipCheck_sound (regQ fq 0) [] 0 0 hi TR d hr
  simpa only [lfieldTower_nil_zero,add_zero] using h



/-! Pole normalization: equal positions add residues without changing a log branch. -/

def poleJoin (s q : PoleR) : PoleR := ⟨s.rr+q.rr,s.ri+q.ri,s.pr,s.pi⟩

theorem poleJoin_term (s q : PoleR) (hpr : s.pr = q.pr) (hpi : s.pi = q.pi) (x : ℝ) :
    ((poleJoin s q).rho*Complex.log ((x : ℂ)-(poleJoin s q).pc)).re =
      (s.rho*Complex.log ((x : ℂ)-s.pc)).re + (q.rho*Complex.log ((x : ℂ)-q.pc)).re := by
  have hp : q.pc = s.pc := by apply Complex.ext <;> simp [PoleR.pc, hpr, hpi]
  have hr : (poleJoin s q).rho = s.rho+q.rho := by
    apply Complex.ext <;> simp [poleJoin, PoleR.rho]
  have hs : (poleJoin s q).pc = s.pc := rfl
  rw [hs, hr, hp, add_mul, Complex.add_re]

def poleInsert (q : PoleR) : List PoleR → List PoleR
  | [] => [q]
  | s :: ss => if s.pr = q.pr ∧ s.pi = q.pi then poleJoin s q :: ss else s :: poleInsert q ss

theorem poleF_cons (q : PoleR) (qs : List PoleR) (x : ℝ) :
    poleF (q :: qs) x = (q.rho*Complex.log ((x : ℂ)-q.pc)).re+poleF qs x := by simp [poleF]

theorem poleInsert_sound (q : PoleR) (x : ℝ) : ∀ qs : List PoleR,
    poleF (poleInsert q qs) x = poleF qs x+(q.rho*Complex.log ((x : ℂ)-q.pc)).re := by
  intro qs
  induction qs with
  | nil => simp [poleInsert, poleF]
  | cons s ss ih =>
      simp only [poleInsert]
      split_ifs with h
      · rw [poleF_cons, poleF_cons, poleJoin_term s q h.1 h.2 x]
        ring
      · rw [poleF_cons, poleF_cons, ih]
        ring

def mergePoles (qs : List PoleR) : List PoleR := qs.foldl (fun acc q => poleInsert q acc) []

theorem mergePoles_fold (x : ℝ) : ∀ (qs acc : List PoleR),
    poleF (qs.foldl (fun a q => poleInsert q a) acc) x = poleF qs x+poleF acc x := by
  intro qs
  induction qs with
  | nil => intro acc; simp [poleF]
  | cons q qs ih =>
      intro acc
      rw [List.foldl_cons, ih, poleInsert_sound, poleF_cons]
      ring

theorem mergePoles_sound (qs : List PoleR) (x : ℝ) : poleF (mergePoles qs) x = poleF qs x := by
  unfold mergePoles
  rw [mergePoles_fold]
  simp [poleF]

def poleClean : List PoleR → List PoleR
  | [] => []
  | q :: qs => if q.rr = 0 ∧ q.ri = 0 then poleClean qs else q :: poleClean qs

theorem poleClean_sound (qs : List PoleR) (x : ℝ) : poleF (poleClean qs) x = poleF qs x := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      simp only [poleClean]
      split_ifs with h
      · have hz : q.rho = 0 := by apply Complex.ext <;> simp [PoleR.rho, h.1, h.2]
        rw [ih, poleF_cons, hz, zero_mul, Complex.zero_re, zero_add]
      · simp only [poleF_cons, ih]

def poleNF (qs : List PoleR) : List PoleR :=
  sortKernel (fun a b => ratPairLE (a.pr,a.pi) (b.pr,b.pi)) (poleClean (mergePoles qs))

theorem poleNF_sound (qs : List PoleR) (x : ℝ) : poleF (poleNF qs) x = poleF qs x := by
  unfold poleNF poleF
  rw [map_sum_sortKernel]
  change poleF (poleClean (mergePoles qs)) x = poleF qs x
  rw [poleClean_sound, mergePoles_sound]

def fieldNF (fq : FieldQ) : FieldQ := ⟨trimPoly fq.poly,siteNF fq.plogs,poleNF fq.poles⟩

theorem fieldNF_sound (fq : FieldQ) (x : ℝ) :
    fieldTower (fieldNF fq) (poleF (fieldNF fq).poles) 0 x = fieldTower fq (poleF fq.poles) 0 x := by
  simp only [fieldNF, fieldTower_zero, poleF]
  rw [trimPoly_sound, siteNF_sound]
  have hp := poleNF_sound fq.poles x
  simp only [poleF] at hp
  rw [hp]

theorem field_eq_of_nf (a b : FieldQ) (h : fieldNF a = fieldNF b) (x : ℝ) :
    fieldTower a (poleF a.poles) 0 x = fieldTower b (poleF b.poles) 0 x := by
  rw [← fieldNF_sound a x, h, fieldNF_sound b x]

/-- A rational code avoids importing trial-specific DecidableEq instances. -/
def poleCode (q : PoleR) : ℚ × ℚ × ℚ × ℚ := (q.rr,q.ri,q.pr,q.pi)

theorem poleCode_inj {a b : PoleR} (h : poleCode a = poleCode b) : a = b := by
  cases a
  cases b
  simp only [poleCode, Prod.mk.injEq] at h
  obtain ⟨h1,h2,h3,h4⟩ := h
  subst_vars
  rfl

theorem poleListCode_inj : ∀ (a b : List PoleR), a.map poleCode = b.map poleCode → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b <;> simp_all
  | cons q qs ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons r rs =>
          simp only [List.map_cons, List.cons.injEq] at h
          rw [poleCode_inj h.1, ih rs h.2]

def fieldNFCode (fq : FieldQ) : List ℚ × List (List ℚ × ℚ) × List (ℚ × ℚ × ℚ × ℚ) :=
  ((fieldNF fq).poly,(fieldNF fq).plogs,(fieldNF fq).poles.map poleCode)

def fieldNFCheck (a b : FieldQ) : Bool := decide (fieldNFCode a = fieldNFCode b)

theorem fieldQ_eq_of_parts (a b : FieldQ) (hp : a.poly = b.poly) (hl : a.plogs = b.plogs)
    (hq : a.poles = b.poles) : a = b := by
  cases a
  cases b
  cases hp
  cases hl
  cases hq
  rfl

theorem fieldNFCheck_eq {a b : FieldQ} (h : fieldNFCheck a b = true) : fieldNF a = fieldNF b := by
  simp only [fieldNFCheck, decide_eq_true_eq, fieldNFCode, Prod.mk.injEq] at h
  exact fieldQ_eq_of_parts _ _ h.1 h.2.1 (poleListCode_inj _ _ h.2.2)

theorem fieldNFCheck_sound {a b : FieldQ} (h : fieldNFCheck a b = true) (x : ℝ) :
    fieldTower a (poleF a.poles) 0 x = fieldTower b (poleF b.poles) 0 x :=
  field_eq_of_nf a b (fieldNFCheck_eq h) x














/-- Assemble closed-interval bounds from the checked adjacent partition.
Nonemptiness discharges the final right endpoint as well as the interiors. -/
theorem pieceCover_bound (hi : ℚ) (f : ℝ → ℝ) (T : ℝ) :
    ∀ (lo : ℚ) (ps : List (ℚ × ℚ)), ps ≠ [] → pieceCover hi lo ps = true →
      (∀ p ∈ ps, ∀ x ∈ Icc (p.1 : ℝ) (p.2 : ℝ), f x ≤ T) →
        ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), f x ≤ T := by
  intro lo ps
  induction ps generalizing lo with
  | nil => intro hn; exact (hn rfl).elim
  | cons p ps ih =>
      intro hn hc hp x hx
      rcases p with ⟨a,b⟩
      simp only [pieceCover, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨rfl,hab⟩,hr⟩ := hc
      by_cases hxb : x ≤ (b : ℝ)
      · exact hp (a,b) (by simp) x ⟨hx.1,hxb⟩
      · by_cases hps : ps = []
        · rw [hps] at hr
          simp only [pieceCover, decide_eq_true_eq] at hr
          have he : (b : ℝ) = (hi : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) hr
          exact (hxb (by rw [he]; exact hx.2)).elim
        · exact ih b hps hr (fun p hm => hp p (List.mem_cons_of_mem _ hm))
            x ⟨(lt_of_not_ge hxb).le,hx.2⟩

#print axioms pieceCover_bound

/-! Exhaustive axiom audit of this module's exported theorems. -/
/-! ## C3 normalized dyadic approximation boundaries -/

def ceilGrid (P : ℕ) (q : ℚ) : ℚ := -dyRound P (-q)

theorem le_ceilGrid (P : ℕ) (q : ℚ) : q ≤ ceilGrid P q := by
  have h := (dyRound_spec P (-q)).1
  unfold ceilGrid
  linarith

def unitRound (P : ℕ) (A : List ℚ) : List ℚ := A.map (dyRound P)

theorem unitRound_zero (P : ℕ) : dyRound P 0 = 0 := by
  simp [dyRound]

theorem unitRound_length (P : ℕ) (A : List ℚ) : (unitRound P A).length = A.length := by
  simp [unitRound]

theorem unitRound_getD (P : ℕ) (A : List ℚ) (k : ℕ) :
    (unitRound P A).getD k 0 = dyRound P (A.getD k 0) := by
  simpa only [unitRound, unitRound_zero] using (List.getD_map A 0 (dyRound P) (n := k))

/-- Existing finite coefficient-error theorem, specialized to the unit interval. -/
theorem unitRound_error (P : ℕ) (A : List ℚ) (u : ℝ) (hu : |u| ≤ 1) :
    |polyTow A 0 u-polyTow (unitRound P A) 0 u| ≤ (A.length : ℝ)/2^P := by
  have hc : ∀ k < A.length,
      |((A.getD k 0 : ℚ) : ℝ)-(((unitRound P A).getD k 0 : ℚ) : ℝ)| ≤ (1 : ℝ)/2^P := by
    intro k _
    rw [unitRound_getD]
    obtain ⟨h0,h1⟩ := dyRound_spec P (A.getD k 0)
    have h0r := (Rat.cast_le (K := ℝ)).mpr h0
    have h1r := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at h0r h1r
    rw [abs_of_nonneg h0r]
    exact h1r
  have h := round_poly_err (fun k => ((A.getD k 0 : ℚ) : ℝ))
    (fun k => (((unitRound P A).getD k 0 : ℚ) : ℝ)) (fun _ => (1 : ℝ)/2^P)
    A.length u 1 hu hc
  have hp : (∑ k ∈ Finset.range A.length, (((unitRound P A).getD k 0 : ℚ) : ℝ)*u^k) =
      polyTow (unitRound P A) 0 u := by
    rw [polyTow_sum,unitRound_length]
  rw [← polyTow_sum A u,hp] at h
  simpa only [one_pow,mul_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one_div] using h

theorem cellRound_sclPow_length (r : ℚ) : ∀ (A : List ℚ) (k : ℕ),
    (sclPow r k A).length = A.length := by
  intro A
  induction A with
  | nil => intro k; rfl
  | cons a as ih => intro k; simp only [sclPow,List.length_cons,ih]

/-- Upper bound in the common coordinate u=(x-c)/r. -/
def BndU (lo hi : ℚ) (g : ℝ → ℝ) (A : List ℚ) (E : ℚ) : Prop :=
  ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
    g x ≤ polyTow A 0 ((x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ))+(E : ℝ)

theorem cellRadius_pos {lo hi : ℚ} (hlo : lo < hi) : (0 : ℝ) < (((hi-lo)/2 : ℚ) : ℝ) := by
  have h := (Rat.cast_lt (K := ℝ)).mpr hlo
  push_cast
  linarith

theorem hx_unit {lo hi : ℚ} (hlo : lo < hi) (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    |(x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)| ≤ 1 := by
  have hr := cellRadius_pos hlo
  rw [abs_div,abs_of_pos hr,div_le_one hr]
  exact hx_abs lo hi x hx

def cellRound (P : ℕ) (lo hi : ℚ) (v : List ℚ × ℚ) : List ℚ × ℚ :=
  (unitRound P (sclPow ((hi-lo)/2) 0 v.1),ceilGrid P (v.2+(v.1.length : ℚ)/2^P))

theorem BndU.round {lo hi : ℚ} {g : ℝ → ℝ} {A : List ℚ} {E : ℚ}
    (hlo : lo < hi) (P : ℕ) (h : Bnd lo hi g A E) :
    BndU lo hi g (cellRound P lo hi (A,E)).1 (cellRound P lo hi (A,E)).2 := by
  intro x hx
  have hr := cellRadius_pos hlo
  let u : ℝ := (x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)
  have hu : |u| ≤ 1 := hx_unit hlo x hx
  have hp := unitRound_error P (sclPow ((hi-lo)/2) 0 A) u hu
  rw [cellRound_sclPow_length] at hp
  have he : ((((hi-lo)/2 : ℚ) : ℝ))*u = x-(((lo+hi)/2 : ℚ) : ℝ) := by
    dsimp only [u]
    field_simp [ne_of_gt hr]
  rw [polyTow_sclPow,pow_zero,one_mul,he] at hp
  have hc := (Rat.cast_le (K := ℝ)).mpr (le_ceilGrid P (E+(A.length : ℚ)/2^P))
  push_cast at hc
  have hv := h x hx
  have hb := (abs_le.mp hp).2
  change g x ≤ polyTow (unitRound P (sclPow ((hi-lo)/2) 0 A)) 0 u+
    ((ceilGrid P (E+(A.length : ℚ)/2^P) : ℚ) : ℝ)
  linarith

theorem BndU.zero (lo hi : ℚ) : BndU lo hi (fun _ => 0) [] 0 := by
  intro x _
  simp [polyTow]

theorem BndU.add {lo hi : ℚ} {f g : ℝ → ℝ} {A B : List ℚ} {E F : ℚ}
    (hf : BndU lo hi f A E) (hg : BndU lo hi g B F) :
    BndU lo hi (fun x => f x+g x) (vecAdd A B) (E+F) := by
  intro x hx
  have h1 := hf x hx
  have h2 := hg x hx
  rw [polyTow_vecAdd,Rat.cast_add]
  linarith

def cellRoundApx (P : ℕ) (lo hi : ℚ) (v : Option (List ℚ × ℚ)) : Option (List ℚ × ℚ) :=
  v.map (cellRound P lo hi)

theorem cellRoundApx_bnd {lo hi : ℚ} {P : ℕ} {v : Option (List ℚ × ℚ)}
    {g : ℝ → ℝ} {A : List ℚ} {E : ℚ} (hlo : lo < hi)
    (hs : ∀ B F, v = some (B,F) → Bnd lo hi g B F)
    (h : cellRoundApx P lo hi v = some (A,E)) : BndU lo hi g A E := by
  cases hv : v with
  | none => simp [cellRoundApx,hv] at h
  | some b =>
      rcases b with ⟨B,F⟩
      simp only [cellRoundApx,hv,Option.map_some,Option.some.injEq] at h
      have hb := BndU.round hlo P (hs B F hv)
      rw [h] at hb
      exact hb

def polyRoundApx (P : ℕ) (lo hi : ℚ) (p : List ℚ) : List ℚ × ℚ :=
  cellRound P lo hi (shiftLK ((lo+hi)/2) p.length p,0)

theorem polyRoundApx_bnd {lo hi : ℚ} (hlo : lo < hi) (P : ℕ) (p : List ℚ) :
    BndU lo hi (fun x => polyTow p 0 x) (polyRoundApx P lo hi p).1 (polyRoundApx P lo hi p).2 := by
  apply BndU.round (A := shiftLK ((lo+hi)/2) p.length p) (E := 0) hlo P
  intro x _
  simpa only [shiftLK_eq',polyTow_shiftL,sub_add_cancel,Rat.cast_zero,add_zero] using
    (le_rfl : polyTow p 0 x ≤ polyTow p 0 x)


/-! ## Per-term rounded folds: all additions occur on dyadic boundaries. -/

def plogRoundTerm (nL nA M P : ℕ) (lo hi : ℚ) (t : List ℚ × ℚ)
    (d : ℚ × (List ℚ × List ℚ)) : Option (List ℚ × ℚ) :=
  cellRoundApx P lo hi (plogTerm nL nA M P lo hi t d)

theorem plogRoundTerm_bnd {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi)
    {t : List ℚ × ℚ} {d : ℚ × (List ℚ × List ℚ)} {A : List ℚ} {E : ℚ}
    (h : plogRoundTerm nL nA M P lo hi t d = some (A,E)) :
    BndU lo hi (fun x => polyTow t.1 0 x * Real.log |x-(t.2 : ℝ)|) A E := by
  exact cellRoundApx_bnd hlo (fun _ _ ht => plogTerm_bnd hlo ht) h

def poleRoundTerm (nL nA M P : ℕ) (lo hi : ℚ) (q : PoleR) (d : ℚ × ℚ) :
    Option (List ℚ × ℚ) := cellRoundApx P lo hi (poleTerm nL nA M P lo hi q d)

theorem poleRoundTerm_bnd {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi)
    {q : PoleR} {d : ℚ × ℚ} {A : List ℚ} {E : ℚ}
    (h : poleRoundTerm nL nA M P lo hi q d = some (A,E)) :
    BndU lo hi (fun x => (q.rho * Complex.log ((x : ℂ)-q.pc)).re) A E := by
  exact cellRoundApx_bnd hlo (fun _ _ ht => poleTerm_bnd hlo ht) h

def laurentRoundTerm (nL M P : ℕ) (lo hi : ℚ) (t : LTerm) (d : LaurentPieceData) :
    Option (List ℚ × ℚ) :=
  cellRoundApx P lo hi (laurentApx nL M P ((lo+hi)/2) ((hi-lo)/2) t d)

theorem laurentRoundTerm_bnd {nL M P : ℕ} {lo hi : ℚ} (hlo : lo < hi)
    {t : LTerm} {d : LaurentPieceData} {A : List ℚ} {E : ℚ}
    (h : laurentRoundTerm nL M P lo hi t d = some (A,E)) :
    BndU lo hi (fun x => mulTower (zTow t.1) (lfTower t.2) 0 x) A E := by
  apply cellRoundApx_bnd hlo ?_ h
  intro B F hb x hx
  have hA := laurentApx_spec hb (x-(((lo+hi)/2 : ℚ) : ℝ)) (hx_abs lo hi x hx)
  have he : (((lo+hi)/2 : ℚ) : ℝ)+(x-(((lo+hi)/2 : ℚ) : ℝ)) = x := by ring
  rw [he] at hA
  have hu := (abs_le.mp hA).2
  linarith
def plogsRoundM (nL nA Ml P : ℕ) (lo hi : ℚ) :
    List (List ℚ × ℚ) → List (ℚ × (List ℚ × List ℚ)) → Option (List ℚ × ℚ)
  | [], [] => some ([], 0)
  | t :: ts, d :: ds =>
    match plogRoundTerm nL nA Ml P lo hi t d, plogsRoundM nL nA Ml P lo hi ts ds with
    | some a, some b => some (vecAdd a.1 b.1, a.2 + b.2)
    | _, _ => none
  | _, _ => none

theorem plogsRoundM_bnd {nL nA Ml P : ℕ} {lo hi : ℚ} (hlo : lo < hi) :
    ∀ (ts : List (List ℚ × ℚ)) (ds : List (ℚ × (List ℚ × List ℚ))) (A : List ℚ) (B : ℚ),
      plogsRoundM nL nA Ml P lo hi ts ds = some (A, B) →
      BndU lo hi (fun x => (ts.map (fun t => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|)).sum) A B := by
  intro ts
  induction ts with
  | nil =>
    intro ds A B h
    cases ds with
    | nil =>
      simp only [plogsRoundM, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using BndU.zero lo hi
    | cons d ds => simp [plogsRoundM] at h
  | cons t ts ih =>
    intro ds A B h
    cases ds with
    | nil => simp [plogsRoundM] at h
    | cons d ds =>
      unfold plogsRoundM at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := (plogRoundTerm_bnd hlo ha).add (ih ds b.1 b.2 hb)
        simpa using this
      · simp at h

def polesRoundM (nL nA M P : ℕ) (lo hi : ℚ) : List PoleR → List (ℚ × ℚ) → Option (List ℚ × ℚ)
  | [], [] => some ([], 0)
  | q :: qs, d :: ds =>
    match poleRoundTerm nL nA M P lo hi q d, polesRoundM nL nA M P lo hi qs ds with
    | some a, some b => some (vecAdd a.1 b.1, a.2 + b.2)
    | _, _ => none
  | _, _ => none

theorem polesRoundM_bnd {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi) :
    ∀ (qs : List PoleR) (ds : List (ℚ × ℚ)) (A : List ℚ) (B : ℚ),
      polesRoundM nL nA M P lo hi qs ds = some (A, B) → BndU lo hi (fun x => poleF qs x) A B := by
  intro qs
  induction qs with
  | nil =>
    intro ds A B h
    cases ds with
    | nil =>
      simp only [polesRoundM, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := BndU.zero lo hi
      simpa [poleF] using this
    | cons d ds => simp [polesRoundM] at h
  | cons q qs ih =>
    intro ds A B h
    cases ds with
    | nil => simp [polesRoundM] at h
    | cons d ds =>
      unfold polesRoundM at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := (poleRoundTerm_bnd hlo ha).add (ih ds b.1 b.2 hb)
        intro x hx
        show poleF (q :: qs) x ≤ _
        have h2 := this x hx
        have e : poleF (q :: qs) x = (q.rho * Complex.log ((x : ℂ) - q.pc)).re + poleF qs x := by
          simp [poleF]
        rw [e]
        exact h2
      · simp at h

def laurentRoundM (nL M P : ℕ) (lo hi : ℚ) :
    List LTerm → List LaurentPieceData → Option (List ℚ × ℚ)
  | [], [] => some ([],0)
  | t :: ts, d :: ds =>
      match laurentRoundTerm nL M P lo hi t d, laurentRoundM nL M P lo hi ts ds with
      | some a, some b => some (vecAdd a.1 b.1, a.2+b.2)
      | _, _ => none
  | _, _ => none

theorem laurentRoundM_bnd {nL M P : ℕ} {lo hi : ℚ} (hlo : lo < hi) :
    ∀ (ts : List LTerm) (ds : List LaurentPieceData) (A : List ℚ) (B : ℚ),
      laurentRoundM nL M P lo hi ts ds = some (A,B) →
        BndU lo hi (fun x => lfieldTower ts 0 x) A B := by
  intro ts
  induction ts with
  | nil =>
      intro ds A B h
      cases ds with
      | nil =>
          simp only [laurentRoundM, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl,rfl⟩ := h
          simpa only [lfieldTower_nil_zero] using BndU.zero lo hi
      | cons d ds => simp [laurentRoundM] at h
  | cons t ts ih =>
      intro ds A B h
      cases ds with
      | nil => simp [laurentRoundM] at h
      | cons d ds =>
          unfold laurentRoundM at h
          split at h
          · rename_i a b ha hb
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl,rfl⟩ := h
            have ht := laurentRoundTerm_bnd hlo ha
            have hs := ht.add (ih ds b.1 b.2 hb)
            intro x hx
            simpa only [lfieldTower, List.map_cons, List.sum_cons] using hs x hx
          · simp at h


/-! ## Rounded merged checker (the input may be put in exact normal form beforehand). -/

def roundMergeUBL (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) : Option ℚ :=
  if lo < hi then
    match plogsRoundM nL nA Ml P lo hi (mergeSites fq.plogs) pd,
      polesRoundM nL nA Mp P lo hi fq.poles qd, laurentRoundM nL ML P lo hi ts ld with
    | some a, some b, some l =>
        let s := polyRoundApx P lo hi fq.poly
        some (chebPolyUB (vecAdd s.1 (vecAdd a.1 (vecAdd b.1 l.1))) γ+s.2+a.2+b.2+l.2)
    | _, _, _ => none
  else none

def chebRoundPieceL (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (T : ℚ) : Bool :=
  match roundMergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ with
  | some v => decide (v ≤ T)
  | none => false

theorem roundMergeUBL_spec (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (v : ℚ) (hv : roundMergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ = some v) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (v : ℝ) := by
  unfold roundMergeUBL at hv
  split_ifs at hv with hlo
  · split at hv
    · rename_i a b l ha hb hl
      simp only [Option.some.injEq] at hv
      subst v
      intro x hx
      have hp := plogsRoundM_bnd hlo (mergeSites fq.plogs) pd a.1 a.2 ha x hx
      beta_reduce at hp
      rw [mergeSites_eq] at hp
      have hq := polesRoundM_bnd hlo fq.poles qd b.1 b.2 hb x hx
      have hL := laurentRoundM_bnd hlo ts ld l.1 l.2 hl x hx
      have hs := polyRoundApx_bnd hlo P fq.poly x hx
      have hc := chebPoly_le
        (vecAdd (polyRoundApx P lo hi fq.poly).1 (vecAdd a.1 (vecAdd b.1 l.1))) γ
        ((x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)) (hx_unit hlo x hx)
      rw [polyTow_vecAdd,polyTow_vecAdd,polyTow_vecAdd] at hc
      rw [fieldTower_zero]
      simp only [Rat.cast_add]
      beta_reduce at hs hq hL
      linarith
    · simp at hv

theorem chebRoundPieceL_sound (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ : List ℚ) (T : ℚ)
    (hchk : chebRoundPieceL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ T = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (T : ℝ) := by
  unfold chebRoundPieceL at hchk
  split at hchk
  · rename_i v hv
    simp only [decide_eq_true_eq] at hchk
    intro x hx
    exact (roundMergeUBL_spec fq ts nL nA Mp Ml ML P lo hi pd qd ld γ v hv x hx).trans
      ((Rat.cast_le (K := ℝ)).mpr hchk)
  · simp at hchk

theorem roundMergeUBL_of_parts (fq : FieldQ) (ts : List LTerm) (nL nA Mp Ml ML P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (ld : List LaurentPieceData)
    (γ S Ap Aq Al : List ℚ) (Es Ep Eq El : ℚ) (hlo : lo < hi)
    (hs : polyRoundApx P lo hi fq.poly = (S,Es))
    (hp : plogsRoundM nL nA Ml P lo hi (mergeSites fq.plogs) pd = some (Ap,Ep))
    (hq : polesRoundM nL nA Mp P lo hi fq.poles qd = some (Aq,Eq))
    (hl : laurentRoundM nL ML P lo hi ts ld = some (Al,El)) :
    roundMergeUBL fq ts nL nA Mp Ml ML P lo hi pd qd ld γ =
      some (chebPolyUB (vecAdd S (vecAdd Ap (vecAdd Aq Al))) γ+Es+Ep+Eq+El) := by
  simp only [roundMergeUBL, if_pos hlo, hp, hq, hl, hs]

#print axioms roundMergeUBL_spec
#print axioms chebRoundPieceL_sound
#print axioms roundMergeUBL_of_parts


/-! Structural cleaning for kernel computation: sorting is unnecessary for piece semantics. -/
def fieldClean (fq : FieldQ) : FieldQ :=
  ⟨trimPoly fq.poly,siteClean (mergeSites fq.plogs),poleClean fq.poles⟩

theorem fieldClean_sound (fq : FieldQ) (x : ℝ) :
    fieldTower (fieldClean fq) (poleF (fieldClean fq).poles) 0 x = fieldTower fq (poleF fq.poles) 0 x := by
  simp only [fieldClean,fieldTower_zero]
  rw [trimPoly_sound,siteClean_sound,mergeSites_eq,poleClean_sound]

def laurentClean (ts : List LTerm) : List LTerm := lfClean (mergeL ts)

theorem laurentClean_sound (ts : List LTerm) (x : ℝ) :
    lfieldTower (laurentClean ts) 0 x = lfieldTower ts 0 x := by
  rw [laurentClean,lfClean_sound,lfieldTower_mergeL]

#print axioms fieldClean_sound
#print axioms laurentClean_sound

#print axioms plogRoundTerm_bnd
#print axioms poleRoundTerm_bnd
#print axioms laurentRoundTerm_bnd
#print axioms plogsRoundM_bnd
#print axioms polesRoundM_bnd
#print axioms laurentRoundM_bnd

#print axioms le_ceilGrid
#print axioms unitRound_zero
#print axioms unitRound_length
#print axioms unitRound_getD
#print axioms unitRound_error
#print axioms cellRound_sclPow_length
#print axioms cellRadius_pos
#print axioms hx_unit
#print axioms BndU.round
#print axioms BndU.zero
#print axioms BndU.add
#print axioms cellRoundApx_bnd
#print axioms polyRoundApx_bnd

#print axioms fieldTower_add
#print axioms lfieldTower_add
#print axioms invBinom_nonneg
#print axioms invPowerSeries
#print axioms invTailQ_spec
#print axioms invTailQ_nonneg
#print axioms endLip
#print axioms endULip_sound
#print axioms pieceCover_sound
#print axioms invBinom_at_zero
#print axioms invBinom_step
#print axioms invBinom_asc
#print axioms invPrefix_step
#print axioms invTailQ_step
#print axioms invTailPosQ_eq
#print axioms logInvTailQ_nonneg
#print axioms series_tail_error
#print axioms series_refined_tail_error
#print axioms monoInv_scaled_eq
#print axioms monoInvSeries
#print axioms zTowAuxSeries
#print axioms lfTowerSeries
#print axioms laurentTaylor_ident
#print axioms monoInv_scaled_bound
#print axioms invMajAux_bound
#print axioms invMajAux_nonneg
#print axioms invMajAuxSeries
#print axioms invMajTail_eq
#print axioms lf_scaled_eq
#print axioms lfMaj_nonneg
#print axioms lfMaj_le_coarse
#print axioms lfMaj_bound
#print axioms mulTower_scaled
#print axioms mulTower_scaled_bound
#print axioms invBinom_sum
#print axioms logInvCoefSeries
#print axioms logInvTailQ_eq
#print axioms geoInvCoefSeries
#print axioms geoInvTail_eq
#print axioms convQ_fin
#print axioms invGeo_conv
#print axioms geoMajAuxSeries
#print axioms geoMajTail_eq
#print axioms convQ_add_left
#print axioms convQ_scale_left
#print axioms invMajAux_conv
#print axioms convQ_delta_right
#print axioms laurentCoarseCoefSeries
#print axioms laurentCoarseTail_eq
#print axioms laurentMajorant_tail
#print axioms polyApprox_error
#print axioms laurentCoeffErr_spec
#print axioms laurentApx_spec
#print axioms laurentM_bnd
#print axioms mergeUBL_spec
#print axioms chebMergePieceL_sound
#print axioms mergeUBL_of_parts
#print axioms trimPoly_sound
#print axioms map_sum_mergeSort
#print axioms siteClean_sound
#print axioms siteNF_sound
#print axioms lfClean_sound
#print axioms laurentNF_sound
#print axioms laurent_eq_of_nf
#print axioms endLipCheck_sound
#print axioms endULipChecked_sound
#print axioms endL0LipChecked_sound
#print axioms poleJoin_term
#print axioms poleF_cons
#print axioms poleInsert_sound
#print axioms mergePoles_fold
#print axioms mergePoles_sound
#print axioms poleClean_sound
#print axioms poleNF_sound
#print axioms fieldNF_sound
#print axioms field_eq_of_nf
#print axioms poleCode_inj
#print axioms poleListCode_inj
#print axioms fieldQ_eq_of_parts
#print axioms fieldNFCheck_eq
#print axioms fieldNFCheck_sound


/-! ## C9 certified parent pole polynomials and child transfer. -/

/-- The mask only partitions a list; absent mask entries stay near. -/
def poleCacheSplit : List PoleR → List Bool → List PoleR × List PoleR
  | [], _ => ([],[])
  | qs, [] => (qs,[])
  | q :: qs, b :: bs =>
      let s := poleCacheSplit qs bs
      if b then (s.1,q :: s.2) else (q :: s.1,s.2)

theorem poleCacheSplit_sound (qs : List PoleR) (bs : List Bool) (x : ℝ) :
    poleF qs x = poleF (poleCacheSplit qs bs).1 x+poleF (poleCacheSplit qs bs).2 x := by
  induction qs generalizing bs with
  | nil => simp [poleCacheSplit,poleF]
  | cons q qs ih =>
      cases bs with
      | nil => simp [poleCacheSplit,poleF]
      | cons b bs =>
          cases b <;> simp only [poleCacheSplit,Bool.false_eq_true,ite_false,ite_true]
          · rw [poleF_cons,poleF_cons,ih bs]; ring
          · rw [poleF_cons,poleF_cons,ih bs]; ring

/-- Exact global-x polynomial for a polynomial in a parent unit coordinate. -/
def poleCacheGlobal (lo hi : ℚ) (A : List ℚ) : List ℚ :=
  let B := sclPow (1/((hi-lo)/2)) 0 A
  shiftLK (-((lo+hi)/2)) B.length B

theorem poleCacheGlobal_spec {lo hi : ℚ} (hlo : lo < hi) (A : List ℚ) (x : ℝ) :
    polyTow (poleCacheGlobal lo hi A) 0 x =
      polyTow A 0 ((x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)) := by
  unfold poleCacheGlobal
  rw [shiftLK_eq',polyTow_shiftL,polyTow_sclPow]
  simp only [pow_zero,one_mul,Rat.cast_div,Rat.cast_one,Rat.cast_neg]
  congr 1
  ring

/-- Parent error includes the original log, argument, Taylor and dyadic errors. -/
theorem poleCacheParent_sound {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi)
    (qs : List PoleR) (ds : List (ℚ × ℚ)) (A B : List ℚ) (E : ℚ)
    (h : polesRoundM nL nA M P lo hi qs ds = some (A,E))
    (hB : poleCacheGlobal lo hi A = B) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), poleF qs x ≤ polyTow B 0 x+(E : ℝ) := by
  intro x hx
  have hp := polesRoundM_bnd hlo qs ds A E h x hx
  rw [← poleCacheGlobal_spec hlo A x,hB] at hp
  exact hp

/-- Surrogate field: original plogs, checked cached polynomial and remaining poles. -/
def poleCacheField (fq : FieldQ) (near : List PoleR) (B : List ℚ) : FieldQ :=
  ⟨vecAdd fq.poly B,fq.plogs,near⟩

theorem poleCacheChild_sound (fq : FieldQ) (ts : List LTerm) (mask : List Bool)
    (near far : List PoleR) (B : List ℚ) (E T lo hi parentLo parentHi : ℚ)
    (hn : (poleCacheSplit fq.poles mask).1 = near)
    (hf : (poleCacheSplit fq.poles mask).2 = far)
    (hlo : parentLo ≤ lo) (hhi : hi ≤ parentHi)
    (hp : ∀ x ∈ Icc (parentLo : ℝ) (parentHi : ℝ), poleF far x ≤ polyTow B 0 x+(E : ℝ))
    (hc : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower (poleCacheField fq near B) (poleF near) 0 x+lfieldTower ts 0 x ≤ ((T-E : ℚ) : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x+lfieldTower ts 0 x ≤ (T : ℝ) := by
  intro x hx
  have hL : (parentLo : ℝ) ≤ (lo : ℝ) := Rat.cast_le.mpr hlo
  have hH : (hi : ℝ) ≤ (parentHi : ℝ) := Rat.cast_le.mpr hhi
  have hparent := hp x ⟨hL.trans hx.1,hx.2.trans hH⟩
  have hchild := hc x hx
  have hs := poleCacheSplit_sound fq.poles mask x
  rw [hn,hf] at hs
  simp only [poleCacheField,fieldTower_zero,polyTow_vecAdd,Rat.cast_sub] at hchild ⊢
  rw [hs]
  linarith

#print axioms poleCacheSplit_sound
#print axioms poleCacheGlobal_spec
#print axioms poleCacheParent_sound
#print axioms poleCacheChild_sound

end CatalanMeasure.GenD.Signed.Data.Cells

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

#print axioms geoMajAuxSeries
#print axioms geoMajTail_eq
#print axioms convQ_add_left
#print axioms convQ_scale_left
#print axioms invMajAux_conv
#print axioms convQ_delta_right

#print axioms invBinom_sum
#print axioms logInvCoefSeries
#print axioms logInvTailQ_eq
#print axioms geoInvCoefSeries
#print axioms geoInvTail_eq
#print axioms convQ_fin
#print axioms invGeo_conv

#print axioms lf_scaled_eq
#print axioms lfMaj_nonneg
#print axioms lfMaj_le_coarse
#print axioms lfMaj_bound
#print axioms mulTower_scaled
#print axioms mulTower_scaled_bound

#print axioms monoInv_scaled_eq
#print axioms monoInv_scaled_bound
#print axioms invMajAux_bound
#print axioms invMajAux_nonneg
#print axioms invMajAuxSeries
#print axioms invMajTail_eq

#print axioms monoInvSeries
#print axioms zTowAuxSeries
#print axioms lfTowerSeries
#print axioms laurentTaylor_ident

#print axioms invBinom_step
#print axioms invBinom_asc
#print axioms invPrefix_step
#print axioms invTailQ_step
#print axioms invTailPosQ_eq
#print axioms logInvTailQ_nonneg
#print axioms series_tail_error
#print axioms series_refined_tail_error

#print axioms fieldTower_add
#print axioms lfieldTower_add
#print axioms invPowerSeries
#print axioms invTailQ_spec
#print axioms invTailQ_nonneg
#print axioms endLip
#print axioms endULip_sound
#print axioms pieceCover_sound

end CatalanMeasure.GenD.Signed.Data.Cells

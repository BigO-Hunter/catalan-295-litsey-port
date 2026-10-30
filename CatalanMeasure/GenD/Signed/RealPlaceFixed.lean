module

public import CatalanMeasure.GenD.Signed.RealPlace
public import CatalanMeasure.GenD.Signed.EnergyFixed
public import CatalanMeasure.GenD.Signed.SignedDischarge

/-!
# The real-place determinant with marked rows, and the signed second sheet for fixed rows
(lane RP2, items 2 and 3)

* `norm_det_gram_le_gen`, `norm_det_gram_le_gen_full`: `norm_det_gram_le` with the removed
  diagonal `Dg` independent of the diagonal `Dp` of `F(1)`; this is the weight structure of the
  marked determinant (free positives carry the weight `-5`, marked rows the weight `1`).
* `abs_det_laurent_le_marked`: `|det markedLaurentMatrix g z mk| ≤ 11^q ∏|z|^{g-(n-1)} |V(z)|
  exp (logRatioZ (q-g) zn zp)`, `mk` marking the rows of weight `1`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section GramMainGen

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `norm_det_gram_le` with `F(1) = K + D_p` and the removed part `D_g` independent: the
matrix is `K + diag(D_-, D_p - 6 D_g)`. -/
theorem norm_det_gram_le_gen {K11 : Matrix m m ℂ} {K12 : Matrix m n ℂ} {K22 Dm Dp Dg : Matrix _ _ ℂ}
    (hK : (fromBlocks K11 K12 K12ᴴ K22).PosDef) (hA : (K11 + Dm).PosDef)
    (hDg : Dg.IsHermitian)
    (h1 : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp)).PosSemidef)
    (h2 : (fromBlocks K11 K12 K12ᴴ K22 - fromBlocks Dm 0 0 Dp).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 - fromBlocks 0 0 0 Dg).PosSemidef)
    (h4 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 + fromBlocks 0 0 0 Dg).PosSemidef) :
    ‖(fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp - (6 : ℂ) • Dg)).det‖ * K11.det.re ≤
      (2 + 6 * τ) ^ Fintype.card n * (K11 + Dm).det.re *
        (fromBlocks K11 K12 K12ᴴ K22).det.re := by
  classical
  have hK11 : K11.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · have := hK.1.submatrix (Sum.inl : m → m ⊕ n)
      convert this using 1
      ext i j; simp
    · have h := hK.dotProduct_mulVec_pos (x := x ⊕ᵥ (0 : n → ℂ))
        (by intro h; apply hx; funext i; simpa using congrFun h (Sum.inl i))
      simpa [fromBlocks_mulVec, Function.star_sumElim] using h
  have : Invertible K11 := hK11.isUnit.invertible
  have : Invertible (K11 + Dm) := hA.isUnit.invertible
  have hSgpos : (K22 - K12ᴴ * K11⁻¹ * K12).PosDef := by
    have hsemi := (PosDef.fromBlocks₁₁ K12 K22 hK11).mp hK.posSemidef
    refine PosDef.of_dotProduct_mulVec_pos hsemi.1 fun y hy => ?_
    rw [← schur_form_eq hK11.1 K12 K22 y]
    refine hK.dotProduct_mulVec_pos ?_
    intro hc
    apply hy
    funext j
    simpa using congrFun hc (Sum.inr j)
  have hS1 : (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12).PosSemidef :=
    (PosDef.fromBlocks₁₁ K12 (K22 + Dp) hA).mp h1
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := Complex.zero_le_real.mpr hτ
  have hSgH := hSgpos.1
  -- the minimiser
  have hFsplit : fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp) =
      fromBlocks K11 K12 K12ᴴ K22 + fromBlocks Dm 0 0 Dp := by
    ext (i | i) (j | j) <;> simp [fromBlocks]
  have hb : ((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
      (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp [Complex.conj_ofNat])).sub
        hS1.1
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e2 := schur_form_ge hA K12 (K22 + Dp) (-((K11⁻¹ * K12) *ᵥ y)) y
      have e3 := h2.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [hFsplit, add_mulVec, dotProduct_add] at e2
      rw [sub_mulVec, dotProduct_sub] at e3
      have e4 : star y ⬝ᵥ (((2 : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) -
          (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12)) *ᵥ y) =
          2 * (star y ⬝ᵥ ((K22 - K12ᴴ * K11⁻¹ * K12) *ᵥ y)) -
            star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y) := by
        rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]; simp
      rw [e4, ← e1]
      set P := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks K11 K12 K12ᴴ K22 *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set Q := star ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ (fromBlocks Dm 0 0 Dp *ᵥ
        ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y))
      set U := star y ⬝ᵥ ((K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12) *ᵥ y)
      have : 2 * P - U = (P - Q) + ((P + Q) - U) := by ring
      rw [this]
      exact add_nonneg e3 (sub_nonneg.mpr e2)
  have hc1 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) - Dg).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).sub hDg
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h3.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
      exact e3
  have hc2 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) + Dg).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).add hDg
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h4.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]
      exact e3
  have hmain := norm_det_schur_le hSgpos hS1 hDg hτ hb hc1 hc2
  -- determinants
  have hdF : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp - (6 : ℂ) • Dg)).det =
      (K11 + Dm).det * (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dg).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
    congr 2
    module
  have hdK : (fromBlocks K11 K12 K12ᴴ K22).det =
      K11.det * (K22 - K12ᴴ * K11⁻¹ * K12).det := by
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hA0 := hA.det_pos
  have hK0 := hK11.det_pos
  have hS0 := hSgpos.det_pos
  rw [hdF, hdK, norm_mul, norm_eq_re_of_pos hA0, re_mul_of_pos hK0 hS0]
  have ha := (Complex.lt_def.mp hA0).1
  have hk := (Complex.lt_def.mp hK0).1
  simp only [Complex.zero_re] at ha hk
  calc (K11 + Dm).det.re * ‖(K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dg).det‖ *
        K11.det.re
      ≤ (K11 + Dm).det.re * ((2 + 6 * τ) ^ Fintype.card n *
          (K22 - K12ᴴ * K11⁻¹ * K12).det.re) * K11.det.re := by
        gcongr
    _ = _ := by ring

end GramMainGen

section GramFullGen

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- `norm_det_gram_le_gen` on a full matrix over `m ⊕ n`. -/
theorem norm_det_gram_le_gen_full (Kf : Matrix (m ⊕ n) (m ⊕ n) ℂ) (d : m ⊕ n → ℝ) (dg : n → ℝ)
    (hK : Kf.PosDef) (hA : (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef)
    (h1 : (Kf + diagC d).PosSemidef) (h2 : (Kf - diagC d).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg)).PosSemidef)
    (h4 : ((τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg)).PosSemidef) :
    ‖(Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p))).det‖ *
        (Kf.submatrix Sum.inl Sum.inl).det.re ≤
      (2 + 6 * τ) ^ Fintype.card n *
        (Kf.submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).det.re * Kf.det.re := by
  classical
  have hKe : ∀ i j, Kf (Sum.inr i) (Sum.inl j) = star (Kf (Sum.inl j) (Sum.inr i)) :=
    fun i j => (hK.1.apply (Sum.inr i) (Sum.inl j)).symm
  have hfb : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ = Kf := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe]
  have hsub : Kf.submatrix Sum.inl Sum.inl = Kf.toBlocks₁₁ := rfl
  rw [hsub] at hA ⊢
  have e1 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ + diagC (fun p => d (Sum.inr p))) = Kf + diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e2 : Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks (diagC (fun a => d (Sum.inl a))) 0 0 (diagC (fun p => d (Sum.inr p))) =
      Kf - diagC d := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply]
  have e3 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ -
      Matrix.fromBlocks 0 0 0 (diagC dg) =
      (τ : ℂ) • Kf - diagC (Sum.elim (fun _ => 0) dg) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e4 : (τ : ℂ) • Matrix.fromBlocks Kf.toBlocks₁₁ Kf.toBlocks₁₂ Kf.toBlocks₁₂ᴴ Kf.toBlocks₂₂ +
      Matrix.fromBlocks 0 0 0 (diagC dg) =
      (τ : ℂ) • Kf + diagC (Sum.elim (fun _ => 0) dg) := by
    rw [hfb]
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, diagC, Matrix.diagonal_apply]
  have e5 : Matrix.fromBlocks (Kf.toBlocks₁₁ + diagC (fun a => d (Sum.inl a))) Kf.toBlocks₁₂
      Kf.toBlocks₁₂ᴴ (Kf.toBlocks₂₂ + diagC (fun p => d (Sum.inr p)) - (6 : ℂ) • diagC dg) =
      Kf + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p)) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, hKe, diagC, Matrix.diagonal_apply] <;> (try split_ifs) <;> (try simp) <;> (try ring)
  have key := norm_det_gram_le_gen (K11 := Kf.toBlocks₁₁) (K12 := Kf.toBlocks₁₂)
    (K22 := Kf.toBlocks₂₂)
    (Dm := diagC (fun a => d (Sum.inl a))) (Dp := diagC (fun p => d (Sum.inr p))) (Dg := diagC dg)
    (by rw [hfb]; exact hK) hA (diagC_conjTranspose _)
    (by rw [e1]; exact h1)
    (by rw [e2]; exact h2)
    hτ
    (by rw [e3]; exact h3)
    (by rw [e4]; exact h4)
  rw [e5, hfb] at key
  exact key

end GramFullGen

section MarkedLaurent

open CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

/-- Weight of the row `i` in the Gram form: `1` on negatives and marked rows, `-5` on free
positives. -/
def omegaM {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) : ℝ :=
  if mk i = true ∨ z i < 0 then 1 else -5

/-- Prefactor of the row `i`: `1/2` on negatives and marked rows, `-1/4` on free positives. -/
def lamM {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) : ℝ :=
  if mk i = true ∨ z i < 0 then 1 / 2 else -(1 / 4)

theorem abs_lamM_le {n : ℕ} (z : Fin n → ℝ) (mk : Fin n → Bool) (i : Fin n) :
    |lamM z mk i| ≤ 1 / 2 := by
  unfold lamM
  split_ifs <;> norm_num [abs_of_pos, abs_of_neg]

theorem markedLaurentEntry_eq {n g : ℕ} (hg : 2 * g + 1 ≤ n) (z : Fin n → ℝ)
    (mk : Fin n → Bool) (hz0 : ∀ i, z i ≠ 0) (i r : Fin n) :
    markedLaurentMatrix g z mk i r =
      lamM z mk i * z i ^ ((g : ℤ) - (n - 1 : ℕ)) *
        (z i ^ (r.rev : ℕ) + omegaM z mk i * z i ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ))) := by
  have h1 : z i ^ ((g : ℤ) - (n - 1 : ℕ)) * z i ^ (r.rev : ℕ) = z i ^ ((g : ℤ) - r) :=
    far_laurent_factor r (hz0 i)
  have h2 : z i ^ ((g : ℤ) - (n - 1 : ℕ)) * z i ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ)) =
      z i ^ ((r : ℤ) - g) := by
    first
      | rw [← zpow_natCast (z i) _, ← zpow_add₀ (hz0 i)]
      | rw [← zpow_add₀ (hz0 i)]
    congr 1
    have := r.isLt
    simp only [Fin.val_rev]
    omega
  by_cases hm : mk i = true
  · have hl : lamM z mk i = 1 / 2 := by simp [lamM, hm]
    have ho : omegaM z mk i = 1 := by simp [omegaM, hm]
    simp only [markedLaurentMatrix, Matrix.of_apply, hm, if_true, hl, ho]
    rw [← h1, ← h2]; ring
  · have hm' : mk i = false := by simpa using hm
    simp only [markedLaurentMatrix, Matrix.of_apply, hm', Bool.false_eq_true, if_false]
    rw [actualLaurentEntry_eq hg (hz0 i) r]
    have hl : lamM z mk i = lamOf (z i) := by simp [lamM, lamOf, hm]
    have ho : omegaM z mk i = omegaOf (z i) := by simp [omegaM, omegaOf, hm]
    rw [hl, ho]

theorem abs_det_laurent_eq_marked {n g : ℕ} (hg : 2 * g + 1 ≤ n) (x : Fin n → ℝ)
    (mk : Fin n → Bool) (hx0 : ∀ i, x i ≠ 0) :
    |(markedLaurentMatrix g x mk).det| =
      (∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
        |(dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).det| := by
  have hmat : (markedLaurentMatrix g x mk) =
      Matrix.diagonal (fun i => lamM x mk i * x i ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin n)) := by
    ext i r
    simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id, dMatW, Fin.revPerm_apply,
      Matrix.of_apply]
    rw [markedLaurentEntry_eq hg x mk hx0]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal, abs_mul, Finset.abs_prod]
  have hperm : |((dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).submatrix id
      (Fin.revPerm : Equiv.Perm (Fin n))).det| =
      |(dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x).det| := by
    simpa using Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin n))
      (Fin.revPerm : Equiv.Perm (Fin n)) (dMatW (omegaM x mk) ((n - 1 - 2 * g) + n - 1) x)
  rw [hperm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_mul, abs_zpow]

/-- **Lemma T on the sign-split index with marked rows**: only the free positives enter the
Loewner form (the marked rows have weight `1`, no `D_p` term). -/
theorem lemmaT_sum_form_marked {n k q e : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n) (x : Fin n → ℝ)
    (mk : Fin n → Bool)
    (hneg : ∀ b, x (σ (Sum.inl b)) < 0) (hpos : ∀ p, 0 < x (σ (Sum.inr p)))
    (hT : ∀ c : Fin n → ℝ, |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        CatalanMeasure.Signed.bDeriv x a * x a ^ e * c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b)) :
    ∀ u : Fin k ⊕ Fin q → ℝ,
      |∑ a, (Sum.elim (fun _ => (0 : ℝ))
          (fun p => if mk (σ (Sum.inr p)) = true then 0 else
            bdr (fun i => x (σ i)) (Sum.inr p) * x (σ (Sum.inr p)) ^ e) a) * u a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, u a * u b / (1 - x (σ a) * x (σ b)) := by
  classical
  intro u
  have h := hT (fun a => u (σ.symm a))
  have hl : ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
      CatalanMeasure.Signed.bDeriv x a * x a ^ e * (u (σ.symm a)) ^ 2 =
      ∑ a, (Sum.elim (fun _ => (0 : ℝ))
        (fun p => if mk (σ (Sum.inr p)) = true then 0 else
          bdr (fun i => x (σ i)) (Sum.inr p) * x (σ (Sum.inr p)) ^ e) a) * u a ^ 2 := by
    rw [Finset.sum_filter, ← Equiv.sum_comp σ, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hn' : ∀ b, ¬ (0 < x (σ (Sum.inl b)) ∧ mk (σ (Sum.inl b)) = false) :=
      fun b hb => absurd (hneg b) (not_lt.mpr hb.1.le)
    simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, zero_add, hn', if_false]
    refine Finset.sum_congr rfl fun p _ => ?_
    cases hm : mk (σ (Sum.inr p)) <;> simp [hm, hpos p, bdr_comp]
  have hr : ∑ a, ∑ b, u (σ.symm a) * u (σ.symm b) / (1 - x a * x b) =
      ∑ a, ∑ b, u a * u b / (1 - x (σ a) * x (σ b)) := by
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp
  rw [hl, hr] at h
  exact h

/-- **The real-place determinant bound with marked rows (Theorem C.3 at the marked Laurent
matrix).**  `mk` marks the rows of weight `1` (marked rows, any sign); the unmarked rows are the
free ones (weight `1/2, 1/2` if negative, `-1/4, 5/4` if positive).  For the sign split `σ`
(all negatives first, all positives second) with at least one negative, more than `2g`
positives, and Lemma T for the free positives (`hT`),
`|det L| ≤ 11^q ∏|z|^{g-(n-1)} |V(z)| exp (logRatioZ (q-g) zn zp)`. -/
theorem abs_det_laurent_le_marked {n k q g : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin n) (x : Fin n → ℝ) (mk : Fin n → Bool)
    (hinj : Function.Injective x) (hx1 : ∀ i, |x i| < 1) (hx0 : ∀ i, x i ≠ 0)
    (hneg : ∀ b, x (σ (Sum.inl b)) < 0) (hpos : ∀ p, 0 < x (σ (Sum.inr p)))
    (hk : 0 < k) (hq : 2 * g < q)
    (hT : ∀ c : Fin n → ℝ, |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        CatalanMeasure.Signed.bDeriv x a * x a ^ (n - 1 - 2 * g) * c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b)) :
    |(markedLaurentMatrix g x mk).det| ≤
      11 ^ q * ((∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) * |(Matrix.vandermonde x).det|) *
        Real.exp (logRatioZ (q - g) (fun b => x (σ (Sum.inl b))) (fun p => x (σ (Sum.inr p)))) := by
  classical
  have hcard := Fintype.card_congr σ
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hg : 2 * g + 1 ≤ n := by omega
  -- node data on the sign-split index type
  obtain ⟨z, hz⟩ : ∃ z : Fin k ⊕ Fin q → ℝ, z = fun i => x (σ i) := ⟨_, rfl⟩
  obtain ⟨xn, hxn⟩ : ∃ xn : Fin k → ℝ, xn = fun b => x (σ (Sum.inl b)) := ⟨_, rfl⟩
  obtain ⟨gp, hgp⟩ : ∃ gp : Fin q → ℝ, gp = fun p => x (σ (Sum.inr p)) := ⟨_, rfl⟩
  have hzx : ∀ i, z i = x (σ i) := fun i => by rw [hz]
  have hxnx : ∀ b, xn b = x (σ (Sum.inl b)) := fun b => by rw [hxn]
  have hgpx : ∀ p, gp p = x (σ (Sum.inr p)) := fun p => by rw [hgp]
  have hzl : ∀ b, z (Sum.inl b) = xn b := fun b => by rw [hzx, hxnx]
  have hzr : ∀ p, z (Sum.inr p) = gp p := fun p => by rw [hzx, hgpx]
  rw [← hxn, ← hgp]
  have hzinj : Function.Injective z := by rw [hz]; exact hinj.comp σ.injective
  have hz1 : ∀ i, |z i| < 1 := fun i => by rw [hzx]; exact hx1 _
  have hz0 : ∀ i, z i ≠ 0 := fun i => by rw [hzx]; exact hx0 _
  have hxninj : Function.Injective xn := fun a b h => by
    rw [hxn] at h; exact Sum.inl_injective (σ.injective (hinj h))
  have hxn1 : ∀ b, |xn b| < 1 := fun b => by rw [hxnx]; exact hx1 _
  have hxn0 : ∀ b, xn b ≠ 0 := fun b => by rw [hxnx]; exact hx0 _
  have hgp1 : ∀ p, |gp p| < 1 := fun p => by rw [hgpx]; exact hx1 _
  -- Laurent matrix to the weighted Vandermonde-type matrix
  have hL := abs_det_laurent_eq_marked hg x mk hx0
  have h51 := lemma51_weighted (omegaM x mk) (n - 1 - 2 * g) x hinj hx0 hx1
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hKx : 0 < (kMat x).det := kR_det_pos hinj hx0 hx1
  -- the reindexed real matrix
  obtain ⟨d, hd⟩ : ∃ d : Fin k ⊕ Fin q → ℝ,
      d = fun i => bdr z i * z i ^ (n - 1 - 2 * g) := ⟨_, rfl⟩
  have hbd : ∀ i, bdr z i = CatalanMeasure.Signed.bDeriv x (σ i) := fun i => by
    rw [hz]; exact bdr_comp σ x i
  have hnb : ∀ a, negBlaschkeDeriv x a = CatalanMeasure.Signed.bDeriv x a := fun a => rfl
  obtain ⟨dg, hdg⟩ : ∃ dg : Fin q → ℝ,
      dg = fun p => if mk (σ (Sum.inr p)) = true then 0 else d (Sum.inr p) := ⟨_, rfl⟩
  obtain ⟨dF, hdF⟩ : ∃ dF : Fin k ⊕ Fin q → ℝ,
      dF = Sum.elim (fun b => d (Sum.inl b)) (fun p => d (Sum.inr p) - 6 * dg p) := ⟨_, rfl⟩
  have hMι : (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).submatrix σ σ =
      kR z + Matrix.diagonal dF := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, kMat, kR, Matrix.of_apply, dW,
      Matrix.diagonal_apply, σ.injective.eq_iff]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      rw [hz]
      rcases i with b | p
      · have h1 : omegaM x mk (σ (Sum.inl b)) = 1 := by simp [omegaM, hneg b]
        simp only [hdF, hd, Sum.elim_inl, h1, hnb, ← hbd, hz]
        ring
      · by_cases hm : mk (σ (Sum.inr p)) = true
        · have h1 : omegaM x mk (σ (Sum.inr p)) = 1 := by simp [omegaM, hm]
          simp only [hdF, hd, hdg, Sum.elim_inr, h1, hnb, ← hbd, hz, hm, if_true]
          ring
        · have h1 : omegaM x mk (σ (Sum.inr p)) = -5 := by
            simp [omegaM, hm, not_lt.mpr (hpos p).le]
          have hm' : mk (σ (Sum.inr p)) = false := by simpa using hm
          simp only [hdF, hd, hdg, Sum.elim_inr, h1, hnb, ← hbd, hz, hm', Bool.false_eq_true, if_false]
          ring
    · rw [if_neg hij, if_neg hij, hz]
  have hdet1 : (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).det =
      (kR z + Matrix.diagonal dF).det := by
    rw [← hMι, Matrix.det_submatrix_equiv_self]
  have hdetK : (kMat x).det = (kR z).det := by
    have : (kMat x).submatrix σ σ = kR z := by
      ext i j; simp [kMat, kR, hz]
    rw [← this, Matrix.det_submatrix_equiv_self]
  -- complex positivity data
  have hKc : (kC z).PosDef := kC_posDef hzinj hz0 hz1
  have h1c : (kC z + diagC d).PosSemidef := by
    rw [hd]; exact pick_F_nonneg hzinj hz0 hz1 (n - 1 - 2 * g)
  have h2c : (kC z - diagC d).PosSemidef := by
    rw [hd]; exact pick_F_le_two_K hzinj hz0 hz1 (n - 1 - 2 * g)
  -- Lemma T on the sign-split index, as complex Loewner inequalities
  have hTι : ∀ u : Fin k ⊕ Fin q → ℝ,
      |∑ a, (Sum.elim (fun _ => (0 : ℝ)) dg a) * u a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, u a * u b / (1 - z a * z b) := by
    rw [hdg, hd, hz]
    exact lemmaT_sum_form_marked σ x mk hneg hpos hT
  obtain ⟨h3c, h4c⟩ := lemmaT_loewner_complex z (Sum.elim (fun _ => (0 : ℝ)) dg) hTι
  -- the negative block
  have hs2 : q < 2 * (q - g) := by omega
  have he2 : (n - 1 - 2 * g) + q + 1 = 2 * (q - g) + k := by omega
  have hnb' := negBlock_posDef z hzinj hz0 hz1 (q - g) (n - 1 - 2 * g) hk hs2 he2
  have hxz : (fun b => z (Sum.inl b)) = xn := funext hzl
  have hgz : (fun p => z (Sum.inr p)) = gp := funext hzr
  rw [hxz, hgz] at hnb'
  obtain ⟨hM1', hA', hM1pos⟩ := hnb'
  have hM1 : (kC z).submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a)) =
      (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).map (fun r : ℝ => (r : ℂ)) := by
    rw [hd]; exact hM1'
  have hA : ((kC z).submatrix Sum.inl Sum.inl + diagC (fun a => d (Sum.inl a))).PosDef := by
    rw [hd]; exact hA'
  have hR0 := route_ratio_pos gp hgp1 (q - g) k (n - 1 - 2 * g) hk hs2 he2 xn hxninj hxn0 hxn1
  have hK11 : 0 < (kMat xn).det := kR_det_pos hxninj hxn0 hxn1
  have hGram := norm_det_gram_le_gen_full (m := Fin k) (n := Fin q) (kC z) d dg hKc hA h1c h2c
    (τ := 3 / 2) (by norm_num) h3c h4c
  have hFc : kC z + diagC (Sum.elim (fun a => d (Sum.inl a)) (fun p => d (Sum.inr p) - 6 * dg p)) =
      (kR z + Matrix.diagonal dF).map (fun r : ℝ => (r : ℂ)) := by
    rw [← hdF]
    ext i j
    simp only [kC, diagC, kR, Matrix.add_apply, Matrix.of_apply, Matrix.map_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  have hsub11 : (kC z).submatrix Sum.inl Sum.inl = (kR xn).map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    simp [kC, kR, hzl]
  rw [hFc, hM1, hsub11, kC_eq_map z, det_map_ofReal, det_map_ofReal, det_map_ofReal,
    det_map_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, Complex.ofReal_re,
    Complex.ofReal_re] at hGram
  have h11 : (2 + 6 * (3 / 2 : ℝ)) = 11 := by norm_num
  rw [h11, Fintype.card_fin] at hGram
  rw [← hdet1, ← hdetK] at hGram
  -- assemble
  have hexp : Real.exp (logRatioZ (q - g) xn gp) =
      (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).det / (kMat xn).det := by
    rw [← log_route_two gp hgp1 (q - g) k (n - 1 - 2 * g) hk hs2 he2 xn hxninj hxn0 hxn1]
    exact Real.exp_log hR0
  rw [hexp]
  set Dw := (kMat x + dW (omegaM x mk) (n - 1 - 2 * g) x).det with hDw
  set Dm := (dMatW (omegaM x mk) (n - 1 - 2 * g + n - 1) x).det with hDm
  set M1d := (kMat xn + dMinus (hOfRoots gp) q (n - 1 - 2 * g) xn).det with hM1d
  have hDmeq : Dm = (Matrix.vandermonde x).det * (Dw / (kMat x).det) := by
    rw [h51]; field_simp
  have hDmabs : |Dm| = |(Matrix.vandermonde x).det| * (|Dw| / (kMat x).det) := by
    rw [hDmeq, abs_mul, abs_div, abs_of_pos hKx]
  have hDw1 : |Dw| ≤ 11 ^ q * M1d * (kMat x).det / (kMat xn).det :=
    (le_div_iff₀ hK11).mpr hGram
  have hbound : |Dw| / (kMat x).det ≤ 11 ^ q * (M1d / (kMat xn).det) := by
    rw [div_le_iff₀ hKx]
    calc |Dw| ≤ 11 ^ q * M1d * (kMat x).det / (kMat xn).det := hDw1
      _ = 11 ^ q * (M1d / (kMat xn).det) * (kMat x).det := by ring
  have hPi : ∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) ≤
      ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) := by
    rw [Finset.prod_mul_distrib]
    have h1 : ∏ i, |lamM x mk i| ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
        (fun i _ => (abs_lamM_le x mk i).trans (by norm_num))
    have h2 : 0 ≤ ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) :=
      Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
    nlinarith
  have hPi1 : 0 ≤ ∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ)) :=
    Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _
  calc |(markedLaurentMatrix g x mk).det|
      = (∏ i, |lamM x mk i| * |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
          (|(Matrix.vandermonde x).det| * (|Dw| / (kMat x).det)) := by rw [hL, hDmabs]
    _ ≤ (∏ i, |x i| ^ ((g : ℤ) - (n - 1 : ℕ))) *
          (|(Matrix.vandermonde x).det| * (11 ^ q * (M1d / (kMat xn).det))) :=
        mul_le_mul hPi (mul_le_mul_of_nonneg_left hbound (abs_nonneg _)) (by positivity) hPi1
    _ = _ := by ring

end MarkedLaurent

section SheetFixed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set

/-- The node vector of the marked sheet on `Fin n`: free rows `x`, then marked rows `y`. -/
def sheetNodes {p m n : ℕ} (hpm : p + m = n) (x : Fin p → ℝ) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun i => Fin.append x y (Fin.cast hpm.symm i)

/-- The marking of the sheet: the rows of `y` are marked. -/
def sheetMarks {p m n : ℕ} (hpm : p + m = n) : Fin n → Bool :=
  fun i => Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)

/-- The relabelling of the four sign groups (free negatives, marked negatives, free positives,
marked positives) onto the `p + m` rows. -/
def quadEquiv {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) :
    Fin ((k + m1) + (q + m2)) ≃ Fin (p + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm)).trans
    ((Equiv.sumSumSumComm (Fin k) (Fin m1) (Fin q) (Fin m2)).trans
      ((Equiv.sumCongr σx σy).trans finSumFinEquiv))

theorem quad_apply {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p)
    (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (i : Fin ((k + m1) + (q + m2))) :
    Fin.append (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
      (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) i =
      Fin.append x y (quadEquiv σx σy i) := by
  obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective i
  rcases u with a | a
  · obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with b | b <;> simp [quadEquiv, fin_append_eq_elim]
  · obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with b | b <;> simp [quadEquiv, fin_append_eq_elim]

/-- `groupedProduct` for `a = b = 0` and any number `r` of free rows. -/
theorem groupedProduct_free_eq (P : Parameters) (N : ℕ) {r : ℕ} (x s : Fin r → ℝ) :
    groupedProduct P N x e0 e0 s =
      (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) * |(Matrix.vandermonde x).det| *
        paramPinPrincipal P N x s := by
  have hap : (Fin.append x e0 : Fin (r + 0) → ℝ) = x := fin_append_nil _ x e0
  unfold groupedProduct groupedPairProduct crossCauchyProduct
  rw [hap, Matrix.det_vandermonde]
  simp

theorem groupedProduct_free_pos {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {r : ℕ} (x s : Fin r → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    0 < groupedProduct P N x e0 e0 s := by
  rw [groupedProduct_free_eq]
  have h1 : 0 < ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) :=
    Finset.prod_pos fun i _ => zpow_pos (abs_pos.mpr (hx0 i)) _
  have h2 : 0 < |(Matrix.vandermonde x).det| :=
    abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hxi)
  exact mul_pos (mul_pos h1 h2) (paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi)

theorem log_groupedProduct_free {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {r : ℕ} (x s : Fin r → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) (hxi : Function.Injective x) (hsi : Function.Injective s) :
    Real.log (groupedProduct P N x e0 e0 s) = (P.n N : ℝ) ^ 2 *
      (groupedConstant P N r 0 0 + pinOffDiagonalInteraction (P.n N : ℝ) 1 x s +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (P.n N : ℝ) ^ 2 +
        (∑ i, populationPhysicalFreeField P N (x i)) / (P.n N : ℝ) +
        (∑ j, populationPhysicalColumnField P N (0 + 0) (s j)) / (P.n N : ℝ)) := by
  have hap : (Fin.append x e0 : Fin (r + 0) → ℝ) = x := fin_append_nil _ x e0
  have h := log_groupedProduct hP hN x e0 e0 s hx (fun i => i.elim0) (fun i => i.elim0) hs hx0
    (fun i => i.elim0) hxi (by rw [hap]; exact hxi) (fun i => i.elim0) hsi
  rw [h]
  congr 1
  exact groupedValue_free_eq _ _ _ _ _ _ x s e0 e0

/-- The constant of the free rows is at most the constant of all `n` rows. -/
theorem groupedConstant_free_le (P : Parameters) (N : ℕ) {r : ℕ} (hr : r ≤ P.n N) :
    groupedConstant P N r 0 0 ≤ groupedConstant P N (P.n N) 0 0 := by
  unfold groupedConstant
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hd : 0 ≤ (1 : ℝ) / (P.n N : ℝ) ^ 2 := by positivity
  have hc : r * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + r.choose 2 ≤
      P.n N * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + (P.n N).choose 2 := by
    have := Nat.choose_le_choose 2 hr
    have := Nat.mul_le_mul_right (P.C N - 1) hr
    omega
  have hcR : ((r * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + r.choose 2 : ℕ) : ℝ) ≤
      ((P.n N * (P.C N - 1) + (0 + 0) * (P.n N - P.g N - 1) + (P.n N).choose 2 : ℕ) : ℝ) := by
    exact_mod_cast hc
  have := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hcR (sq_nonneg (P.n N : ℝ))) hl
  simpa using this

end SheetFixed

section ClassFixed

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set CatalanMeasure.GenD.Signed

/-- The four sign groups, appended: `(free negatives, marked negatives, free positives,
marked positives)` (the node list `Z` of `signed_second_energy_fixed_nodes`). -/
def quadNodes {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (x : Fin p → ℝ) (y : Fin m → ℝ) : Fin ((k + m1) + (q + m2)) → ℝ :=
  Fin.append (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
    (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))))

theorem quadNodes_apply {k q m1 m2 p m : ℕ} (σx : Fin k ⊕ Fin q ≃ Fin p)
    (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (x : Fin p → ℝ) (y : Fin m → ℝ)
    (i : Fin ((k + m1) + (q + m2))) :
    quadNodes σx σy x y i = Fin.append x y (quadEquiv σx σy i) :=
  quad_apply σx σy x y i

theorem append_forall {p m : ℕ} {Q : ℝ → Prop} {x : Fin p → ℝ} {y : Fin m → ℝ}
    (hx : ∀ i, Q (x i)) (hy : ∀ j, Q (y j)) (j : Fin (p + m)) : Q (Fin.append x y j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hx, hy]

/-- **Class-branch bound for the marked sheet (deterministic).**  Given the determinant data
(Lemma T for the free positives), the energy inequality `hE` of
`signed_second_energy_fixed_nodes` in its explicit form and the per-row field comparison
`hrow`, the sheet core is at most `11^(q+m₂) exp (n² Bd + c₂ N m)`. -/
theorem fixed_class_core_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {m k q m1 m2 : ℕ} (hpm : k + q + m = P.n N)
    (σx : Fin k ⊕ Fin q ≃ Fin (k + q)) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (x s : Fin (k + q) → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ i, s i ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective (Fin.append x y))
    (hsi : Function.Injective s)
    (hxneg : ∀ b, x (σx (Sum.inl b)) < 0) (hxpos : ∀ b, 0 < x (σx (Sum.inr b)))
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (hk : 0 < k) (hq : 2 * P.g N < q)
    (hT : ∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a ∧ sheetMarks hpm a = false),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b))
    (c2 Bd : ℝ)
    (hE : groupedConstant P N (P.n N) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1
          (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) s +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |quadNodes σx σy x y j - quadNodes σx σy x y i|) /
          (P.n N : ℝ) ^ 2 +
        (∑ i, populationPhysicalFreeField P N (quadNodes σx σy x y i)) / (P.n N : ℝ) +
        (∑ j, populationPhysicalColumnField P N (0 + 0) (s j)) / (P.n N : ℝ) +
        logRatioZ (q + m2 - P.g N)
          (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
          (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) /
          (P.n N : ℝ) ^ 2 ≤ Bd)
    (hrow : ∀ j, Real.log (markedSheetWeight P N (y j)) ≤
      (P.n N : ℝ) * populationPhysicalFreeField P N (y j) + c2 * N) :
    markedSheetCore P N hpm x y s ≤
      11 ^ (q + m2) * Real.exp ((P.n N : ℝ) ^ 2 * Bd + c2 * N * m) := by
  classical
  have hn1 : 1 ≤ P.n N := n_pos hP hN
  have hg2 := two_g_lt_n hP hN
  have hnR : (0 : ℝ) < (P.n N : ℝ) := by exact_mod_cast hn1
  have hn2 : (0 : ℝ) < (P.n N : ℝ) ^ 2 := by positivity
  obtain ⟨z, hzd⟩ : ∃ z : Fin (P.n N) → ℝ, z = sheetNodes hpm x y := ⟨_, rfl⟩
  obtain ⟨mk, hmkd⟩ : ∃ mk : Fin (P.n N) → Bool, mk = sheetMarks hpm := ⟨_, rfl⟩
  rw [← hzd, ← hmkd] at hT
  obtain ⟨e4, he4⟩ : ∃ e4 : Fin ((k + m1) + (q + m2)) ≃ Fin (P.n N),
      e4 = (quadEquiv σx σy).trans (finCongr hpm) := ⟨_, rfl⟩
  have hzZ : ∀ i, z (e4 i) = quadNodes σx σy x y i := by
    intro i
    rw [hzd, he4, quadNodes_apply]
    simp [sheetNodes]
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (k + m1) ⊕ Fin (q + m2) ≃ Fin (P.n N),
      σ = finSumFinEquiv.trans e4 := ⟨_, rfl⟩
  have hzσl : ∀ b, z (σ (Sum.inl b)) =
      Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))) b := by
    intro b
    rw [hσ]
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rw [hzZ]
    unfold quadNodes
    simp
  have hzσr : ∀ b, z (σ (Sum.inr b)) =
      Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))) b := by
    intro b
    rw [hσ]
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_right]
    rw [hzZ]
    unfold quadNodes
    simp
  have hzm : ∀ i, z i ∈ Ioo (-1 : ℝ) 1 := fun i => by
    rw [hzd]; exact append_forall (Q := fun t => t ∈ Ioo (-1 : ℝ) 1) hx hy _
  have hz1 : ∀ i, |z i| < 1 := fun i => abs_lt.mpr (hzm i)
  have hz0 : ∀ i, z i ≠ 0 := fun i => by
    rw [hzd]; exact append_forall (Q := fun t => t ≠ 0) hx0 hy0 _
  have hzinj : Function.Injective z := by
    rw [hzd]; exact hzi.comp (Fin.cast_injective _)
  have hxi : Function.Injective x := by
    intro a b hab
    have := hzi (show Fin.append x y (Fin.castAdd m a) = Fin.append x y (Fin.castAdd m b) by
      simpa using hab)
    simpa using this
  have hneg : ∀ b, z (σ (Sum.inl b)) < 0 := fun b => by
    rw [hzσl]; exact append_forall (Q := fun t => t < 0) hxneg hyneg b
  have hpos : ∀ b, 0 < z (σ (Sum.inr b)) := fun b => by
    rw [hzσr]; exact append_forall (Q := fun t => 0 < t) hxpos hypos b
  have hdet := abs_det_laurent_le_marked (g := P.g N) σ z mk hzinj hz1 hz0 hneg hpos
    (by omega) (by omega) hT
  have hLRe : logRatioZ (q + m2 - P.g N) (fun b => z (σ (Sum.inl b)))
      (fun b => z (σ (Sum.inr b))) =
      logRatioZ (q + m2 - P.g N)
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) := by
    congr 1 <;> funext b
    · exact hzσl b
    · exact hzσr b
  rw [hLRe] at hdet
  -- the sheet core in terms of the Laurent determinant
  have hcore : markedSheetCore P N hpm x y s =
      |(markedLaurentMatrix (P.g N) z mk).det| * (∏ j, paramRowNodeWeight P N (y j)) *
        paramPinPrincipal P N x s /
          ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    rw [hzd, hmkd]; rfl
  have hRpos : 0 < ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    apply Finset.prod_pos
    intro j _
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hWnn : 0 ≤ ∏ j, paramRowNodeWeight P N (y j) :=
    Finset.prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)
  have hpinpos := paramPinPrincipal_pos hP hN x s hx hs hx0 hxi hsi
  -- factorisations
  have hZ : ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) =
      (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        ∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) := by
    rw [hzd]
    unfold sheetNodes
    have := prod_fin_cast hpm (fun j : Fin (k + q + m) =>
      |Fin.append x y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)))
    rw [this, Fin.prod_univ_add]
    simp
  have hcancel : (∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        (∏ j, paramRowNodeWeight P N (y j)) =
      (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
        ∏ j, markedSheetWeight P N (y j) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ =>
      marked_sheet_weight_cancellation hP hN (hy j) (hy0 j)
  -- energy bookkeeping: relabellings
  have hpinR : pinOffDiagonalInteraction (P.n N : ℝ) 1
      (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) s =
      pinOffDiagonalInteraction (P.n N : ℝ) 1 x s := by
    rw [append_split_eq σx x]
    have := pinOff_perm (P.n N : ℝ) 1 x s (splitEquiv σx) (Equiv.refl _)
    simpa using this
  have hquad : quadNodes σx σy x y = fun i => z (e4 i) := funext fun i => (hzZ i).symm
  have hVz4 : (∑ i, ∑ j ∈ Finset.Ioi i,
      Real.log |quadNodes σx σy x y j - quadNodes σx σy x y i|) =
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| := by
    rw [hquad]
    exact sum_Ioi_equiv (fun a b => Real.log |b - a|) (fun a b => by rw [abs_sub_comm]) z e4
  have hRz4 : (∑ i, populationPhysicalFreeField P N (quadNodes σx σy x y i)) =
      (∑ i, populationPhysicalFreeField P N (x i)) +
        ∑ j, populationPhysicalFreeField P N (y j) := by
    rw [hquad]
    rw [Equiv.sum_comp e4 (fun a => populationPhysicalFreeField P N (z a)), hzd]
    unfold sheetNodes
    have := sum_fin_cast hpm (fun j : Fin (k + q + m) =>
      populationPhysicalFreeField P N (Fin.append x y j))
    rw [this, Fin.sum_univ_add]
    simp
  rw [hpinR, hVz4, hRz4] at hE
  -- notation
  set Zx := ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) with hZx
  set Zy := ∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) with hZy
  set W := ∏ j, paramRowNodeWeight P N (y j) with hW
  set R := ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| with hR
  set M := ∏ j, markedSheetWeight P N (y j) with hM
  set pin := paramPinPrincipal P N x s with hpin
  set Vz := |(Matrix.vandermonde z).det| with hVz
  set Vx := |(Matrix.vandermonde x).det| with hVx
  set LR := logRatioZ (q + m2 - P.g N)
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) with hLR
  have hZxpos : 0 < Zx := Finset.prod_pos fun i _ => zpow_pos (abs_pos.mpr (hx0 i)) _
  have hMpos : 0 < M := Finset.prod_pos fun j _ => markedSheetWeight_pos P N _
  have hVzpos : 0 < Vz := abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hzinj)
  have hVxpos : 0 < Vx := abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hxi)
  have heLRpos : 0 < Real.exp LR := Real.exp_pos _
  -- the bound by U
  have hbound : markedSheetCore P N hpm x y s ≤
      11 ^ (q + m2) * (Real.exp LR * Zx * Vz * pin * M) := by
    rw [hcore, div_le_iff₀ hRpos]
    calc |(markedLaurentMatrix (P.g N) z mk).det| * W * pin
        ≤ (11 ^ (q + m2) * ((∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) * Vz) *
            Real.exp LR) * W * pin := by
          gcongr
      _ = 11 ^ (q + m2) * (Real.exp LR * Zx * Vz * pin) * (Zy * W) := by rw [hZ]; ring
      _ = 11 ^ (q + m2) * (Real.exp LR * Zx * Vz * pin) * (R * M) := by rw [hcancel]
      _ = _ := by ring
  refine hbound.trans ?_
  have h11 : (0 : ℝ) < 11 ^ (q + m2) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h11.le
  have hUpos : 0 < Real.exp LR * Zx * Vz * pin * M :=
    mul_pos (mul_pos (mul_pos (mul_pos heLRpos hZxpos) hVzpos) hpinpos) hMpos
  refine (Real.log_le_iff_le_exp hUpos).mp ?_
  -- logarithms
  have hlogU : Real.log (Real.exp LR * Zx * Vz * pin * M) =
      LR + Real.log Zx + Real.log Vz + Real.log pin + Real.log M := by
    rw [Real.log_mul (mul_pos (mul_pos (mul_pos heLRpos hZxpos) hVzpos) hpinpos).ne' hMpos.ne',
      Real.log_mul (mul_pos (mul_pos heLRpos hZxpos) hVzpos).ne' hpinpos.ne',
      Real.log_mul (mul_pos heLRpos hZxpos).ne' hVzpos.ne',
      Real.log_mul heLRpos.ne' hZxpos.ne', Real.log_exp]
  have hlogVz : Real.log Vz = ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| := by
    rw [hVz, Matrix.det_vandermonde]
    exact log_abs_vandermonde z hzinj
  have hlogVx : Real.log Vx = ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| := by
    rw [hVx, Matrix.det_vandermonde]
    exact log_abs_vandermonde x hxi
  have hlogM : Real.log M = ∑ j, Real.log (markedSheetWeight P N (y j)) :=
    Real.log_prod (fun j _ => (markedSheetWeight_pos P N _).ne')
  have hGP := log_groupedProduct_free hP hN x s hx hs hx0 hxi hsi
  have hGPeq := groupedProduct_free_eq P N x s
  have hlogGP : Real.log (groupedProduct P N x e0 e0 s) =
      Real.log Zx + Real.log Vx + Real.log pin := by
    rw [hGPeq, Real.log_mul (mul_pos hZxpos hVxpos).ne' hpinpos.ne',
      Real.log_mul hZxpos.ne' hVxpos.ne']
  have hcp : groupedConstant P N (k + q) 0 0 ≤ groupedConstant P N (P.n N) 0 0 :=
    groupedConstant_free_le P N (by omega)
  have hmsw : (∑ j, Real.log (markedSheetWeight P N (y j))) ≤
      (P.n N : ℝ) * (∑ j, populationPhysicalFreeField P N (y j)) + c2 * N * m := by
    calc (∑ j, Real.log (markedSheetWeight P N (y j)))
        ≤ ∑ j, ((P.n N : ℝ) * populationPhysicalFreeField P N (y j) + c2 * N) :=
          Finset.sum_le_sum fun j _ => hrow j
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
        ring
  -- assemble
  set SVx := ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| with hSVx
  set SVz := ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| with hSVz
  set SRx := ∑ i, populationPhysicalFreeField P N (x i) with hSRx
  set SRy := ∑ j, populationPhysicalFreeField P N (y j) with hSRy
  set SC := ∑ j, populationPhysicalColumnField P N (0 + 0) (s j) with hSC
  set Pin := pinOffDiagonalInteraction (P.n N : ℝ) 1 x s with hPin
  set c0 := groupedConstant P N (P.n N) 0 0 with hc0
  set cp := groupedConstant P N (k + q) 0 0 with hcp'
  set nn := (P.n N : ℝ) with hnn
  have hE' : nn ^ 2 * c0 + nn ^ 2 * Pin + SVz + nn * SRx + nn * SRy + nn * SC + LR ≤
      nn ^ 2 * Bd := by
    have h := mul_le_mul_of_nonneg_left hE hn2.le
    have e : nn ^ 2 * (c0 + Pin + SVz / nn ^ 2 + (SRx + SRy) / nn + SC / nn + LR / nn ^ 2) =
        nn ^ 2 * c0 + nn ^ 2 * Pin + SVz + nn * SRx + nn * SRy + nn * SC + LR := by
      field_simp
      ring
    linarith
  have hGP' : Real.log Zx + SVx + Real.log pin =
      nn ^ 2 * cp + nn ^ 2 * Pin + SVx + nn * SRx + nn * SC := by
    have e : nn ^ 2 * (cp + Pin + SVx / nn ^ 2 + SRx / nn + SC / nn) =
        nn ^ 2 * cp + nn ^ 2 * Pin + SVx + nn * SRx + nn * SC := by
      field_simp
    rw [hlogVx] at hlogGP
    rw [← e, ← hGP, hlogGP]
  have hcpn : nn ^ 2 * cp ≤ nn ^ 2 * c0 := mul_le_mul_of_nonneg_left hcp hn2.le
  rw [hlogU, hlogVz, hlogM]
  linarith [hE', hGP', hcpn, hmsw]

end ClassFixed

section SheetFixedFinal

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan Filter Set CatalanMeasure.GenD.Signed

/-- **Class-branch link data for fixed rows** (the Lemma K / Lemma T / `FixAdm` side of the
consumer, supplied with the class `Cls` of free configurations).  For the marked sheet with free
rows `x`, marked rows `y` (all in `G`), a free class configuration `Cls N p x`, and for every
sign split of the free rows and of the marked rows:
* Lemma T for the free positives of the sheet (`sheetNodes`, `sheetMarks`);
* at least one free negative, more than `2g` free positives, the negative-fraction range of
  every α-interval of `T` containing `α = (m₁ + m₂)/n`, membership in `T.Clsf` and `T.FixAdm`. -/
def SignedFixedClassLink (P : Parameters) {I : ℕ} (T : SignedFixedBounds I)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (G : ℝ → Prop) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ),
    (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) → (∀ j, y j ∈ Ioo (-1 : ℝ) 1) →
    (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Function.Injective (Fin.append x y) → Cls N p x →
    (∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a ∧ sheetMarks hpm a = false),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b)) ∧
    ∀ (k q m1 m2 : ℕ) (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m),
      (∀ b, x (σx (Sum.inl b)) < 0) → (∀ b, 0 < x (σx (Sum.inr b))) →
      (∀ b, y (σy (Sum.inl b)) < 0) → (∀ b, 0 < y (σy (Sum.inr b))) →
      0 < k ∧ 2 * P.g N < q ∧
      (∀ i, T.lo i ≤ ((m1 + m2 : ℕ) : ℝ) / (T.ncount N : ℝ) →
        ((m1 + m2 : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
        T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i) ∧
      T.Clsf N k q m1 m2 (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
        (fun b => y (σy (Sum.inl b))) (fun b => y (σy (Sum.inr b))) ∧
      T.FixAdm N m1 m2 (fun b => y (σy (Sum.inl b))) (fun b => y (σy (Sum.inr b)))

/-- **The signed second-case sheet bound with marked rows (`α₁ > 0`)**: `SignedSecondSheetCore`
for the α-interval contract `SignedFixedBounds`, from
* the non-class branch (`hnon`: the old energy route, restricted to the complement of `Cls`, via
  `SheetCopy.second_marked_sheet_product_on_restr`);
* the class branch: the marked Laurent determinant bound `abs_det_laurent_le_marked`
  (Theorem C.3 with weights `1` on marked rows and `-5` on free positives), the energy
  inequality `signed_second_energy_fixed_nodes` (relabelled onto the sheet by `quadEquiv`), and
  the per-row field comparison `hrow` (the marked row factor `markedSheetWeight` against the
  contract's row field `Rf`, with cost `c₂ N` per row: Phase 2 / the cap `G`);
* the identification of `T` with the sheet's data (`hn`, `hconst`, `hRf`, `hCf`, `hLRf`, `hB`);
* the class link `hlink`. -/
theorem signedSecondSheetFixed {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedFixedBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N, T.constant N = groupedConstant P N (P.n N) 0 0)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2 xn gp yn yp, T.LRf N k q m1 m2 xn gp yn yp =
      logRatioZ (q + m2 - P.g N) (Fin.append xn yn) (Fin.append gp yp))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (hlink : SignedFixedClassLink P T Cls G)
    (hrow : ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, y ∈ Ioo (-1 : ℝ) 1 → y ≠ 0 → G y →
      Real.log (markedSheetWeight P N y) ≤
        (P.n N : ℝ) * populationPhysicalFreeField P N y + c2 * N) :
    SignedSecondSheetCore P G target0 c2 T.α1 := by
  intro ε hε
  filter_upwards [second_marked_sheet_product_on_restr hP target0 c2 G _ hnon hε,
    signed_second_energy_fixed_nodes T hε, hlink, hrow, eventually_gt_atTop (0 : ℕ)]
    with N hnonN hE hl hr hN0 p m hpm x y s hmle hx hx0 hy hy0 hyG hs hzi hsi hcase
  by_cases hc : Cls N p x
  · -- class branch
    obtain ⟨hT, hrest⟩ := hl p m hpm x y hx hx0 hy hy0 hyG hzi hc
    obtain ⟨k, q, σx, hxneg, hxpos⟩ := exists_sign_split x hx0
    obtain ⟨m1, m2, σy, hyneg, hypos⟩ := exists_sign_split y hy0
    obtain ⟨hk, hq, hκ, hCls, hAdm⟩ := hrest k q m1 m2 σx σy hxneg hxpos hyneg hypos
    have hkq := Fintype.card_congr σx
    simp only [Fintype.card_sum, Fintype.card_fin] at hkq
    have hm12 := Fintype.card_congr σy
    simp only [Fintype.card_sum, Fintype.card_fin] at hm12
    subst hkq
    have hn1 : 1 ≤ P.n N := n_pos hP hN0
    have hxi : Function.Injective x := by
      intro a b hab
      have := hzi (show Fin.append x y (Fin.castAdd m a) = Fin.append x y (Fin.castAdd m b) by
        simpa using hab)
      simpa using this
    have hkqN : (k + m1) + (q + m2) = T.ncount N := by rw [hn]; omega
    have hα : ((m1 + m2 : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) := by
      rw [hm12, hn]; exact hmle
    have hinjF : Function.Injective
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) := by
      rw [append_split_eq]; exact hxi.comp (splitEquiv σx).injective
    have hinjZ : Function.Injective
        (Fin.append (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
          (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))))) := by
      have h := hzi.comp (quadEquiv σx σy).injective
      have e : (Fin.append x y ∘ quadEquiv σx σy) = quadNodes σx σy x y :=
        funext fun i => (quad_apply σx σy x y i).symm
      rw [e] at h
      exact h
    have hEc := hE k q m1 m2 hkqN hα hκ _ _ _ _ s
      (fun b => ⟨(hx _).1, hxneg b⟩) (fun b => ⟨hxpos b, (hx _).2⟩)
      (fun b => ⟨(hy _).1, hyneg b⟩) (fun b => ⟨hypos b, (hy _).2⟩) hinjF hinjZ
      (fun j => hs j) hsi hCls hAdm
    rw [hLRf, hconst, hRf, hCf, hB, hn] at hEc
    have hcore := fixed_class_core_le hP hN0 hpm σx σy x s y hx hx0 hy hy0 hs hzi hsi hxneg hxpos
      hyneg hypos hk hq hT c2 (-target0 + Real.log 2 / 2 + ε) hEc
      (fun j => hr (y j) (hy j) (hy0 j) (hyG j))
    have hnR : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
    have hcardσ : q + m2 ≤ P.n N := by omega
    have h11 := eleven_pow_le hcardσ hn1
    have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
    have hpos1 : (0 : ℝ) < (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N := by positivity
    calc markedSheetCore P N hpm x y s
        ≤ 11 ^ (q + m2) * Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 + ε) +
            c2 * N * m) := hcore
      _ ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) :=
          mul_le_mul_of_nonneg_right h11 (Real.exp_pos _).le
      _ ≤ 5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) := by
          rw [← hnR, mul_assoc (5 ^ m : ℝ)]
          exact le_mul_of_one_le_left (mul_nonneg hpos1.le (Real.exp_pos _).le) h5
  · -- non-class branch
    have hb := hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase
      (fun _ _ _ _ => hc)
    rw [markedSheetProduct_eq_factor_mul_core] at hb
    have hf : (1 : ℝ) ≤ (∏ i, (1 + s i)) ^ m := by
      apply one_le_pow₀
      calc (1 : ℝ) = ∏ _i : Fin p, (1 : ℝ) := by simp
        _ ≤ ∏ i, (1 + s i) :=
          by gcongr with i _; linarith [(hs i).1]
    have hcnn : 0 ≤ markedSheetCore P N hpm x y s := by
      unfold markedSheetCore
      dsimp only
      exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)) (Finset.prod_nonneg fun j _ => abs_nonneg _)
    exact (le_mul_of_one_le_left hcnn hf).trans hb

end SheetFixedFinal

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.norm_det_gram_le_gen
#print axioms CatalanMeasure.Signed.norm_det_gram_le_gen_full
#print axioms CatalanMeasure.Signed.abs_det_laurent_eq_marked
#print axioms CatalanMeasure.Signed.lemmaT_sum_form_marked
#print axioms CatalanMeasure.Signed.abs_det_laurent_le_marked
#print axioms CatalanMeasure.Signed.quad_apply
#print axioms CatalanMeasure.Signed.log_groupedProduct_free
#print axioms CatalanMeasure.Signed.fixed_class_core_le
#print axioms CatalanMeasure.Signed.signedSecondSheetFixed

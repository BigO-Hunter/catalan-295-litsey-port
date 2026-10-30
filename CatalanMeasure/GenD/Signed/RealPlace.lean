module

public import CatalanMeasure.GenD.Signed.PickDet
public import CatalanMeasure.GenD.Analytic.MarkedSheet
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The real-place determinant at the level of Gram matrices (A8, theorem layer)

PROOF-C Theorem C.3 is stated for the operator `L = I + T` on the model space `K_B`.  The
Lean data are the Gram matrices in the Szegő-kernel basis `k_a`: with `K = [1/(1 - x_a x_b)]`
and `F(w) = K + diag(D_-, w D_+)` (`D_± = diag(B'(x_a) x_a^e)` on the weight-1 / weight-`w`
nodes) one has `det L(w) = det F(w) / det K`.  A Gram matrix is not in an orthonormal frame, so
`abs_det_fromBlocks_le_eleven` cannot be applied verbatim.  This file proves the metric-aware form:

* `norm_det_le_of_loewner_gram`: `-rSg ≤ M ≤ rSg` gives `‖det M‖ ≤ r^n det Sg` (Cholesky of `Sg`);
* `norm_det_schur_le`: the Schur-complement form of C.3, `‖det (S₁ - 6 D)‖ ≤ (2+6τ)^n det Sg`;
* `det_gram_blocks`: `det F(w) = det(K₋₋ + D₋) · det(S₀ + w D₊)` and `det K = det K₋₋ · det Sg`;
* `schur_form_*`: the quadratic-form facts turning the Gram-level hypotheses
  (`F(1) ≥ 0`, `F(1) ≤ 2K`, `±D₊ ≤ τ K` on all vectors, which is exactly the shape delivered by
  `lemmaT_of_class`) into the Schur-complement hypotheses;
* `norm_det_gram_le`: the combined statement
  `‖det F(-5)‖ ≤ (2+6τ)^q · det(K₋₋ + D₋) / det K₋₋ · det K`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section Loewner

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `-rSg ≤ M ≤ rSg` with `Sg` positive definite gives `‖det M‖ ≤ r ^ n · det Sg`. -/
theorem norm_det_le_of_loewner_gram {Sg M : Matrix n n ℂ} (hSg : Sg.PosDef)
    (hM : M.IsHermitian) {r : ℝ}
    (h1 : ((r : ℂ) • Sg - M).PosSemidef) (h2 : ((r : ℂ) • Sg + M).PosSemidef) :
    ‖M.det‖ ≤ r ^ Fintype.card n * Sg.det.re := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSg.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hR
  have hdetSg : Sg.det = star R.det * R.det := by
    rw [hR, det_mul, det_conjTranspose]
  have hpos : 0 < Sg.det := hSg.det_pos
  have hRu : IsUnit R.det := by
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    rw [h] at hdetSg
    simp at hdetSg
    exact hpos.ne' hdetSg
  have hRu' : IsUnit R := (isUnit_iff_isUnit_det R).mpr hRu
  set Ri : Matrix n n ℂ := R⁻¹ with hRi
  have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv _ hRu
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul _ hRu
  set M' : Matrix n n ℂ := Riᴴ * M * Ri with hM'
  have hRiH : Rᴴ * Riᴴ = 1 := by rw [← conjTranspose_mul, hRiR]; simp
  have hRRiH : Riᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRRi]; simp
  have hM'h : M'.IsHermitian := by
    show M'ᴴ = M'
    simp [hM', conjTranspose_mul, hM.eq, Matrix.mul_assoc]
  have hSg1 : Riᴴ * Sg * Ri = 1 := by
    rw [hR]
    calc Riᴴ * (Rᴴ * R) * Ri = (Riᴴ * Rᴴ) * (R * Ri) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hRRiH, hRRi, Matrix.one_mul]
  have e1 : (r : ℂ) • (1 : Matrix n n ℂ) - M' = Riᴴ * ((r : ℂ) • Sg - M) * Ri := by
    simp only [hM', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hSg1]
  have e2 : (r : ℂ) • (1 : Matrix n n ℂ) + M' = Riᴴ * ((r : ℂ) • Sg + M) * Ri := by
    simp only [hM', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hSg1]
  have hb := CatalanMeasure.GenD.Signed.norm_det_le_of_loewner hM'h
    (by rw [e1]; exact h1.conjTranspose_mul_mul_same Ri)
    (by rw [e2]; exact h2.conjTranspose_mul_mul_same Ri)
  have hMeq : M = Rᴴ * M' * R := by
    have : Rᴴ * M' * R = (Rᴴ * Riᴴ) * M * (Ri * R) := by
      simp only [hM', Matrix.mul_assoc]
    rw [this, hRiH, hRiR]; simp
  have hnorm : ‖M.det‖ = ‖M'.det‖ * Sg.det.re := by
    have hSgre : Sg.det.re = ‖R.det‖ ^ 2 := by
      rw [hdetSg]
      have : star R.det * R.det = ((Complex.normSq R.det : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]; rfl
      rw [this, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hSgre]
    conv_lhs => rw [hMeq]
    rw [det_mul, det_mul, det_conjTranspose, norm_mul, norm_mul, norm_star]
    ring
  have hre : 0 ≤ Sg.det.re := (Complex.lt_def.mp hpos).1.le
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right hb hre

end Loewner

section SchurLevel

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Theorem C.3 in the metric of the Gram matrix `Sg` (Schur complement of the Cauchy matrix on
the weight-`w` nodes): `0 ≤ S₁ ≤ 2 Sg`, `-τ Sg ≤ D ≤ τ Sg` give `‖det (S₁ - 6 D)‖ ≤ (2+6τ)^n det Sg`. -/
theorem norm_det_schur_le {Sg S1 Dp : Matrix n n ℂ} (hSg : Sg.PosDef)
    (hS1 : S1.PosSemidef) (hDp : Dp.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ)
    (hb : ((2 : ℂ) • Sg - S1).PosSemidef)
    (hc1 : ((τ : ℂ) • Sg - Dp).PosSemidef) (hc2 : ((τ : ℂ) • Sg + Dp).PosSemidef) :
    ‖(S1 - (6 : ℂ) • Dp).det‖ ≤ (2 + 6 * τ) ^ Fintype.card n * Sg.det.re := by
  have hτc : (0 : ℂ) ≤ (τ : ℂ) := Complex.zero_le_real.mpr hτ
  have h6 : (0 : ℂ) ≤ 6 := by norm_num
  have hM : (S1 - (6 : ℂ) • Dp).IsHermitian := hS1.1.sub (hDp.smul (by
    rw [IsSelfAdjoint, Complex.star_def]; simp [Complex.conj_ofNat]))
  refine norm_det_le_of_loewner_gram hSg hM ?_ ?_
  · have : (((2 + 6 * τ : ℝ) : ℂ)) • Sg - (S1 - (6 : ℂ) • Dp) =
        ((2 : ℂ) • Sg - S1) + (6 : ℂ) • ((τ : ℂ) • Sg + Dp) := by
      push_cast; module
    rw [this]; exact hb.add (hc2.smul h6)
  · have : (((2 + 6 * τ : ℝ) : ℂ)) • Sg + (S1 - (6 : ℂ) • Dp) =
        ((2 : ℂ) • Sg + S1) + (6 : ℂ) • ((τ : ℂ) • Sg - Dp) := by
      push_cast; module
    rw [this]
    exact ((hSg.posSemidef.smul (by norm_num : (0 : ℂ) ≤ 2)).add hS1).add (hc1.smul h6)

end SchurLevel

section GramBlocks

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The quadratic form of a Hermitian block matrix dominates the Schur-complement form, with
equality on the minimiser (Mathlib's `schur_complement_eq₁₁`). -/
theorem schur_form_ge {X11 : Matrix m m ℂ} (hX : X11.PosDef) [Invertible X11]
    (X12 : Matrix m n ℂ) (X22 : Matrix n n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star y ⬝ᵥ ((X22 - X12ᴴ * X11⁻¹ * X12) *ᵥ y) ≤
      star (x ⊕ᵥ y) ⬝ᵥ ((fromBlocks X11 X12 X12ᴴ X22) *ᵥ (x ⊕ᵥ y)) := by
  have h := schur_complement_eq₁₁ X12 X22 x y hX.1
  simp only [← dotProduct_mulVec] at h
  rw [h]
  exact le_add_of_nonneg_left (hX.posSemidef.dotProduct_mulVec_nonneg _)

theorem schur_form_eq {X11 : Matrix m m ℂ} (hX : X11.IsHermitian) [Invertible X11]
    (X12 : Matrix m n ℂ) (X22 : Matrix n n ℂ) (y : n → ℂ) :
    star ((-((X11⁻¹ * X12) *ᵥ y)) ⊕ᵥ y) ⬝ᵥ ((fromBlocks X11 X12 X12ᴴ X22) *ᵥ
        ((-((X11⁻¹ * X12) *ᵥ y)) ⊕ᵥ y)) =
      star y ⬝ᵥ ((X22 - X12ᴴ * X11⁻¹ * X12) *ᵥ y) := by
  have h := schur_complement_eq₁₁ X12 X22 (-((X11⁻¹ * X12) *ᵥ y)) y hX
  simp only [← dotProduct_mulVec] at h
  rw [h]
  simp

end GramBlocks

section GramMain

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem norm_eq_re_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  have h := Complex.lt_def.mp hz
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using h.2.symm)
  rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h.1)]
  simp

theorem re_mul_of_pos {a b : ℂ} (ha : 0 < a) (hb : 0 < b) : (a * b).re = a.re * b.re := by
  have h1 := (Complex.lt_def.mp ha).2
  have h2 := (Complex.lt_def.mp hb).2
  rw [Complex.mul_re, ← h1, ← h2]; simp

theorem form_blockDp (Dp : Matrix n n ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (x ⊕ᵥ y) ⬝ᵥ ((fromBlocks (0 : Matrix m m ℂ) (0 : Matrix m n ℂ) (0 : Matrix n m ℂ) Dp) *ᵥ
      (x ⊕ᵥ y)) = star y ⬝ᵥ (Dp *ᵥ y) := by
  simp [fromBlocks_mulVec, Function.star_sumElim]

/-- **The Gram-level form of Theorem C.3 with `b = 2`, `c = 6`** (`F(-5)` against the Cauchy
matrix `K`).  With `K = [[K₁₁, K₁₂], [K₁₂ᴴ, K₂₂]]` positive definite (weight-1 nodes first),
`F(w) = K + diag(D_-, w D_+)`:
* `F(1) ≥ 0` (`h1`), `F(1) ≤ 2K` (`h2`), `K₁₁ + D_-` positive definite (`hA`);
* `-τ K ≤ (0 ⊕ D_+) ≤ τ K` on all vectors (`h3`, `h4`), the shape given by `lemmaT_of_class`.
Then `‖det F(-5)‖ · det K₁₁ ≤ (2+6τ)^q · det(K₁₁ + D_-) · det K`, i.e.
`|det L| ≤ (2+6τ)^q det L₋₋`, `det L = det F / det K`, `det L₋₋ = det(K₁₁+D_-)/det K₁₁`. -/
theorem norm_det_gram_le {K11 : Matrix m m ℂ} {K12 : Matrix m n ℂ} {K22 Dm Dp : Matrix _ _ ℂ}
    (hK : (fromBlocks K11 K12 K12ᴴ K22).PosDef) (hA : (K11 + Dm).PosDef)
    (hDp : Dp.IsHermitian)
    (h1 : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 + Dp)).PosSemidef)
    (h2 : (fromBlocks K11 K12 K12ᴴ K22 - fromBlocks Dm 0 0 Dp).PosSemidef)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (h3 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 - fromBlocks 0 0 0 Dp).PosSemidef)
    (h4 : ((τ : ℂ) • fromBlocks K11 K12 K12ᴴ K22 + fromBlocks 0 0 0 Dp).PosSemidef) :
    ‖(fromBlocks (K11 + Dm) K12 K12ᴴ (K22 - (5 : ℂ) • Dp)).det‖ * K11.det.re ≤
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
  have hc1 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) - Dp).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).sub hDp
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h3.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul]
      exact e3
  have hc2 : ((τ : ℂ) • (K22 - K12ᴴ * K11⁻¹ * K12) + Dp).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · exact (hSgH.smul (by rw [IsSelfAdjoint, Complex.star_def]; simp)).add hDp
    · have e1 := schur_form_eq hK11.1 K12 K22 y
      have e3 := h4.dotProduct_mulVec_nonneg ((-((K11⁻¹ * K12) *ᵥ y)) ⊕ᵥ y)
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, form_blockDp, e1] at e3
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul]
      exact e3
  have hmain := norm_det_schur_le hSgpos hS1 hDp hτ hb hc1 hc2
  -- determinants
  have hdF : (fromBlocks (K11 + Dm) K12 K12ᴴ (K22 - (5 : ℂ) • Dp)).det =
      (K11 + Dm).det * (K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dp).det := by
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
  calc (K11 + Dm).det.re * ‖(K22 + Dp - K12ᴴ * (K11 + Dm)⁻¹ * K12 - (6 : ℂ) • Dp).det‖ *
        K11.det.re
      ≤ (K11 + Dm).det.re * ((2 + 6 * τ) ^ Fintype.card n *
          (K22 - K12ᴴ * K11⁻¹ * K12).det.re) * K11.det.re := by
        gcongr
    _ = _ := by ring

end GramMain

section Consumer

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric OAI.InternalCatalan Filter Set

/-- The sheet product **without** the factor `(∏ (1 + s_i))^m` (PROOF-RHO §2.5, §5):
`|det markedLaurentMatrix| · ∏ paramRowNodeWeight(y_j) · paramPinPrincipal / ∏ |rowCommonFactor(y_j)|`. -/
def markedSheetCore (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ := fun i => Fin.append x y (Fin.cast hpm.symm i)
  let marked : Fin (P.n N) → Bool := fun i =>
    Fin.addCases (fun _ => false) (fun _ => true) (Fin.cast hpm.symm i)
  |(markedLaurentMatrix (P.g N) z marked).det| *
    (∏ j, paramRowNodeWeight P N (y j)) * paramPinPrincipal P N x s /
      ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|

/-- `markedSheetProduct` is the removed factor times the core. -/
theorem markedSheetProduct_eq_factor_mul_core (P : Parameters) (N : ℕ) {p m : ℕ}
    (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    markedSheetProduct P N hpm x y s = (∏ i, (1 + s i)) ^ m * markedSheetCore P N hpm x y s := by
  unfold markedSheetProduct markedSheetCore
  simp only
  ring

/-- **Statement of the signed second-case sheet bound, factor-free form (the A9 statement).**
Same hypotheses as `SignedSecondSheet` (PHASE0 §2.3) but for `markedSheetCore`, with the cost per
marked row and unit `N` a parameter `c2` (PROOF-RHO: `58 c₂''`) instead of a hard-coded constant.
The prefactor `5^m (1 + 10 e^12 n)^n` is `exp(o(N²))` for `m ≤ n`. -/
def SignedSecondSheetCore (P : Parameters) (G : ℝ → Prop) (target0 c2 alpha1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (m : ℝ) ≤ alpha1 * (P.n N : ℝ) →
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m)

end Consumer

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.norm_det_le_of_loewner_gram
#print axioms CatalanMeasure.Signed.norm_det_schur_le
#print axioms CatalanMeasure.Signed.norm_det_gram_le
#print axioms CatalanMeasure.Signed.markedSheetProduct_eq_factor_mul_core

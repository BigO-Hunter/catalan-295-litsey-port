module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block

@[expose] public section

set_option Elab.async false

/-! # Mixed-fibre response identities for the wrapped UF layer

A balanced residue has an extra row and an extra column at different nodes.
These identities justify the response cancellations without treating that
nonsymmetric fibre as an ordinary common-node extension.
-/

namespace CatalanCore.Uniform.Content.UFSimple.WrapAlgebra

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Replacing one column and the corresponding load preserves the bilinear
response. No symmetry of either matrix is assumed. -/
theorem updateCol_response_mixed (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (uR uC v : ι → R) (h : ι)
    (hM : IsUnit (Q.updateCol h v).det) :
    Function.update uC h ((uC ᵥ* Q⁻¹) ⬝ᵥ v) ⬝ᵥ
        (Q.updateCol h v)⁻¹ *ᵥ uR = uC ⬝ᵥ Q⁻¹ *ᵥ uR := by
  have hu : (uC ᵥ* Q⁻¹) ᵥ* Q = uC := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul Q hQ, Matrix.vecMul_one]
  have hrow : Function.update uC h ((uC ᵥ* Q⁻¹) ⬝ᵥ v) =
      (uC ᵥ* Q⁻¹) ᵥ* Q.updateCol h v := by
    ext j
    by_cases hj : j = h
    · subst j
      simp only [Function.update_self, Matrix.vecMul, Matrix.updateCol_self,
        dotProduct]
    · rw [Function.update_of_ne hj]
      have he := congrFun hu j
      simpa only [Matrix.vecMul, Matrix.updateCol_ne hj] using he.symm
  rw [hrow, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one, ← Matrix.dotProduct_mulVec]

/-- Equal-load specialization of the mixed column replacement response. -/
theorem updateCol_response (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (u v : ι → R) (h : ι)
    (hM : IsUnit (Q.updateCol h v).det) :
    Function.update u h ((u ᵥ* Q⁻¹) ⬝ᵥ v) ⬝ᵥ
        (Q.updateCol h v)⁻¹ *ᵥ u = u ⬝ᵥ Q⁻¹ *ᵥ u :=
  updateCol_response_mixed Q hQ u u v h hM

/-- A mixed border with one own-direction load has zero added response,
regardless of its other border column and its other load. -/
theorem mixedBorder_response_mixed (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (uR uC sX sY : ι → R) (h zX zY : R)
    (hzX : sX ⬝ᵥ Q⁻¹ *ᵥ uR = zX)
    (hM : IsUnit (Matrix.fromBlocks Q (Matrix.of fun i (_ : Unit) => sY i)
      (Matrix.of fun (_ : Unit) j => sX j) (Matrix.of fun (_ _ : Unit) => h)).det) :
    Sum.elim uC (fun (_ : Unit) => zY) ⬝ᵥ
      (Matrix.fromBlocks Q (Matrix.of fun i (_ : Unit) => sY i)
        (Matrix.of fun (_ : Unit) j => sX j) (Matrix.of fun (_ _ : Unit) => h))⁻¹ *ᵥ
      Sum.elim uR (fun (_ : Unit) => zX) = uC ⬝ᵥ Q⁻¹ *ᵥ uR := by
  let M := Matrix.fromBlocks Q (Matrix.of fun i (_ : Unit) => sY i)
    (Matrix.of fun (_ : Unit) j => sX j) (Matrix.of fun (_ _ : Unit) => h)
  let y := Sum.elim (Q⁻¹ *ᵥ uR) (fun (_ : Unit) => (0 : R))
  have hsolve : M *ᵥ y = Sum.elim uR (fun (_ : Unit) => zX) := by
    rw [show M = Matrix.fromBlocks Q (Matrix.of fun i (_ : Unit) => sY i)
      (Matrix.of fun (_ : Unit) j => sX j) (Matrix.of fun (_ _ : Unit) => h) from rfl,
      Matrix.fromBlocks_mulVec]
    ext i
    cases i with
    | inl i =>
      change (∑ j, Q i j * (Q⁻¹ *ᵥ uR) j) +
        (∑ _j : Unit, sY i * 0) = uR i
      simp only [mul_zero, Finset.sum_const_zero, add_zero]
      exact congrFun (by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec] : Q *ᵥ Q⁻¹ *ᵥ uR = uR) i
    | inr i =>
      change (∑ j, sX j * (Q⁻¹ *ᵥ uR) j) +
        (∑ _j : Unit, h * 0) = zX
      simp only [mul_zero, Finset.sum_const_zero, add_zero]
      exact hzX
  have hinv : M⁻¹ *ᵥ Sum.elim uR (fun (_ : Unit) => zX) = y := by
    rw [← hsolve, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM,
      Matrix.one_mulVec]
  change Sum.elim uC (fun (_ : Unit) => zY) ⬝ᵥ
    M⁻¹ *ᵥ Sum.elim uR (fun (_ : Unit) => zX) = _
  rw [hinv]
  simp only [y, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]

/-- A cleared numerator bound survives any specialization whose ORIGINAL
clearing denominator becomes a unit. Elimination pivots are not denominators
in this statement and may specialize to zero. -/
theorem specialize_cleared {A B : Type*} [CommRing A] [CommRing B]
    (phi : A →+* B) (c D f : A) (h : c ∣ D * f) (hD : IsUnit (phi D)) :
    phi c ∣ phi f := by
  apply hD.dvd_mul_left.mp
  obtain ⟨a, ha⟩ := h
  refine ⟨phi a, ?_⟩
  simpa only [map_mul] using congrArg phi ha

end CatalanCore.Uniform.Content.UFSimple.WrapAlgebra




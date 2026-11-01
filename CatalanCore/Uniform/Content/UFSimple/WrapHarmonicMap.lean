module

public import CatalanCore.Uniform.Content.UFSimple.WrapHarmonic

@[expose] public section

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapHarmonicMap

variable {F K : Type*} [Field F] [Field K]

theorem load (f : F →+* K) (a : F) (epsilon : Bool) (j : ℕ) :
    f (WrapHarmonic.load a epsilon j)=WrapHarmonic.load (f a) epsilon j := by
  unfold WrapHarmonic.load
  simp only [map_sub,map_sum,map_div₀,map_one,map_add,map_natCast]

theorem testShift (f : F →+* K) (b : ℕ) (epsilon : Bool) :
    f (WrapHarmonic.testShift b epsilon)=WrapHarmonic.testShift b epsilon := by
  cases epsilon <;> simp [WrapHarmonic.testShift]

theorem entry (f : F →+* K) (b x y : ℕ) (epsilon : Bool) :
    f (WrapHarmonic.entry (K:=F) b epsilon x y)=WrapHarmonic.entry (K:=K) b epsilon x y := by
  unfold WrapHarmonic.entry
  simp only [map_div₀,map_sub,load,testShift,map_natCast]

theorem matrix (f : F →+* K) (b : ℕ) (epsilon : Bool) (x y : Fin b → ℕ) :
    (WrapHarmonic.matrix (K:=F) b epsilon x y).map f=
      WrapHarmonic.matrix (K:=K) b epsilon x y := by
  apply Matrix.ext; intro i j
  exact entry f b (x i) (y j) epsilon

theorem inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : F →+* K) (Q : Matrix ι ι F) (hQ : IsUnit Q.det) :
    (Q.map f)⁻¹=(Q⁻¹).map f := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul,Matrix.nonsing_inv_mul Q hQ,Matrix.map_one _ f.map_zero f.map_one]

theorem reference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : F →+* K) (Q : Matrix ι ι F) (hQ : IsUnit Q.det) (sigma : ι → F) :
    f (1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1))=
      1-(fun i => f (sigma i)) ⬝ᵥ ((Q.map f)⁻¹ *ᵥ 1) := by
  rw [inverse f Q hQ]
  simp only [dotProduct,Matrix.mulVec,Matrix.map_apply,Pi.one_apply,mul_one,
    map_sub,map_one,map_sum,map_mul]

end CatalanCore.Uniform.Content.UFSimple.WrapHarmonicMap

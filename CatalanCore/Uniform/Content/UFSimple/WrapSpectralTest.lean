module

public import CatalanCore.Uniform.Content.UFSimple.WrapArrow
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

open Polynomial Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapSpectralTest

variable {K ι κ : Type*} [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A mixed spectral test is nonzero in the actual coefficient rational
function field whenever its constant balanced block is nonsingular. -/
theorem mixed_det_ne (A : Matrix ι ι K) (B : Matrix ι κ K)
    (E : Matrix κ ι K) (D : Matrix κ κ K) (hD : D.det≠0) :
    (Matrix.fromBlocks ((RatFunc.X:RatFunc K) • (1:Matrix ι ι (RatFunc K))+A.map RatFunc.C)
      (B.map RatFunc.C) (E.map RatFunc.C) (D.map RatFunc.C)).det≠0 := by
  let f := algebraMap K[X] (RatFunc K)
  let M := Matrix.fromBlocks ((X:K[X]) • (1:Matrix ι ι K[X])+A.map C)
    (B.map C) (E.map C) (D.map C)
  have hM : M.det≠0 := WrapPivot.mixed_det_ne_zero A B E D hD
  have hm : M.map f=Matrix.fromBlocks
      ((RatFunc.X:RatFunc K) • (1:Matrix ι ι (RatFunc K))+A.map RatFunc.C)
      (B.map RatFunc.C) (E.map RatFunc.C) (D.map RatFunc.C) := by
    apply Matrix.ext; intro i j
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j <;>
        simp [M,f,Matrix.one_apply,hij,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
    · simp [M,f,RatFunc.algebraMap_C]
    · simp [M,f,RatFunc.algebraMap_C]
    · simp [M,f,RatFunc.algebraMap_C]
  rw [← hm]
  change (f.mapMatrix M).det≠0
  rw [← RingHom.map_det]
  intro hz
  apply hM
  apply IsFractionRing.injective K[X] (RatFunc K)
  simpa only [map_zero] using hz

/-- The cleared balanced reference makes the whole mixed spectral arrow
nonzero, with arbitrary independent common-to-balanced couplings. -/
theorem arrow_det_ne (A : Matrix ι ι K) (B : Matrix ι (κ ⊕ Unit) K)
    (E : Matrix (κ ⊕ Unit) ι K) (D : Matrix κ κ K) (sigma : κ → K)
    (hD : D.det≠0) (href : 1-sigma ⬝ᵥ (D⁻¹ *ᵥ 1)≠0) :
    (Matrix.fromBlocks ((RatFunc.X:RatFunc K) • (1:Matrix ι ι (RatFunc K))+A.map RatFunc.C)
      (B.map RatFunc.C) (E.map RatFunc.C) ((WrapArrow.arrow D sigma).map RatFunc.C)).det≠0 :=
  mixed_det_ne A B E _ (WrapArrow.det_arrow_ne D hD sigma href)

end CatalanCore.Uniform.Content.UFSimple.WrapSpectralTest

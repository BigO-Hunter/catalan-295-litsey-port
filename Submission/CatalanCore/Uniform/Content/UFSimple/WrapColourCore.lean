module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapEntryRelation
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapColourCore

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Reuse the existing block-triangular determinant product to assemble
nonzero own-colour blocks. Colours are their original finite values. -/
theorem det_ne (Q : Matrix ι ι K) (col : ι → ℕ)
    (hzero : ∀ i j,col i≠col j → Q i j=0)
    (hown : ∀ c∈univ.image col,(Q.toSquareBlock col c).det≠0) : Q.det≠0 := by
  classical
  have ht : Matrix.BlockTriangular Q col := by
    intro i j hij
    exact hzero i j (ne_of_gt hij)
  rw [ht.det]
  exact Finset.prod_ne_zero_iff.mpr hown

variable {R : Type*} [CommRing R]

theorem mapped_det_ne (phi : R →+* K) (Q : Matrix ι ι R) (col : ι → ℕ)
    (hzero : ∀ i j,col i≠col j → phi (Q i j)=0)
    (hown : ∀ c∈univ.image col,phi (Q.toSquareBlock col c).det≠0) : phi Q.det≠0 := by
  rw [RingHom.map_det]
  change (Q.map phi).det≠0
  apply det_ne _ col hzero
  intro c hc
  change ((Q.toSquareBlock col c).map phi).det≠0
  change (phi.mapMatrix (Q.toSquareBlock col c)).det≠0
  rw [← RingHom.map_det]
  exact hown c hc

/-- Own-colour unit blocks give the global core unit in any of the
original or generic residue-local rings. -/
theorem unit (phi : R →+* K) (hunit : ∀ a,phi a≠0 → IsUnit a)
    (Q : Matrix ι ι R) (col : ι → ℕ)
    (hzero : ∀ i j,col i≠col j → phi (Q i j)=0)
    (hown : ∀ c∈univ.image col,IsUnit (Q.toSquareBlock col c).det) : IsUnit Q.det := by
  apply hunit
  apply mapped_det_ne phi Q col hzero
  intro c hc
  exact ((hown c hc).map phi).ne_zero

/-- Actual different-colour entries vanish in the generic residue,
by their exact original-node displacement. -/
theorem entry_zero (p : ℕ) [Fact p.Prime] (q o N : ℕ) (u : GaussLoc p)
    (hN : N<p*p) (a b : ℕ) (ha : a<N) (hb : b<N)
    (hcol : (a:ZMod p)≠(b:ZMod p)) :
    WrapDeform.residue p (WrapDeformedEntry.entry p q o u a b)=0 := by
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hh := congrArg (WrapDeform.residue p) (WrapEntryRelation.commutator p q o N u hN a b ha hb)
  simp only [map_mul,map_sub,map_natCast,hpi,zero_mul] at hh
  have hden : (b:RatFunc (RatFunc (ZMod p)))-(a:RatFunc (RatFunc (ZMod p)))≠0 := by
    apply sub_ne_zero.mpr
    intro he
    apply hcol
    have hinj := (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).injective.comp
      (RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
    apply hinj
    simpa only [Function.comp_apply,map_natCast] using he.symm
  exact (mul_eq_zero.mp hh).resolve_left hden

end CatalanCore.Uniform.Content.UFSimple.WrapColourCore

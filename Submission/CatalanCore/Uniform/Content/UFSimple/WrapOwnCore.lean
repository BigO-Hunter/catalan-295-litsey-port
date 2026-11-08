module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapBalancedResidue
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapConstantMatrix
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapEntryConstant

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnCore

noncomputable def constants (p : ℕ) [Fact p.Prime] := (WrapDeform.embed p).comp
  (Polynomial.C:GaussLoc p →+* (GaussLoc p)[X])

variable {p : ℕ} [Fact p.Prime] {q o k j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
variable (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual common nodes and independently indexed balanced nodes of one
colour. The common block alone retains the original spectral diagonal. -/
noncomputable def actual (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y) (s u : GaussLoc p) (c : ι → ℕ) :
    Matrix (ι ⊕ Fin b) (ι ⊕ Fin b) (WrapDeform.Extension p) :=
  let f := fun a d => WrapDeformedEntry.entry p q o u (gamma+a*p) (gamma+d*p)
  Matrix.fromBlocks (constants p s • (1:Matrix ι ι (WrapDeform.Extension p))+
    Matrix.of (fun i j => f (c i) (c j)))
    (Matrix.of (fun i j => f (c i) (y j)))
    (Matrix.of (fun i j => f (x i) (c j)))
    (Matrix.of (fun i j => f (x i) (y j)))

noncomputable def test (s u : GaussLoc p) (c : ι → ℕ) :
    Matrix (ι ⊕ Fin b) (ι ⊕ Fin b) (GaussLoc p) :=
  let f := fun a d => WrapEntryTest.value p q o H.point u (gamma+a*p) (gamma+d*p)
  Matrix.fromBlocks (s • (1:Matrix ι ι (GaussLoc p))+
    Matrix.of (fun i j => f (c i) (c j)))
    (Matrix.of (fun i j => f (c i) (y j)))
    (Matrix.of (fun i j => f (x i) (c j)))
    (Matrix.of (fun i j => f (x i) (y j)))

include H

/-- Elementary test relations for every actual mixed own-core entry. -/
theorem entry_at (s u : GaussLoc p) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J) :
    ∀ i j,WrapPoleTest.At p H.point (actual H s u c i j) (test H s u c i j) := by
  classical
  have he (a d : ℕ) (ha : a≤J) (hd : d≤J) :
      WrapPoleTest.At p H.point (WrapDeformedEntry.entry p q o u (gamma+a*p) (gamma+d*p))
        (WrapEntryTest.value p q o H.point u (gamma+a*p) (gamma+d*p)) :=
    WrapOwnTest.entry_at p q o k j0 gamma J m N b H.hq0 H.hqp H.hq2 H.hoq H.hk0 H.hk
      H.hg H.hroot H.hsize H.hN hJ H.hb H.hb0 u _ _
      (by have := Nat.mul_le_mul_right p ha; omega) (by have := Nat.mul_le_mul_right p hd; omega)
  have hspec (i j : ι) : WrapPoleTest.At p H.point
      ((constants p s • (1:Matrix ι ι (WrapDeform.Extension p))) i j)
      ((s • (1:Matrix ι ι (GaussLoc p))) i j) := by
    by_cases hij : i=j
    · simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij,↓reduceIte,mul_one]
      exact WrapEvaluation.Rel.constant s
    · simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,hij,↓reduceIte,mul_zero]
      exact ⟨0,1,by simp,by simp,by simp⟩
  have hentry : ∀ i j,WrapPoleTest.At p H.point (actual H s u c i j) (test H s u c i j) := by
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · change WrapPoleTest.At p H.point
        (((constants p s • (1:Matrix ι ι (WrapDeform.Extension p))) i j)+
          WrapDeformedEntry.entry p q o u (gamma+c i*p) (gamma+c j*p))
        (((s • (1:Matrix ι ι (GaussLoc p))) i j)+
          WrapEntryTest.value p q o H.point u (gamma+c i*p) (gamma+c j*p))
      exact WrapEvaluation.Rel.add (hspec i j) (he _ _ (hc i) (hc j))
    · exact he _ _ (hc i) (hyJ j)
    · exact he _ _ (hxJ i) (hc j)
    · exact he _ _ (hxJ i) (hyJ j)
  exact hentry

/-- The actual whole own-core test determinant has nonzero residue. -/
theorem test_det_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J) : res p (test H s u c).det≠0 := by
  classical
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hlocal : gamma+J*p+1<p*p := by omega
  have hpole : ∀ t,1≤t → t<gamma+J*p+1 → ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*H.point) := by
    intro t ht1 ht hz
    exact WrapOwnTest.pole_unit_before p q o k j0 gamma J m N b t H.hq0 H.hqp H.hq2 H.hoq
      H.hk0 H.hk H.hg H.hroot H.hsize H.hN hJ H.hb H.hb0 ht1 (by omega) hz
  have hpnt : WrapConstant.Has p H.point :=
    WrapConstant.point p q j0 b (if k≤gamma then 1 else 0) (WrapSimplePole.q_res_ne p q H.hq0 H.hqp)
  have hnode (a : ℕ) (ha : a≤J) : gamma+a*p<gamma+J*p+1 := by
    have := Nat.mul_le_mul_right p ha
    omega
  have hec (a d : ℕ) (ha : a≤J) (hd : d≤J) :
      WrapConstant.Has p (WrapEntryTest.value p q o H.point u (gamma+a*p) (gamma+d*p)) :=
    WrapEntryConstant.entry p q o (gamma+J*p+1) H.point u hpnt huc H.hoq hlocal hpole
      _ _ (hnode a ha) (hnode d hd)
  have htest : res p (test H s u c).det≠0 := by
    unfold test
    apply WrapConstantMatrix.original_test_ne p _ _ _ _ s hs
    · intro i j; exact hec _ _ (hc i) (hc j)
    · intro i j; exact hec _ _ (hc i) (hyJ j)
    · intro i j; exact hec _ _ (hxJ i) (hc j)
    · intro i j; exact hec _ _ (hxJ i) (hyJ j)
    · exact H.det_ne u hu
  exact htest

/-- Actual deformed own cores, including every retained common node,
are units under original arithmetic and original-node bounds alone. -/
theorem unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J) : IsUnit (actual H s u c).det := by
  have htest := test_det_ne H s u hs hu huc c J hJ hc hxJ hyJ
  have hentry := entry_at H s u c J hJ hc hxJ hyJ
  have hd := WrapBalancedTest.det_relation p H.point (actual H s u c) (test H s u c) hentry
  have hgeneric := WrapBalancedTest.transfer p (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p) hd htest
  exact WrapBalancedTest.unit_ne p (actual H s u c).det hgeneric

end CatalanCore.Uniform.Content.UFSimple.WrapOwnCore

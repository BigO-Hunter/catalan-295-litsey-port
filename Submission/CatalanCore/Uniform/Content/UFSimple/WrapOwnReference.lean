module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapOwnCore
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapArrowCore

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnReference

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

theorem map_arrow (f : R →+* S) (Q : Matrix ι ι R) (sigma : ι → R) :
    (WrapArrowCore.arrow Q sigma).map f=
      WrapArrowCore.arrow (Q.map f) (fun i => f (sigma i)) := by
  apply Matrix.ext; intro i j
  rcases i with i|i <;> rcases j with j|j
  · rfl
  · simp [WrapArrowCore.arrow]
  · rfl
  · cases i; cases j; simp [WrapArrowCore.arrow]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The full original test arrow, including its arbitrary common-node
couplings, has nonzero residue from the balanced reference. -/
theorem original_test_ne (p : ℕ) [Fact p.Prime]
    (A : Matrix ι ι (GaussLoc p)) (B : Matrix ι κ (GaussLoc p))
    (E : Matrix κ ι (GaussLoc p)) (D : Matrix κ κ (GaussLoc p))
    (sigmaC : ι → GaussLoc p) (sigmaB : κ → GaussLoc p)
    (s : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hA : ∀ i j,WrapConstant.Has p (A i j))
    (hB : ∀ i j,WrapConstant.Has p (B i j))
    (hE : ∀ i j,WrapConstant.Has p (E i j))
    (hDc : ∀ i j,WrapConstant.Has p (D i j))
    (hSC : ∀ i,WrapConstant.Has p (sigmaC i))
    (hSB : ∀ i,WrapConstant.Has p (sigmaB i))
    (hD : res p D.det≠0)
    (href : 1-(fun i => res p (sigmaB i)) ⬝ᵥ (((D.map (res p))⁻¹) *ᵥ 1)≠0) :
    res p (WrapArrowCore.arrow
      (Matrix.fromBlocks (s • (1:Matrix ι ι (GaussLoc p))+A) B E D)
      (Sum.elim sigmaC sigmaB)).det≠0 := by
  classical
  let Q := Matrix.fromBlocks (s • (1:Matrix ι ι (GaussLoc p))+A) B E D
  have hm : Q.map (res p)=Matrix.fromBlocks
      ((RatFunc.X:RatFunc (ZMod p)) • (1:Matrix ι ι (RatFunc (ZMod p)))+A.map (res p))
      (B.map (res p)) (E.map (res p)) (D.map (res p)) := by
    apply Matrix.ext; intro i j
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j <;> simp [Q,Matrix.one_apply,hij,map_add,map_mul,hs]
    · simp [Q]
    · simp [Q]
    · simp [Q]
  have hsig : (fun i => res p (Sum.elim sigmaC sigmaB i))=
      Sum.elim (fun i => res p (sigmaC i)) (fun i => res p (sigmaB i)) := by
    funext i; cases i <;> rfl
  rw [RingHom.map_det (R:=GaussLoc p) (S:=RatFunc (ZMod p))]
  change ((WrapArrowCore.arrow Q (Sum.elim sigmaC sigmaB)).map (res p)).det≠0
  rw [map_arrow,hm,hsig]
  apply WrapArrowCore.spectral_ne
  · intro i j; exact hA i j
  · intro i j; exact hB i j
  · intro i j; exact hE i j
  · intro i j; exact hDc i j
  · intro i; exact hSC i
  · intro i; exact hSB i
  · change ((res p).mapMatrix D).det≠0
    rw [← RingHom.map_det (R:=GaussLoc p) (S:=RatFunc (ZMod p))]
    exact hD
  · exact href

variable {p : ℕ} [Fact p.Prime] {q o k j0 gamma m N b : ℕ} {x y : Fin b → ℕ}
variable (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y)

noncomputable def sigma (H : WrapBalancedResidue.Hyp p q o k j0 gamma m N b x y) (u : GaussLoc p) (c : ι → ℕ) (t : ℕ) : ι ⊕ Fin b → WrapDeform.Extension p :=
  Sum.elim (fun i => WrapDeformedEntry.entry p q o u (gamma+t*p) (gamma+c i*p))
    (fun j => WrapDeformedEntry.entry p q o u (gamma+t*p) (gamma+y j*p))

noncomputable def testSigma (u : GaussLoc p) (c : ι → ℕ) (t : ℕ) : ι ⊕ Fin b → GaussLoc p :=
  Sum.elim (fun i => WrapEntryTest.value p q o H.point u (gamma+t*p) (gamma+c i*p))
    (fun j => WrapEntryTest.value p q o H.point u (gamma+t*p) (gamma+y j*p))

include H

/-- The actual whole own-core row normalization is a unit. Its common
nodes may be any retained family; its independent balanced nodes and
virtual node satisfy only the original arithmetic geometry. -/
theorem unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (c : ι → ℕ)
    (J : ℕ) (hJ : gamma+J*p<N) (hc : ∀ i,c i≤J)
    (hxJ : ∀ i,x i≤J) (hyJ : ∀ i,y i≤J)
    (t : ℕ) (htJ : t≤J) (hxt : ∀ i,x i≠t) (hyt : ∀ j,y j≠t) :
    IsUnit (1-sigma H u c t ⬝ᵥ ((WrapOwnCore.actual H s u c)⁻¹ *ᵥ 1)) := by
  classical
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hlocal : gamma+J*p+1<p*p := by omega
  have hnode (a : ℕ) (ha : a≤J) : gamma+a*p<gamma+J*p+1 := by
    have := Nat.mul_le_mul_right p ha
    omega
  have htN : gamma+t*p<N := by
    have := Nat.mul_le_mul_right p htJ
    omega
  have hpole : ∀ a,1≤a → a<gamma+J*p+1 → ∀ hz : res p (WrapIncrement.argument p q o a)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o a) hz+(q:GaussLoc p)*H.point) := by
    intro a ha1 ha hz
    exact WrapOwnTest.pole_unit_before p q o k j0 gamma J m N b a H.hq0 H.hqp H.hq2 H.hoq
      H.hk0 H.hk H.hg H.hroot H.hsize H.hN hJ H.hb H.hb0 ha1 (by omega) hz
  have hpnt : WrapConstant.Has p H.point :=
    WrapConstant.point p q j0 b (if k≤gamma then 1 else 0) (WrapSimplePole.q_res_ne p q H.hq0 H.hqp)
  have hec (a d : ℕ) (ha : a≤J) (hd : d≤J) :
      WrapConstant.Has p (WrapEntryTest.value p q o H.point u (gamma+a*p) (gamma+d*p)) :=
    WrapEntryConstant.entry p q o (gamma+J*p+1) H.point u hpnt huc H.hoq hlocal hpole
      _ _ (hnode a ha) (hnode d hd)
  have htest : res p (WrapArrowCore.arrow (WrapOwnCore.test H s u c) (testSigma H u c t)).det≠0 := by
    unfold WrapOwnCore.test testSigma
    apply original_test_ne p _ _ _ _ _ _ s hs
    · intro i j; exact hec _ _ (hc i) (hc j)
    · intro i j; exact hec _ _ (hc i) (hyJ j)
    · intro i j; exact hec _ _ (hxJ i) (hc j)
    · intro i j; exact hec _ _ (hxJ i) (hyJ j)
    · intro i; exact hec _ _ htJ (hc i)
    · intro j; exact hec _ _ htJ (hyJ j)
    · exact H.det_ne u hu
    · exact H.reference_ne u hu t htN hxt hyt
  have hsig : ∀ i,WrapPoleTest.At p H.point (sigma H u c t i) (testSigma H u c t i) := by
    intro i
    rcases i with i|i
    · exact WrapOwnTest.entry_at p q o k j0 gamma J m N b H.hq0 H.hqp H.hq2 H.hoq H.hk0 H.hk
        H.hg H.hroot H.hsize H.hN hJ H.hb H.hb0 u _ _
        (by have := Nat.mul_le_mul_right p htJ; omega) (by have := Nat.mul_le_mul_right p (hc i); omega)
    · exact WrapOwnTest.entry_at p q o k j0 gamma J m N b H.hq0 H.hqp H.hq2 H.hoq H.hk0 H.hk
        H.hg H.hroot H.hsize H.hN hJ H.hb H.hb0 u _ _
        (by have := Nat.mul_le_mul_right p htJ; omega) (by have := Nat.mul_le_mul_right p (hyJ i); omega)
  have hentries : ∀ i j,WrapPoleTest.At p H.point
      (WrapArrowCore.arrow (WrapOwnCore.actual H s u c) (sigma H u c t) i j)
      (WrapArrowCore.arrow (WrapOwnCore.test H s u c) (testSigma H u c t) i j) := by
    intro i j
    rcases i with i|i <;> rcases j with j|j
    · exact WrapOwnCore.entry_at H s u c J hJ hc hxJ hyJ i j
    · cases j
      change WrapPoleTest.At p H.point (1:WrapDeform.Extension p) (1:GaussLoc p)
      exact ⟨1,1,by simp,by simp,by simp⟩
    · exact hsig j
    · cases i; cases j
      change WrapPoleTest.At p H.point (1:WrapDeform.Extension p) (1:GaussLoc p)
      exact ⟨1,1,by simp,by simp,by simp⟩
  have hd := WrapBalancedTest.det_relation p H.point _ _ hentries
  have hgeneric := WrapBalancedTest.transfer p (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p) hd htest
  have harrow := WrapBalancedTest.unit_ne p _ hgeneric
  have hQ := WrapOwnCore.unit H s u hs hu huc c J hJ hc hxJ hyJ
  rw [WrapArrowCore.det_arrow _ hQ] at harrow
  exact isUnit_of_mul_isUnit_right harrow

end CatalanCore.Uniform.Content.UFSimple.WrapOwnReference

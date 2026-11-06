module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusMultiplicity
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Choose
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K shared R3 reserve; concrete cover/box checks unmeasured
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover
noncomputable section
open Set CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusMultiplicity
open scoped BigOperators

def rootSet (p : Polynomial Real) (s : Set Real) : Finset Real := by
  classical
  exact p.roots.toFinset.filter (fun x => x∈s)

theorem mem_rootSet (p : Polynomial Real) (s : Set Real) (x : Real) :
    x∈rootSet p s ↔ x∈p.roots ∧ x∈s := by
  classical
  simp only [rootSet,Finset.mem_filter,Multiset.mem_toFinset]

/-- Injection into positive real roots gives an upper bound on distinct interval roots.
Multiplicity preservation is proved separately in rootMultiplicity_H. -/
theorem interval_card_le_positive_roots (a b d : Real) (hab : a<b) (hd : 0<d)
    (p : Polynomial Real) (hp : p≠0) (n : Nat) (hn : p.natDegree≤n) :
    (rootSet p (Ioo (a/d) (b/d))).card≤(H a b d p n).roots.countP (0<·) := by
  classical
  let q := H a b d p n
  let target := (q.roots.filter (0<·)).toFinset
  have hq : q≠0 := H_ne_zero a b d hab hd p hp n hn
  have hm : Set.MapsTo (U a b d)
      (rootSet p (Ioo (a/d) (b/d)) : Set Real) (target : Set Real) := by
    intro x hx
    obtain ⟨hroot,hx⟩ := (mem_rootSet p _ x).mp hx
    have hu := U_pos a b d x hd hx
    have hden : d*(1+U a b d x)≠0 :=
      mul_ne_zero (ne_of_gt hd) (ne_of_gt (by linarith))
    have hz : q.eval (U a b d x)=0 := by
      change (H a b d p n).eval (U a b d x)=0
      rw [H_eval a b d p n hn _ hden,T_U a b d x hab hd hx]
      rw [Polynomial.isRoot_of_mem_roots hroot,zero_mul]
    exact Multiset.mem_toFinset.mpr
      (Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hq).mpr hz,hu⟩)
  have hi : (rootSet p (Ioo (a/d) (b/d)) : Set Real).InjOn (U a b d) := by
    intro x hx y hy he
    have hxx := (mem_rootSet p _ x).mp hx
    have hyy := (mem_rootSet p _ y).mp hy
    calc
      x=T a b d (U a b d x) := (T_U a b d x hab hd hxx.2).symm
      _=T a b d (U a b d y) := congrArg (T a b d) he
      _=y := T_U a b d y hab hd hyy.2
  have hcard := Finset.card_le_card_of_injOn (U a b d) hm hi
  exact hcard.trans ((Multiset.toFinset_card_le _).trans_eq
    (Multiset.countP_eq_card_filter (fun x : Real => 0<x) q.roots).symm)

/-- Cover premises include every root in the domain; nonroot internal cuts must be
discharged when producing this premise, never inferred from interval labels. -/
theorem cover_card_le_sum {ι : Type} [DecidableEq ι]
    (p : Polynomial Real) (hp : p≠0) (s : Set Real) (index : Finset ι)
    (domain : ι → Set Real) (v : ι → Nat)
    (hcover : ∀ x∈s,p.IsRoot x → ∃ i∈index,x∈domain i)
    (hcount : ∀ i∈index,(rootSet p (domain i)).card≤v i) :
    (rootSet p s).card≤∑ i∈index,v i := by
  classical
  have hs : rootSet p s⊆index.biUnion (fun i => rootSet p (domain i)) := by
    intro x hx
    obtain ⟨hroot,hxs⟩ := (mem_rootSet p s x).mp hx
    obtain ⟨i,hi,hxi⟩ := hcover x hxs (Polynomial.isRoot_of_mem_roots hroot)
    exact Finset.mem_biUnion.mpr ⟨i,hi,(mem_rootSet p _ x).mpr ⟨hroot,hxi⟩⟩
  exact (Finset.card_le_card hs).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum hcount))

theorem exists_bracket_root (p : Polynomial Real) (l r : Real) (hlr : l<r)
    (hsign : p.eval l*p.eval r<0) : ∃ x∈Ioo l r,p.IsRoot x := by
  rcases mul_neg_iff.mp hsign with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · exact intermediate_value_Ioo' hlr.le p.continuousOn ⟨hr,hl⟩
  · exact intermediate_value_Ioo hlr.le p.continuousOn ⟨hl,hr⟩

/-- Saturation gives exactly one distinct root in every disjoint bracket and no extras.
No simplicity claim is made by this finite-set theorem. -/
theorem bracket_saturation (p : Polynomial Real) (hp : p≠0) (s : Set Real)
    (n : Nat) (l r : Fin n → Real)
    (hlr : ∀ i,l i<r i) (hsign : ∀ i,p.eval (l i)*p.eval (r i)<0)
    (hsub : ∀ i,Icc (l i) (r i)⊆s)
    (hdis : ∀ i j,i≠j → Disjoint (Icc (l i) (r i)) (Icc (l j) (r j)))
    (hupper : (rootSet p s).card≤n) :
    ∃ rho : Fin n → Real,
      (∀ i,rho i∈Ioo (l i) (r i) ∧ p.IsRoot (rho i)) ∧
      Function.Injective rho ∧
      (∀ x∈s,p.IsRoot x → ∃ i,x=rho i) ∧
      (∀ i x,x∈Icc (l i) (r i) → p.IsRoot x → x=rho i) := by
  classical
  choose rho hrho using (fun i => exists_bracket_root p (l i) (r i) (hlr i) (hsign i))
  have hinj : Function.Injective rho := by
    intro i j he
    by_contra hne
    have hi : rho i∈Icc (l i) (r i) := ⟨(hrho i).1.1.le,(hrho i).1.2.le⟩
    have hj : rho i∈Icc (l j) (r j) := by
      rw [he]
      exact ⟨(hrho j).1.1.le,(hrho j).1.2.le⟩
    exact Set.disjoint_left.mp (hdis i j hne) hi hj
  have himage : Finset.univ.image rho⊆rootSet p s := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_rootSet p s _).mpr ⟨(Polynomial.mem_roots hp).mpr (hrho i).2,
      hsub i ⟨(hrho i).1.1.le,(hrho i).1.2.le⟩⟩
  have hcard : (Finset.univ.image rho).card=n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have heq : Finset.univ.image rho=rootSet p s :=
    Finset.eq_of_subset_of_card_le himage (hupper.trans_eq hcard.symm)
  have hcomplete : ∀ x∈s,p.IsRoot x → ∃ i,x=rho i := by
    intro x hxs hxroot
    have hx := (mem_rootSet p s x).mpr ⟨(Polynomial.mem_roots hp).mpr hxroot,hxs⟩
    rw [← heq] at hx
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    exact ⟨i,he.symm⟩
  refine ⟨rho,hrho,hinj,hcomplete,?_⟩
  intro i x hxi hxroot
  obtain ⟨j,hxj⟩ := hcomplete x (hsub i hxi) hxroot
  have hij : i=j := by
    by_contra hne
    have hxjbox : x∈Icc (l j) (r j) := by
      rw [hxj]
      exact ⟨(hrho j).1.1.le,(hrho j).1.2.le⟩
    exact Set.disjoint_left.mp (hdis i j hne) hxi hxjbox
  simpa only [hij] using hxj

#print axioms interval_card_le_positive_roots
#print axioms cover_card_le_sum
#print axioms exists_bracket_root
#print axioms bracket_saturation
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover

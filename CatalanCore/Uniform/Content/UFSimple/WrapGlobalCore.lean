module

public import CatalanCore.Uniform.Content.UFSimple.WrapFibreCore
public import CatalanCore.Uniform.Content.UFSimple.WrapColourCore

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapGlobalCore

variable (p : ℕ) [Fact p.Prime]
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

open WrapFibreIndex

theorem cross_zero (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (hN : N<p*p)
    (i j : ι ⊕ β) (hne : (colour p c xs i).val≠(colour p c xs j).val) :
    WrapDeform.residue p (WrapFibreCore.core p q o s u c xs ys i j)=0 := by
  have hrow : Sum.elim c xs i<N := by cases i <;> simp_all
  have hcolumn : Sum.elim c ys j<N := by cases j <;> simp_all
  have hce : ((Sum.elim c ys j:ℕ):ZMod p)=colour p c xs j := by
    cases j with
    | inl j => rfl
    | inr j => exact (hcol j).symm
  have hrc : ((Sum.elim c xs i:ℕ):ZMod p)=colour p c xs i := by cases i <;> rfl
  have hdis : ((Sum.elim c xs i:ℕ):ZMod p)≠((Sum.elim c ys j:ℕ):ZMod p) := by
    intro he
    apply hne
    exact congrArg ZMod.val (hrc.symm.trans (he.trans hce))
  have he := WrapColourCore.entry_zero p q o N u hN _ _ hrow hcolumn hdis
  rcases i with i|i <;> rcases j with j|j
  · have hij : i≠j := by intro heq; subst j; exact hne rfl
    simpa [WrapFibreCore.core,Matrix.one_apply,hij] using he
  · simpa [WrapFibreCore.core] using he
  · simpa [WrapFibreCore.core] using he
  · simpa [WrapFibreCore.core] using he

theorem fibre_hyp (q o k j0 m N : ℕ) (xs ys : β → ℕ)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q) (hk0 : 0<k) (hk : k≤p)
    (hroot : q*k=j0*p+o) (hsize : 2*m≤N) (hN : q*N<p*p)
    (hx : Function.Injective xs) (hy : Function.Injective ys)
    (hxN : ∀ i,xs i<N) (hyN : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (hdis : ∀ i j,xs i≠ys j)
    (gamma : ZMod p)
    (hcard : 1≤Fintype.card (Balanced p xs gamma) ∧ Fintype.card (Balanced p xs gamma)≤m/p+1) :
    WrapBalancedResidue.Hyp p q o k j0 gamma.val m N
      (Fintype.card (Balanced p xs gamma)) (rowQuotient p xs gamma) (colQuotient p xs ys gamma) := by
  refine {
    hq0 := hq0
    hqp := hqp
    hq2 := hq2
    hoq := hoq
    hk0 := hk0
    hk := hk
    hg := ZMod.val_lt gamma
    hroot := hroot
    hsize := hsize
    hN := hN
    hb := hcard.2
    hb0 := hcard.1
    hx := row_injective p xs hx gamma
    hy := col_injective p xs ys hy hcol gamma
    hxN := ?_
    hyN := ?_
    hxy := quotient_disjoint p xs ys hcol hdis gamma
  }
  · intro i
    rw [← row_node p xs gamma i]
    exact hxN _
  · intro i
    rw [← col_node p xs ys hcol gamma i]
    exact hyN _

theorem own_unit (q o k j0 m N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q) (hk0 : 0<k) (hk : k≤p)
    (hroot : q*k=j0*p+o) (hsize : 2*m≤N) (hN : q*N<p*p)
    (hc : ∀ i,c i<N) (hx : Function.Injective xs) (hy : Function.Injective ys)
    (hxN : ∀ i,xs i<N) (hyN : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (hdis : ∀ i j,xs i≠ys j)
    (gamma : ZMod p)
    (hcard : 1≤Fintype.card (Balanced p xs gamma) ∧ Fintype.card (Balanced p xs gamma)≤m/p+1) :
    IsUnit ((WrapFibreCore.core p q o s u c xs ys).toSquareBlock (colour p c xs) gamma).det := by
  classical
  let H := fibre_hyp p q o k j0 m N xs ys hq0 hqp hq2 hoq hk0 hk hroot hsize hN
    hx hy hxN hyN hcol hdis gamma hcard
  have hgN : gamma.val<N := by
    have hh := H.hxN ⟨0,hcard.1⟩
    omega
  let J := (N-1-gamma.val)/p
  have hJ := WrapFibreCore.quotient_cap p gamma.val N hgN
  have hcJ : ∀ i:Common p c gamma,commonQuotient p c gamma i≤J := by
    intro i
    apply WrapFibreCore.le_quotient_cap p gamma.val N
    rw [← common_node p c gamma i]
    exact hc i.1
  have hxJ : ∀ i,rowQuotient p xs gamma i≤J :=
    fun i => WrapFibreCore.le_quotient_cap p gamma.val N _ (H.hxN i)
  have hyJ : ∀ i,colQuotient p xs ys gamma i≤J :=
    fun i => WrapFibreCore.le_quotient_cap p gamma.val N _ (H.hyN i)
  have hown := WrapOwnCore.unit H s u hs hu huc (commonQuotient p c gamma) J hJ hcJ hxJ hyJ
  have hb := WrapFibreCore.block_eq p q o k j0 m N s u c xs ys hcol gamma H
  rw [← hb] at hown
  let e := equiv p c xs gamma
  have he : ((WrapFibreCore.core p q o s u c xs ys).toSquareBlock (colour p c xs) gamma).submatrix e e=
      (WrapFibreCore.core p q o s u c xs ys).submatrix (fun i => (e i).1) (fun j => (e j).1) := rfl
  rw [← Matrix.det_submatrix_equiv_self e]
  simpa only [he] using hown

/-- The actual full mixed core is a unit, uniformly in every retained
common family. Its local matrices and their units are derived above. -/
theorem unit (q o k j0 m N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q) (hk0 : 0<k) (hk : k≤p)
    (hroot : q*k=j0*p+o) (hsize : 2*m≤N) (hN : q*N<p*p)
    (hc : ∀ i,c i<N) (hx : Function.Injective xs) (hy : Function.Injective ys)
    (hxN : ∀ i,xs i<N) (hyN : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (hdis : ∀ i j,xs i≠ys j)
    (hcard : ∀ gamma:ZMod p,1≤Fintype.card (Balanced p xs gamma) ∧
      Fintype.card (Balanced p xs gamma)≤m/p+1) :
    IsUnit (WrapFibreCore.core p q o s u c xs ys).det := by
  classical
  let Q := WrapFibreCore.core p q o s u c xs ys
  let col := fun i => (colour p c xs i).val
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N hq0) hN
  apply WrapColourCore.unit (WrapDeform.residue p) (WrapBalancedTest.unit_ne p) Q col
    (cross_zero p q o N s u c xs ys hc hxN hyN hcol hsingle)
  intro a ha
  obtain ⟨i,hi,hia⟩ := mem_image.mp ha
  let gamma := colour p c xs i
  let e : Whole p c xs gamma ≃ {j // col j=a} :=
    { toFun := fun j => ⟨j.1,(congrArg ZMod.val j.2).trans hia⟩
      invFun := fun j => ⟨j.1,ZMod.val_injective p (j.2.trans hia.symm)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : (Q.toSquareBlock col a).submatrix e e=Q.toSquareBlock (colour p c xs) gamma := rfl
  rw [← Matrix.det_submatrix_equiv_self e,he]
  exact own_unit p q o k j0 m N s u c xs ys hs hu huc hq0 hqp hq2 hoq hk0 hk hroot hsize hN
    hc hx hy hxN hyN hcol hdis gamma (hcard gamma)

end CatalanCore.Uniform.Content.UFSimple.WrapGlobalCore

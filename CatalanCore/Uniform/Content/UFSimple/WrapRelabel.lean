module

public import CatalanCore.Uniform.Content.UFSimple.WrapActual
public import CatalanCore.Uniform.Content.UFMoments.TopExt2

@[expose] public section

/-! # Common-core source invariance under finite relabelling -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapRelabel

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {ι τ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

/-- Own-block extraction commutes with common relabelling. -/
theorem Dmat_reindex (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (e : τ ≃ ι) :
    Dmat (c ∘ e) (Q.submatrix e e)=(Dmat c Q).submatrix e e := rfl

/-- Own inverse responses commute with common relabelling. -/
theorem own_response_reindex (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (e : τ ≃ ι)
    (t : ℕ) (sigma : ι → (LocRing p)[X]) (v : ι → GaussLoc p) :
    (sOwn (c ∘ e) t (sigma ∘ e) ᵥ* (Dmat (c ∘ e) (Q.submatrix e e))⁻¹) ⬝ᵥ (v ∘ e)=
      (sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ v := by
  rw [Dmat_reindex]
  have hh := WrapTransport.response_reindex (Dmat c Q) e e v (sOwn c t sigma)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hh
  exact hh

/-- The intrinsic common direction is independent of the finite index representation. -/
theorem dirOf_reindex (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (e : τ ≃ ι)
    (t : ℕ) (sigma : ι → (LocRing p)[X]) :
    dirOf Fr (c ∘ e) (Q.submatrix e e) t (sigma ∘ e)=dirOf Fr c Q t sigma := by
  have hL := own_response_reindex c Q e t sigma (fun a => ellL p Fr (c a))
  have hB := own_response_reindex c Q e t sigma (fun _ => 1)
  simp only [Function.comp_def,dotProduct,mul_one] at hB
  unfold dirOf
  erw [hL,hB]

/-- Fibre moments are independent of their finite index representation. -/
theorem fibMom_reindex (c : ι → ℕ) (D : Matrix ι ι (GaussLoc p)) (e : τ ≃ ι)
    (y : ι → GaussLoc p) (u : ZMod p) :
    fibMom (c ∘ e) (D.submatrix e e) (y ∘ e) u=fibMom c D y u := by
  unfold fibMom
  rw [Matrix.inv_submatrix_equiv]
  have hv : ∀ i,((D⁻¹).submatrix e e *ᵥ (y ∘ e)) i=(D⁻¹ *ᵥ y) (e i) := by
    intro i
    simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,Function.comp_def]
    exact Equiv.sum_comp e (fun j => D⁻¹ (e i) j*y j)
  simp_rw [hv]
  rw [Finset.sum_filter,Finset.sum_filter]
  exact Equiv.sum_comp e (fun i => if colOf (p:=p) c i=u then
    res p ((D⁻¹ *ᵥ y) i)*res p (y i) else 0)

/-- The normalized common weight is invariant under finite relabelling. -/
theorem vS7_reindex (q o : ℕ) (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X]) (e : τ ≃ ι)
    (t : ℕ) (u : ZMod p) :
    vS7 p q o Fr (c ∘ e) (Q.submatrix e e) t u=vS7 p q o Fr c Q t u := by
  dsimp only [vS7,vDer]
  erw [dirOf_reindex (Fr:=Fr) c Q e t (loewRow p Fr c t),Dmat_reindex]
  erw [fibMom_reindex c (Dmat c Q) e
    (fun a => ellL p Fr (c a)-dirOf Fr c Q t (loewRow p Fr c t)) ((t:ℕ):ZMod p),
    fibMom_reindex c (Dmat c Q) e
      (fun a => ellL p Fr (c a)-dirOf Fr c Q t (loewRow p Fr c t)) u]

/-- Canonical common-index equivalence between Fin r and range r. -/
def finRangeEquiv (r : ℕ) : Fin r ≃ (Finset.range r) where
  toFun a := ⟨a,Finset.mem_range.2 a.2⟩
  invFun a := ⟨a,Finset.mem_range.1 a.2⟩
  left_inv a := rfl
  right_inv a := rfl

/-- The existing top-extension common weight theorem also holds on Fin r. -/
theorem fin_top_zero {q o N : ℕ} (T : TwoTermData Fr q o) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0)
    (r : ℕ) (hc : ∀ a:Fin r,(a:ℕ)<N) (t0 delta : ℕ) (htN : t0<N)
    (hr : r≤t0) (hd : delta≤t0) (hlt : t0-delta<r) (hr3 : r≤t0-delta+p)
    (htp : t0<r+p) (hdiv : (t0-delta)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) (t0-delta) delta) :
    vS7 p q o Fr (fun a:Fin r => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ))) t0
        ((t0-delta:ℕ):ZMod p)=0 := by
  let D := twoTermPoleData T hN.le hsq hnorm hnorm0
  let c := fun a : (Finset.range r) => (a:ℕ)
  have hc' : ∀ a : (Finset.range r),(a:ℕ)<N := fun a => hc ⟨a,Finset.mem_range.1 a.2⟩
  have hh := vS7_topext T hN.le hsq hnorm hnorm0 hN ho hq (Finset.range r) rfl
    (fun i:Fin 0 => Fin.elim0 i) (fun i:Fin 0 => Fin.elim0 i) hc'
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) t0 delta htN hr hd hlt hr3 htp hdiv hw
  rw [← WrapBalanced.commonLift_eq_core D hN c (fun i:Fin 0 => Fin.elim0 i)
    (fun i:Fin 0 => Fin.elim0 i) hc' (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)] at hh
  have he := vS7_reindex (Fr:=Fr) q o c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
    (finRangeEquiv r) t0 ((t0-delta:ℕ):ZMod p)
  rw [WrapActual.commonLift_submatrix c (finRangeEquiv r) (finRangeEquiv r).injective] at he
  exact he.trans hh

end CatalanCore.Uniform.Content.UFSimple.WrapRelabel

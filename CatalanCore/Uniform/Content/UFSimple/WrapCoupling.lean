module

public import CatalanCore.Uniform.Content.UFSimple.WrapWeights

@[expose] public section

/-! # First-order coupling in the actual mixed core -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapCoupling

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Reduction of an independently loaded mixed inverse response uses
only its own colour block. No symmetry is assumed. -/
theorem mixed_own_response_res (D : PoleData Fr p N) (cr cc : ι → ℕ)
    (hcr : ∀ a,cr a<N) (hcc : ∀ a,cc a<N)
    (hcol : ∀ a,colOf (p:=p) cr a=colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b,nL p Fr*(nd p (cc b)-nd p (cr a))*Q a b=PF p Fr (cc b)-PF p Fr (cr a))
    (hdet : phiP p Q.det≠0) (t : ℕ) (ht : t<N) (sigma : ι → (LocRing p)[X])
    (hsigma : ∀ a,nL p Fr*(nd p (cc a)-nd p t)*sigma a=PF p Fr (cc a)-PF p Fr t)
    (v : ι → GaussLoc p) :
    res p ((fun a => algebraMap _ (GaussLoc p) (sigma a)) ⬝ᵥ
      ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ v))=
      res p ((sOwn cr t sigma ᵥ* (Dmat cr Q)⁻¹) ⬝ᵥ v) := by
  let Qm := Q.map (algebraMap (LocRing p)[X] (GaussLoc p))
  let Dm := Dmat cr Q
  have hQu := isUnit_map_det Q hdet
  have hDu := WrapNodes.isUnit_mixedDmat_det D cr cc hcr hcc hcol Q hQ hdet
  have hsplit := WrapNodes.mixed_core_split D cr cc hcr hcc hcol Q hQ
  have hmat : Qm.map (res p)=Dm.map (res p) := by
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M => res p (M i j)) hsplit
    simpa only [Qm,Dm,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      map_add,map_mul,res_piL,zero_mul,add_zero] using hh
  have hinv : (Qm⁻¹).map (res p)=(Dm⁻¹).map (res p) := by
    rw [← map_inv_of_unit (res p) Qm hQu,← map_inv_of_unit (res p) Dm hDu,hmat]
  have hs := node_split D cc hcc t ht sigma hsigma
  have hown : sOwn cc t sigma=sOwn cr t sigma := by
    funext a
    simp only [sOwn,← hcol a]
  have hsres : (fun a => res p (algebraMap _ (GaussLoc p) (sigma a)))=
      fun a => res p (sOwn cr t sigma a) := by
    rw [← hown]
    funext a
    have hh := congrArg (fun f => res p (f a)) hs
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,res_piL,zero_mul,add_zero] using hh
  rw [← Matrix.dotProduct_mulVec]
  simp only [RingHom.map_dotProduct,RingHom.map_mulVec,Function.comp_def]
  change (fun a => res p (algebraMap _ (GaussLoc p) (sigma a))) ⬝ᵥ
      ((Qm⁻¹).map (res p) *ᵥ fun a => res p (v a))=
    (fun a => res p (sOwn cr t sigma a)) ⬝ᵥ
      ((Dm⁻¹).map (res p) *ᵥ fun a => res p (v a))
  rw [hsres,hinv]

variable {κ : Type} [Fintype κ] [DecidableEq κ]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized row kill wedge is exactly the reduced own moment,
up to the nonzero frame norm. This applies to independent mixed coordinates. -/
theorem row_wedge_res (D : PoleData Fr p N)
    (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (cr cc : ι → ℕ) (xs ys : κ → ℕ)
    (hcr : ∀ a,cr a<N) (hcc : ∀ a,cc a<N) (hx : ∀ z,xs z<N)
    (hcol : ∀ a,colOf (p:=p) cr a=colOf cc a)
    (hcomm : ∀ i j,nL p Fr*(nd p (colNode cc ys j)-nd p (rowNode cr xs i))*A i j=
      PF p Fr (colNode cc ys j)-PF p Fr (rowNode cr xs i))
    (hdet : phiP p A.toBlocks₁₁.det≠0) (d : GaussLoc p) (z : κ) :
    wedgeR A Fr cr xs d z= -res p (algebraMap _ (GaussLoc p) (nL p Fr))*
      res p ((ellL p Fr (xs z)-d)-(sOwn cr (xs z) (A.toBlocks₂₁ z) ᵥ* (Dmat cr A.toBlocks₁₁)⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (cr a)-d)) := by
  let f := algebraMap (LocRing p)[X] (GaussLoc p)
  let Q := A.toBlocks₁₁
  let Qm := Q.map f
  let sigma := A.toBlocks₂₁ z
  let sm := fun a => f (sigma a)
  let u := f (nL p Fr)
  have hQu := isUnit_map_det Q hdet
  have hQr : ∀ a b,nL p Fr*(nd p (cc b)-nd p (cr a))*Q a b=PF p Fr (cc b)-PF p Fr (cr a) :=
    fun a b => hcomm (Sum.inl a) (Sum.inl b)
  have hsr : ∀ a,nL p Fr*(nd p (cc a)-nd p (xs z))*sigma a=PF p Fr (cc a)-PF p Fr (xs z) :=
    fun a => hcomm (Sum.inr z) (Sum.inl a)
  have hd : res p Qm.det=phiP p Q.det := by
    simp only [Qm,Matrix.det_apply',map_sum,map_mul,map_intCast,map_prod,Matrix.map_apply,f,res_algebraMap]
    apply Finset.sum_congr rfl
    intro perm _
    congr 1
    rcases Int.units_eq_one_or (Equiv.Perm.sign perm) with h|h <;> simp [h]
  have hA : f (rowMomA A z)=Qm.det*(1-sm ⬝ᵥ (Qm⁻¹ *ᵥ 1)) := by
    simpa only [rowMomA,Qm,sm,Q,sigma] using (momA_map (R:=GaussLoc p) (algebraMap (LocRing p)[X] (GaussLoc p)) Q hQu sigma)
  have hB : f (rowMomB1 A Fr cr xs z)=Qm.det*u*
      (ellL p Fr (xs z)-sm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a))) := by
    have hh := momB_map (R:=GaussLoc p) (algebraMap (LocRing p)[X] (GaussLoc p)) Q hQu sigma (fun a => PF1 p Fr (cr a)) (PF1 p Fr (xs z))
    have hP : (fun a => f (PF1 p Fr (cr a)))=fun a => u*ellL p Fr (cr a) := by
      funext a
      exact algebraMap_PF1 D (cr a)
    change f (rowMomB1 A Fr cr xs z)=Qm.det*(f (PF1 p Fr (xs z))-
      sm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => f (PF1 p Fr (cr a)))) at hh
    rw [hP] at hh
    have hs : sm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => u*ellL p Fr (cr a))=
        u*(sm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a))) :=
      lin_scale Qm⁻¹ sm (fun a => ellL p Fr (cr a)) u
    rw [hs,algebraMap_PF1 D (xs z)] at hh
    change f (rowMomB1 A Fr cr xs z)=_
    rw [hh]
    dsimp only [u]
    ring
  have hAr := congrArg (res p) hA
  have hBr := congrArg (res p) hB
  rw [res_algebraMap,map_mul,map_sub,map_one,hd] at hAr
  rw [res_algebraMap,map_mul,map_mul,hd,map_sub] at hBr
  have hr := mixed_own_response_res D cr cc hcr hcc hcol Q hQr hdet (xs z) (hx z) sigma hsr
    (fun a => ellL p Fr (cr a)-d)
  have hlin := congrArg (res p) (lin_shift Qm⁻¹ sm (fun a => ellL p Fr (cr a)) d (ellL p Fr (xs z)))
  simp only [map_sub,map_mul,map_one] at hlin
  rw [hr] at hlin
  unfold wedgeR
  apply (div_eq_iff hdet).2
  rw [hAr,hBr,map_mul]
  dsimp only [u] at *
  simp only [map_sub]
  dsimp only [f,Q,Qm,sm,sigma] at hlin ⊢
  linear_combination -(phiP p Q.det)*res p (f (nL p Fr))*hlin

/-- Reordering preserves bounds of all original row nodes. -/
theorem rowCoords_lt (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (i : (ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) : WrapActual.rowCoords c r s l hl hls i<N := by
  change rowNode _ _ (WrapGeometry.rowFullEquiv ι s l hl hls i)<N
  rcases WrapGeometry.rowFullEquiv ι s l hl hls i with a|j
  · exact hc a
  · exact hx j

/-- Reordering preserves bounds of all original col nodes. -/
theorem colCoords_lt (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (i : (ι ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) : WrapActual.colCoords c r s l hl hls i<N := by
  change colNode _ _ (WrapGeometry.colFullEquiv ι s l hl hls i)<N
  rcases WrapGeometry.colFullEquiv ι s l hl hls i with a|j
  · exact hc a
  · exact hy j

/-- Every actual normalized surplus row wedge equals its original
common-core wedge, for every direction and every common-node list. -/
theorem actual_row_wedge_eq {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    wedgeR A Fr cr xx d z=wedgeR Ao Fr c (WrapActual.xs r) d
      (WrapGeometry.rowSlot s l hl hls (Sum.inr z)) := by
  intro D hint Ao A cr cc xx yy
  let j := WrapGeometry.rowSlot s l hl hls (Sum.inr z)
  have hcr : ∀ a,cr a<N := fun a => rowCoords_lt c r s l hl hls hc hx hy (Sum.inl a)
  have hcc : ∀ a,cc a<N := fun a => colCoords_lt c r s l hl hls hc hx hy (Sum.inl a)
  have hxx : ∀ a,xx a<N := fun a => rowCoords_lt c r s l hl hls hc hx hy (Sum.inr a)
  have hdet : phiP p A.toBlocks₁₁.det≠0 :=
    WrapActual.core_primitive T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hint
  have hcomm : ∀ i j,nL p Fr*(nd p (colNode cc yy j)-nd p (rowNode cr xx i))*A i j=
      PF p Fr (colNode cc yy j)-PF p Fr (rowNode cr xx i) := by
    have hrFull : rowNode cr xx=WrapActual.rowCoords c r s l hl hls := by
      funext i
      cases i <;> rfl
    have hcFull : colNode cc yy=WrapActual.colCoords c r s l hl hls := by
      funext i
      cases i <;> rfl
    intro i j
    rw [hrFull,hcFull]
    exact WrapActual.reordered_commutator D hN c r s l hl hls hc hx hy i j
  have hr := row_wedge_res D A cr cc xx yy hcr hcc hxx (WrapActual.core_colours c r s l hl hls hp)
    hcomm hdet d z
  have hro := row_wedge_res D Ao c c (WrapActual.xs r) (WrapActual.ys r) hc hc hx (fun _ => rfl)
    (WrapEntries.sLift_commutator D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
    (sLift_core_det c _ _ _) d j
  rw [hr,hro]
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy
  have hDo : IsUnit (Dmat c Ao.toBlocks₁₁).det :=
    isUnit_Dmat_det D c hc Ao.toBlocks₁₁ (sLift_core_rel D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det c _ _ _)
  have htlo : r+2*l-1≤xx z := by change r+2*l-1≤r+2*(l+(z:ℕ)); omega
  have hthi : xx z<r+p := by change r+2*(l+(z:ℕ))<r+p; have := z.2; omega
  have hresp := WrapActual.surplus_own_response c r s l (xx z) hl hls hp htlo hthi hint
    (loewRow p Fr cc (xx z)) (fun a => ellL p Fr (cr a)-d) hDa hDo
  have hloadA : A.toBlocks₂₁ z=loewRow p Fr cc (xx z) :=
    WrapActual.surplus_row_load D hN c r s l hl hls hc hx hy z
  have hloadO : Ao.toBlocks₂₁ j=loewRow p Fr c (WrapActual.xs r j) := by
    funext a
    exact sLift_row_entry D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy j a
  rw [hloadA,hloadO]
  erw [hresp]
  rfl

/-- The transposed actual surplus coupling is its original common-core coupling. -/
theorem actual_col_row_wedge_eq {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (d : GaussLoc p) (z : Fin (s+1-l)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    wedgeR Aᵀ Fr cc yy d z=wedgeR Aoᵀ Fr c (WrapActual.ys r) d
      (WrapGeometry.colSlot s l hl hls (Sum.inr z)) := by
  intro D hint Ao A cr cc xx yy
  let j := WrapGeometry.colSlot s l hl hls (Sum.inr z)
  have hcr : ∀ a,cr a<N := fun a => rowCoords_lt c r s l hl hls hc hx hy (Sum.inl a)
  have hcc : ∀ a,cc a<N := fun a => colCoords_lt c r s l hl hls hc hx hy (Sum.inl a)
  have hyy : ∀ a,yy a<N := fun a => colCoords_lt c r s l hl hls hc hx hy (Sum.inr a)
  have hdet : phiP p A.toBlocks₁₁.det≠0 :=
    WrapActual.core_primitive T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hint
  have hdetT : phiP p (Aᵀ.toBlocks₁₁).det≠0 := by
    change phiP p A.toBlocks₁₁ᵀ.det≠0
    rwa [Matrix.det_transpose]
  have hdetO : phiP p (Aoᵀ.toBlocks₁₁).det≠0 := by
    change phiP p Ao.toBlocks₁₁ᵀ.det≠0
    rw [Matrix.det_transpose]
    exact sLift_core_det c _ _ _
  have hcomm : ∀ i j,nL p Fr*(nd p (colNode cc yy j)-nd p (rowNode cr xx i))*A i j=
      PF p Fr (colNode cc yy j)-PF p Fr (rowNode cr xx i) := by
    have hrFull : rowNode cr xx=WrapActual.rowCoords c r s l hl hls := by funext i; cases i <;> rfl
    have hcFull : colNode cc yy=WrapActual.colCoords c r s l hl hls := by funext i; cases i <;> rfl
    intro i j
    rw [hrFull,hcFull]
    exact WrapActual.reordered_commutator D hN c r s l hl hls hc hx hy i j
  have hr := row_wedge_res D Aᵀ cc cr yy xx hcc hcr hyy
    (fun a => (WrapActual.core_colours c r s l hl hls hp a).symm)
    (WrapResponse.commutator_transpose A (rowNode cr xx) (colNode cc yy) hcomm) hdetT d z
  have hro := row_wedge_res D Aoᵀ c c (WrapActual.ys r) (WrapActual.xs r) hc hc hy (fun _ => rfl)
    (WrapResponse.commutator_transpose Ao (rowNode c (WrapActual.xs r)) (colNode c (WrapActual.ys r))
      (WrapEntries.sLift_commutator D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy)) hdetO d j
  rw [hr,hro]
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy
  have hDo : IsUnit (Dmat c Ao.toBlocks₁₁).det :=
    isUnit_Dmat_det D c hc Ao.toBlocks₁₁ (sLift_core_rel D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy)
      (sLift_core_det c _ _ _)
  have hDac := WrapActual.Dmat_transpose_unit cr cc (WrapActual.core_colours c r s l hl hls hp) A.toBlocks₁₁ hDa
  have hDoc := WrapActual.Dmat_transpose_unit c c (fun _ => rfl) Ao.toBlocks₁₁ hDo
  have htlo : r+2*l-1≤yy z := by change r+2*l-1≤r+2*(l-1+(z:ℕ))+1; omega
  have hthi : yy z<r+p := by change r+2*(l-1+(z:ℕ))+1<r+p; have := z.2; omega
  have hresp := WrapActual.surplus_col_own_response c r s l (yy z) hl hls hp htlo hthi hint
    (loewRow p Fr cr (yy z)) (fun a => ellL p Fr (cc a)-d) hDac hDoc
  have hloadA : Aᵀ.toBlocks₂₁ z=loewRow p Fr cr (yy z) :=
    WrapActual.surplus_col_load D hN c r s l hl hls hc hx hy z
  have hloadO : Aoᵀ.toBlocks₂₁ j=loewRow p Fr c (WrapActual.ys r j) := by
    funext a
    exact sLift_col_entry D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy a j
  rw [hloadA,hloadO]
  erw [hresp]
  rfl

/-- Transposing a first prefix moment exchanges its row and column forms. -/
theorem rowMomB1_transpose (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (cc : ι → ℕ) (ys : κ → ℕ) (y : κ) :
    rowMomB1 Aᵀ Fr cc ys y=colMomB1 A Fr cc ys y := by
  have hQ : Aᵀ.toBlocks₁₁=A.toBlocks₁₁ᵀ := rfl
  unfold rowMomB1 colMomB1
  rw [hQ,Matrix.det_transpose,← Matrix.adjugate_transpose]
  simp only [Matrix.transpose_apply,Matrix.toBlocks₂₁,Matrix.toBlocks₁₂,Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (A (Sum.inl i) (Sum.inr y))]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

/-- The normalized transposed row wedge is the negative column wedge. -/
theorem wedgeR_transpose (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (cc : ι → ℕ) (ys : κ → ℕ) (d : GaussLoc p) (y : κ) :
    wedgeR Aᵀ Fr cc ys d y= -(wedgeC A Fr cc ys d y)/phiP p A.toBlocks₁₁.det := by
  unfold wedgeR wedgeC
  rw [WrapResponse.rowMomA_transpose,rowMomB1_transpose]
  change (_-_)/phiP p A.toBlocks₁₁ᵀ.det=_
  rw [Matrix.det_transpose]
  ring

/-- Distinct original prefix residues supply this actual nonzero kill wedge. -/
theorem actual_row_wedge_ne_of_V {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (t0 : ℕ) (ht0 : t0<N) (z : Fin (s+1-l))
    (hV : (twoTermPoleData T hN.le hsq hnorm hnorm0).V t0≠
      (twoTermPoleData T hN.le hsq hnorm hnorm0).V
        (WrapActual.rowCoords c r s l hl hls (Sum.inr z))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    let d := dirOf Fr c Ao.toBlocks₁₁ t0 (loewRow p Fr c t0)
    wedgeR A Fr cr xx d z≠0 := by
  intro D hint Ao A cr cc xx yy d
  rw [actual_row_wedge_eq T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy d z]
  exact CatalanCore.Uniform.Content.UFSimple.wedgeR_ne_of_V D hN c (WrapActual.xs r) (WrapActual.ys r)
    hc hx hy t0 ht0 (WrapGeometry.rowSlot s l hl hls (Sum.inr z)) hV

/-- Distinct original prefix residues supply this actual nonzero kill wedge. -/
theorem actual_col_wedge_ne_of_V {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (t0 : ℕ) (ht0 : t0<N) (z : Fin (s+1-l))
    (hV : (twoTermPoleData T hN.le hsq hnorm hnorm0).V t0≠
      (twoTermPoleData T hN.le hsq hnorm hnorm0).V
        (WrapActual.colCoords c r s l hl hls (Sum.inr z))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    let d := dirOf Fr c Ao.toBlocks₁₁ t0 (loewRow p Fr c t0)
    wedgeC A Fr cc yy d z≠0 := by
  intro D hint Ao A cr cc xx yy d
  let j := WrapGeometry.colSlot s l hl hls (Sum.inr z)
  have hwo := CatalanCore.Uniform.Content.UFSimple.wedgeC_ne_of_V D hN c (WrapActual.xs r) (WrapActual.ys r)
    hc hx hy t0 ht0 j hV
  have hdO : phiP p Ao.toBlocks₁₁.det≠0 := sLift_core_det c _ _ _
  have hro : wedgeR Aoᵀ Fr c (WrapActual.ys r) d j≠0 := by
    rw [wedgeR_transpose]
    exact div_ne_zero (neg_ne_zero.2 hwo) hdO
  have hra : wedgeR Aᵀ Fr cc yy d z≠0 := by
    rw [actual_col_row_wedge_eq T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize hc hx hy d z]
    exact hro
  intro hz
  apply hra
  rw [wedgeR_transpose,hz,neg_zero,zero_div]

/-- A separating singular index supplies this actual nonzero coupling. -/
theorem actual_row_wedge_ne_of_sep {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (t0 : ℕ) (ht0 : t0<N) (z : Fin (s+1-l))
    (hsep : (t0<WrapActual.rowCoords c r s l hl hls (Sum.inr z) ∧ WrapActual.rowCoords c r s l hl hls (Sum.inr z)<t0+p ∧
      ∃ k,t0<k ∧ k≤WrapActual.rowCoords c r s l hl hls (Sum.inr z) ∧ (p∣k ∨ p∣q*k-o)) ∨
      (WrapActual.rowCoords c r s l hl hls (Sum.inr z)<t0 ∧ t0<WrapActual.rowCoords c r s l hl hls (Sum.inr z)+p ∧
        ∃ k,WrapActual.rowCoords c r s l hl hls (Sum.inr z)<k ∧ k≤t0 ∧ (p∣k ∨ p∣q*k-o))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    let d := dirOf Fr c Ao.toBlocks₁₁ t0 (loewRow p Fr c t0)
    wedgeR A Fr cr xx d z≠0 := by
  exact actual_row_wedge_ne_of_V T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize
    hc hx hy t0 ht0 z (CatalanCore.Uniform.Content.UFSimple.V_ne_of_sep T hqp hN.le hsq hnorm hnorm0
      ht0 (rowCoords_lt c r s l hl hls hc hx hy (Sum.inr z)) hsep)

/-- A separating singular index supplies this actual nonzero coupling. -/
theorem actual_col_wedge_ne_of_sep {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (c : ι → ℕ) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a,c a<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (t0 : ℕ) (ht0 : t0<N) (z : Fin (s+1-l))
    (hsep : (t0<WrapActual.colCoords c r s l hl hls (Sum.inr z) ∧ WrapActual.colCoords c r s l hl hls (Sum.inr z)<t0+p ∧
      ∃ k,t0<k ∧ k≤WrapActual.colCoords c r s l hl hls (Sum.inr z) ∧ (p∣k ∨ p∣q*k-o)) ∨
      (WrapActual.colCoords c r s l hl hls (Sum.inr z)<t0 ∧ t0<WrapActual.colCoords c r s l hl hls (Sum.inr z)+p ∧
        ∃ k,WrapActual.colCoords c r s l hl hls (Sum.inr z)<k ∧ k≤t0 ∧ (p∣k ∨ p∣q*k-o))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let hint := hint_of_poleData D hN hc hx hy
    let Ao := sLift c (WrapActual.xs r) (WrapActual.ys r) hint
    let A := WrapActual.reordered c r s l hl hls hint
    let cr := fun a => WrapActual.rowCoords c r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords c r s l hl hls (Sum.inl a)
    let xx := fun z => WrapActual.rowCoords c r s l hl hls (Sum.inr z)
    let yy := fun z => WrapActual.colCoords c r s l hl hls (Sum.inr z)
    let d := dirOf Fr c Ao.toBlocks₁₁ t0 (loewRow p Fr c t0)
    wedgeC A Fr cc yy d z≠0 := by
  exact actual_col_wedge_ne_of_V T hqp hN hsq hnorm hnorm0 c r s l hl hls hp hsize
    hc hx hy t0 ht0 z (CatalanCore.Uniform.Content.UFSimple.V_ne_of_sep T hqp hN.le hsq hnorm hnorm0
      ht0 (colCoords_lt c r s l hl hls hc hx hy (Sum.inr z)) hsep)

end CatalanCore.Uniform.Content.UFSimple.WrapCoupling

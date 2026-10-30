module

public import CatalanCore.Uniform.Content.UFSimple.WrapCell

@[expose] public section

/-! # Credited classes of the actual wrapped source -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapCredit

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- A surplus colour has no node in the extra virtual common interval. -/
theorem virtual_surplus_lt (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p)
    (a : Fin (r+b)) (ha : ((a:ℕ):ZMod p)=((t:ℕ):ZMod p)) : (a:ℕ)<r := by
  by_contra h
  have har : r≤(a:ℕ) := by omega
  have he : (a:ℕ)=r+((a:ℕ)-r) := by omega
  have ht : t=r+(t-r) := by omega
  rw [he,ht] at ha
  exact WrapActual.offset_colours (by have := a.2; omega) (by omega)
    (by have := a.2; omega) ha

/-- The virtual own fibre at a surplus colour consists of original common nodes. -/
noncomputable def virtual_surplus_equiv (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p) :
    {a:Fin (r+b) // ((a:ℕ):ZMod p)=((t:ℕ):ZMod p)} ≃
      {a:Fin r // ((a:ℕ):ZMod p)=((t:ℕ):ZMod p)} where
  toFun a := ⟨⟨a.1,virtual_surplus_lt r b t hlo hhi a.1 a.2⟩,a.2⟩
  invFun a := ⟨⟨a.1,by have := a.1.2; omega⟩,a.2⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv a := by apply Subtype.ext; apply Fin.ext; rfl

/-- Restricting a virtual common core to original common indices gives
exactly the original common core, including its spectral diagonal. -/
theorem virtual_common_restrict (r b : ℕ) :
    (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ))).submatrix
      (fun a:Fin r => (⟨a,by have := a.2; omega⟩:Fin (r+b)))
      (fun a:Fin r => (⟨a,by have := a.2; omega⟩:Fin (r+b)))=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ)) := by
  apply WrapActual.commonLift_submatrix
  intro a a2 h
  apply Fin.ext
  exact congrArg (fun z:Fin (r+b) => (z:ℕ)) h

/-- The two original common fibre blocks are literally equal under the
surplus equivalence. -/
theorem virtual_surplus_block (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let co := fun a:Fin r => (a:ℕ)
    let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
    let DO := Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co)
    let E := virtual_surplus_equiv r b t hlo hhi
    (blk DV (colOf cv) ((t:ℕ):ZMod p)).submatrix E.symm E.symm=
      blk DO (colOf co) ((t:ℕ):ZMod p) := by
  intro cv co DV DO E
  apply Matrix.ext
  intro i j
  have hV : colOf (p:=p) cv (E.symm i).1=colOf cv (E.symm j).1 :=
    ((E.symm i).2).trans ((E.symm j).2).symm
  have hO : colOf (p:=p) co i.1=colOf co j.1 := i.2.trans j.2.symm
  change (if colOf (p:=p) cv (E.symm i).1=colOf cv (E.symm j).1 then
    algebraMap _ (GaussLoc p) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv (E.symm i).1 (E.symm j).1)
    else 0)=(if colOf (p:=p) co i.1=colOf co j.1 then
      algebraMap _ (GaussLoc p) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co i.1 j.1) else 0)
  rw [if_pos hV,if_pos hO]
  exact congrArg (algebraMap _ (GaussLoc p))
    (congrArg (fun M => M i.1 j.1) (virtual_common_restrict (p:=p) (Fr:=Fr) r b))

/-- The virtual representative's own linear response is the original
common response. This statement covers both direction and denominator loads. -/
theorem virtual_surplus_own (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p)
    (sigma : Fin (r+b) → (LocRing p)[X]) (v : Fin (r+b) → GaussLoc p)
    (hV : IsUnit (Dmat (fun a:Fin (r+b) => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ)))).det)
    (hO : IsUnit (Dmat (fun a:Fin r => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ)))).det) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let co := fun a:Fin r => (a:ℕ)
    let inc := fun a:Fin r => (⟨a,by have := a.2; omega⟩:Fin (r+b))
    (sOwn cv t sigma ᵥ* (Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv))⁻¹) ⬝ᵥ v=
      (sOwn co t (sigma ∘ inc) ᵥ* (Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co))⁻¹) ⬝ᵥ
        (v ∘ inc) := by
  intro cv co inc
  let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
  let DO := Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co)
  let tau : ZMod p := ((t:ℕ):ZMod p)
  have hbV : ∀ a b,colOf (p:=p) cv a≠colOf cv b → DV a b=0 := by
    intro a b h; simp [DV,Dmat,h]
  have hbO : ∀ a b,colOf (p:=p) co a≠colOf co b → DO a b=0 := by
    intro a b h; simp [DO,Dmat,h]
  have hsV : ∀ a,colOf (p:=p) cv a≠tau → sOwn cv t sigma a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  have hsO : ∀ a,colOf (p:=p) co a≠tau → sOwn co t (sigma ∘ inc) a=0 := by
    intro a h; simp [sOwn,h,tau] at *
  rw [own_fiber_form DV (colOf cv) hV hbV tau (sOwn cv t sigma) v hsV,
    own_fiber_form DO (colOf co) hO hbO tau (sOwn co t (sigma ∘ inc)) (v ∘ inc) hsO]
  let E := virtual_surplus_equiv r b t hlo hhi
  have hh := WrapTransport.response_reindex (blk DV (colOf cv) tau) E.symm E.symm
    (fun a => v a.1) (fun a => sOwn cv t sigma a.1)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hh
  erw [virtual_surplus_block r b t hlo hhi] at hh
  exact hh.symm

/-- The virtual moment at a surplus colour is the original common
moment, for every choice of the direction. -/
theorem virtual_surplus_moment (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p)
    (d : GaussLoc p)
    (hV : IsUnit (Dmat (fun a:Fin (r+b) => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin (r+b) => (a:ℕ)))).det)
    (hO : IsUnit (Dmat (fun a:Fin r => (a:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun a:Fin r => (a:ℕ)))).det) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let co := fun a:Fin r => (a:ℕ)
    fibMom cv (Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv))
      (fun a => ellL p Fr (cv a)-d) ((t:ℕ):ZMod p)=
    fibMom co (Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co))
      (fun a => ellL p Fr (co a)-d) ((t:ℕ):ZMod p) := by
  intro cv co
  let DV := Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv)
  let DO := Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co)
  let tau : ZMod p := ((t:ℕ):ZMod p)
  let yV := fun a => ellL p Fr (cv a)-d
  let yO := fun a => ellL p Fr (co a)-d
  have hbV : ∀ a b,colOf (p:=p) cv a≠colOf cv b → DV a b=0 := by
    intro a b h; simp [DV,Dmat,h]
  have hbO : ∀ a b,colOf (p:=p) co a≠colOf co b → DO a b=0 := by
    intro a b h; simp [DO,Dmat,h]
  change (∑ a∈univ.filter (fun a => colOf cv a=tau),res p ((DV⁻¹ *ᵥ yV) a)*res p (yV a))=
    ∑ a∈univ.filter (fun a => colOf co a=tau),res p ((DO⁻¹ *ᵥ yO) a)*res p (yO a)
  rw [WrapType.mixed_fiber_moment_response DV (colOf cv) hV hbV tau yV yV (res p),
    WrapType.mixed_fiber_moment_response DO (colOf co) hO hbO tau yO yO (res p)]
  let E := virtual_surplus_equiv r b t hlo hhi
  have hh := WrapTransport.response_reindex (blk DV (colOf cv) tau) E.symm E.symm
    (fun a => yV a.1) (fun a => yV a.1)
  erw [virtual_surplus_block r b t hlo hhi] at hh
  exact congrArg (res p) hh.symm

/-- The original common representative direction already annihilates
the virtual own moment. No parity assumption is made on r+b. -/
theorem virtual_representative_zero (D : PoleData Fr p N) (hN : N<p*p)
    (r b t : ℕ) (hlo : r+b≤t) (hhi : t<r+p) (htN : t<N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hv : ∀ a:Fin (r+b),(a:ℕ)<N) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let co := fun a:Fin r => (a:ℕ)
    let QV := WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv
    let QO := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
    let d := dirOf Fr co QO t (loewRow p Fr co t)
    (ellL p Fr t-d)-(sOwn cv t (loewRow p Fr cv t) ᵥ* (Dmat cv QV)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (cv a)-d)=0 := by
  intro cv co QV QO d
  have hV := WrapActual.reference_Dmat_unit D hN cv hv
  have hO := WrapActual.reference_Dmat_unit D hN co hc
  have hh := virtual_surplus_own r b t hlo hhi (loewRow p Fr cv t)
    (fun a => ellL p Fr (cv a)-d) hV hO
  rw [hh]
  exact own_dir_zero Fr co QO t (loewRow p Fr co t)
    (WrapBalanced.commonLift_own_unit D hN co hc t htN)

/-- The original representative direction transports through the
virtual finite window, including its absorbed balanced classes. -/
theorem virtual_transport_zero {q o : ℕ} (T : TwoTermData Fr q o) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r b t0 delta : ℕ) (hc : ∀ a:Fin r,(a:ℕ)<N) (hv : ∀ a:Fin (r+b),(a:ℕ)<N)
    (hr : r+b≤t0) (ht0p : t0<r+p) (htp : t0+delta<r+b+p)
    (hq : (t0+delta)/p=t0/p) (htN : t0+delta<N)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 delta) :
    let cv := fun a:Fin (r+b) => (a:ℕ)
    let co := fun a:Fin r => (a:ℕ)
    let QV := WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv
    let QO := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
    let d := dirOf Fr co QO t0 (loewRow p Fr co t0)
    res p ((ellL p Fr (t0+delta)-d)-
      (sOwn cv (t0+delta) (loewRow p Fr cv (t0+delta)) ᵥ* (Dmat cv QV)⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (cv a)-d))=0 := by
  intro cv co QV QO d
  let D := twoTermPoleData T hN.le hsq hnorm hnorm0
  have hDu := WrapActual.reference_Dmat_unit D hN cv hv
  have hz := virtual_representative_zero D hN r b t0 hr ht0p (by omega) hc hv
  have hT := WrapCell.typeData_window T hN hsq hnorm hnorm0 hp2 ho hq0 (r+b) t0 delta hv
    hr htp hq htN hw 0
  dsimp only at hz hT
  exact WrapType.own_type_transport cv QV hDu t0 (loewRow p Fr cv t0) d hz _ _
    (t0+delta) (loewRow p Fr cv (t0+delta)) hT

/-- The concrete lower/upper orientation of every actual balanced
fibre is invertible. The odd parity follows by transposition. -/
theorem balanced_inverse_normalized (D : PoleData Fr p N) (hN : N<p*p)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (t : Fin (2*l-1))
    (hDa : IsUnit (Dmat
      (fun a => WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l hl hls (Sum.inl a))
      (WrapActual.reordered (fun a:Fin r => (a:ℕ)) r s l hl hls
        (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).det) :
    IsUnit ((WrapBalanced.mixedLift (p:=p) (Fr:=Fr)
      (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ))
      (r+(t:ℕ)) (r+(t:ℕ)+p)).map (algebraMap _ (GaussLoc p))).det := by
  have hh := WrapActual.balanced_fibre_inverse_unit D hN r s l hl hls hp hc hx hy t hDa
  unfold WrapBalanced.rowNode WrapBalanced.colNode at hh
  rw [WrapGeometry.rowBalanced_node,WrapGeometry.colBalanced_node] at hh
  by_cases ht : (t:ℕ)%2=0
  · simpa only [ht,↓reduceIte,Nat.add_zero,← hp] using hh
  · simp only [ht,↓reduceIte,Nat.add_zero,← hp] at hh
    rw [← WrapBalanced.mixedLift_transpose,Matrix.transpose_map,Matrix.det_transpose] at hh
    exact hh

/-- An ordinary credited balanced class has exactly its virtual common
moment. The own-direction transport is supplied by the original finite window. -/
theorem balanced_moment_credit {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (t : Fin (2*l-1))
    (hq : (r+(t:ℕ)+p)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (r+(t:ℕ)+p-t0)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let co := fun a:Fin r => (a:ℕ)
    let cv := fun a:Fin (r+(2*l-1)) => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords co r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords co r s l hl hls (Sum.inl a)
    let Q := (WrapActual.reordered co r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co) t0 (loewRow p Fr co t0)
    WrapNodes.mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a)-d)
      (fun a => ellL p Fr (cc a)-d) ((r+(t:ℕ):ℕ):ZMod p)=
      fibMom cv (Dmat cv (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv))
        (fun a => ellL p Fr (cv a)-d) ((r+(t:ℕ):ℕ):ZMod p) := by
  intro D co cv cr cc Q d
  let lo := r+(t:ℕ)
  let hi := r+(t:ℕ)+p
  let cref := WrapBalanced.extendNodes
    (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ)) lo
  have hb : 2*l-1<p := by omega
  have hv : ∀ a:Fin (r+(2*l-1)),(a:ℕ)<N := by intro a; have := a.2; omega
  have hhi : hi<N := by have := t.2; dsimp [hi]; omega
  have heq : t0+(hi-t0)=hi := by dsimp [hi]; omega
  have hDu := WrapActual.reference_Dmat_unit D hN cv hv
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 co r s l hl hls hp hsize hc hx hy
  have hG := virtual_transport_zero T hN hsq hnorm hnorm0 hp2 ho hq0 r (2*l-1) t0 (hi-t0)
    hc hv (by omega) ht0p (by rw [heq]; have := t.2; dsimp [hi]; omega)
    (by rw [heq]; exact hq) (by rw [heq]; exact hhi) hw
  dsimp only at hG
  rw [heq] at hG
  have hcolHi : ((hi:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p) := by
    simp only [hi,Nat.cast_add,ZMod.natCast_self,add_zero]
  erw [WrapActual.virtual_own_response r (2*l-1) t hb t.2 hi hcolHi d hDu] at hG
  have hcRef : ∀ a,cref a<N := by
    intro a
    rcases a with a|a
    · exact hc a.1
    · change lo<N
      dsimp [lo]
      have := t.2
      omega
  have hcol : ∀ a,colOf (p:=p) cref a=((hi:ℕ):ZMod p) := by
    intro a
    rw [hcolHi]
    rcases a with a|a
    · exact a.2
    · rfl
  have hB := WrapBalanced.commonLift_own_unit D hN cref hcRef hi hhi
  have hQr := WrapBalanced.commonLift_isUnit D hN cref hcRef
  have hMr := balanced_inverse_normalized D hN r s l hl hls hp hc hx hy t hDa
  have hcredit := WrapBalanced.actual_column_response_residue
    (fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ)) lo hi d
    hcol hB hQr hMr hG
  rw [WrapActual.balanced_moment_normalize D hN r s l hl hls hp hc hx hy t d hDa]
  rw [hcredit]
  exact (WrapActual.virtual_fibre_moment r (2*l-1) t hb t.2 d hDu).symm

section CommonRestriction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A common own block retains precisely its original common spectral diagonal. -/
theorem common_fibre_block (c : ι → ℕ) (t : ℕ) :
    blk (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)) (colOf c) ((t:ℕ):ZMod p)=
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr)
        (fun a : {a // colOf (p:=p) c a=((t:ℕ):ZMod p)} => c a.1)).map
          (algebraMap _ (GaussLoc p)) := by
  erw [← WrapActual.commonLift_submatrix c Subtype.val Subtype.val_injective]
  apply Matrix.ext
  intro i j
  have he : colOf (p:=p) c i.1=colOf c j.1 := i.2.trans j.2.symm
  change (if colOf (p:=p) c i.1=colOf c j.1 then _ else 0)=_
  rw [if_pos he]
  rfl

/-- A common own linear response is its concrete fibre response. -/
theorem common_own_restrict (c : ι → ℕ) (t : ℕ) (d : GaussLoc p)
    (hD : IsUnit (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)).det) :
    let cref := fun a : {a // colOf (p:=p) c a=((t:ℕ):ZMod p)} => c a.1
    (sOwn c t (loewRow p Fr c t) ᵥ* (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c))⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d)=
    (sOwn cref t (loewRow p Fr cref t) ᵥ*
      (Dmat cref (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref))⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (cref a)-d) := by
  intro cref
  let D := Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
  have hb : ∀ a b,colOf (p:=p) c a≠colOf c b → D a b=0 := by
    intro a b h; simp [D,Dmat,h]
  have hs : ∀ a,colOf (p:=p) c a≠((t:ℕ):ZMod p) → sOwn c t (loewRow p Fr c t) a=0 := by
    intro a h; simp [sOwn,h]
  have hloc : Dmat cref (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref)=
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cref).map (algebraMap _ (GaussLoc p)) := by
    apply Matrix.ext
    intro i j
    have he : colOf (p:=p) cref i=colOf cref j := i.2.trans j.2.symm
    simp only [Dmat,Matrix.of_apply,he,↓reduceIte,Matrix.map_apply]
  rw [own_fiber_form D (colOf c) hD hb ((t:ℕ):ZMod p)
    (sOwn c t (loewRow p Fr c t)) (fun a => ellL p Fr (c a)-d) hs]
  erw [common_fibre_block c t,hloc]
  rfl

/-- A common source moment is its concrete quadratic fibre response. -/
theorem common_moment_restrict (c : ι → ℕ) (t : ℕ) (d : GaussLoc p)
    (hD : IsUnit (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)).det) :
    fibMom c (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c))
      (fun a => ellL p Fr (c a)-d) ((t:ℕ):ZMod p)=
      res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr)
        (fun a : {a // colOf (p:=p) c a=((t:ℕ):ZMod p)} => c a.1) d) := by
  let D := Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
  let y := fun a => ellL p Fr (c a)-d
  have hb : ∀ a b,colOf (p:=p) c a≠colOf c b → D a b=0 := by
    intro a b h; simp [D,Dmat,h]
  change (∑ a∈univ.filter (fun a => colOf c a=((t:ℕ):ZMod p)),res p ((D⁻¹ *ᵥ y) a)*res p (y a))=_
  rw [WrapType.mixed_fiber_moment_response D (colOf c) hD hb ((t:ℕ):ZMod p) y y (res p)]
  erw [common_fibre_block c t]
  rfl

end CommonRestriction

/-- A credited balanced top extension has the representative common moment.
The backward direction condition follows from reversible reduced own transport. -/
theorem balanced_top_moment_credit {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (t : Fin (2*l-1))
    (hq : t0/p=(r+(t:ℕ))/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) (r+(t:ℕ)) (t0-(r+(t:ℕ)))) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let co := fun a:Fin r => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords co r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords co r s l hl hls (Sum.inl a)
    let Q := (WrapActual.reordered co r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co) t0 (loewRow p Fr co t0)
    WrapNodes.mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a)-d)
      (fun a => ellL p Fr (cc a)-d) ((r+(t:ℕ):ℕ):ZMod p)=
      fibMom co (Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co))
        (fun a => ellL p Fr (co a)-d) ((t0:ℕ):ZMod p) := by
  intro D co cr cc Q d
  let lo := r+(t:ℕ)
  let hi := r+(t:ℕ)+p
  let Qo := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
  let cref := fun a : {x:Fin r // ((x:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p)} => (a.1:ℕ)
  have hLo : lo≤t0 := by have := t.2; dsimp [lo]; omega
  have heq : lo+(t0-lo)=t0 := Nat.add_sub_of_le hLo
  have ht0N : t0<N := by omega
  have hloN : lo<N := by omega
  have hDu := WrapActual.reference_Dmat_unit D hN co hc
  have hDa := WrapActual.actual_Dmat_unit T hqp hN hsq hnorm hnorm0 co r s l hl hls hp hsize hc hx hy
  have hz := own_dir_zero Fr co Qo t0 (loewRow p Fr co t0)
    (WrapBalanced.commonLift_own_unit D hN co hc t0 ht0N)
  have hT := WrapCell.typeData_window T hN hsq hnorm hnorm0 hp2 ho hq0 r lo (t0-lo) hc
    (by dsimp [lo]; omega) (by rw [heq]; exact ht0p)
    (by rw [heq]; exact hq) (by rw [heq]; exact ht0N) hw 0
  dsimp only at hT
  rw [heq] at hT
  have hEq := WrapType.own_type_residue_eq co Qo hDu lo (loewRow p Fr co lo) d
    _ _ t0 (loewRow p Fr co t0) hT
  rw [hz,map_zero] at hEq
  have hG := hEq.symm
  erw [common_own_restrict co lo d hDu] at hG
  have hcRef : ∀ a,cref a<N := fun a => hc a.1
  have hcol : ∀ a,colOf (p:=p) cref a=((lo:ℕ):ZMod p) := fun a => a.2
  have hB := WrapBalanced.commonLift_own_unit D hN cref hcRef lo hloN
  have hQr := WrapBalanced.commonLift_isUnit D hN cref hcRef
  have hMr := balanced_inverse_normalized D hN r s l hl hls hp hc hx hy t hDa
  have hcredit := WrapBalanced.actual_border_response_residue cref lo hi d hcol hB hQr hMr hG
  have hQ : ∀ a b, a≠b → nL p Fr*(nd p (co b)-nd p (co a))*Qo a b=PF p Fr (co b)-PF p Fr (co a) := by
    rw [show Qo=WrapBalanced.commonLift (p:=p) (Fr:=Fr) co from rfl,
      WrapBalanced.commonLift_eq_core D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy]
    exact sLift_core_rel D hN co (WrapActual.xs r) (WrapActual.ys r) hc hx hy
  have hm := TypeData.fibMom_eq D co hc Qo hQ (WrapBalanced.commonLift_primitive D hN co hc)
    lo (loewRow p Fr co lo) _ _ t0 (loewRow p Fr co t0) d hT
  rw [WrapActual.balanced_moment_normalize D hN r s l hl hls hp hc hx hy t d hDa]
  rw [hcredit]
  erw [← common_moment_restrict co lo d hDu]
  exact hm.symm

/-- An ordinary credited balanced class has the original representative moment. -/
theorem balanced_moment_representative {q o : ℕ} (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) (hp2 : p≠2) (ho : (o:ZMod p)≠0) (hq0 : (q:ZMod p)≠0)
    (r s l : ℕ) (hl : 1≤l) (hls : l≤s) (hp : p=2*s+1) (hsize : r+2*(s+l)≤N)
    (hc : ∀ a:Fin r,(a:ℕ)<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (ht0p : t0<r+p) (t : Fin (2*l-1))
    (hq : (r+(t:ℕ)+p)/p=t0/p)
    (hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) t0 (r+(t:ℕ)+p-t0)) :
    let D := twoTermPoleData T hN.le hsq hnorm hnorm0
    let co := fun a:Fin r => (a:ℕ)
    let cv := fun a:Fin (r+(2*l-1)) => (a:ℕ)
    let cr := fun a => WrapActual.rowCoords co r s l hl hls (Sum.inl a)
    let cc := fun a => WrapActual.colCoords co r s l hl hls (Sum.inl a)
    let Q := (WrapActual.reordered co r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
    let d := dirOf Fr co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co) t0 (loewRow p Fr co t0)
    WrapNodes.mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a)-d)
      (fun a => ellL p Fr (cc a)-d) ((r+(t:ℕ):ℕ):ZMod p)=
      fibMom co (Dmat co (WrapBalanced.commonLift (p:=p) (Fr:=Fr) co))
        (fun a => ellL p Fr (co a)-d) ((t0:ℕ):ZMod p) := by
  intro D co cv cr cc Q d
  let hi := r+(t:ℕ)+p
  let Qv := WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv
  have hv : ∀ a:Fin (r+(2*l-1)),(a:ℕ)<N := by intro a; have := a.2; omega
  have hhiN : hi<N := by have := t.2; dsimp [hi]; omega
  have heq : t0+(hi-t0)=hi := by dsimp [hi]; omega
  have hDu := WrapActual.reference_Dmat_unit D hN cv hv
  have hDo := WrapActual.reference_Dmat_unit D hN co hc
  have hm := balanced_moment_credit T hqp hN hsq hnorm hnorm0 hp2 ho hq0 r s l hl hls hp hsize
    hc hx hy t0 ht0 ht0p t hq hw
  dsimp only at hm
  rw [hm]
  have hT := WrapCell.typeData_window T hN hsq hnorm hnorm0 hp2 ho hq0 (r+(2*l-1)) t0 (hi-t0) hv
    (by omega) (by rw [heq]; have := t.2; dsimp [hi]; omega)
    (by rw [heq]; exact hq) (by rw [heq]; exact hhiN) hw 0
  dsimp only at hT
  rw [heq] at hT
  have hQv : ∀ a b,a≠b → nL p Fr*(nd p (cv b)-nd p (cv a))*Qv a b=PF p Fr (cv b)-PF p Fr (cv a) := by
    rw [show Qv=WrapBalanced.commonLift (p:=p) (Fr:=Fr) cv from rfl,
      WrapBalanced.commonLift_eq_core D hN cv (fun i:Fin 0 => Fin.elim0 i)
        (fun i:Fin 0 => Fin.elim0 i) hv (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
    exact sLift_core_rel D hN cv _ _ hv (fun i:Fin 0 => Fin.elim0 i) (fun i:Fin 0 => Fin.elim0 i)
  have hmV := TypeData.fibMom_eq D cv hv Qv hQv (WrapBalanced.commonLift_primitive D hN cv hv)
    t0 (loewRow p Fr cv t0) _ _ hi (loewRow p Fr cv hi) d hT
  have hcolHi : ((hi:ℕ):ZMod p)=((r+(t:ℕ):ℕ):ZMod p) := by
    simp only [hi,Nat.cast_add,ZMod.natCast_self,add_zero]
  rw [hcolHi] at hmV
  rw [hmV]
  exact virtual_surplus_moment r (2*l-1) t0 (by omega) ht0p d hDu hDo

end CatalanCore.Uniform.Content.UFSimple.WrapCredit

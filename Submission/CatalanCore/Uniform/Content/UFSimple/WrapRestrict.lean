module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapKeep
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapMember

@[expose] public section

/-! # Exact restriction of the original independently ordered matrices -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapRestrict

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}
variable {ι τ κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ]

/-- Restriction of common indices preserves precisely the original
spectral diagonal and every original scaled entry. -/
theorem sLift_submatrix (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N)
    (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N) (f : τ → ι) (hf : Function.Injective f) :
    sLift (c ∘ f) xs ys (hint_of_poleData D hN (fun i => hc (f i)) hx hy)=
      (sLift c xs ys (hint_of_poleData D hN hc hx hy)).submatrix (Sum.map f id) (Sum.map f id) := by
  apply Matrix.ext; intro i j
  rw [Matrix.submatrix_apply,
    WrapActual.scaled_entry D hN (c ∘ f) xs ys (fun i => hc (f i)) hx hy i j,
    WrapActual.scaled_entry D hN c xs ys hc hx hy (Sum.map f id i) (Sum.map f id j)]
  rcases i with i|i <;> rcases j with j|j
  · simp [rowNode,colNode,Function.comp_def,Matrix.one_apply,hf.eq_iff]
  · rfl
  · rfl
  · rfl

/-- The embedding of a restricted actual mixed core. -/
def coreMap {b : ℕ} (f : τ → ι) : τ ⊕ Fin b → ι ⊕ Fin b := Sum.map f id

/-- The embedding of a restricted independently ordered full matrix. -/
def fullMap {b d : ℕ} (f : τ → ι) : (τ ⊕ Fin b) ⊕ Fin d → (ι ⊕ Fin b) ⊕ Fin d :=
  Sum.map (coreMap f) id

theorem row_diagram (f : τ → ι) (s l : ℕ) (hl : 1≤l) (hls : l≤s) :
    (Sum.map f id) ∘ WrapGeometry.rowFullEquiv τ s l hl hls=
      WrapGeometry.rowFullEquiv ι s l hl hls ∘ fullMap f := by
  funext i
  rcases i with (i|i)|i <;> rfl

theorem col_diagram (f : τ → ι) (s l : ℕ) (hl : 1≤l) (hls : l≤s) :
    (Sum.map f id) ∘ WrapGeometry.colFullEquiv τ s l hl hls=
      WrapGeometry.colFullEquiv ι s l hl hls ∘ fullMap f := by
  funext i
  rcases i with (i|i)|i <;> rfl

/-- Original common deletion commutes with the actual independent row
and column reorderings, with no witness specialization. -/
theorem reordered_submatrix (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ i,c i<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (f : τ → ι) (hf : Function.Injective f) :
    WrapActual.reordered (c ∘ f) r s l hl hls
      (hint_of_poleData D hN (fun i => hc (f i)) hx hy)=
      (WrapActual.reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)).submatrix
        (fullMap f) (fullMap f) := by
  unfold WrapActual.reordered
  rw [sLift_submatrix D hN c (WrapActual.xs r) (WrapActual.ys r) hc hx hy f hf]
  rw [Matrix.submatrix_submatrix,Matrix.submatrix_submatrix,row_diagram,col_diagram]

/-- A general restriction preserving one colour fibre preserves its
independently loaded source response, even for nonsymmetric matrices. -/
theorem mixed_moment_fibre (c : ι → ℕ) (f : τ → ι) (u : ZMod p)
    (E : {i : τ // colOf (p:=p) (c ∘ f) i=u} ≃ {i : ι // colOf (p:=p) c i=u})
    (hE : ∀ i,f i.1=(E i).1)
    (Q : Matrix ι ι (GaussLoc p)) (hQ : IsUnit Q.det)
    (hb : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0)
    (hQf : IsUnit (Q.submatrix f f).det) (yR yC : ι → GaussLoc p) :
    WrapNodes.mixedFibMom (c ∘ f) (Q.submatrix f f) (yR ∘ f) (yC ∘ f) u=
      WrapNodes.mixedFibMom c Q yR yC u := by
  have hbf : ∀ i j,colOf (p:=p) (c ∘ f) i≠colOf (c ∘ f) j →
      (Q.submatrix f f) i j=0 := fun i j hij => hb (f i) (f j) hij
  have hmat : blk (Q.submatrix f f) (colOf (c ∘ f)) u=
      (blk Q (colOf c) u).submatrix E E := by
    apply Matrix.ext; intro i j
    change Q (f i.1) (f j.1)=Q (E i).1 (E j).1
    rw [hE i,hE j]
  have hR : (fun i => yR (f i.1))=(fun i => yR i.1) ∘ E := by
    funext i; exact congrArg yR (hE i)
  have hC : (fun i => yC (f i.1))=(fun i => yC i.1) ∘ E := by
    funext i; exact congrArg yC (hE i)
  unfold WrapNodes.mixedFibMom
  erw [WrapType.mixed_fiber_moment_response (Q.submatrix f f) (colOf (c ∘ f)) hQf hbf u
    (yR ∘ f) (yC ∘ f) (res p),
    WrapType.mixed_fiber_moment_response Q (colOf c) hQ hb u yR yC (res p)]
  erw [hmat,hR,hC]
  exact congrArg (res p) (WrapTransport.response_reindex (blk Q (colOf c) u) E E
    (fun i => yR i.1) (fun i => yC i.1))

/-- Original node coordinates commute with common restriction on the
independently ordered row axis. -/
theorem rowCoords_comp (c : ι → ℕ) (f : τ → ι) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) :
    WrapActual.rowCoords (c ∘ f) r s l hl hls=
      WrapActual.rowCoords c r s l hl hls ∘ fullMap f := by
  funext i
  change rowNode (c ∘ f) (WrapActual.xs r) (WrapGeometry.rowFullEquiv τ s l hl hls i)=
    rowNode c (WrapActual.xs r) (WrapGeometry.rowFullEquiv ι s l hl hls (fullMap f i))
  have hd := congrFun (row_diagram f s l hl hls) i
  change Sum.map f id (WrapGeometry.rowFullEquiv τ s l hl hls i)=
    WrapGeometry.rowFullEquiv ι s l hl hls (fullMap f i) at hd
  rw [← hd]
  cases WrapGeometry.rowFullEquiv τ s l hl hls i <;> rfl

/-- The same exact coordinate identity on the independent column axis. -/
theorem colCoords_comp (c : ι → ℕ) (f : τ → ι) (r s l : ℕ)
    (hl : 1≤l) (hls : l≤s) :
    WrapActual.colCoords (c ∘ f) r s l hl hls=
      WrapActual.colCoords c r s l hl hls ∘ fullMap f := by
  funext i
  change colNode (c ∘ f) (WrapActual.ys r) (WrapGeometry.colFullEquiv τ s l hl hls i)=
    colNode c (WrapActual.ys r) (WrapGeometry.colFullEquiv ι s l hl hls (fullMap f i))
  have hd := congrFun (col_diagram f s l hl hls) i
  change Sum.map f id (WrapGeometry.colFullEquiv τ s l hl hls i)=
    WrapGeometry.colFullEquiv ι s l hl hls (fullMap f i) at hd
  rw [← hd]
  cases WrapGeometry.colFullEquiv τ s l hl hls i <;> rfl


/-- Untouched mixed-core fibres include all balanced coordinates and
exactly the undeleted original common coordinates. -/
def sumFibreEquiv (c : ι ⊕ κ → ℕ) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (fun i => colOf (p:=p) c (Sum.inl i))) :
    {i : WrapKeep.Keep K ⊕ κ // colOf (p:=p) (c ∘ Sum.map Subtype.val id) i=u} ≃
      {i : ι ⊕ κ // colOf (p:=p) c i=u} where
  toFun i := ⟨Sum.map Subtype.val id i.1,i.2⟩
  invFun i := match i with
    | ⟨Sum.inl j,hj⟩ => ⟨Sum.inl ⟨j,by
        intro hk
        exact hu (Finset.mem_image.mpr ⟨j,hk,hj⟩)⟩,hj⟩
    | ⟨Sum.inr j,hj⟩ => ⟨Sum.inr j,hj⟩
  left_inv i := by rcases i with ⟨i,hi⟩; cases i <;> rfl
  right_inv i := by rcases i with ⟨i,hi⟩; cases i <;> rfl

/-- Actual mixed colour-block matrices are literal principal
restrictions after a common deletion, including spectral entries. -/
theorem actual_Dmat_submatrix (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (r s l : ℕ) (hl : 1≤l) (hls : l≤s)
    (hc : ∀ i,c i<N) (hx : ∀ i:Fin (s+l),WrapActual.xs r i<N)
    (hy : ∀ i:Fin (s+l),WrapActual.ys r i<N) (f : τ → ι) (hf : Function.Injective f) :
    Dmat (fun i => WrapActual.rowCoords (c ∘ f) r s l hl hls (Sum.inl i))
      (WrapActual.reordered (c ∘ f) r s l hl hls
        (hint_of_poleData D hN (fun i => hc (f i)) hx hy)).toBlocks₁₁=
      (Dmat (fun i => WrapActual.rowCoords c r s l hl hls (Sum.inl i))
        (WrapActual.reordered c r s l hl hls (hint_of_poleData D hN hc hx hy)).toBlocks₁₁).submatrix
        (coreMap f) (coreMap f) := by
  rw [reordered_submatrix D hN c r s l hl hls hc hx hy f hf,rowCoords_comp c f r s l hl hls]
  rfl

/-- Source moments at every untouched actual colour agree before and
after common deletion. Both balanced parities are covered at once. -/
theorem actual_moment_unchanged {q o r s l : ℕ} {T : TwoTermData Fr q o}
    (H : WrapClosed.Hyp Fr q o r s l p N T)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (colOf (p:=p) c)) (d : GaussLoc p) :
    let cK := c ∘ (Subtype.val : WrapKeep.Keep K → ι)
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let AK := WrapActual.reordered cK r s l H.hl H.hls
      (hint_of_poleData H.D H.hN (fun i => hc i.1) H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let crK := fun i => WrapActual.rowCoords cK r s l H.hl H.hls (Sum.inl i)
    let ccK := fun i => WrapActual.colCoords cK r s l H.hl H.hls (Sum.inl i)
    WrapNodes.mixedFibMom crK (Dmat crK AK.toBlocks₁₁)
      (fun i => ellL p Fr (crK i)-d) (fun i => ellL p Fr (ccK i)-d) u=
    WrapNodes.mixedFibMom cr (Dmat cr A.toBlocks₁₁)
      (fun i => ellL p Fr (cr i)-d) (fun i => ellL p Fr (cc i)-d) u := by
  intro cK A AK cr cc crK ccK
  let f : WrapKeep.Keep K ⊕ Fin (2*l-1) → ι ⊕ Fin (2*l-1) :=
    coreMap (Subtype.val : WrapKeep.Keep K → ι)
  let Q := Dmat cr A.toBlocks₁₁
  have hmat : Dmat crK AK.toBlocks₁₁=Q.submatrix f f :=
    actual_Dmat_submatrix H.D H.hN c r s l H.hl H.hls hc H.xs_bound H.ys_bound
      (Subtype.val : WrapKeep.Keep K → ι) Subtype.val_injective
  have hrow : crK=cr ∘ f := by
    funext i
    exact congrFun (rowCoords_comp c (Subtype.val : WrapKeep.Keep K → ι) r s l H.hl H.hls) (Sum.inl i)
  have hcol : ccK=cc ∘ f := by
    funext i
    exact congrFun (colCoords_comp c (Subtype.val : WrapKeep.Keep K → ι) r s l H.hl H.hls) (Sum.inl i)
  have hQu : IsUnit Q.det := WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0
    c r s l H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound
  have hQK : IsUnit (Q.submatrix f f).det := by
    rw [← hmat]
    exact WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0
      cK r s l H.hl H.hls H.hp H.hsize (fun i => hc i.1) H.xs_bound H.ys_bound
  have hb : ∀ i j,colOf (p:=p) cr i≠colOf cr j → Q i j=0 := by
    intro i j hij; simp [Q,Dmat,hij]
  let E := sumFibreEquiv cr K u hu
  have hh := mixed_moment_fibre cr f u E (fun _ => rfl) Q hQu hb hQK
    (fun i => ellL p Fr (cr i)-d) (fun i => ellL p Fr (cc i)-d)
  rw [hmat,hrow,hcol]
  exact hh

/-- Common source moments at untouched colours remain equal when the
member representative direction is changed only by zero residue. -/
theorem common_moment_unchanged (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (colOf (p:=p) c)) (dK d : GaussLoc p) (hd : res p dK=res p d) :
    let cK := c ∘ (Subtype.val : WrapKeep.Keep K → ι)
    fibMom cK (Dmat cK (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cK))
      (fun i => ellL p Fr (cK i)-dK) u=
    fibMom c (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c))
      (fun i => ellL p Fr (c i)-d) u := by
  intro cK
  let f := (Subtype.val : WrapKeep.Keep K → ι)
  let Q := Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
  let QK := Dmat cK (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cK)
  have hmat : QK=Q.submatrix f f := by
    rw [show QK=Dmat (c ∘ f) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ f)) from rfl,
      ← WrapActual.commonLift_submatrix c f Subtype.val_injective]
    rfl
  have hQ := WrapActual.reference_Dmat_unit D hN c hc
  have hQK : IsUnit (Q.submatrix f f).det := by
    rw [← hmat]
    exact WrapActual.reference_Dmat_unit D hN cK (fun i => hc i.1)
  have hb : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0 := by
    intro i j hij; simp [Q,Dmat,hij]
  change WrapNodes.mixedFibMom cK QK (fun i => ellL p Fr (cK i)-dK)
    (fun i => ellL p Fr (cK i)-dK) u=
      WrapNodes.mixedFibMom c Q (fun i => ellL p Fr (c i)-d) (fun i => ellL p Fr (c i)-d) u
  rw [WrapKeep.mixed_moment_direction cK cK cK QK dK d hd u,hmat]
  exact WrapKeep.mixed_moment_unchanged c K u hu Q hQ hb hQK
    (fun i => ellL p Fr (c i)-d) (fun i => ellL p Fr (c i)-d)

/-- Use the original window's single-level data for arbitrary members. -/
def windowHyp {q o r s l : ℕ} {T : TwoTermData Fr q o}
    (W : WrapWindow.Window Fr q o r s l p N T) : WrapClosed.Hyp Fr q o r s l p N T :=
  ⟨W.hl,W.hls,W.hp,W.hqp,W.hN,W.hsize,W.hsq,W.hnorm,W.hnorm0⟩

/-- The original source normalization is retained by every untouched
member representative in the selected window. -/
theorem referenceC0_unchanged {q o r s l : ℕ} {T : TwoTermData Fr q o}
    (W : WrapWindow.Window Fr q o r s l p N T) (K : Finset (Fin r))
    (t1 : ℕ) (ht1 : W.t0≤t1 ∧ t1≤W.tv) (hp1 : t1<r+p)
    (hu1 : (t1:ZMod p)∉K.image (colOf (p:=p) (fun i:Fin r => (i:ℕ)))) :
    WrapWeights.referenceC0 p q o Fr (fun i : WrapKeep.Keep K => (i.1:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun i : WrapKeep.Keep K => (i.1:ℕ))) t1=
    WrapWeights.referenceC0 p q o Fr (fun i:Fin r => (i:ℕ))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun i:Fin r => (i:ℕ))) W.t0 := by
  let co := fun i:Fin r => (i:ℕ)
  let cK := fun i : WrapKeep.Keep K => (i.1:ℕ)
  let Qo := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
  let QK := WrapBalanced.commonLift (p:=p) (Fr:=Fr) cK
  let d := dirOf Fr co Qo W.t0 (loewRow p Fr co W.t0)
  let dK := dirOf Fr cK QK t1 (loewRow p Fr cK t1)
  have hd : res p dK=res p d := WrapMember.window_direction W K t1 ht1 hp1 hu1
  have hquiet := common_moment_unchanged W.D W.hN co W.common_bound K (t1:ZMod p) hu1 dK d hd
  have he : W.t0+(t1-W.t0)=t1 := Nat.add_sub_of_le ht1.1
  have htN : t1<N := by have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega
  have hT := WrapCell.typeData_window T W.hN W.hsq W.hnorm W.hnorm0 W.hp2 W.ho W.hq0
    r W.t0 (t1-W.t0) W.common_bound W.t0_common
    (by rw [he]; exact hp1) (by rw [he]; exact W.selected_div t1 ht1.1 ht1.2)
    (by rw [he]; exact htN) (W.selected_window t1 ht1.1 ht1.2) 0
  dsimp only at hT
  rw [he] at hT
  have hQ : ∀ i j,i≠j → nL p Fr*(nd p (co j)-nd p (co i))*Qo i j=PF p Fr (co j)-PF p Fr (co i) := by
    rw [show Qo=WrapBalanced.commonLift (p:=p) (Fr:=Fr) co from rfl,
      WrapBalanced.commonLift_eq_core W.D W.hN co (WrapActual.xs r) (WrapActual.ys r)
        W.common_bound W.xs_bound W.ys_bound]
    exact sLift_core_rel W.D W.hN co (WrapActual.xs r) (WrapActual.ys r)
      W.common_bound W.xs_bound W.ys_bound
  have hm := TypeData.fibMom_eq W.D co W.common_bound Qo hQ
    (WrapBalanced.commonLift_primitive W.D W.hN co W.common_bound) W.t0 (loewRow p Fr co W.t0)
    _ _ t1 (loewRow p Fr co t1) d hT
  have hs := WrapMember.window_step_equal W t1 W.t0 ht1 ⟨le_rfl,W.htv⟩ hp1 W.ht0p
  dsimp only [WrapWeights.referenceC0]
  erw [hquiet,hm,hs]

/-- Every untouched colour has exactly its original normalized mixed
source weight after common deletion and representative re-anchoring. -/
theorem weight_unchanged {q o r s l : ℕ} {T : TwoTermData Fr q o}
    (W : WrapWindow.Window Fr q o r s l p N T) (K : Finset (Fin r))
    (t1 : ℕ) (ht1 : W.t0≤t1 ∧ t1≤W.tv) (hp1 : t1<r+p)
    (hu1 : (t1:ZMod p)∉K.image (colOf (p:=p) (fun i:Fin r => (i:ℕ))))
    (u : ZMod p) (hu : u∉K.image (colOf (p:=p) (fun i:Fin r => (i:ℕ)))) :
    WrapWeights.actualV Fr q o (fun i : WrapKeep.Keep K => (i.1:ℕ)) r s l W.hl W.hls
      (hint_of_poleData W.D W.hN (fun i => W.common_bound i.1) W.xs_bound W.ys_bound) t1 u=W.weight u := by
  let co := fun i:Fin r => (i:ℕ)
  let cK := fun i : WrapKeep.Keep K => (i.1:ℕ)
  let Qo := WrapBalanced.commonLift (p:=p) (Fr:=Fr) co
  let QK := WrapBalanced.commonLift (p:=p) (Fr:=Fr) cK
  let d := dirOf Fr co Qo W.t0 (loewRow p Fr co W.t0)
  let dK := dirOf Fr cK QK t1 (loewRow p Fr cK t1)
  let A := WrapActual.reordered co r s l W.hl W.hls
    (hint_of_poleData W.D W.hN W.common_bound W.xs_bound W.ys_bound)
  let AK := WrapActual.reordered cK r s l W.hl W.hls
    (hint_of_poleData W.D W.hN (fun i => W.common_bound i.1) W.xs_bound W.ys_bound)
  let cr := fun i => WrapActual.rowCoords co r s l W.hl W.hls (Sum.inl i)
  let cc := fun i => WrapActual.colCoords co r s l W.hl W.hls (Sum.inl i)
  let crK := fun i => WrapActual.rowCoords cK r s l W.hl W.hls (Sum.inl i)
  let ccK := fun i => WrapActual.colCoords cK r s l W.hl W.hls (Sum.inl i)
  have hd : res p dK=res p d := WrapMember.window_direction W K t1 ht1 hp1 hu1
  have hdir := WrapKeep.mixed_moment_direction (Fr:=Fr) crK crK ccK (Dmat crK AK.toBlocks₁₁) dK d hd u
  have hquiet := actual_moment_unchanged (windowHyp W) co W.common_bound K u hu d
  have hm : WrapNodes.mixedFibMom crK (Dmat crK AK.toBlocks₁₁)
      (fun i => ellL p Fr (crK i)-dK) (fun i => ellL p Fr (ccK i)-dK) u=
    WrapNodes.mixedFibMom cr (Dmat cr A.toBlocks₁₁)
      (fun i => ellL p Fr (cr i)-d) (fun i => ellL p Fr (cc i)-d) u := hdir.trans hquiet
  have hC0 := referenceC0_unchanged W K t1 ht1 hp1 hu1
  have he := WrapBalanced.commonLift_eq_core W.D W.hN co (WrapActual.xs r) (WrapActual.ys r)
    W.common_bound W.xs_bound W.ys_bound
  have heK := WrapBalanced.commonLift_eq_core W.D W.hN cK (WrapActual.xs r) (WrapActual.ys r)
    (fun i => W.common_bound i.1) W.xs_bound W.ys_bound
  change WrapWeights.actualV Fr q o cK r s l W.hl W.hls
    (hint_of_poleData W.D W.hN (fun i => W.common_bound i.1) W.xs_bound W.ys_bound) t1 u=
      WrapWeights.actualV Fr q o co r s l W.hl W.hls
        (hint_of_poleData W.D W.hN W.common_bound W.xs_bound W.ys_bound) W.t0 u
  unfold WrapWeights.actualV
  rw [← he,← heK]
  unfold WrapResponse.mixedV
  erw [hC0,hm]

/-- The original common own-colour moment in an arbitrary direction. -/
noncomputable def ownMoment (c : ι → ℕ) (t : ℕ) (d : GaussLoc p) : GaussLoc p :=
  (ellL p Fr t-d)-(sOwn c t (loewRow p Fr c t) ᵥ*
    (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c))⁻¹) ⬝ᵥ
      (fun i => ellL p Fr (c i)-d)

/-- At an untouched colour the original own moment, hence its
first-order coupling, is unchanged after common deletion. -/
theorem ownMoment_unchanged (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (K : Finset ι) (t : ℕ)
    (hu : (t:ZMod p)∉K.image (colOf (p:=p) c))
    (dK d : GaussLoc p) (hd : res p dK=res p d) :
    res p (ownMoment (Fr:=Fr) (c ∘ (Subtype.val : WrapKeep.Keep K → ι)) t dK)=
      res p (ownMoment (Fr:=Fr) c t d) := by
  let f := (Subtype.val : WrapKeep.Keep K → ι)
  let cK := c ∘ f
  let Q := Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
  let QK := Dmat cK (WrapBalanced.commonLift (p:=p) (Fr:=Fr) cK)
  have hmat : QK=Q.submatrix f f := by
    rw [show QK=Dmat (c ∘ f) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ f)) from rfl,
      ← WrapActual.commonLift_submatrix c f Subtype.val_injective]
    rfl
  have hsOwn : sOwn cK t (loewRow p Fr cK t)=(sOwn c t (loewRow p Fr c t)) ∘ f := rfl
  have hQ := WrapActual.reference_Dmat_unit D hN c hc
  have hQK : IsUnit (Q.submatrix f f).det := by
    rw [← hmat]
    exact WrapActual.reference_Dmat_unit D hN cK (fun i => hc i.1)
  have hb : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0 := by
    intro i j hij; simp [Q,Dmat,hij]
  have hs : ∀ i,colOf (p:=p) c i≠(t:ZMod p) → sOwn c t (loewRow p Fr c t) i=0 := by
    intro i hi; simp [sOwn,hi]
  have hR := WrapKeep.own_response_unchanged c K (t:ZMod p) hu Q hQ hb hQK
    (sOwn c t (loewRow p Fr c t)) (fun i => ellL p Fr (c i)-d) hs
  change res p (ownMoment (Fr:=Fr) cK t dK)=res p (ownMoment (Fr:=Fr) c t d)
  have hresp : (sOwn cK t (loewRow p Fr cK t) ᵥ* QK⁻¹) ⬝ᵥ (fun i => ellL p Fr (cK i)-d)=
      (sOwn c t (loewRow p Fr c t) ᵥ* Q⁻¹) ⬝ᵥ (fun i => ellL p Fr (c i)-d) := by
    erw [hmat,hsOwn]
    exact hR
  calc
    _=res p (ownMoment (Fr:=Fr) cK t d) := by
      unfold ownMoment
      simp only [map_sub,RingHom.map_dotProduct,Function.comp_def,hd]
    _=_ := by
      change res p ((ellL p Fr t-d)-(sOwn cK t (loewRow p Fr cK t) ᵥ* QK⁻¹) ⬝ᵥ
        (fun i => ellL p Fr (cK i)-d))=res p ((ellL p Fr t-d)-
          (sOwn c t (loewRow p Fr c t) ᵥ* Q⁻¹) ⬝ᵥ (fun i => ellL p Fr (c i)-d))
      rw [hresp]

end CatalanCore.Uniform.Content.UFSimple.WrapRestrict

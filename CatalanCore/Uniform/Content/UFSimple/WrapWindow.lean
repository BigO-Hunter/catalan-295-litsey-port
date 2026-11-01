module

public import CatalanCore.Uniform.Content.UFSimple.WrapJBlock
public import CatalanCore.Uniform.Content.UFSimple.WrapSource

@[expose] public section

/-! # Actual wrapped window data and retained support -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapWindow

/-- Arithmetic hypotheses of a wrapped regular window. All matrix and
source data are derived below from the original two-term frame. -/
structure Window (Fr : Frame) (q o r s l p N : ℕ) (T : TwoTermData Fr q o) [Fact p.Prime] where
  hl : 1≤l
  hls : l≤s
  hp : p=2*s+1
  hqp : q<p
  hN : N<p*p
  hsize : r+2*(s+l)≤N
  hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o
  hnorm : Fr.norm∈S p
  hnorm0 : red p Fr.norm≠0
  hp2 : p≠2
  ho : (o:ZMod p)≠0
  hq0 : (q:ZMod p)≠0
  w0 : ℕ
  t0 : ℕ
  tv : ℕ
  hmax : t0=max (r+2*l-1) w0
  ht0p : t0<r+p
  htv : t0≤tv
  htvp : tv<r+(2*l-1)+p
  hwin : tv<w0+p
  hdiv : tv/p=w0/p
  hw : NoSingWin (twoTermPoleData T hN.le hsq hnorm hnorm0) w0 (tv-w0)
  hsepL : ∀ v,r+2*l-1≤v → v<t0 → ∃ k,v<k ∧ k≤t0 ∧ (p∣k ∨ p∣q*k-o)
  hsepR : ∀ v,tv<v → v<r+p → ∃ k,t0<k ∧ k≤v ∧ (p∣k ∨ p∣q*k-o)

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}

namespace Window

variable (H : Window Fr q o r s l p N T)

include H

noncomputable def D : PoleData Fr p N := twoTermPoleData T H.hN.le H.hsq H.hnorm H.hnorm0

theorem common_bound (a : Fin r) : (a:ℕ)<N := by
  have := a.2; have := H.hl; have := H.hls; have := H.hsize; omega

theorem xs_bound (i : Fin (s+l)) : WrapActual.xs r i<N := by
  change r+2*(i:ℕ)<N
  have := i.2; have := H.hsize; omega

theorem ys_bound (i : Fin (s+l)) : WrapActual.ys r i<N := by
  change r+2*(i:ℕ)+1<N
  have := i.2; have := H.hsize; omega

noncomputable def hint : ∀ i j,(p:ℚ)^2*Fr.Mn
    (rowNode (fun a:Fin r => (a:ℕ)) (WrapActual.xs r (m:=s+l)) i)
    (colNode (fun a:Fin r => (a:ℕ)) (WrapActual.ys r (m:=s+l)) j)∈LocRing p :=
  hint_of_poleData H.D H.hN H.common_bound H.xs_bound H.ys_bound

noncomputable def original := sLift (fun a:Fin r => (a:ℕ)) (WrapActual.xs r) (WrapActual.ys r) H.hint
noncomputable def matrix := WrapActual.reordered (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hint
noncomputable def row := fun a => WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls (Sum.inl a)
noncomputable def col := fun a => WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls (Sum.inl a)
noncomputable def rowBorder := fun a => WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls (Sum.inr a)
noncomputable def colBorder := fun a => WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls (Sum.inr a)
noncomputable def direction := dirOf Fr (fun a:Fin r => (a:ℕ)) H.original.toBlocks₁₁ H.t0
  (loewRow p Fr (fun a:Fin r => (a:ℕ)) H.t0)
noncomputable def C0 := WrapWeights.referenceC0 p q o Fr (fun a:Fin r => (a:ℕ)) H.original.toBlocks₁₁ H.t0
noncomputable def weight := WrapWeights.actualV Fr q o (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hint H.t0
noncomputable def constant := res p (algebraMap _ (GaussLoc p) (nL p Fr))*
  (-(rfH p (cauchyH (wT p q o) ((H.t0:ℕ):ZMod p)))*(rfH p (red p Fr.norm))⁻¹)

open Classical in
noncomputable def Jr : Finset (Fin (s+1-l)) := univ.filter (fun i => H.t0≤H.rowBorder i ∧ H.rowBorder i≤H.tv)
open Classical in
noncomputable def Jc : Finset (Fin (s+1-l)) := univ.filter (fun i => H.t0≤H.colBorder i ∧ H.colBorder i≤H.tv)
open Classical in
noncomputable def TC : Finset (Fin (s+1-l)) := univ.filter (fun i => H.colBorder i<H.t0 ∨ H.tv<H.colBorder i)
open Classical in
noncomputable def TR : Finset (Fin (s+1-l)) := univ.filter (fun i => H.rowBorder i<H.t0 ∨ H.tv<H.rowBorder i)
open Classical in
noncomputable def TR' : Finset (Fin (s+1-l)) := H.TR.filter (fun i => H.weight ((H.rowBorder i:ℕ):ZMod p)≠0)

theorem t0_lower : r+2*l-1≤H.t0 := by have := H.hmax; omega
theorem t0_common : r≤H.t0 := by have := H.t0_lower; have := H.hl; omega
theorem t0_bound : H.t0<N := by have := H.ht0p; have := H.hp; have := H.hsize; have := H.hl; have := H.hls; omega

theorem rowBorder_eq (i : Fin (s+1-l)) : H.rowBorder i=(r+2*l-1)+2*(i:ℕ)+1 :=
  WrapGeometry.surplus_row_node r l i H.hl

theorem colBorder_eq (i : Fin (s+1-l)) : H.colBorder i=(r+2*l-1)+2*(i:ℕ) :=
  WrapGeometry.surplus_col_node r l i H.hl

theorem rowBorder_range (i : Fin (s+1-l)) : r+2*l-1≤H.rowBorder i ∧ H.rowBorder i<r+p := by
  rw [H.rowBorder_eq]
  have := i.2; have := H.hp; have := H.hl; have := H.hls; omega

theorem colBorder_range (i : Fin (s+1-l)) : r+2*l-1≤H.colBorder i ∧ H.colBorder i<r+p := by
  rw [H.colBorder_eq]
  have := i.2; have := H.hp; have := H.hl; have := H.hls; omega

theorem row_bound (i : Fin r ⊕ Fin (2*l-1)) : H.row i<N :=
  WrapCoupling.rowCoords_lt (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.common_bound H.xs_bound H.ys_bound (Sum.inl i)

theorem col_bound (i : Fin r ⊕ Fin (2*l-1)) : H.col i<N :=
  WrapCoupling.colCoords_lt (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.common_bound H.xs_bound H.ys_bound (Sum.inl i)

theorem rowBorder_bound (i : Fin (s+1-l)) : H.rowBorder i<N :=
  WrapCoupling.rowCoords_lt (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.common_bound H.xs_bound H.ys_bound (Sum.inr i)

theorem colBorder_bound (i : Fin (s+1-l)) : H.colBorder i<N :=
  WrapCoupling.colCoords_lt (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.common_bound H.xs_bound H.ys_bound (Sum.inr i)

theorem commutator (i j : (Fin r ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) :
    nL p Fr*(nd p (colNode H.col H.colBorder j)-nd p (rowNode H.row H.rowBorder i))*H.matrix i j=
      PF p Fr (colNode H.col H.colBorder j)-PF p Fr (rowNode H.row H.rowBorder i) := by
  have hr : rowNode H.row H.rowBorder=WrapActual.rowCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls := by
    funext i; cases i <;> rfl
  have hc : colNode H.col H.colBorder=WrapActual.colCoords (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls := by
    funext i; cases i <;> rfl
  rw [hr,hc]
  exact WrapActual.reordered_commutator H.D H.hN (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.common_bound H.xs_bound H.ys_bound i j

theorem primitive : phiP p H.matrix.toBlocks₁₁.det≠0 :=
  WrapActual.core_primitive T H.hqp H.hN H.hsq H.hnorm H.hnorm0 (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp H.hsize H.hint

theorem schur : H.matrix.toBlocks₁₁.det • H.matrix.toBlocks₂₂-
    H.matrix.toBlocks₂₁*H.matrix.toBlocks₁₁.adjugate*H.matrix.toBlocks₁₂=
      Polynomial.C ((p:ℕ):LocRing p) • WrapSchur.dividedSchur H.matrix :=
  WrapActual.schur_eq T H.hqp H.hN H.hsq H.hnorm H.hnorm0 (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound

theorem distinct (i j : Fin (s+1-l)) : ((H.rowBorder i:ℕ):ZMod p)≠((H.colBorder j:ℕ):ZMod p) :=
  WrapActual.surplus_colours (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp i j

theorem weight_zero (n : ℕ) (hn0 : H.w0≤n) (hntv : n≤H.tv) : H.weight ((n:ℕ):ZMod p)=0 :=
  WrapWeights.credited_V_zero T H.hqp H.hN H.hsq H.hnorm H.hnorm0 H.hp2 H.ho H.hq0 r s l H.hl H.hls H.hp H.hsize
    H.common_bound H.xs_bound H.ys_bound H.w0 H.t0 H.tv H.hmax H.ht0p H.htv H.htvp H.hwin H.hdiv H.hw n hn0 hntv

theorem selected_div (n : ℕ) (hn0 : H.t0≤n) (hntv : n≤H.tv) : n/p=H.t0/p := by
  have hw0 : H.w0≤H.t0 := by have := H.hmax; omega
  have ht : H.t0/p=H.w0/p := div_eq_of_between hw0 H.htv H.hdiv
  exact (div_eq_of_between (by omega : H.w0≤n) hntv H.hdiv).trans ht.symm

theorem selected_window (n : ℕ) (hn0 : H.t0≤n) (hntv : n≤H.tv) : NoSingWin H.D H.t0 (n-H.t0) := by
  intro k hk1 hk2
  apply H.hw k (by have := H.hmax; omega)
  have := H.hmax
  omega

/-- The actual selected row moments have the normalized Cauchy source. -/
theorem row_source (z : Fin (s+1-l)) (hz : z∈H.Jr) : ∃ Φ : GaussLoc p,
    algebraMap _ (GaussLoc p) (rowMomB H.matrix Fr H.row H.rowBorder z)=
      algebraMap _ (GaussLoc p) (rowMomA H.matrix z)*
        (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*H.direction)+
          CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
    res p Φ=H.constant+hDer (retOf H.weight) H.weight ((H.rowBorder z:ℕ):ZMod p) := by
  have hz' := (Finset.mem_filter.1 hz).2
  have heq : H.t0+(H.rowBorder z-H.t0)=H.rowBorder z := Nat.add_sub_of_le hz'.1
  have hh := WrapCell.actual_row_moment_source T H.hqp H.hN H.hsq H.hnorm H.hnorm0 H.hp2 H.ho H.hq0
    r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.t0 (H.rowBorder z-H.t0)
    H.t0_lower (by rw [heq]; exact (H.rowBorder_range z).2)
    (by rw [heq]; exact H.selected_div _ hz'.1 hz'.2) (by rw [heq]; exact H.rowBorder_bound z)
    (H.selected_window _ hz'.1 hz'.2) H.C0 z heq
  dsimp only at hh
  obtain ⟨Φ,h1,h2⟩ := hh
  refine ⟨Φ,h1,?_⟩
  have h2' : res p Φ=H.constant+hDer univ H.weight ((H.rowBorder z:ℕ):ZMod p) := by
    simpa only [heq,weight,constant,C0,matrix,original,hint,D,WrapWeights.actualV] using h2
  rwa [hDer_retOf] at h2'

/-- An outside selected-row node has a nonzero actual coupling. -/
theorem kill_row (z : Fin (s+1-l)) (hz : z∈H.TR) :
    wedgeR H.matrix Fr H.row H.rowBorder H.direction z≠0 := by
  have hz' := (Finset.mem_filter.1 hz).2
  have hrange := H.rowBorder_range z
  dsimp only [rowBorder] at hz' hrange
  have ht := H.t0_common
  have hl := H.hl
  have ht0p := H.ht0p
  have htv := H.htv
  apply WrapCoupling.actual_row_wedge_ne_of_sep T H.hqp H.hN H.hsq H.hnorm H.hnorm0
    (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound
    H.t0 H.t0_bound z
  rcases hz' with hz'|hz'
  · exact Or.inr ⟨hz',by omega,H.hsepL _ hrange.1 hz'⟩
  · exact Or.inl ⟨by omega,by omega,H.hsepR _ hz' hrange.2⟩

/-- A selected row node has zero actual source weight. -/
theorem Jr_zero (z : Fin (s+1-l)) (hz : z∈H.Jr) : H.weight ((H.rowBorder z:ℕ):ZMod p)=0 := by
  have hz' := (Finset.mem_filter.1 hz).2
  exact H.weight_zero _ (by have := H.hmax; omega) hz'.2

/-- The actual selected col moments have the normalized Cauchy source. -/
theorem col_source (z : Fin (s+1-l)) (hz : z∈H.Jc) : ∃ Φ : GaussLoc p,
    algebraMap _ (GaussLoc p) (colMomB H.matrix Fr H.col H.colBorder z)=
      algebraMap _ (GaussLoc p) (colMomA H.matrix z)*
        (CatalanCore.Uniform.Content.UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*H.direction)+
          CatalanCore.Uniform.Content.UFMoments.piL p^2*Φ) ∧
    res p Φ=H.constant+hDer (retOf H.weight) H.weight ((H.colBorder z:ℕ):ZMod p) := by
  have hz' := (Finset.mem_filter.1 hz).2
  have heq : H.t0+(H.colBorder z-H.t0)=H.colBorder z := Nat.add_sub_of_le hz'.1
  have hh := WrapCell.actual_col_moment_source T H.hqp H.hN H.hsq H.hnorm H.hnorm0 H.hp2 H.ho H.hq0
    r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.t0 (H.colBorder z-H.t0)
    H.t0_lower (by rw [heq]; exact (H.colBorder_range z).2)
    (by rw [heq]; exact H.selected_div _ hz'.1 hz'.2) (by rw [heq]; exact H.colBorder_bound z)
    (H.selected_window _ hz'.1 hz'.2) H.C0 z heq
  dsimp only at hh
  obtain ⟨Φ,h1,h2⟩ := hh
  refine ⟨Φ,h1,?_⟩
  have h2' : res p Φ=H.constant+hDer univ H.weight ((H.colBorder z:ℕ):ZMod p) := by
    simpa only [heq,weight,constant,C0,matrix,original,hint,D,WrapWeights.actualV] using h2
  rwa [hDer_retOf] at h2'

/-- An outside selected-col node has a nonzero actual coupling. -/
theorem kill_col (z : Fin (s+1-l)) (hz : z∈H.TC) :
    wedgeC H.matrix Fr H.col H.colBorder H.direction z≠0 := by
  have hz' := (Finset.mem_filter.1 hz).2
  have hrange := H.colBorder_range z
  dsimp only [colBorder] at hz' hrange
  have ht := H.t0_common
  have hl := H.hl
  have ht0p := H.ht0p
  have htv := H.htv
  apply WrapCoupling.actual_col_wedge_ne_of_sep T H.hqp H.hN H.hsq H.hnorm H.hnorm0
    (fun a:Fin r => (a:ℕ)) r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound
    H.t0 H.t0_bound z
  rcases hz' with hz'|hz'
  · exact Or.inr ⟨hz',by omega,H.hsepL _ hrange.1 hz'⟩
  · exact Or.inl ⟨by omega,by omega,H.hsepR _ hz' hrange.2⟩

/-- A selected col node has zero actual source weight. -/
theorem Jc_zero (z : Fin (s+1-l)) (hz : z∈H.Jc) : H.weight ((H.colBorder z:ℕ):ZMod p)=0 := by
  have hz' := (Finset.mem_filter.1 hz).2
  exact H.weight_zero _ (by have := H.hmax; omega) hz'.2

theorem Jr_eq : H.Jr=WrapCell.rows (r+2*l-1) (s+1-l) H.t0 H.tv := by
  classical
  ext z
  simp only [Jr,WrapCell.rows,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [H.rowBorder_eq]

theorem Jc_eq : H.Jc=WrapCell.cols (r+2*l-1) (s+1-l) H.t0 H.tv := by
  classical
  ext z
  simp only [Jc,WrapCell.cols,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [H.colBorder_eq]

theorem selected_card : H.Jr.card+H.Jc.card=min (H.tv+1) ((r+2*l-1)+2*(s+1-l))-H.t0 := by
  rw [H.Jr_eq,H.Jc_eq]
  exact WrapCell.rows_add_cols _ _ _ _ H.t0_lower

open Classical in
noncomputable def Iset : Finset (ZMod p) := (Finset.Icc H.w0 H.tv).image (fun n:ℕ => ((n:ℕ):ZMod p))

theorem Iset_zero : ∀ u∈H.Iset,H.weight u=0 := by
  intro u hu
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.1 hu
  exact H.weight_zero n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2

/-- Every outside virtual-border colour is an actual row or column kill. -/
theorem outside_sub :
    (outNodes p (r+2*l-1) (s+1-l) H.w0 H.tv).image (fun n:ℕ => ((n:ℕ):ZMod p)) ⊆
      H.TC.image (fun z => ((H.colBorder z:ℕ):ZMod p)) ∪
        H.TR.image (fun z => ((H.rowBorder z:ℕ):ZMod p)) := by
  classical
  intro u hu
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨⟨hv0,hv1⟩,hvout⟩ := mem_outNodes.1 hv
  have hout : v<H.t0 ∨ H.tv<v := by
    by_contra hn
    have hwt : H.w0≤H.t0 := by have := H.hmax; omega
    exact hvout ⟨v,Finset.mem_Icc.2 ⟨by omega,by omega⟩,rfl⟩
  let a := r+2*l-1
  let j : Fin (s+1-l) := ⟨(v-a)/2,by dsimp only [a]; omega⟩
  have hmod : (v-a)%2=0 ∨ (v-a)%2=1 := by omega
  rcases hmod with hmod|hmod
  · have he : H.colBorder j=v := by rw [H.colBorder_eq]; dsimp only [j,a] at *; omega
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨j,Finset.mem_filter.2 ⟨Finset.mem_univ _,by rwa [he]⟩,by rw [he]⟩
  · have he : H.rowBorder j=v := by rw [H.rowBorder_eq]; dsimp only [j,a] at *; omega
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨j,Finset.mem_filter.2 ⟨Finset.mem_univ _,by rwa [he]⟩,by rw [he]⟩

/-- Complete actual retained-source bound in the closed arithmetic form. -/
theorem retained_bound :
    (retOf H.weight \ (H.TC.image (fun z => ((H.colBorder z:ℕ):ZMod p)) ∪
      H.TR'.image (fun z => ((H.rowBorder z:ℕ):ZMod p)))).card≤
    p-((H.tv+1-H.w0)+(2*(s+1-l)-beta3 (s+1-l) (r+2*l-1) p H.w0 H.tv)) := by
  classical
  have hc := WrapJBlock.retained_union_bound H.weight H.Iset H.TC H.TR
    (fun z => ((H.rowBorder z:ℕ):ZMod p)) (fun z => ((H.colBorder z:ℕ):ZMod p)) H.Iset_zero
  dsimp only at hc
  have hcard := WrapCell.residue_union_count (p:=p) (r+2*l-1) (s+1-l) H.w0 H.tv H.hwin
    (by have := H.hp; have := H.hl; have := H.hls; omega)
    (by have := H.hmax; have := H.htv; have := H.hwin; have := H.hp; have := H.hl; have := H.hls; omega)
    (by have := H.htvp; have := H.hl; have : 0<p := (Fact.out : p.Prime).pos; omega)
  have hsub : H.Iset ∪ (outNodes p (r+2*l-1) (s+1-l) H.w0 H.tv).image
      (fun n:ℕ => ((n:ℕ):ZMod p)) ⊆ H.Iset ∪
        (H.TC.image (fun z => ((H.colBorder z:ℕ):ZMod p)) ∪ H.TR.image (fun z => ((H.rowBorder z:ℕ):ZMod p))) :=
    Finset.union_subset_union_right H.outside_sub
  have hc2 := Finset.card_le_card hsub
  have hU := hcard.trans hc2
  exact hc.trans (Nat.sub_le_sub_left hU p)

open Classical in
/-- Actual divided Schur J-block with all outside coupling kills. -/
noncomputable def jblock : JBlockKill (WrapSchur.dividedSchur H.matrix) :=
  WrapJBlock.jblock_kill_of_local H.D H.matrix (WrapSchur.dividedSchur H.matrix)
    H.row H.col H.rowBorder H.colBorder H.row_bound H.col_bound H.rowBorder_bound H.colBorder_bound
    H.commutator H.primitive H.schur H.distinct H.Jr H.Jc (retOf H.weight) H.weight H.direction H.constant
    H.row_source H.col_source H.Jr_zero H.Jc_zero H.TC H.TR' H.kill_col
    (fun z hz => H.kill_row z (Finset.mem_filter.1 hz).1) (fun z hz => (Finset.mem_filter.1 hz).2)

theorem jblock_rows : H.jblock.Jr=H.Jr := rfl
theorem jblock_cols : H.jblock.Jc=H.Jc := rfl

theorem jblock_count : H.jblock.sJ=
    (retOf H.weight \ (H.TC.image (fun z => ((H.colBorder z:ℕ):ZMod p)) ∪
      H.TR'.image (fun z => ((H.rowBorder z:ℕ):ZMod p)))).card := rfl

theorem jblock_bound : H.jblock.sJ≤
    p-((H.tv+1-H.w0)+(2*(s+1-l)-beta3 (s+1-l) (r+2*l-1) p H.w0 H.tv)) := by
  rw [H.jblock_count]
  exact H.retained_bound

/-- Two-level data of the actual divided Schur complement. -/
noncomputable def data : TwoLevelData (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
    (WrapSchur.dividedSchur H.matrix) (H.Jr.card+H.Jc.card-(s+1-l)) H.jblock.sJ := by
  classical
  have hh := H.jblock.twoLevel
  rw [H.jblock_rows,H.jblock_cols,Fintype.card_fin] at hh
  exact Classical.choice hh

/-- Three-level witness of the original scaled determinant in its actual
independent row/column ordering. -/
noncomputable def witness :=
  WrapActual.witness_of_data T H.hqp H.hN H.hsq H.hnorm H.hnorm0 (fun a:Fin r => (a:ℕ))
    r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.data

theorem witness_price : H.witness.price=2*(r+s+l)-((s+1-l)+
    ((H.Jr.card+H.Jc.card-(s+1-l))+((H.Jr.card+H.Jc.card-(s+1-l))-H.jblock.sJ))) := by
  simpa only [witness,Fintype.card_fin] using
    (WrapActual.witness_of_data_price T H.hqp H.hN H.hsq H.hnorm H.hnorm0 (fun a:Fin r => (a:ℕ))
      r s l H.hl H.hls H.hp H.hsize H.common_bound H.xs_bound H.ys_bound H.data)

/-- Closed wrapped price of the actual original matrix. -/
theorem price_le : H.witness.price≤closedBound (s+1-l) (r+2*l-1) p H.t0 H.tv H.w0 := by
  rw [H.witness_price]
  unfold closedBound
  rw [← H.selected_card]
  have hb := H.jblock_bound
  have hl := H.hl
  have hls := H.hls
  omega


end Window

end CatalanCore.Uniform.Content.UFSimple.WrapWindow

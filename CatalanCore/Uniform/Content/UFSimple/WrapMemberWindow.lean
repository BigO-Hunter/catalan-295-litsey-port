module

public import CatalanCore.Uniform.Content.UFSimple.WrapMemberSource
public import CatalanCore.Uniform.Content.UFSimple.WrapMemberCoupling
public import CatalanCore.Uniform.Content.UFSimple.WrapSingle
public import CatalanCore.Uniform.Content.UFSimple.WrapMemberCount

@[expose] public section

/-! # Actual original member data at an untouched window representative -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMemberWindow

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}

/-- A surviving actual selected representative; its existence follows
from a positive surviving sigma by WrapMemberCount.representative_exists. -/
structure Setup (W : WrapWindow.Window Fr q o r s l p N T) where
  deleted : Finset (Fin r)
  rep : ℕ
  hrep : W.t0≤rep ∧ rep≤W.tv
  hrepp : rep<r+p
  hunedited : (rep:ZMod p)∉WrapMemberCount.edited deleted

namespace Setup

variable {W : WrapWindow.Window Fr q o r s l p N T} (M : Setup W)
include M

def H (_M : Setup W) : WrapClosed.Hyp Fr q o r s l p N T := WrapRestrict.windowHyp W

def common : WrapKeep.Keep M.deleted → ℕ := fun i => (i.1:ℕ)

theorem common_bound (i : WrapKeep.Keep M.deleted) : M.common i<N := W.common_bound i.1

noncomputable def hint : ∀ i j,(p:ℚ)^2*Fr.Mn
    (rowNode M.common (WrapActual.xs r (m:=s+l)) i)
    (colNode M.common (WrapActual.ys r (m:=s+l)) j)∈LocRing p :=
  hint_of_poleData W.D W.hN M.common_bound W.xs_bound W.ys_bound

noncomputable def original := sLift M.common (WrapActual.xs r) (WrapActual.ys r) M.hint
noncomputable def matrix := WrapActual.reordered M.common r s l W.hl W.hls M.hint
noncomputable def row := fun i => WrapActual.rowCoords M.common r s l W.hl W.hls (Sum.inl i)
noncomputable def col := fun i => WrapActual.colCoords M.common r s l W.hl W.hls (Sum.inl i)
noncomputable def rowBorder (_M : Setup W) := W.rowBorder
noncomputable def colBorder (_M : Setup W) := W.colBorder
noncomputable def direction := dirOf Fr M.common (WrapBalanced.commonLift (p:=p) (Fr:=Fr) M.common)
  M.rep (loewRow p Fr M.common M.rep)
noncomputable def C0 := WrapWeights.referenceC0 p q o Fr M.common
  (WrapBalanced.commonLift (p:=p) (Fr:=Fr) M.common) M.rep
noncomputable def V := fun u => rfH p (wT p q o u)*(rfH p (red p Fr.norm))⁻¹-M.C0
noncomputable def constant := res p (algebraMap _ (GaussLoc p) (nL p Fr))*
  (-(∑ u : ZMod p,M.V u*rfH p (u-(M.rep:ZMod p))⁻¹))
noncomputable def weight := WrapWeights.actualV Fr q o M.common r s l W.hl W.hls M.hint M.rep
noncomputable def Jr := WrapMemberCount.rows W M.deleted
noncomputable def Jc := WrapMemberCount.cols W M.deleted
open Classical in
noncomputable def TC := univ.filter (fun z => wedgeC M.matrix Fr M.col M.colBorder M.direction z≠0)
open Classical in
noncomputable def TR := univ.filter (fun z => wedgeR M.matrix Fr M.row M.rowBorder M.direction z≠0 ∧
  M.weight (M.rowBorder z:ZMod p)≠0)

/-- The source uses the original member's own common matrix. -/
theorem commonCore_eq : WrapBalanced.commonLift (p:=p) (Fr:=Fr) M.common=M.original.toBlocks₁₁ :=
  WrapBalanced.commonLift_eq_core W.D W.hN M.common (WrapActual.xs r) (WrapActual.ys r)
    M.common_bound W.xs_bound W.ys_bound

theorem weight_eq : M.weight=WrapResponse.mixedV Fr M.row M.col M.matrix.toBlocks₁₁ M.direction M.V := by
  unfold weight WrapWeights.actualV direction V C0
  dsimp only
  erw [← M.commonCore_eq]
  rfl

theorem rep_lower : r+2*l-1≤M.rep := by have := W.t0_lower; have := M.hrep; omega

theorem rep_bound : M.rep<N := by
  have := M.hrepp; have := W.hp; have := W.hl; have := W.hls; have := W.hsize; omega

theorem row_bound (i : WrapKeep.Keep M.deleted ⊕ Fin (2*l-1)) : M.row i<N :=
  WrapCoupling.rowCoords_lt M.common r s l W.hl W.hls M.common_bound W.xs_bound W.ys_bound (Sum.inl i)

theorem col_bound (i : WrapKeep.Keep M.deleted ⊕ Fin (2*l-1)) : M.col i<N :=
  WrapCoupling.colCoords_lt M.common r s l W.hl W.hls M.common_bound W.xs_bound W.ys_bound (Sum.inl i)

theorem rowBorder_bound (i : Fin (s+1-l)) : M.rowBorder i<N := W.rowBorder_bound i

theorem colBorder_bound (i : Fin (s+1-l)) : M.colBorder i<N := W.colBorder_bound i

theorem row_coords : rowNode M.row M.rowBorder=WrapActual.rowCoords M.common r s l W.hl W.hls := by
  funext i; cases i <;> rfl

theorem col_coords : colNode M.col M.colBorder=WrapActual.colCoords M.common r s l W.hl W.hls := by
  funext i; cases i <;> rfl

theorem commutator (i j : (WrapKeep.Keep M.deleted ⊕ Fin (2*l-1)) ⊕ Fin (s+1-l)) :
    nL p Fr*(nd p (colNode M.col M.colBorder j)-nd p (rowNode M.row M.rowBorder i))*M.matrix i j=
      PF p Fr (colNode M.col M.colBorder j)-PF p Fr (rowNode M.row M.rowBorder i) := by
  rw [M.row_coords,M.col_coords]
  exact WrapActual.reordered_commutator W.D W.hN M.common r s l W.hl W.hls
    M.common_bound W.xs_bound W.ys_bound i j

theorem primitive : phiP p M.matrix.toBlocks₁₁.det≠0 :=
  WrapActual.core_primitive T W.hqp W.hN W.hsq W.hnorm W.hnorm0 M.common r s l W.hl W.hls W.hp W.hsize M.hint

theorem schur : M.matrix.toBlocks₁₁.det • M.matrix.toBlocks₂₂-
    M.matrix.toBlocks₂₁*M.matrix.toBlocks₁₁.adjugate*M.matrix.toBlocks₁₂=
      Polynomial.C ((p:ℕ):LocRing p) • WrapSchur.dividedSchur M.matrix :=
  WrapActual.schur_eq T W.hqp W.hN W.hsq W.hnorm W.hnorm0 M.common r s l W.hl W.hls W.hp W.hsize
    M.common_bound W.xs_bound W.ys_bound

theorem distinct (i j : Fin (s+1-l)) : (M.rowBorder i:ZMod p)≠(M.colBorder j:ZMod p) := W.distinct i j

/-- Every untouched selected node has the re-anchored original member
joint type, with the actual normalized source used above. -/
theorem type_data (t : ℕ) (ht : W.t0≤t ∧ t≤W.tv) (htp : t<r+p)
    (hu : (t:ZMod p)∉WrapMemberCount.edited M.deleted) :
    TypeData Fr M.common (WrapBalanced.commonLift (p:=p) (Fr:=Fr) M.common)
      M.rep (loewRow p Fr M.common M.rep)
      (-(∑ u : ZMod p,M.V u*rfH p (u-(M.rep:ZMod p))⁻¹)) M.V t (loewRow p Fr M.common t) :=
  WrapMember.window_type_data W M.deleted M.rep t M.hrep ht M.hrepp htp M.hunedited hu M.C0

/-- Original row moments of the actual member have the normalized
second-order source at every surviving selected row. -/
theorem row_source (z : Fin (s+1-l)) (hz : z∈M.Jr) : ∃ Phi : GaussLoc p,
    algebraMap _ (GaussLoc p) (rowMomB M.matrix Fr M.row M.rowBorder z)=
      algebraMap _ (GaussLoc p) (rowMomA M.matrix z)*
        (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*M.direction)+UFMoments.piL p^2*Phi) ∧
    res p Phi=M.constant+hDer (retOf M.weight) M.weight (M.rowBorder z:ZMod p) := by
  have hz' := Finset.mem_filter.mp hz
  have hsel := (Finset.mem_filter.mp hz'.1).2
  have hrange := W.rowBorder_range z
  have hT := M.type_data (M.rowBorder z) hsel hrange.2 hz'.2
  have hh := WrapMemberSource.row_moment_source M.H M.common M.common_bound M.rep (M.rowBorder z)
    M.rep_lower M.hrepp hrange.1 hrange.2
    (-(∑ u : ZMod p,M.V u*rfH p (u-(M.rep:ZMod p))⁻¹)) M.V z rfl hT
  obtain ⟨Phi,h1,h2⟩ := hh
  refine ⟨Phi,h1,?_⟩
  have h2' : res p Phi=M.constant+hDer univ M.weight (M.rowBorder z:ZMod p) := by
    rw [M.weight_eq]
    unfold constant
    convert h2 using 1 <;> rfl
  rwa [hDer_retOf] at h2'

/-- The independent column moments use the same member source. -/
theorem col_source (z : Fin (s+1-l)) (hz : z∈M.Jc) : ∃ Phi : GaussLoc p,
    algebraMap _ (GaussLoc p) (colMomB M.matrix Fr M.col M.colBorder z)=
      algebraMap _ (GaussLoc p) (colMomA M.matrix z)*
        (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*M.direction)+UFMoments.piL p^2*Phi) ∧
    res p Phi=M.constant+hDer (retOf M.weight) M.weight (M.colBorder z:ZMod p) := by
  have hz' := Finset.mem_filter.mp hz
  have hsel := (Finset.mem_filter.mp hz'.1).2
  have hrange := W.colBorder_range z
  have hT := M.type_data (M.colBorder z) hsel hrange.2 hz'.2
  have hh := WrapMemberSource.col_moment_source M.H M.common M.common_bound M.rep (M.colBorder z)
    M.rep_lower M.hrepp hrange.1 hrange.2
    (-(∑ u : ZMod p,M.V u*rfH p (u-(M.rep:ZMod p))⁻¹)) M.V z rfl hT
  obtain ⟨Phi,h1,h2⟩ := hh
  refine ⟨Phi,h1,?_⟩
  have h2' : res p Phi=M.constant+hDer univ M.weight (M.colBorder z:ZMod p) := by
    rw [M.weight_eq]
    unfold constant
    convert h2 using 1 <;> rfl
  rwa [hDer_retOf] at h2'

theorem Jr_zero (z : Fin (s+1-l)) (hz : z∈M.Jr) : M.weight (M.rowBorder z:ZMod p)=0 := by
  have hz' := Finset.mem_filter.mp hz
  have hsel := (Finset.mem_filter.mp hz'.1).2
  have hrange := W.rowBorder_range z
  have hT := M.type_data (M.rowBorder z) hsel hrange.2 hz'.2
  exact WrapMemberSource.selected_weight_zero M.H M.common M.common_bound M.rep (M.rowBorder z)
    hrange.1 hrange.2 _ M.V hT
    (WrapMember.window_step_equal W (M.rowBorder z) M.rep hsel M.hrep hrange.2 M.hrepp)

theorem Jc_zero (z : Fin (s+1-l)) (hz : z∈M.Jc) : M.weight (M.colBorder z:ZMod p)=0 := by
  have hz' := Finset.mem_filter.mp hz
  have hsel := (Finset.mem_filter.mp hz'.1).2
  have hrange := W.colBorder_range z
  have hT := M.type_data (M.colBorder z) hsel hrange.2 hz'.2
  exact WrapMemberSource.selected_weight_zero M.H M.common M.common_bound M.rep (M.colBorder z)
    hrange.1 hrange.2 _ M.V hT
    (WrapMember.window_step_equal W (M.colBorder z) M.rep hsel M.hrep hrange.2 M.hrepp)

theorem kill_col (z : Fin (s+1-l)) (hz : z∈M.TC) : wedgeC M.matrix Fr M.col M.colBorder M.direction z≠0 := by
  classical
  exact (Finset.mem_filter.mp hz).2

theorem kill_row (z : Fin (s+1-l)) (hz : z∈M.TR) : wedgeR M.matrix Fr M.row M.rowBorder M.direction z≠0 := by
  classical
  exact (Finset.mem_filter.mp hz).2.1

theorem kill_weight (z : Fin (s+1-l)) (hz : z∈M.TR) : M.weight (M.rowBorder z:ZMod p)≠0 := by
  classical
  exact (Finset.mem_filter.mp hz).2.2

open Classical in
/-- Actual member J-block: every source and kill supplier is derived
from the original matrix, not supplied as an abstract content assumption. -/
noncomputable def jblock : JBlockKill (WrapSchur.dividedSchur M.matrix) :=
  WrapJBlock.jblock_kill_of_local W.D M.matrix (WrapSchur.dividedSchur M.matrix)
    M.row M.col M.rowBorder M.colBorder M.row_bound M.col_bound M.rowBorder_bound M.colBorder_bound
    M.commutator M.primitive M.schur M.distinct M.Jr M.Jc (retOf M.weight) M.weight M.direction M.constant
    M.row_source M.col_source M.Jr_zero M.Jc_zero M.TC M.TR M.kill_col M.kill_row M.kill_weight

open Classical in
noncomputable def retained := retOf M.weight \ (M.TC.image (fun z => (M.colBorder z:ZMod p)) ∪
  M.TR.image (fun z => (M.rowBorder z:ZMod p)))

theorem jblock_rows : M.jblock.Jr=M.Jr := rfl

theorem jblock_cols : M.jblock.Jc=M.Jc := rfl

theorem jblock_count : M.jblock.sJ=M.retained.card := rfl

noncomputable def data : TwoLevelData (phiP p) (Polynomial.C ((p:ℕ):LocRing p))
    (WrapSchur.dividedSchur M.matrix) (M.Jr.card+M.Jc.card-(s+1-l)) M.jblock.sJ := by
  have hh := M.jblock.twoLevel
  rw [M.jblock_rows,M.jblock_cols,Fintype.card_fin] at hh
  exact Classical.choice hh

/-- Direct original member determinant price from its actual J-block. -/
theorem gle : GLE p (2*(r-M.deleted.card+s+l)-((s+1-l)+
      WrapCount.gain (M.Jr.card+M.Jc.card-(s+1-l)) M.retained.card))
    (FullN Fr M.common (WrapActual.xs r (m:=s+l)) (WrapActual.ys r) (X:ℚ[X])).det := by
  have hh := WrapMember.gle_of_data M.H M.common M.common_bound M.data
  rw [M.jblock_count] at hh
  simpa only [WrapMember.keep_card] using hh

end Setup

end CatalanCore.Uniform.Content.UFSimple.WrapMemberWindow

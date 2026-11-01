module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixType
public import CatalanCore.Uniform.Content.UFSimple.WrapType
public import CatalanCore.Uniform.Content.UFSimple.WrapCell

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixWindow

variable (p : ℕ) [Fact p.Prime]

section OriginalFibre
variable (r n e b d shift q o : ℕ) (hp : p=2*shift+1) (hp2 : 2<p)
variable (s u : GaussLoc p) (er ec : (Fin b ⊕ Fin d) ≃ Fin e) (gamma : ZMod p)
variable (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠gamma)
include hp hp2 hres

/-- Any independently loaded response on the ORIGINAL colour block is
its canonical mixed-profile response, under the actual node equivalence. -/
theorem profile_response (FR FC : ℕ → WrapDeform.Extension p) :
    (fun a:WrapFibreIndex.Whole p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) gamma =>
      FC (Sum.elim (fun i:Fin r => (i:ℕ))
        (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) a.1)) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
        (WrapPrefixCoreGeometry.xs p (n:=n) r er)
        (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)).toSquareBlock
          (WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)) gamma)⁻¹ *ᵥ
      (fun a => FR (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) a.1))=
    (fun i => FC (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) n gamma.val i)) ⬝ᵥ
      (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u)⁻¹ *ᵥ
        (fun i => FR (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) n gamma.val i)) := by
  let Q := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
    (WrapPrefixCoreGeometry.xs p (n:=n) r er)
    (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
  let col := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
  let W := WrapJointProfile.wholeEquiv p r n e b d hp2 er gamma hres
  let yr : {a // col a=gamma} → WrapDeform.Extension p := fun a =>
    FR (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) a.1)
  let yc : {a // col a=gamma} → WrapDeform.Extension p := fun a =>
    FC (Sum.elim (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) a.1)
  have hm : (Q.toSquareBlock col gamma).submatrix W W=
      WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u :=
    WrapJointProfile.whole_core p r n e b d shift q o hp hp2 s u er ec gamma hres
  have hr : yr ∘ W=fun i => FR (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) n gamma.val i) := by
    funext i
    dsimp only [yr,Function.comp_apply]
    rw [WrapJointProfile.whole_row p r n e b d hp2 (by omega) er gamma hres]
    rfl
  have hc : yc ∘ W=fun i => FC (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) n gamma.val i) := by
    funext i
    dsimp only [yc,Function.comp_apply]
    rw [WrapJointProfile.whole_col p r n e b d shift hp hp2 er ec gamma hres]
    rfl
  have he := WrapTransport.response_reindex (Q.toSquareBlock col gamma) W W yr yc
  rw [hm,hr,hc] at he
  exact he.symm

/-- The global own source is bound to the ACTUAL original mixed profile,
not supplied as an abstract source witness. -/
theorem own_response (t : ℕ) (direction : WrapDeform.Extension p) :
    let Q := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
    let col := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
    let sig := fun i => WrapDeformedEntry.entry p q o u t
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) i)
    IsUnit (WrapPrefixSource.own p col Q).det →
    ((fun i => if col i=gamma then sig i else 0) ᵥ* (WrapPrefixSource.own p col Q)⁻¹) ⬝ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) i)-direction)=
    (fun i => WrapDeformedEntry.entry p q o u t
      (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) n gamma.val i)) ⬝ᵥ
      (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
          (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) n gamma.val i)-direction) := by
  dsimp only
  intro hD
  rw [WrapPrefixType.own_response_local p _ _ gamma _ _ hD]
  exact profile_response p r n e b d shift q o hp hp2 s u er ec gamma hres
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-direction)
    (fun a => WrapDeformedEntry.entry p q o u t a)


/-- The global own reference is its literal original profile reference. -/
theorem own_reference (t : ℕ) :
    let Q := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
    let col := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
    let sig := fun i => WrapDeformedEntry.entry p q o u t
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) i)
    IsUnit (WrapPrefixSource.own p col Q).det →
    1-∑ i,((fun i => if col i=gamma then sig i else 0) ᵥ* (WrapPrefixSource.own p col Q)⁻¹) i=
      1-(fun i => WrapDeformedEntry.entry p q o u t
        (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) n gamma.val i)) ⬝ᵥ
        (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u)⁻¹ *ᵥ 1 := by
  dsimp only
  intro hD
  rw [WrapPrefixType.own_reference_local p _ _ gamma _ hD]
  have he := profile_response p r n e b d shift q o hp hp2 s u er ec gamma hres
    (fun _ => (1:WrapDeform.Extension p)) (fun a => WrapDeformedEntry.entry p q o u t a)
  simpa only [dotProduct,Matrix.mulVec,Pi.one_apply,mul_one] using
    congrArg (fun z : WrapDeform.Extension p => 1-z) he

/-- The original global mixed source moment is exactly its actual
canonical mixed moment, with independent row/column loads. -/
theorem mixed_moment (direction : WrapDeform.Extension p) :
    let Q := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (WrapPrefixCoreGeometry.xs p (n:=n) r er)
      (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
    let col := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
    let D := WrapPrefixSource.own p col Q
    let yR := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) i)-direction
    let yC := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) i)-direction
    IsUnit D.det →
    ∑ a∈univ.filter (fun a => col a=gamma),WrapDeform.residue p ((D⁻¹ *ᵥ yR) a)*WrapDeform.residue p (yC a)=
      WrapPrefixType.moment p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u direction := by
  classical
  let Q := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
    (WrapPrefixCoreGeometry.xs p (n:=n) r er)
    (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec)
  let col := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er)
  let D := WrapPrefixSource.own p col Q
  let yR : (Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) → WrapDeform.Extension p := fun i =>
    WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r er) i)-direction
  let yC : (Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) → WrapDeform.Extension p := fun i =>
    WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift ec) i)-direction
  change IsUnit D.det → _
  intro hD
  have hb : ∀ a b,col a≠col b → D a b=0 := by intro a b hab; exact if_neg hab
  have hblk : blk D col gamma=Q.toSquareBlock col gamma := by
    ext i j
    change (if col i.1=col j.1 then Q i.1 j.1 else 0)=Q i.1 j.1
    rw [if_pos (i.2.trans j.2.symm)]
  have he := WrapType.mixed_fiber_moment_response D col hD hb gamma yR yC (WrapDeform.residue p)
  rw [hblk] at he
  have hf := profile_response p r n e b d shift q o hp hp2 s u er ec gamma hres
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-direction)
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-direction)
  exact he.trans (congrArg (WrapDeform.residue p) hf)

end OriginalFibre


noncomputable def reference (q o r k n gamma t : ℕ) (s u : GaussLoc p) : WrapDeform.Extension p :=
  1-(fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.cols p r k n gamma i)) ⬝ᵥ
    (WrapPrefixType.core p q o r k n gamma s u)⁻¹ *ᵥ 1

noncomputable def columnReference (q o r k n gamma t : ℕ) (s u : GaussLoc p) : WrapDeform.Extension p :=
  1-(fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.rows p r k n gamma i)) ⬝ᵥ
    (WrapPrefixType.core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ 1

noncomputable def rowOwn (q o r k n gamma t : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p) :=
  (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
    (fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.cols p r k n gamma i)) ⬝ᵥ
      (WrapPrefixType.core p q o r k n gamma s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (WrapPrefixType.rows p r k n gamma i)-direction)

noncomputable def colOwn (q o r k n gamma t : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p) :=
  (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
    (fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.rows p r k n gamma i)) ⬝ᵥ
      (WrapPrefixType.core p q o r k n gamma s u)ᵀ⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (WrapPrefixType.cols p r k n gamma i)-direction)

/-- The actual regular joint type supplies the exact own coefficient,
its normalized residue, and the nonzero reference needed by the global
mixed source formula. Both parity cases consume the same original anchor. -/
theorem type_source (q o r k n gamma delta t : ℕ) (s u : GaussLoc p)
    (hg : gamma<p) (hd : delta<p) (hgd : gamma≤delta)
    (hcount : WrapJointProfile.count p r gamma=WrapJointProfile.count p r delta)
    (htcol : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ0 : IsUnit (WrapPrefixType.core p q o r k n gamma s u).det)
    (hQ1 : IsUnit (WrapPrefixType.core p q o r k n delta s u).det)
    (direction : WrapDeform.Extension p)
    (hz : rowOwn p q o r k n gamma t s u direction=0)
    (hzT : colOwn p q o r k n gamma t s u direction=0)
    (hB : IsUnit (reference p q o r k n gamma t s u))
    (hBT : IsUnit (columnReference p q o r k n gamma t s u)) :
    ∃ G1 : WrapDeform.Extension p,
      rowOwn p q o r k n delta (t+(delta-gamma)) s u direction=WrapDeform.uniformizer p*G1 ∧
      WrapDeform.residue p G1=
        WrapDeform.residue p (WrapOwnCore.constants p u*∑ h∈Icc 1 (delta-gamma),WrapPrefixSource.regular p q o (t+h))*
          WrapDeform.residue p (reference p q o r k n delta (t+(delta-gamma)) s u) ∧
      WrapDeform.residue p (reference p q o r k n delta (t+(delta-gamma)) s u)≠0 := by
  classical
  let K := WrapOwnCore.constants p u*∑ h∈Icc 1 (delta-gamma),WrapPrefixSource.regular p q o (t+h)
  let M := rowOwn p q o r k n delta (t+(delta-gamma)) s u direction
  let B := reference p q o r k n delta (t+(delta-gamma)) s u
  change ∃ G1,M=WrapDeform.uniformizer p*G1 ∧
    WrapDeform.residue p G1=WrapDeform.residue p K*WrapDeform.residue p B ∧ WrapDeform.residue p B≠0
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have finish (B0 E : WrapDeform.Extension p)
      (hm : M=K*B0*WrapDeform.uniformizer p+WrapDeform.uniformizer p^2*E)
      (hr : WrapDeform.residue p B=WrapDeform.residue p B0) (hu : IsUnit B0) :
      ∃ G1,M=WrapDeform.uniformizer p*G1 ∧
        WrapDeform.residue p G1=WrapDeform.residue p K*WrapDeform.residue p B ∧ WrapDeform.residue p B≠0 := by
    refine ⟨K*B0+WrapDeform.uniformizer p*E,?_,?_,?_⟩
    · rw [hm]; ring
    · simp only [map_add,map_mul,hpi,zero_mul,add_zero,hr]
    · rw [hr]
      exact (hu.map (WrapDeform.residue p)).ne_zero
  have hbits := WrapJointProfile.bit_transport p r gamma delta (Fact.out:p.Prime).pos hg hd hgd hcount
  have hh := Nat.mod_lt (delta-gamma) (by decide:0<2)
  have he : (delta-gamma)%2=0 ∨ (delta-gamma)%2=1 := by omega
  rcases he with he|he
  · have hb : WrapJointProfile.bit p r gamma=WrapJointProfile.bit p r delta := by
      rw [he] at hbits
      have hblt := WrapJointProfile.bit_lt p r gamma
      omega
    obtain ⟨E,hE⟩ := WrapPrefixType.even_transport p q o r k n gamma delta t s u hgd hcount hb htcol hw hQ0 hQ1 direction hz
    have hS : 1-∑ i,((fun j => WrapDeformedEntry.entry p q o u t (WrapPrefixType.cols p r k n gamma j)) ᵥ*
        (WrapPrefixType.core p q o r k n gamma s u)⁻¹) i=reference p q o r k n gamma t s u := by
      unfold reference
      rw [dotProduct_mulVec,dotProduct]
      simp only [Pi.one_apply,mul_one]
    rw [hS] at hE
    exact finish _ E hE (WrapPrefixType.reference_even p s u hgd hcount htcol hw hQ0 hQ1 hb) hB
  · have hb : WrapJointProfile.bit p r delta=1-WrapJointProfile.bit p r gamma := by
      rw [he] at hbits
      have hblt := WrapJointProfile.bit_lt p r gamma
      omega
    obtain ⟨E,hE⟩ := WrapPrefixType.odd_transport p q o r k n gamma delta t s u hgd hcount hb htcol hw hQ0 hQ1 direction hzT
    have hS : 1-∑ i,((fun j => WrapDeformedEntry.entry p q o u t (WrapPrefixType.rows p r k n gamma j)) ᵥ*
        (WrapPrefixType.core p q o r k n gamma s u)ᵀ⁻¹) i=columnReference p q o r k n gamma t s u := by
      unfold columnReference
      rw [dotProduct_mulVec,dotProduct]
      simp only [Pi.one_apply,mul_one]
    rw [hS] at hE
    exact finish _ E hE (WrapPrefixType.reference_odd p s u hgd hcount htcol hw hQ0 hQ1 hb) hBT


/-- The actual wrapped surplus arc excludes every residual balanced
colour, after restoring all original full periods. -/
theorem wrapped_residual_absent (r n shift l t : ℕ) (hl : 1≤l) (hls : l≤shift)
    (hp : p=2*shift+1) (hlo : r+2*n*p+(2*l-1)≤t) (hhi : t<r+2*n*p+p)
    (i : Fin (2*l-1)) :
    (WrapPrefixCoreGeometry.xs p (n:=n) r (WrapGeometry.rowEquiv shift l hl hls) (Sum.inr i):ZMod p)≠(t:ZMod p) := by
  have he : WrapPrefixCoreGeometry.xs p (n:=n) r (WrapGeometry.rowEquiv shift l hl hls) (Sum.inr i)=
      WrapBalanced.rowNode (r+2*n*p) shift i := by
    change r+2*(n*p+WrapGeometry.rowBalanced shift i)=(r+2*n*p)+2*WrapGeometry.rowBalanced shift i
    ring
  rw [he]
  exact WrapActual.balanced_not_surplus (r+2*n*p) shift l t hl hls hp (by omega) hhi i

/-- Existing original common-chain transport proves the exact common
count remains fixed inside the regular arithmetic cell. -/
theorem common_count_cell (r a b : ℕ) (hra : r≤a) (hab : a≤b)
    (hbr : b<r+p) (hdiv : b/p=a/p) :
    WrapJointProfile.count p r (a:ZMod p).val=WrapJointProfile.count p r (b:ZMod p).val := by
  have he : a+(b-a)=b := Nat.add_sub_of_le hab
  have E := WrapCell.finChainShift (p:=p) r a (b-a) hra (by rw [he]; exact hbr) (by rw [he]; exact hdiv)
  have E' : WrapFibreIndex.Common p (fun i:Fin r => (i:ℕ)) (b:ZMod p) ≃
      WrapFibreIndex.Common p (fun i:Fin r => (i:ℕ)) (a:ZMod p) := by
    simpa only [he] using E
  have hc := Fintype.card_congr ((WrapJointProfile.commonEquiv p r (a:ZMod p)).trans
    (E'.symm.trans (WrapJointProfile.commonEquiv p r (b:ZMod p)).symm))
  simpa only [Fintype.card_fin] using hc


/-- An explicit original anchor, independent of which target colour is
subsequently transported. -/
noncomputable def anchorDirection (q o r k n gamma t : ℕ) (s u : GaussLoc p) :=
  (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-
    (fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.cols p r k n gamma i)) ⬝ᵥ
      (WrapPrefixType.core p q o r k n gamma s u)⁻¹ *ᵥ
        (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (WrapPrefixType.rows p r k n gamma i)))*
    Ring.inverse (reference p q o r k n gamma t s u)

theorem row_own_unique (q o r k n gamma t : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p)
    (hz : rowOwn p q o r k n gamma t s u direction=0)
    (hB : IsUnit (reference p q o r k n gamma t s u)) :
    direction=anchorDirection p q o r k n gamma t s u := by
  let Q := WrapPrefixType.core p q o r k n gamma s u
  let sig : Fin k ⊕ Fin n → WrapDeform.Extension p := fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.cols p r k n gamma i)
  let y : Fin k ⊕ Fin n → WrapDeform.Extension p := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (WrapPrefixType.rows p r k n gamma i)
  let Lt := WrapOwnCore.constants p u*WrapEntryRelation.load p q o t
  let B := reference p q o r k n gamma t s u
  change (Lt-direction)-sig ⬝ᵥ Q⁻¹ *ᵥ (fun i => y i-direction)=0 at hz
  have hv : (fun i => y i-direction)=y-direction • (1:Fin k ⊕ Fin n → WrapDeform.Extension p) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hv,Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,dotProduct_smul] at hz
  simp only [smul_eq_mul] at hz
  have he : direction*B=Lt-sig ⬝ᵥ Q⁻¹ *ᵥ y := by
    change direction*(1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)=_
    linear_combination -hz
  have hi : B*Ring.inverse B=1 := Ring.mul_inverse_cancel B hB
  change direction=(Lt-sig ⬝ᵥ Q⁻¹ *ᵥ y)*Ring.inverse B
  calc
    _=direction*(B*Ring.inverse B) := by rw [hi,mul_one]
    _=_ := by rw [← mul_assoc,he]

/-- The original arithmetic and actual profile nodes construct the whole
own source coefficient. No pivot, reference, direction or source witness is
assumed: each is derived from the actual core and the original anchor. -/
theorem arithmetic_source {q o root j0 r k n gamma delta m N : ℕ}
    (H0 : WrapBalancedResidue.Hyp p q o root j0 gamma m N n
      (WrapPrefixType.rowQuot p r k n gamma) (WrapPrefixType.colQuot p r k n gamma))
    (H1 : WrapBalancedResidue.Hyp p q o root j0 delta m N n
      (WrapPrefixType.rowQuot p r k n delta) (WrapPrefixType.colQuot p r k n delta))
    (hC0 : WrapJointProfile.count p r gamma=k) (hC1 : WrapJointProfile.count p r delta=k)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (ho : (o:ZMod p)≠0)
    (hc0 : ∀ i:Fin k,gamma+(i:ℕ)*p<N) (hc1 : ∀ i:Fin k,delta+(i:ℕ)*p<N)
    (ht0 : gamma+(k+2*n)*p<N) (hgd : gamma≤delta)
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((gamma+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (gamma+(k+2*n)*p+h))≠0) :
    let direction := anchorDirection p q o r k n gamma (gamma+(k+2*n)*p) s u
    ∃ G1 : WrapDeform.Extension p,
      rowOwn p q o r k n delta (delta+(k+2*n)*p) s u direction=WrapDeform.uniformizer p*G1 ∧
      WrapDeform.residue p G1=
        (WrapDeform.residue p (WrapOwnCore.constants p u)*
          RatFunc.C (RatFunc.C (cauchyH (wT p q o) (delta:ZMod p)-cauchyH (wT p q o) (gamma:ZMod p))))*
          WrapDeform.residue p (reference p q o r k n delta (delta+(k+2*n)*p) s u) ∧
      WrapDeform.residue p (reference p q o r k n delta (delta+(k+2*n)*p) s u)≠0 := by
  dsimp only
  have hQ0 := WrapPrefixType.core_unit p H0 hC0 s u hs hu huc hc0
  have hQ1 := WrapPrefixType.core_unit p H1 hC1 s u hs hu huc hc1
  obtain ⟨direction,hz,hzT,hB,hBT⟩ := WrapPrefixType.anchor p H0 hC0 s u hs hu huc hc0 ht0
  have htcol : ((gamma+(k+2*n)*p:ℕ):ZMod p)=(gamma:ZMod p) := by simp
  obtain ⟨G1,hm,hr,hne⟩ := type_source p q o r k n gamma delta (gamma+(k+2*n)*p) s u H0.hg H1.hg hgd
    (hC0.trans hC1.symm) htcol hw hQ0 hQ1 direction hz hzT hB hBT
  have htip : gamma+(k+2*n)*p+(delta-gamma)=delta+(k+2*n)*p := by omega
  rw [htip] at hm hr hne
  have hdir := row_own_unique p q o r k n gamma (gamma+(k+2*n)*p) s u direction hz hB
  rw [hdir] at hm
  have hp2 : p≠2 := by have := H0.hq2; have := H0.hqp; omega
  have hq : (q:ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff q p).mp he
    have hh := Nat.le_of_dvd H0.hq0 hd
    have := H0.hqp
    omega
  have hsource := WrapPrefixSource.actual_step_source p q o (gamma+(k+2*n)*p) (delta-gamma) u hp2 ho hq hw
  have hcast : ((gamma+(k+2*n)*p+(delta-gamma):ℕ):ZMod p)=(delta:ZMod p) := by rw [htip]; simp
  rw [hcast,htcol] at hsource
  rw [hsource] at hr
  exact ⟨G1,hm,hr,hne⟩


/-- Restore the actual virtual surplus node from its ORIGINAL common
count. The quotient shift is 2n; the common count is never compressed. -/
theorem original_tip (r n t : ℕ) (hlo : r+2*n*p≤t) (hhi : t<r+2*n*p+p) :
    t=(t:ZMod p).val+(WrapJointProfile.count p r (t:ZMod p).val+2*n)*p := by
  rw [ZMod.val_natCast]
  let gamma := t%p
  let v := t-2*n*p
  change t=gamma+(WrapJointProfile.count p r gamma+2*n)*p
  have hp0 := (Fact.out:p.Prime).pos
  have hg : gamma<p := Nat.mod_lt _ hp0
  have hv : r≤v ∧ v<r+p := by dsimp only [v]; omega
  have ht : t=v+2*n*p := by dsimp only [v]; omega
  have hmod : v%p=gamma := by
    have he := congrArg (fun a:ℕ => a%p) ht
    simp only [Nat.add_mul_mod_self_right] at he
    exact he.symm
  have hc := WrapJointProfile.two_candidates p r gamma v hp0 hg hv.1 (by omega) hmod
  have hl := WrapJointProfile.lower_bounds p r gamma hp0 hg
  have he : v=WrapJointProfile.lower p r gamma := by rcases hc with hc|hc; exact hc; omega
  calc
    t=v+2*n*p := ht
    _=WrapJointProfile.lower p r gamma+2*n*p := by rw [he]
    _=_ := by unfold WrapJointProfile.lower; ring

/-- A regular physical quotient cell gives the same original common
count after removing the full-cycle translation. -/
theorem common_count_full_cell (r n a b : ℕ) (hlo : r+2*n*p≤a) (hab : a≤b)
    (hhi : b<r+2*n*p+p) (hdiv : b/p=a/p) :
    WrapJointProfile.count p r (a:ZMod p).val=WrapJointProfile.count p r (b:ZMod p).val := by
  let va := a-2*n*p
  let vb := b-2*n*p
  have ha : a=va+2*n*p := by dsimp only [va]; omega
  have hb : b=vb+2*n*p := by dsimp only [vb]; omega
  have hdiv' : vb/p=va/p := by
    rw [ha,hb,Nat.add_mul_div_right _ _ (Fact.out:p.Prime).pos,
      Nat.add_mul_div_right _ _ (Fact.out:p.Prime).pos] at hdiv
    omega
  have hca : (va:ZMod p)=(a:ZMod p) := by rw [ha]; simp
  have hcb : (vb:ZMod p)=(b:ZMod p) := by rw [hb]; simp
  have hc := common_count_cell p r va vb (by dsimp only [va]; omega)
    (by dsimp only [va,vb]; omega) (by dsimp only [vb]; omega) hdiv'
  rw [hca,hcb] at hc
  exact hc

/-- Inside one original quotient cell the residue displacement is the
actual node displacement, including both interval endpoints. -/
theorem residue_displacement (a b : ℕ) (hab : a≤b) (hdiv : b/p=a/p) :
    (a:ZMod p).val≤(b:ZMod p).val ∧
      (b:ZMod p).val-(a:ZMod p).val=b-a := by
  rw [ZMod.val_natCast,ZMod.val_natCast]
  have ha := Nat.mod_add_div a p
  have hb := Nat.mod_add_div b p
  rw [hdiv] at hb
  omega


/-- Original arithmetic and geometry of a regular prefix window.
There are no matrix-unit, source, Smith or deletion certificates here. -/
structure Setup (p q o r n e b d shift N : ℕ) [Fact p.Prime] where
  hp : p=2*shift+1
  hn : 1≤n
  he : e<p
  hq0 : 0<q
  hqp : q<p
  hq2 : 2≤q
  hoq : o<q
  ho : (o:ZMod p)≠0
  root : ℕ
  j0 : ℕ
  hroot0 : 0<root
  hrootp : root≤p
  hroot : q*root=j0*p+o
  hsize : r+2*(n*p+e)≤N
  hN : q*N<p*p
  er : (Fin b ⊕ Fin d) ≃ Fin e
  ec : (Fin b ⊕ Fin d) ≃ Fin e
  hres : ∀ i:Fin b,((r+2*n*p+2*(er (Sum.inl i):ℕ):ℕ):ZMod p)=
    ((r+2*n*p+2*(ec (Sum.inl i):ℕ)+1:ℕ):ZMod p)
  t0 : ℕ
  tv : ℕ
  hlo : r+2*n*p≤t0
  hle : t0≤tv
  hhi : tv<r+2*n*p+p
  htvN : tv<N
  hdiv : tv/p=t0/p
  hw : ∀ h∈Icc 1 (tv-t0),res p ((t0+h:ℕ):GaussLoc p)≠0 ∧
    res p (WrapIncrement.argument p q o (t0+h))≠0
  hfree : ∀ t∈Icc t0 tv,∀ i:Fin b,
    (WrapPrefixCoreGeometry.xs p (n:=n) r er (Sum.inr i):ZMod p)≠(t:ZMod p)

namespace Setup
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : Setup p q o r n e b d shift N)
include H

noncomputable def xs := WrapPrefixCoreGeometry.xs p (n:=n) r H.er
noncomputable def ys := WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift H.ec
noncomputable def colour := WrapFibreIndex.colour p (fun i:Fin r => (i:ℕ)) H.xs
noncomputable def core (s u : GaussLoc p) := WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
noncomputable def own (s u : GaussLoc p) := WrapPrefixSource.own p H.colour (H.core s u)
def commonCount := WrapJointProfile.count p r (H.t0:ZMod p).val

theorem hp2 : 2<p := by have := H.hq2; have := H.hqp; omega

theorem common_bound (i : Fin r) : (i:ℕ)<N := by have := i.2; have := H.hsize; omega

theorem row_bound (i : (Fin n × Fin p) ⊕ Fin b) : H.xs i<N :=
  WrapPrefixCoreGeometry.xs_bound p r N H.er H.hsize i

theorem col_bound (i : (Fin n × Fin p) ⊕ Fin b) : H.ys i<N :=
  WrapPrefixCoreGeometry.ys_bound p r N (Fact.out:p.Prime).pos shift H.ec H.hsize i

theorem same_colour (i : (Fin n × Fin p) ⊕ Fin b) : (H.xs i:ZMod p)=(H.ys i:ZMod p) :=
  WrapPrefixCoreGeometry.same_colour p (n:=n) r shift H.hp H.er H.ec H.hres i

theorem core_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : IsUnit (H.core s u).det :=
  WrapPrefixCoreGeometry.core_unit p (n:=n) (e:=e) (b:=b) (d:=d) q o H.root H.j0 r shift N s u hs hu huc
    H.hq0 H.hqp H.hq2 H.hoq H.hroot0 H.hrootp H.hroot H.hN H.hn H.hp H.he H.er H.ec H.hres
    H.hsize (fun i:Fin r => (i:ℕ)) (fun i => i.2)

theorem own_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : IsUnit (H.own s u).det := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  apply WrapPrefixSource.own_unit p H.colour (H.core s u) (H.core_unit s u hs hu huc)
  intro i j hij
  exact WrapGlobalCore.cross_zero p q o N s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
    H.common_bound H.row_bound H.col_bound H.same_colour hsingle i j
      (fun he => hij (ZMod.val_injective p he))

theorem div_eq (t : ℕ) (ht : t∈Icc H.t0 H.tv) : t/p=H.t0/p := by
  have hlo := Nat.div_le_div_right (c:=p) (mem_Icc.mp ht).1
  have hhi := Nat.div_le_div_right (c:=p) (mem_Icc.mp ht).2
  have := H.hdiv
  omega

theorem count_eq (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    WrapJointProfile.count p r (t:ZMod p).val=H.commonCount := by
  exact (common_count_full_cell p r n H.t0 t H.hlo (mem_Icc.mp ht).1
    (lt_of_le_of_lt (mem_Icc.mp ht).2 H.hhi) (H.div_eq t ht)).symm

theorem tip (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    t=(t:ZMod p).val+(H.commonCount+2*n)*p := by
  have he := original_tip p r n t (by have := (mem_Icc.mp ht).1; have := H.hlo; omega)
    (lt_of_le_of_lt (mem_Icc.mp ht).2 H.hhi)
  rw [H.count_eq t ht] at he
  exact he

theorem profile_common_bound (t : ℕ) (ht : t∈Icc H.t0 H.tv) (i : Fin H.commonCount) :
    (t:ZMod p).val+(i:ℕ)*p<N := by
  have hi : (i:ℕ)<WrapJointProfile.count p r (t:ZMod p).val := by rw [H.count_eq t ht]; exact i.2
  have hb := (WrapJointProfile.common_bound p r (t:ZMod p).val i (Fact.out:p.Prime).pos (ZMod.val_lt (t:ZMod p))).mpr hi
  have := H.hsize
  omega

/-- Derive each complete arithmetic profile hypothesis from original
cycle/residual nodes, including both actual independent node bounds. -/
theorem profile_hyp (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    WrapBalancedResidue.Hyp p q o H.root H.j0 (t:ZMod p).val (n*p+e) N n
      (WrapPrefixType.rowQuot p r H.commonCount n (t:ZMod p).val)
      (WrapPrefixType.colQuot p r H.commonCount n (t:ZMod p).val) := by
  have hp0 := (Fact.out:p.Prime).pos
  have hdim : n≤(n*p+e)/p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
  apply WrapPrefixType.profile_hyp p q o H.root H.j0 r H.commonCount n (t:ZMod p).val (n*p+e) N
    (H.count_eq t ht) H.hq0 H.hqp H.hq2 H.hoq H.hroot0 H.hrootp (ZMod.val_lt (t:ZMod p))
    H.hroot (by have := H.hsize; omega) H.hN H.hn (by omega)
  · intro i
    rw [← WrapJointProfile.fullBalanced_row p r n e b d H.hp2 (by have := H.hp; omega) H.er (t:ZMod p) (H.hfree t ht) i]
    exact H.row_bound _
  · intro i
    rw [← WrapJointProfile.fullBalanced_col p r n e b d shift H.hp H.hp2 H.er H.ec (t:ZMod p) (H.hfree t ht) i]
    exact H.col_bound _


noncomputable def anchor (s u : GaussLoc p) :=
  anchorDirection p q o r H.commonCount n (H.t0:ZMod p).val H.t0 s u

/-- Original arithmetic discharges all own-source premises throughout
this physical window, in ONE explicit original anchor direction. -/
theorem arithmetic_source (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    ∃ G1 : WrapDeform.Extension p,
      rowOwn p q o r H.commonCount n (t:ZMod p).val t s u (H.anchor s u)=WrapDeform.uniformizer p*G1 ∧
      WrapDeform.residue p G1=
        (WrapDeform.residue p (WrapOwnCore.constants p u)*
          RatFunc.C (RatFunc.C (cauchyH (wT p q o) (t:ZMod p)-cauchyH (wT p q o) (H.t0:ZMod p))))*
          WrapDeform.residue p (reference p q o r H.commonCount n (t:ZMod p).val t s u) ∧
      WrapDeform.residue p (reference p q o r H.commonCount n (t:ZMod p).val t s u)≠0 := by
  have hm0 : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have htip0 := H.tip H.t0 hm0
  have htip := H.tip t ht
  have hwidth := residue_displacement p H.t0 t (mem_Icc.mp ht).1 (H.div_eq t ht)
  have hw : ∀ h∈Icc 1 ((t:ZMod p).val-(H.t0:ZMod p).val),
      res p (((H.t0:ZMod p).val+(H.commonCount+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
        res p (WrapIncrement.argument p q o ((H.t0:ZMod p).val+(H.commonCount+2*n)*p+h))≠0 := by
    intro h hh
    rw [hwidth.2] at hh
    have hh' : h∈Icc 1 (H.tv-H.t0) := by
      have := mem_Icc.mp hh
      have := mem_Icc.mp ht
      simp only [mem_Icc]
      omega
    simpa only [← htip0] using H.hw h hh'
  have hsource := WrapPrefixWindow.arithmetic_source p (H.profile_hyp H.t0 hm0) (H.profile_hyp t ht)
    (H.count_eq H.t0 hm0) (H.count_eq t ht) s u hs hu huc H.ho
    (H.profile_common_bound H.t0 hm0) (H.profile_common_bound t ht)
    (by rw [← htip0]; exact lt_of_le_of_lt H.hle H.htvN) hwidth.1 hw
  dsimp only at hsource
  rw [← htip0,← htip] at hsource
  simpa only [anchor,ZMod.natCast_zmod_val] using hsource


noncomputable def rowLoad (u : GaussLoc p) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i)

noncomputable def colLoad (u : GaussLoc p) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)

noncomputable def sigma (u : GaussLoc p) (t : ℕ) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  WrapDeformedEntry.entry p q o u t (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)

noncomputable def ownSigma (u : GaussLoc p) (t : ℕ) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  if H.colour i=(t:ZMod p) then H.sigma u t i else 0

noncomputable def ownReference (s u : GaussLoc p) (t : ℕ) :=
  1-∑ i,(H.ownSigma u t ᵥ* (H.own s u)⁻¹) i

noncomputable def moment (s u : GaussLoc p) (gamma : ZMod p) :=
  ∑ a∈univ.filter (fun a => H.colour a=gamma),
    WrapDeform.residue p (((H.own s u)⁻¹ *ᵥ (fun i => H.rowLoad u i-H.anchor s u)) a)*
      WrapDeform.residue p (H.colLoad u a-H.anchor s u)

/-- The complete original global own source, with every hypothesis
supplied by the arithmetic window and its actual original fibres. -/
theorem own_source (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    ∃ G1 : WrapDeform.Extension p,
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u)-
        (H.ownSigma u t ᵥ* (H.own s u)⁻¹) ⬝ᵥ (fun i => H.rowLoad u i-H.anchor s u)=
          WrapDeform.uniformizer p*G1 ∧
      WrapDeform.residue p G1=
        (WrapDeform.residue p (WrapOwnCore.constants p u)*
          RatFunc.C (RatFunc.C (cauchyH (wT p q o) (t:ZMod p)-cauchyH (wT p q o) (H.t0:ZMod p))))*
          WrapDeform.residue p (H.ownReference s u t) ∧
      WrapDeform.residue p (H.ownReference s u t)≠0 := by
  obtain ⟨G1,hm,hr,hne⟩ := H.arithmetic_source t ht s u hs hu huc
  have hD := H.own_unit s u hs hu huc
  have hresp := WrapPrefixWindow.own_response p r n e b d shift q o H.hp H.hp2 s u H.er H.ec
    (t:ZMod p) (H.hfree t ht) t (H.anchor s u) hD
  have hBref := WrapPrefixWindow.own_reference p r n e b d shift q o H.hp H.hp2 s u H.er H.ec
    (t:ZMod p) (H.hfree t ht) t hD
  have hcount : WrapJointProfile.count p r (t:ZMod p).val=H.commonCount := H.count_eq t ht
  change H.ownReference s u t=reference p q o r (WrapJointProfile.count p r (t:ZMod p).val) n (t:ZMod p).val t s u at hBref
  have hBrefK := hBref.trans (congrArg (fun kc:ℕ => reference p q o r kc n (t:ZMod p).val t s u) hcount)
  have hM : (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u)-
      (H.ownSigma u t ᵥ* (H.own s u)⁻¹) ⬝ᵥ (fun i => H.rowLoad u i-H.anchor s u)=
      rowOwn p q o r (WrapJointProfile.count p r (t:ZMod p).val) n (t:ZMod p).val t s u (H.anchor s u) :=
    congrArg (fun z:WrapDeform.Extension p => WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u-z) hresp
  refine ⟨G1,?_,?_,?_⟩
  · exact hM.trans ((congrArg (fun kc:ℕ => rowOwn p q o r kc n (t:ZMod p).val t s u (H.anchor s u)) hcount).trans hm)
  · rw [hBrefK]
    exact hr
  · rw [hBrefK]
    exact hne


theorem profile_moment (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    H.moment s u (t:ZMod p)=
      WrapPrefixType.moment p q o r H.commonCount n (t:ZMod p).val s u (H.anchor s u) := by
  have he := WrapPrefixWindow.mixed_moment p r n e b d shift q o H.hp H.hp2 s u H.er H.ec
    (t:ZMod p) (H.hfree t ht) (H.anchor s u) (H.own_unit s u hs hu huc)
  exact he.trans (congrArg (fun kc:ℕ => WrapPrefixType.moment p q o r kc n (t:ZMod p).val s u (H.anchor s u)) (H.count_eq t ht))

noncomputable def sourceConstant (s u : GaussLoc p) :=
  RatFunc.C (RatFunc.C (wT p q o (H.t0:ZMod p)))*WrapDeform.residue p (WrapOwnCore.constants p u)-
    H.moment s u (H.t0:ZMod p)

noncomputable def weight (s u : GaussLoc p) (gamma : ZMod p) :=
  RatFunc.C (RatFunc.C (wT p q o gamma))*WrapDeform.residue p (WrapOwnCore.constants p u)-
    H.moment s u gamma-H.sourceConstant s u

/-- Every original selected colour has zero actual global source weight. -/
theorem weight_zero (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : H.weight s u (t:ZMod p)=0 := by
  have hm0 : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have hwidth := residue_displacement p H.t0 t (mem_Icc.mp ht).1 (H.div_eq t ht)
  have hw : ∀ h∈Icc 1 ((t:ZMod p).val-(H.t0:ZMod p).val),
      res p ((H.t0+h:ℕ):GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o (H.t0+h))≠0 := by
    intro h hh
    rw [hwidth.2] at hh
    have hh' : h∈Icc 1 (H.tv-H.t0) := by
      have := mem_Icc.mp hh
      have := mem_Icc.mp ht
      simp only [mem_Icc]
      omega
    exact H.hw h hh'
  have htcol : (H.t0:ZMod p)=((H.t0:ZMod p).val:ZMod p) := by rw [ZMod.natCast_zmod_val]
  have hq : (q:ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff q p).mp he
    have hh := Nat.le_of_dvd H.hq0 hd
    have := H.hqp
    omega
  have hQ0 := WrapPrefixType.core_unit p (H.profile_hyp H.t0 hm0) (H.count_eq H.t0 hm0)
    s u hs hu huc (H.profile_common_bound H.t0 hm0)
  have hQ1 := WrapPrefixType.core_unit p (H.profile_hyp t ht) (H.count_eq t ht)
    s u hs hu huc (H.profile_common_bound t ht)
  have he := WrapPrefixType.weight_zero p q o r H.commonCount n (H.t0:ZMod p).val (t:ZMod p).val H.t0 s u
    (ZMod.val_lt (H.t0:ZMod p)) (ZMod.val_lt (t:ZMod p)) hwidth.1
    ((H.count_eq H.t0 hm0).trans (H.count_eq t ht).symm) H.ho hq htcol hw hQ0 hQ1 (H.anchor s u)
  unfold weight sourceConstant
  rw [H.profile_moment t ht s u hs hu huc,H.profile_moment H.t0 hm0 s u hs hu huc]
  simpa only [WrapPrefixType.weight,ZMod.natCast_zmod_val] using he

noncomputable def sourceOffset (s u : GaussLoc p) :=
  -WrapDeform.residue p (WrapOwnCore.constants p u)*
    RatFunc.C (RatFunc.C (cauchyH (wT p q o) (H.t0:ZMod p)))


end Setup

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixWindow

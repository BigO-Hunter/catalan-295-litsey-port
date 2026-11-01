module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixFamily
public import CatalanCore.Uniform.Content.UFSimple.WrapExpr
public import CatalanCore.Uniform.Content.UFSimple.WrapBivariate
public import CatalanCore.Uniform.Content.BankShared.Reindex
public import Mathlib.Algebra.Group.ForwardDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed

/-- The ordinary residual ordering has no absorbed residual pair. -/
def ordinaryEquiv (e : ℕ) : (Fin 0 ⊕ Fin e) ≃ Fin e where
  toFun := Sum.elim Fin.elim0 id
  invFun := Sum.inr
  left_inv i := by cases i with | inl i => exact Fin.elim0 i | inr i => rfl
  right_inv _ := rfl

/-- Distinct alternating surplus slots have distinct original colours
throughout any interval of length at most one period. -/
theorem alternating_colour_injective (p base d : ℕ) (hwidth : 2*d≤p) :
    Function.Injective (Sum.elim (fun i:Fin d => ((base+2*(i:ℕ):ℕ):ZMod p))
      (fun i:Fin d => ((base+2*(i:ℕ)+1:ℕ):ZMod p))) := by
  let off : Fin d ⊕ Fin d → ℕ := Sum.elim (fun i => 2*(i:ℕ)) (fun i => 2*(i:ℕ)+1)
  have hbound : ∀ i,off i<p := by
    intro i
    cases i with
    | inl i => have := i.2; dsimp only [off,Sum.elim_inl]; omega
    | inr i => have := i.2; dsimp only [off,Sum.elim_inr]; omega
  have he : Sum.elim (fun i:Fin d => ((base+2*(i:ℕ):ℕ):ZMod p))
      (fun i:Fin d => ((base+2*(i:ℕ)+1:ℕ):ZMod p))=fun i => (base:ZMod p)+(off i:ZMod p) := by
    funext i
    cases i <;> simp only [off,Sum.elim_inl,Sum.elim_inr,Nat.cast_add,Nat.cast_one,add_assoc]
  intro i j hij
  rw [he] at hij
  have hm := (ZMod.natCast_eq_natCast_iff' (off i) (off j) p).mp (add_left_cancel hij)
  rw [Nat.mod_eq_of_lt (hbound i),Nat.mod_eq_of_lt (hbound j)] at hm
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg Sum.inl (Fin.ext (by dsimp only [off,Sum.elim_inl] at hm; omega))
    | inr j => dsimp only [off,Sum.elim_inl,Sum.elim_inr] at hm; omega
  | inr i => cases j with
    | inl j => dsimp only [off,Sum.elim_inl,Sum.elim_inr] at hm; omega
    | inr j => exact congrArg Sum.inr (Fin.ext (by dsimp only [off,Sum.elim_inr] at hm; omega))

variable {p : ℕ} [Fact p.Prime]

theorem ordinary_row (r n e shift : ℕ) (i:Fin e) :
    r+2*(WrapPrefixGeometry.rowBorderEquiv (n:=n) (p:=p) (ordinaryEquiv e) (Sum.inr i):ℕ)=r+2*n*p+2*(i:ℕ) := by
  simpa only [ordinaryEquiv,Equiv.coe_fn_mk,Sum.elim_inr,id_eq] using
    WrapPrefixGeometry.row_surplus (p:=p) (n:=n) r (ordinaryEquiv e) i

theorem ordinary_col (r n e shift : ℕ) (i:Fin e) :
    r+2*(WrapPrefixGeometry.colBorderEquiv (n:=n) (p:=p) (Fact.out:p.Prime).pos shift (ordinaryEquiv e) (Sum.inr i):ℕ)+1=
      r+2*n*p+2*(i:ℕ)+1 := by
  simpa only [ordinaryEquiv,Equiv.coe_fn_mk,Sum.elim_inr,id_eq] using
    WrapPrefixGeometry.col_surplus (p:=p) (n:=n) r (Fact.out:p.Prime).pos shift (ordinaryEquiv e) i

/-- Original arithmetic for either residual orientation; no matrix,
source, retained-support or Smith witness is part of these hypotheses. -/
structure Region (Fr : Frame) (q o r n e shift N : ℕ) (T : TwoTermData Fr q o) where
  hn : 1≤n
  hp : p=2*shift+1
  he : e<p
  hqp : q<p
  hN : q*N<p*p
  hsize : r+2*(n*p+e)≤N
  hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o
  hnorm : Fr.norm∈S p
  hnorm0 : red p Fr.norm≠0
  root : ℕ
  j0 : ℕ
  hroot0 : 0<root
  hrootp : root≤p
  hroot : q*root=j0*p+o

namespace Region
variable {Fr : Frame} {q o r n e shift N : ℕ} {T : TwoTermData Fr q o}
variable (A : Region (p:=p) Fr q o r n e shift N T)
include A

theorem qpos : 0<q := by have := T.o_pos; have := T.o_lt; omega
theorem qtwo : 2≤q := by have := T.o_pos; have := T.o_lt; omega
theorem offset_ne : (o:ZMod p)≠0 := by
  intro he
  have hd := (ZMod.natCast_eq_zero_iff o p).mp he
  have ho := Nat.le_of_dvd T.o_pos hd
  have := T.o_lt
  have := A.hqp
  omega

noncomputable def D : PoleData Fr p N :=
  twoTermPoleData T (by have := A.qpos; exact le_of_lt (lt_of_le_of_lt (Nat.le_mul_of_pos_left N A.qpos) A.hN))
    A.hsq A.hnorm A.hnorm0

/-- Restore the original period translation before constructing an
ordinary arithmetic window. All source hypotheses follow from this setup. -/
noncomputable def ordinarySetup (t0 tv : ℕ) (hlo : r+2*n*p≤t0) (hle : t0≤tv)
    (hhi : tv<r+2*n*p+p) (htvN : tv<N) (hdiv : tv/p=t0/p)
    (hw : ∀ h∈Icc 1 (tv-t0),res p ((t0+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t0+h))≠0) :
    WrapPrefixWindow.Setup p q o r n e 0 e shift N where
  hp := A.hp
  hn := A.hn
  he := A.he
  hq0 := A.qpos
  hqp := A.hqp
  hq2 := A.qtwo
  hoq := T.o_lt
  ho := A.offset_ne
  root := A.root
  j0 := A.j0
  hroot0 := A.hroot0
  hrootp := A.hrootp
  hroot := A.hroot
  hsize := A.hsize
  hN := A.hN
  er := ordinaryEquiv e
  ec := ordinaryEquiv e
  hres := fun i => Fin.elim0 i
  t0 := t0
  tv := tv
  hlo := hlo
  hle := hle
  hhi := hhi
  htvN := htvN
  hdiv := hdiv
  hw := hw
  hfree := fun _ _ i => Fin.elim0 i

end Region


section Wrapped
variable {Fr : Frame} {q o r n shift N : ℕ} {T : TwoTermData Fr q o}

noncomputable def wrappedSetup (l : ℕ) (hl : 1≤l) (hls : l≤shift)
    (A : Region (p:=p) Fr q o r n (shift+l) shift N T)
    (t0 tv : ℕ) (hlo : r+2*n*p+(2*l-1)≤t0) (hle : t0≤tv)
    (hhi : tv<r+2*n*p+p) (htvN : tv<N) (hdiv : tv/p=t0/p)
    (hw : ∀ h∈Icc 1 (tv-t0),res p ((t0+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t0+h))≠0) :
    WrapPrefixWindow.Setup p q o r n (shift+l) (2*l-1) (shift+1-l) shift N where
  hp := A.hp
  hn := A.hn
  he := A.he
  hq0 := A.qpos
  hqp := A.hqp
  hq2 := A.qtwo
  hoq := T.o_lt
  ho := A.offset_ne
  root := A.root
  j0 := A.j0
  hroot0 := A.hroot0
  hrootp := A.hrootp
  hroot := A.hroot
  hsize := A.hsize
  hN := A.hN
  er := WrapGeometry.rowEquiv shift l hl hls
  ec := WrapGeometry.colEquiv shift l hl hls
  hres := by
    intro i
    have he := WrapPrefixCoreGeometry.wrapped_residual r n shift l hl hls i
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).mpr
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ (2*shift+1)).mp he
    simpa only [A.hp] using hm
  t0 := t0
  tv := tv
  hlo := by omega
  hle := hle
  hhi := hhi
  htvN := htvN
  hdiv := hdiv
  hw := hw
  hfree := by
    intro t ht i
    exact WrapPrefixWindow.wrapped_residual_absent p r n shift l t hl hls A.hp
      (by have := (mem_Icc.mp ht).1; omega) (lt_of_le_of_lt (mem_Icc.mp ht).2 hhi) i

theorem wrapped_row (r n shift l : ℕ) (hl : 1≤l) (hls : l≤shift) (i:Fin (shift+1-l)) :
    r+2*(WrapPrefixGeometry.rowBorderEquiv (n:=n) (p:=p) (WrapGeometry.rowEquiv shift l hl hls) (Sum.inr i):ℕ)=
      (r+2*n*p+(2*l-1))+2*(i:ℕ)+1 := by
  rw [WrapPrefixGeometry.row_surplus]
  change r+2*n*p+2*(l+(i:ℕ))=_
  omega

theorem wrapped_col (r n shift l : ℕ) (hl : 1≤l) (hls : l≤shift) (i:Fin (shift+1-l)) :
    r+2*(WrapPrefixGeometry.colBorderEquiv (n:=n) (p:=p) (Fact.out:p.Prime).pos shift
      (WrapGeometry.colEquiv shift l hl hls) (Sum.inr i):ℕ)+1=
      (r+2*n*p+(2*l-1))+2*(i:ℕ) := by
  rw [WrapPrefixGeometry.col_surplus]
  change r+2*n*p+2*(l-1+(i:ℕ))+1=_
  omega

end Wrapped

section RetainedCount
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def windowColours : Finset (ZMod p) := (Icc H.t0 H.tv).image (fun t:ℕ => (t:ZMod p))

theorem windowColours_card : (windowColours H).card=H.tv+1-H.t0 := by
  apply card_image_window (Fact.out:p.Prime).pos
  have h := H.hhi
  have h0 := H.hlo
  omega

/-- Every selected arithmetic colour is absent from the actual retained
source; this is a direct finite count of the proved original source zeros. -/
theorem retained_window_bound (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    (WrapPrefixMember.fullRetained H s u).card≤p-(H.tv+1-H.t0) := by
  classical
  have hdis : Disjoint (WrapPrefixMember.fullRetained H s u) (windowColours H) := by
    apply Finset.disjoint_left.mpr
    intro gamma hg hw
    have hn := (mem_filter.mp (mem_sdiff.mp hg).1).2
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hw
    exact hn (H.weight_zero t ht s u hs hu huc)
  have hc := Finset.card_union_of_disjoint hdis
  have hle : (WrapPrefixMember.fullRetained H s u∪windowColours H).card≤p := by
    simpa only [ZMod.card] using Finset.card_le_univ (WrapPrefixMember.fullRetained H s u∪windowColours H)
  rw [hc,windowColours_card H] at hle
  omega

/-- The existing residue-union count consumes actual source zeros and
actual kills; zero-weight outside colours require no artificial kill. -/
theorem retained_credit_bound (s u : GaussLoc p) (I O : Finset (ZMod p))
    (hI : ∀ gamma∈I,H.weight s u gamma=0)
    (hO : ∀ gamma∈O,H.weight s u gamma=0 ∨
      gamma∈WrapPrefixSchur.killedColumns H s u∪WrapPrefixSchur.killedRows H s u) :
    (WrapPrefixMember.fullRetained H s u).card≤p-(I∪O).card := by
  classical
  have hdis : Disjoint (WrapPrefixMember.fullRetained H s u) (I∪O) := by
    apply Finset.disjoint_left.mpr
    intro gamma hg hcredit
    have hh := mem_sdiff.mp hg
    have hw := (mem_filter.mp hh.1).2
    rcases mem_union.mp hcredit with hi|ho
    · exact hw (hI gamma hi)
    · rcases hO gamma ho with hz|hk
      · exact hw hz
      · exact hh.2 hk
  have hc := Finset.card_union_of_disjoint hdis
  have hle : (WrapPrefixMember.fullRetained H s u∪(I∪O)).card≤p := by
    simpa only [ZMod.card] using Finset.card_le_univ (WrapPrefixMember.fullRetained H s u∪(I∪O))
  rw [hc] at hle
  omega

/-- The selected arithmetic window gives a completely explicit family
price, without a retained-support witness in the conclusion. -/
theorem window_price_gle {Fr : Frame} (T : TwoTermData Fr q o)
    (D : PoleData Fr p N) (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (Jr Jc : Finset (Fin d))
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (hJr : ∀ z∈Jr,WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv)
    (K : Finset (Fin r)) :
    GLE p (2*(r+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d) (p-(H.tv+1-H.t0))))
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  let s := algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X
  let u := WrapOriginalEntry.normInv p Fr
  have hb := retained_window_bound H s u (WrapFrameResidue.spectral p)
    (WrapFrameResidue.normInv_ne p D) (WrapFrameResidue.normInv_constant p D)
  have hg := WrapPrefixFamily.window_gle H T D hsq Jr Jc hinj hJr hJc K
  apply hg.mono
  dsimp only [WrapCount.gain]
  change 2*(r+n*p+e)-(d+((Jr.card+Jc.card-d)+((Jr.card+Jc.card-d)-
    (WrapPrefixMember.fullRetained H s u).card)))≤_
  omega

end RetainedCount

section ReducedBorder
variable {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]

/-- The mixed-border moment identity needs only an own-source zero in
the residue field, so it applies to regularly transported directions. -/
theorem mixedBorder_response_mod (phi : R →+* K) (Q : Matrix α α R)
    (hQ : IsUnit Q.det) (uR uC sX sY : α → R) (h zX zY : R)
    (hz : phi (zX-sX ⬝ᵥ Q⁻¹ *ᵥ uR)=0)
    (hM : IsUnit (Matrix.fromBlocks Q (Matrix.of fun i (_:Unit) => sY i)
      (Matrix.of fun (_:Unit) j => sX j) (Matrix.of fun (_ _:Unit) => h)).det) :
    phi (Sum.elim uC (fun _:Unit => zY) ⬝ᵥ
      (Matrix.fromBlocks Q (Matrix.of fun i (_:Unit) => sY i)
        (Matrix.of fun (_:Unit) j => sX j) (Matrix.of fun (_ _:Unit) => h))⁻¹ *ᵥ
      Sum.elim uR (fun _:Unit => zX))=phi (uC ⬝ᵥ Q⁻¹ *ᵥ uR) := by
  classical
  let M := Matrix.fromBlocks Q (Matrix.of fun i (_:Unit) => sY i)
    (Matrix.of fun (_:Unit) j => sX j) (Matrix.of fun (_ _:Unit) => h)
  have hm : M.map phi=Matrix.fromBlocks (Q.map phi)
      (Matrix.of fun i (_:Unit) => phi (sY i))
      (Matrix.of fun (_:Unit) j => phi (sX j)) (Matrix.of fun (_ _:Unit) => phi h) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;> rfl
  have hmr : phi ∘ Sum.elim uR (fun _:Unit => zX)=
      Sum.elim (phi ∘ uR) (fun _:Unit => phi zX) := by
    funext i; cases i <;> rfl
  have hmc : phi ∘ Sum.elim uC (fun _:Unit => zY)=
      Sum.elim (phi ∘ uC) (fun _:Unit => phi zY) := by
    funext i; cases i <;> rfl
  have hsource : (phi ∘ sX) ⬝ᵥ (Q.map phi)⁻¹ *ᵥ (phi ∘ uR)=phi zX := by
    rw [map_sub] at hz
    exact (WrapPrefixMember.mapped_response phi Q hQ uR sX).trans (sub_eq_zero.mp hz).symm
  have hunit := WrapPrefixMember.mapped_block_unit phi M hM
  rw [hm] at hunit
  have hh := WrapAlgebra.mixedBorder_response_mixed (Q.map phi)
    (WrapPrefixMember.mapped_block_unit phi Q hQ) (phi ∘ uR) (phi ∘ uC)
    (phi ∘ sX) (phi ∘ sY) (phi h) (phi zX) (phi zY) hsource hunit
  have he := WrapPrefixMember.mapped_response phi M hM
    (Sum.elim uR (fun _:Unit => zX)) (Sum.elim uC (fun _:Unit => zY))
  rw [hm,hmr,hmc] at he
  exact he.symm.trans (hh.trans (WrapPrefixMember.mapped_response phi Q hQ uR uC))

end ReducedBorder

section ProfileAppend

/-- Append the last balanced row and column while preserving every
original common spectral coordinate. -/
def appendEquiv (k n : ℕ) : ((Fin k ⊕ Fin n) ⊕ Unit) ≃ (Fin k ⊕ Fin (n+1)) where
  toFun := Sum.elim (Sum.map id Fin.castSucc) (fun _ => Sum.inr (Fin.last n))
  invFun := Sum.elim (fun i => Sum.inl (Sum.inl i))
    (Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Sum.inr i)))
  left_inv i := by
    rcases i with (i|i)|i
    · rfl
    · simp
    · cases i; simp
  right_inv i := by
    cases i with
    | inl i => rfl
    | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- The next actual balanced pair is a mixed border, with independent
row and column nodes and no added common spectral entry. -/
theorem append_core (q o r k n gamma : ℕ) (s u : GaussLoc p) :
    (WrapPrefixType.core p q o r k (n+1) gamma s u).submatrix (appendEquiv k n) (appendEquiv k n)=
      Matrix.fromBlocks (WrapPrefixType.core p q o r k n gamma s u)
        (Matrix.of fun i (_:Unit) => WrapDeformedEntry.entry p q o u
          (WrapPrefixType.rows p r k n gamma i) (WrapJointProfile.colProfile p r gamma n))
        (Matrix.of fun (_:Unit) j => WrapDeformedEntry.entry p q o u
          (WrapJointProfile.rowProfile p r gamma n) (WrapPrefixType.cols p r k n gamma j))
        (Matrix.of fun (_ _:Unit) => WrapDeformedEntry.entry p q o u
          (WrapJointProfile.rowProfile p r gamma n) (WrapJointProfile.colProfile p r gamma n)) := by
  classical
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp [appendEquiv,WrapPrefixType.core,WrapFibreCore.core,
      WrapPrefixType.rows,WrapPrefixType.cols,Matrix.fromBlocks]


/-- Appending the actual pair only needs the transported own-source zero modulo p. -/
theorem append_moment_mod (q o r k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p)
    (hQ : IsUnit (WrapPrefixType.core p q o r k n gamma s u).det)
    (hM : IsUnit (WrapPrefixType.core p q o r k (n+1) gamma s u).det)
    (hz : WrapDeform.residue p (WrapPrefixWindow.rowOwn p q o r k n gamma
      (WrapJointProfile.rowProfile p r gamma n) s u direction)=0) :
    WrapPrefixType.moment p q o r k (n+1) gamma s u direction=
      WrapPrefixType.moment p q o r k n gamma s u direction := by
  classical
  let Q := WrapPrefixType.core p q o r k n gamma s u
  let uR := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
    (WrapPrefixType.rows p r k n gamma i)-direction
  let uC := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
    (WrapPrefixType.cols p r k n gamma i)-direction
  let sx := fun j => WrapDeformedEntry.entry p q o u
    (WrapJointProfile.rowProfile p r gamma n) (WrapPrefixType.cols p r k n gamma j)
  let sy := fun i => WrapDeformedEntry.entry p q o u
    (WrapPrefixType.rows p r k n gamma i) (WrapJointProfile.colProfile p r gamma n)
  let zx := WrapOwnCore.constants p u*WrapEntryRelation.load p q o
    (WrapJointProfile.rowProfile p r gamma n)-direction
  let zy := WrapOwnCore.constants p u*WrapEntryRelation.load p q o
    (WrapJointProfile.colProfile p r gamma n)-direction
  have hsource : WrapDeform.residue p (zx-sx ⬝ᵥ Q⁻¹ *ᵥ uR)=0 := hz
  have hb := append_core (p:=p) q o r k n gamma s u
  have hunit : IsUnit ((WrapPrefixType.core p q o r k (n+1) gamma s u).submatrix
      (appendEquiv k n) (appendEquiv k n)).det := by
    rw [Matrix.det_submatrix_equiv_self]
    exact hM
  rw [hb] at hunit
  have hm := mixedBorder_response_mod (WrapDeform.residue p) Q hQ uR uC sx sy
    (WrapDeformedEntry.entry p q o u (WrapJointProfile.rowProfile p r gamma n)
      (WrapJointProfile.colProfile p r gamma n)) zx zy hsource hunit
  have he := WrapTransport.response_reindex
    (WrapPrefixType.core p q o r k (n+1) gamma s u) (appendEquiv k n) (appendEquiv k n)
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (WrapPrefixType.rows p r k (n+1) gamma i)-direction)
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (WrapPrefixType.cols p r k (n+1) gamma i)-direction)
  have hr : (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (WrapPrefixType.rows p r k (n+1) gamma i)-direction) ∘ appendEquiv k n=
      Sum.elim uR (fun _:Unit => zx) := by
    funext i
    rcases i with (i|i)|i <;> rfl
  have hc : (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (WrapPrefixType.cols p r k (n+1) gamma i)-direction) ∘ appendEquiv k n=
      Sum.elim uC (fun _:Unit => zy) := by
    funext i
    rcases i with (i|i)|i <;> rfl
  rw [hr,hc,hb] at he
  exact (congrArg (WrapDeform.residue p) he.symm).trans hm
end ProfileAppend

section ResidualProfile
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- An actual residual balanced row occupies precisely the next row of
its original mixed quotient profile. -/
theorem residual_row_profile (gamma : ZMod p) (i : Fin b)
    (hi : (H.xs (Sum.inr i):ZMod p)=gamma) :
    H.xs (Sum.inr i)=WrapJointProfile.rowProfile p r gamma.val n := by
  have he : (H.er (Sum.inl i):ℕ)<p := lt_trans (H.er (Sum.inl i)).2 H.he
  have hf : H.xs (Sum.inr i)=r+2*n*p+2*(H.er (Sum.inl i):ℕ) := by
    change r+2*(n*p+(H.er (Sum.inl i):ℕ))=_
    ring
  have hc : ((r+2*(H.er (Sum.inl i):ℕ):ℕ):ZMod p)=gamma := by
    simpa only [hf,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using hi
  have hm := congrArg ZMod.val hc
  simp only [ZMod.val_natCast] at hm
  have hn := WrapJointProfile.row_node p r gamma.val (r+2*(H.er (Sum.inl i):ℕ))
    (Fact.out:p.Prime).pos (by rw [H.hp]; omega) (ZMod.val_lt gamma)
    (by omega) (by omega) hm (by omega)
  rw [hf,show r+2*n*p+2*(H.er (Sum.inl i):ℕ)=
    (r+2*(H.er (Sum.inl i):ℕ))+2*n*p by ring,hn]
  unfold WrapJointProfile.rowProfile
  ring

/-- The same original balanced slot retains its independent column
node at the next column of the complementary quotient profile. -/
theorem residual_col_profile (gamma : ZMod p) (i : Fin b)
    (hi : (H.xs (Sum.inr i):ZMod p)=gamma) :
    H.ys (Sum.inr i)=WrapJointProfile.colProfile p r gamma.val n := by
  have he : (H.ec (Sum.inl i):ℕ)<p := lt_trans (H.ec (Sum.inl i)).2 H.he
  have hf : H.ys (Sum.inr i)=r+2*n*p+2*(H.ec (Sum.inl i):ℕ)+1 := by
    change r+2*(n*p+(H.ec (Sum.inl i):ℕ))+1=_
    ring
  have hc : ((r+2*(H.ec (Sum.inl i):ℕ)+1:ℕ):ZMod p)=gamma := by
    have hy := (H.same_colour (Sum.inr i)).symm.trans hi
    simpa only [hf,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] using hy
  have hm := congrArg ZMod.val hc
  simp only [ZMod.val_natCast] at hm
  have hn := WrapJointProfile.col_node p r gamma.val (r+2*(H.ec (Sum.inl i):ℕ)+1)
    (Fact.out:p.Prime).pos (by rw [H.hp]; omega) (ZMod.val_lt gamma)
    (by omega) (by omega) hm (by omega)
  rw [hf,show r+2*n*p+2*(H.ec (Sum.inl i):ℕ)+1=
    (r+2*(H.ec (Sum.inl i):ℕ)+1)+2*n*p by ring,hn]
  unfold WrapJointProfile.colProfile
  ring

/-- Original residual balanced colours cannot occur twice. -/
theorem residual_colour_injective :
    Function.Injective (fun i:Fin b => (H.xs (Sum.inr i):ZMod p)) := by
  have hs : Function.Injective (fun i:Fin b => (H.er (Sum.inl i):ℕ)) := by
    intro i j he
    exact Sum.inl.inj (H.er.injective (Fin.ext he))
  have hh := WrapFibreCount.residual_injective p (r+2*n*p) H.hp2
    (fun i:Fin b => (H.er (Sum.inl i):ℕ)) hs
    (fun i => lt_trans (H.er (Sum.inl i)).2 H.he)
  simpa only [WrapPrefixWindow.Setup.xs,WrapPrefixCoreGeometry.xs_eq,WrapFibreCount.balancedRow] using hh

/-- A colour with a residual balanced pair has exactly n+1 actual
balanced slots, enumerated by the full periods and that unique pair. -/
noncomputable def balancedAppendEquiv (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) :
    (Fin n ⊕ Unit) ≃ WrapFibreIndex.Balanced p H.xs gamma where
  toFun := Sum.elim (fun c => ⟨Sum.inl (c,WrapJointProfile.colourSlot p r H.hp2 gamma),by
      unfold WrapPrefixWindow.Setup.xs WrapPrefixCoreGeometry.xs
      rw [WrapPrefixGeometry.row_cycle,WrapFibreCount.full_colour,WrapJointProfile.colourSlot_spec]⟩)
    (fun _ => ⟨Sum.inr j,hj⟩)
  invFun a := match a.1 with
    | Sum.inl (c,_) => Sum.inl c
    | Sum.inr _ => Sum.inr ()
  left_inv i := by cases i with | inl i => rfl | inr i => cases i; rfl
  right_inv a := by
    rcases a with ⟨⟨c,i⟩|i,hi⟩
    · apply Subtype.ext
      apply congrArg Sum.inl
      apply Prod.ext
      · rfl
      · apply WrapFibreCount.colour_injective p r H.hp2
        unfold WrapPrefixWindow.Setup.xs WrapPrefixCoreGeometry.xs at hi
        rw [WrapPrefixGeometry.row_cycle,WrapFibreCount.full_colour] at hi
        exact (WrapJointProfile.colourSlot_spec p r H.hp2 gamma).trans hi.symm
    · apply Subtype.ext
      exact congrArg Sum.inr (residual_colour_injective H (hj.trans hi.symm))

/-- Whole original colour fibre with its unique residual balanced pair. -/
noncomputable def wholeAppendEquiv (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) :
    ((Fin (WrapJointProfile.count p r gamma.val) ⊕ Fin n) ⊕ Unit) ≃
      {a // H.colour a=gamma} :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (WrapJointProfile.commonEquiv p r gamma)
      (balancedAppendEquiv H gamma j hj)).trans
      (Equiv.subtypeSum (p:=fun a => H.colour a=gamma)).symm)

theorem wholeAppend_row (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma)
    (i : (Fin (WrapJointProfile.count p r gamma.val) ⊕ Fin n) ⊕ Unit) :
    Sum.elim (fun a:Fin r => (a:ℕ)) H.xs (wholeAppendEquiv H gamma j hj i).1=
      WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val
        (appendEquiv _ n i) := by
  rcases i with (i|i)|i
  · rfl
  · change H.xs (Sum.inl (i,WrapJointProfile.colourSlot p r H.hp2 gamma))=_
    unfold WrapPrefixWindow.Setup.xs WrapPrefixCoreGeometry.xs
    rw [WrapPrefixGeometry.row_cycle]
    apply WrapJointProfile.full_row_profile p r gamma.val (Fact.out:p.Prime).pos
      (by rw [H.hp]; omega) (ZMod.val_lt gamma) i
    have he : (WrapCycles.row r p i (WrapJointProfile.colourSlot p r H.hp2 gamma):ZMod p)=gamma := by
      rw [WrapFibreCount.full_colour,WrapJointProfile.colourSlot_spec]
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast] using hv
  · exact residual_row_profile H gamma j hj

theorem wholeAppend_col (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma)
    (i : (Fin (WrapJointProfile.count p r gamma.val) ⊕ Fin n) ⊕ Unit) :
    Sum.elim (fun a:Fin r => (a:ℕ)) H.ys (wholeAppendEquiv H gamma j hj i).1=
      WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val
        (appendEquiv _ n i) := by
  rcases i with (i|i)|i
  · rfl
  · change H.ys (Sum.inl (i,WrapJointProfile.colourSlot p r H.hp2 gamma))=_
    unfold WrapPrefixWindow.Setup.ys WrapPrefixCoreGeometry.ys
    rw [WrapPrefixGeometry.col_cycle]
    apply WrapJointProfile.full_col_profile p r gamma.val shift (Fact.out:p.Prime).pos
      (by rw [H.hp]; omega) (ZMod.val_lt gamma) i
    have he : (WrapCycles.col r p (Fact.out:p.Prime).pos shift i
        (WrapJointProfile.colourSlot p r H.hp2 gamma):ZMod p)=gamma := by
      rw [←WrapCycles.colour_eq r p shift H.hp,WrapFibreCount.full_colour,WrapJointProfile.colourSlot_spec]
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast] using hv
  · exact residual_col_profile H gamma j hj

/-- Exact binding of the original colour block to n+1 balanced pairs;
only original common coordinates carry the spectral variable. -/
theorem wholeAppend_core (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) (s u : GaussLoc p) :
    ((H.core s u).toSquareBlock H.colour gamma).submatrix
      (wholeAppendEquiv H gamma j hj) (wholeAppendEquiv H gamma j hj)=
      (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val s u).submatrix
        (appendEquiv _ n) (appendEquiv _ n) := by
  classical
  have he (i k : (Fin (WrapJointProfile.count p r gamma.val) ⊕ Fin n) ⊕ Unit) :
      WrapDeformedEntry.entry p q o u
        (Sum.elim (fun a:Fin r => (a:ℕ)) H.xs (wholeAppendEquiv H gamma j hj i).1)
        (Sum.elim (fun a:Fin r => (a:ℕ)) H.ys (wholeAppendEquiv H gamma j hj k).1)=
      WrapDeformedEntry.entry p q o u
        (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val (appendEquiv _ n i))
        (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val (appendEquiv _ n k)) := by
    rw [wholeAppend_row H gamma j hj i,wholeAppend_col H gamma j hj k]
  ext i k
  change (H.core s u) (wholeAppendEquiv H gamma j hj i).1 (wholeAppendEquiv H gamma j hj k).1=_
  simp only [WrapPrefixWindow.Setup.core,WrapFibreCore.core,Matrix.add_apply,Matrix.of_apply,
    Matrix.submatrix_apply] at *
  rw [he]
  congr 1
  rcases i with (i|i)|i <;> rcases k with (k|k)|k
  · change WrapOwnCore.constants p s*(if (WrapJointProfile.commonEquiv p r gamma i).1=
        (WrapJointProfile.commonEquiv p r gamma k).1 then 1 else 0)=
      WrapOwnCore.constants p s*(if i=k then 1 else 0)
    have heq : (WrapJointProfile.commonEquiv p r gamma i).1=
        (WrapJointProfile.commonEquiv p r gamma k).1 ↔ i=k :=
      ⟨fun h => (WrapJointProfile.commonEquiv p r gamma).injective (Subtype.ext h),fun h => by rw [h]⟩
    simp only [heq]
  all_goals rfl

/-- Every independently loaded response on a residual-present original
colour block is its n+1-pair canonical response. -/
theorem residual_profile_response (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) (s u : GaussLoc p)
    (FR FC : ℕ → WrapDeform.Extension p) :
    (fun a:{a // H.colour a=gamma} =>
      FC (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys a.1)) ⬝ᵥ
      ((H.core s u).toSquareBlock H.colour gamma)⁻¹ *ᵥ
      (fun a => FR (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs a.1))=
    (fun i => FC (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i)) ⬝ᵥ
      (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val s u)⁻¹ *ᵥ
      (fun i => FR (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i)) := by
  let E : ((Fin (WrapJointProfile.count p r gamma.val) ⊕ Fin n) ⊕ Unit) ≃
      {a // H.colour a=gamma} := wholeAppendEquiv H gamma j hj
  let A := appendEquiv (WrapJointProfile.count p r gamma.val) n
  have hactual := WrapTransport.response_reindex ((H.core s u).toSquareBlock H.colour gamma) E E
    (fun a => FR (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs a.1))
    (fun a => FC (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys a.1))
  have hcanonical := WrapTransport.response_reindex
    (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val s u) A A
    (fun i => FR (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i))
    (fun i => FC (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i))
  have hr : (fun a:{a // H.colour a=gamma} => FR (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs a.1)) ∘ E=
      (fun i => FR (WrapPrefixType.rows p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i)) ∘ A := by
    funext i
    exact congrArg FR (wholeAppend_row H gamma j hj i)
  have hc : (fun a:{a // H.colour a=gamma} => FC (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys a.1)) ∘ E=
      (fun i => FC (WrapPrefixType.cols p r (WrapJointProfile.count p r gamma.val) (n+1) gamma.val i)) ∘ A := by
    funext i
    exact congrArg FC (wholeAppend_col H gamma j hj i)
  rw [hr,hc,wholeAppend_core H gamma j hj s u] at hactual
  exact hactual.symm.trans hcanonical

/-- The source moment of an original residual-present colour is
exactly its canonical n+1-pair mixed moment. -/
theorem residual_profile_moment (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    H.moment s u gamma=WrapPrefixType.moment p q o r
      (WrapJointProfile.count p r gamma.val) (n+1) gamma.val s u (H.anchor s u) := by
  classical
  have hD := H.own_unit s u hs hu huc
  have hb : ∀ a b,H.colour a≠H.colour b → H.own s u a b=0 := by
    intro a b hab
    exact if_neg hab
  have hblk : blk (H.own s u) H.colour gamma=(H.core s u).toSquareBlock H.colour gamma := by
    ext i k
    change (if H.colour i.1=H.colour k.1 then H.core s u i.1 k.1 else 0)=H.core s u i.1 k.1
    rw [if_pos (i.2.trans k.2.symm)]
  have he := WrapType.mixed_fiber_moment_response (H.own s u) H.colour hD hb gamma
    (fun i => H.rowLoad u i-H.anchor s u) (fun i => H.colLoad u i-H.anchor s u)
    (WrapDeform.residue p)
  rw [hblk] at he
  have hf := residual_profile_response H gamma j hj s u
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-H.anchor s u)
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-H.anchor s u)
  exact he.trans (congrArg (WrapDeform.residue p) hf)

/-- The canonical n+1-pair matrix is a unit because it is the
literal original own block under the proved fibre equivalence. -/
theorem residual_profile_unit (gamma : ZMod p) (j : Fin b)
    (hj : (H.xs (Sum.inr j):ZMod p)=gamma) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val)
      (n+1) gamma.val s u).det := by
  classical
  have hD := H.own_unit s u hs hu huc
  have hb : ∀ a b,H.colour a≠H.colour b → H.own s u a b=0 := by
    intro a b hab
    exact if_neg hab
  have hblk : blk (H.own s u) H.colour gamma=(H.core s u).toSquareBlock H.colour gamma := by
    ext i k
    change (if H.colour i.1=H.colour k.1 then H.core s u i.1 k.1 else 0)=H.core s u i.1 k.1
    rw [if_pos (i.2.trans k.2.symm)]
  have hunit := (inv_restrict (H.own s u) H.colour hD hb gamma).1
  rw [hblk] at hunit
  have he := congrArg Matrix.det (wholeAppend_core H gamma j hj s u)
  rw [Matrix.det_submatrix_equiv_self,Matrix.det_submatrix_equiv_self] at he
  exact he ▸ hunit

end ResidualProfile

section VirtualTranslation
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Regular translation preserves the reduced whole matrix, even for
virtual target nodes beyond the original determinant's last node. -/
theorem translated_matrix_map (q o t delta : ℕ) (u : GaussLoc p)
    (rows cols : α → ℕ) (P : Matrix α α (WrapDeform.Extension p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 delta,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P).map
      (WrapDeform.residue p)=
    (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P).map
      (WrapDeform.residue p) := by
  ext i j
  simp only [Matrix.map_apply,Matrix.add_apply,Matrix.of_apply,map_add]
  rw [WrapPrefixType.entry_residue_shift p q o _ _ t delta u (hr i) (hc j) hw]

/-- A virtual target matrix is a unit because its reduction is the
original unit matrix's reduction. No bound on the virtual node is needed. -/
theorem unit_of_same_reduction (Q0 Q1 : Matrix α α (WrapDeform.Extension p))
    (hQ : IsUnit Q0.det)
    (hm : Q1.map (WrapDeform.residue p)=Q0.map (WrapDeform.residue p)) :
    IsUnit Q1.det := by
  apply WrapBalancedTest.unit_ne p
  change WrapDeform.residue p Q1.det≠0
  have he : WrapDeform.residue p Q1.det=WrapDeform.residue p Q0.det := by
    simpa only [RingHom.map_det,RingHom.mapMatrix_apply] using congrArg Matrix.det hm
  rw [he]
  exact (hQ.map (WrapDeform.residue p)).ne_zero

/-- The independently loaded mixed moment is unchanged by regular
translation of every original node, with target units inferred from the
unchanged reduction rather than a virtual-node arithmetic hypothesis. -/
theorem translated_moment (q o t delta : ℕ) (s u : GaussLoc p)
    (rows cols : α → ℕ) (P : Matrix α α (WrapDeform.Extension p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 delta,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ : IsUnit (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P).det)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (cols i+delta)-direction) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P)⁻¹ *ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+delta)-direction))=
    WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (cols i)-direction) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P)⁻¹ *ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)-direction)) := by
  let Q0 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P
  let Q1 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P
  have hm : Q1.map (WrapDeform.residue p)=Q0.map (WrapDeform.residue p) :=
    translated_matrix_map q o t delta u rows cols P hr hc hw
  have hQ1 := unit_of_same_reduction Q0 Q1 hQ hm
  have hi : Q1⁻¹.map (WrapDeform.residue p)=Q0⁻¹.map (WrapDeform.residue p) := by
    rw [←map_inv_of_unit (WrapDeform.residue p) Q1 hQ1,
      ←map_inv_of_unit (WrapDeform.residue p) Q0 hQ,hm]
  simp only [dotProduct,Matrix.mulVec,map_sum,map_mul,map_sub]
  apply Finset.sum_congr rfl
  intro i _
  have hci := WrapPrefixType.load_residue_shift p q o _ t delta u (hc i) hw
  simp only [map_mul] at hci
  rw [hci]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hrj := WrapPrefixType.load_residue_shift p q o _ t delta u (hr j) hw
  simp only [map_mul] at hrj
  rw [hrj]
  have he := congrFun (congrFun hi i) j
  exact congrArg (fun z => z*(WrapDeform.residue p
    (WrapOwnCore.constants p u)*WrapDeform.residue p (WrapEntryRelation.load p q o (rows j))-
      WrapDeform.residue p direction)) he

/-- Virtual regular translation preserves the reduced own source,
including the original spectral part and both physical node families. -/
theorem translated_own_source (q o t delta : ℕ) (u : GaussLoc p)
    (rows cols : α → ℕ) (P : Matrix α α (WrapDeform.Extension p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 delta,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ : IsUnit (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P).det)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p ((WrapOwnCore.constants p u*WrapEntryRelation.load p q o (t+delta)-direction)-
      (fun i => WrapDeformedEntry.entry p q o u (t+delta) (cols i+delta)) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P)⁻¹ *ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+delta)-direction))=
    WrapDeform.residue p ((WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-direction)-
      (fun i => WrapDeformedEntry.entry p q o u t (cols i)) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P)⁻¹ *ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)-direction)) := by
  let Q0 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P
  let Q1 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P
  have hm : Q1.map (WrapDeform.residue p)=Q0.map (WrapDeform.residue p) :=
    translated_matrix_map q o t delta u rows cols P hr hc hw
  have hQ1 := unit_of_same_reduction Q0 Q1 hQ hm
  have he := WrapPrefixType.response_map_congr (WrapDeform.residue p) Q1 Q0 hQ1 hQ
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i+delta)-direction)
    (fun i => WrapDeformedEntry.entry p q o u (t+delta) (cols i+delta))
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)-direction)
    (fun i => WrapDeformedEntry.entry p q o u t (cols i)) hm
    (fun i => by
      simp only [map_sub]
      rw [WrapPrefixType.load_residue_shift p q o _ t delta u (hr i) hw])
    (fun i => WrapPrefixType.entry_residue_shift p q o t _ t delta u rfl (hc i) hw)
  simp only [map_sub]
  rw [he]
  have ht := WrapPrefixType.load_residue_shift p q o t t delta u rfl hw
  exact congrArg (fun z => z-WrapDeform.residue p direction-
    WrapDeform.residue p ((fun i => WrapDeformedEntry.entry p q o u t (cols i)) ⬝ᵥ Q0⁻¹ *ᵥ
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (rows i)-direction))) ht


end VirtualTranslation

section ReducedReplacement
variable {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]

/-- Column replacement preserves the reduced mixed moment when its
zone load is an own-source zero modulo the uniformizer. Exact equality
of generic elimination fractions is unnecessary. -/
theorem updateCol_response_mod (phi : R →+* K) (Q : Matrix α α R)
    (hQ : IsUnit Q.det) (uR uC v : α → R) (h : α) (z : R)
    (hM : IsUnit (Q.updateCol h v).det)
    (hz : phi (z-uC ⬝ᵥ Q⁻¹ *ᵥ v)=0) :
    phi (Function.update uC h z ⬝ᵥ (Q.updateCol h v)⁻¹ *ᵥ uR)=
      phi (uC ⬝ᵥ Q⁻¹ *ᵥ uR) := by
  classical
  let Q' := Q.map phi
  let r' := phi ∘ uR
  let c' := phi ∘ uC
  let v' := phi ∘ v
  have hQ' : IsUnit Q'.det := WrapPrefixMember.mapped_block_unit phi Q hQ
  have hM' : IsUnit (Q'.updateCol h v').det := by
    have hh := WrapPrefixMember.mapped_block_unit phi (Q.updateCol h v) hM
    simpa only [Matrix.map_updateCol,Function.comp_def,Q',v'] using hh
  have hz' : phi z=c' ⬝ᵥ Q'⁻¹ *ᵥ v' := by
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).trans (WrapPrefixMember.mapped_response phi Q hQ v uC).symm
  have he : phi ∘ Function.update uC h z=
      Function.update c' h ((c' ᵥ* Q'⁻¹) ⬝ᵥ v') := by
    funext i
    by_cases hi : i=h
    · subst i
      simp only [Function.comp_apply,Function.update_self]
      rw [←Matrix.dotProduct_mulVec]
      exact hz'
    · simp only [Function.comp_apply,Function.update_of_ne hi,c']
  have hh := WrapAlgebra.updateCol_response_mixed Q' hQ' r' c' v' h hM'
  have hm := WrapPrefixMember.mapped_response phi (Q.updateCol h v) hM uR (Function.update uC h z)
  rw [he] at hm
  have hmatrix : (Q.updateCol h v).map phi=Q'.updateCol h v' := by
    simp only [Matrix.map_updateCol,Function.comp_def,Q',v']
  rw [hmatrix] at hm
  exact hm.symm.trans (hh.trans (WrapPrefixMember.mapped_response phi Q hQ uR uC))

end ReducedReplacement

section CommonCut

/-- Across the common-count cut, the first balanced row becomes the
last reference common row; every other row retains its original node. -/
def rowCutEquiv (k n : ℕ) : (Fin k ⊕ Fin (n+1)) ≃ (Fin (k+1) ⊕ Fin n) where
  toFun := Sum.elim (fun i => Sum.inl i.castSucc)
    (Fin.cases (Sum.inl (Fin.last k)) (fun i => Sum.inr i))
  invFun := Sum.elim (Fin.lastCases (Sum.inr 0) (fun i => Sum.inl i))
    (fun i => Sum.inr i.succ)
  left_inv i := by
    cases i with
    | inl i => simp
    | inr i => refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    cases i with
    | inl i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    | inr i => simp

/-- Independently, the last balanced column occupies the last reference
common column, the unique column replaced by the actual zone column. -/
def colCutEquiv (k n : ℕ) : (Fin k ⊕ Fin (n+1)) ≃ (Fin (k+1) ⊕ Fin n) where
  toFun := Sum.elim (fun i => Sum.inl i.castSucc)
    (Fin.lastCases (Sum.inl (Fin.last k)) (fun i => Sum.inr i))
  invFun := Sum.elim (Fin.lastCases (Sum.inr (Fin.last n)) (fun i => Sum.inl i))
    (fun i => Sum.inr i.castSucc)
  left_inv i := by
    cases i with
    | inl i => simp
    | inr i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv i := by
    cases i with
    | inl i => refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    | inr i => simp

/-- The row permutation binds the lower and upper quotient profiles
pointwise, without identifying their independent column orderings. -/
theorem rowCut_nodes (gamma k n : ℕ) (i : Fin k ⊕ Fin (n+1)) :
    Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
      (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p) i=
    Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) (rowCutEquiv k n i) := by
  cases i with
  | inl i => rfl
  | inr i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rowCutEquiv]
    · simp [rowCutEquiv,Fin.val_succ]
      congr 1
      omega

/-- Every unchanged column has its literal reference node; the last
balanced column is precisely the one replaced by the zone column. -/
theorem colCut_nodes (gamma k n : ℕ) (i : Fin k ⊕ Fin (n+1))
    (hi : i≠Sum.inr (Fin.last n)) :
    Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
      (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ)+1)*p) i=
    Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) (colCutEquiv k n i) := by
  cases i with
  | inl i => rfl
  | inr i =>
    have hlast : i≠Fin.last n := fun he => hi (congrArg Sum.inr he)
    obtain ⟨j,rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    simp [colCutEquiv]
    congr 1
    omega

/-- Original lower-count profile, including its last balanced pair. -/
noncomputable def lowerCutCore (q o gamma k n : ℕ) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun i:Fin (n+1) => gamma+(k+2*(i:ℕ))*p)
    (fun i:Fin (n+1) => gamma+(k+2*(i:ℕ)+1)*p)

/-- Transported upper-count reference profile, with its original
common spectral coordinates and n balanced pairs. -/
noncomputable def upperCutCore (q o gamma k n : ℕ) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (fun i:Fin (k+1) => gamma+(i:ℕ)*p)
    (fun i:Fin n => gamma+(k+2+2*(i:ℕ))*p)
    (fun i:Fin n => gamma+(k+1+2*(i:ℕ))*p)

/-- The actual matrix across the count cut is exactly one column
replacement of the independently reindexed reference. -/
theorem cut_core_updateCol (q o gamma k n : ℕ) (s u : GaussLoc p) :
    lowerCutCore (p:=p) q o gamma k n s u=
      ((upperCutCore (p:=p) q o gamma k n s u).submatrix
        (rowCutEquiv k n) (colCutEquiv k n)).updateCol (Sum.inr (Fin.last n))
        (fun i => WrapDeformedEntry.entry p q o u
          (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
            (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p) i)
          (gamma+(k+2*n+1)*p)) := by
  classical
  ext i j
  by_cases hj : j=Sum.inr (Fin.last n)
  · subst j
    rw [Matrix.updateCol_self]
    cases i <;> simp [lowerCutCore,WrapFibreCore.core]
  · rw [Matrix.updateCol_ne hj]
    have he : WrapDeformedEntry.entry p q o u
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
          (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p) i)
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
          (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ)+1)*p) j)=
      WrapDeformedEntry.entry p q o u
        (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) (rowCutEquiv k n i))
        (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) (colCutEquiv k n j)) := by
      rw [rowCut_nodes,colCut_nodes (p:=p) gamma k n j hj]
    change WrapDeformedEntry.entry p q o u
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
          (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p) i)
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
          (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ)+1)*p) j)+
        (Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix (Fin k) (Fin k) (WrapDeform.Extension p))) 0 0 0) i j =
      WrapDeformedEntry.entry p q o u
        (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) (rowCutEquiv k n i))
        (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) (colCutEquiv k n j))+
        (Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix (Fin (k+1)) (Fin (k+1)) (WrapDeform.Extension p))) 0 0 0)
          (rowCutEquiv k n i) (colCutEquiv k n j)
    rw [he]
    congr 1
    cases j with
    | inl j =>
      cases i with
      | inl i => simp [rowCutEquiv,colCutEquiv,Matrix.one_apply]
      | inr i => refine Fin.cases ?_ (fun z => ?_) i <;>
          simp [rowCutEquiv,colCutEquiv,Matrix.one_apply,Fin.castSucc_ne_last,Ne.symm (Fin.castSucc_ne_last j)]
    | inr j =>
      have hlast : j≠Fin.last n := fun h => hj (congrArg Sum.inr h)
      obtain ⟨z,rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
      cases i with
      | inl i => simp [rowCutEquiv,colCutEquiv]
      | inr i => refine Fin.cases ?_ (fun z => ?_) i <;> simp [rowCutEquiv,colCutEquiv]

/-- The actual mixed response across the common-count cut agrees
with the transported reference whenever the replaced column's own
source vanishes in the residue field. -/
theorem cut_response (q o gamma k n : ℕ) (s u : GaussLoc p)
    (FR FC : ℕ → WrapDeform.Extension p)
    (hQ : IsUnit (upperCutCore (p:=p) q o gamma k n s u).det)
    (hM : IsUnit (lowerCutCore (p:=p) q o gamma k n s u).det)
    (hz : WrapDeform.residue p (FC (gamma+(k+2*n+1)*p)-
      (fun i => FC (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) i)) ⬝ᵥ
      (upperCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => WrapDeformedEntry.entry p q o u
        (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) i)
        (gamma+(k+2*n+1)*p)))=0) :
    WrapDeform.residue p ((fun i => FC (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
        (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ)+1)*p) i)) ⬝ᵥ
      (lowerCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => FR (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
        (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p) i)))=
    WrapDeform.residue p ((fun i => FC (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) i)) ⬝ᵥ
      (upperCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => FR (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) i))) := by
  classical
  let R0 := Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
    (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ))*p)
  let C0 := Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
    (fun j:Fin (n+1) => gamma+(k+2*(j:ℕ)+1)*p)
  let R1 := Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p)
  let C1 := Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p)
  let Q := upperCutCore (p:=p) q o gamma k n s u
  let G := Q.submatrix (rowCutEquiv k n) (colCutEquiv k n)
  let z := gamma+(k+2*n+1)*p
  let v := fun i => WrapDeformedEntry.entry p q o u (R0 i) z
  let uc := FC ∘ C1
  let ur := FR ∘ R1
  have hG : IsUnit G.det := by
    apply Matrix.isUnit_iff_isUnit_det G |>.mp
    apply (Matrix.isUnit_submatrix_equiv (rowCutEquiv k n) (colCutEquiv k n)).mpr
    exact (Matrix.isUnit_iff_isUnit_det Q).mpr hQ
  have hcore : lowerCutCore (p:=p) q o gamma k n s u=G.updateCol (Sum.inr (Fin.last n)) v :=
    cut_core_updateCol q o gamma k n s u
  have hMG : IsUnit (G.updateCol (Sum.inr (Fin.last n)) v).det := hcore ▸ hM
  have hrow : ur ∘ rowCutEquiv k n=FR ∘ R0 := by
    funext i
    exact congrArg FR (rowCut_nodes (p:=p) gamma k n i).symm
  have hcol : Function.update (uc ∘ colCutEquiv k n) (Sum.inr (Fin.last n)) (FC z)=FC ∘ C0 := by
    funext i
    by_cases hi : i=Sum.inr (Fin.last n)
    · subst i
      simp only [Function.update_self,Function.comp_apply,C0,Sum.elim_inr,Fin.val_last,z]
    · rw [Function.update_of_ne hi]
      exact congrArg FC (colCut_nodes (p:=p) gamma k n i hi).symm
  have hsig : (fun i => WrapDeformedEntry.entry p q o u (R1 i) z) ∘ rowCutEquiv k n=v := by
    funext i
    exact congrArg (fun t => WrapDeformedEntry.entry p q o u t z) (rowCut_nodes (p:=p) gamma k n i).symm
  have he := WrapTransport.response_reindex Q (rowCutEquiv k n) (colCutEquiv k n)
    (fun i => WrapDeformedEntry.entry p q o u (R1 i) z) uc
  rw [hsig] at he
  have hzG : WrapDeform.residue p (FC z-(uc ∘ colCutEquiv k n) ⬝ᵥ G⁻¹ *ᵥ v)=0 := by
    rw [he]
    exact hz
  have hg := updateCol_response_mod (WrapDeform.residue p) G hG
    (ur ∘ rowCutEquiv k n) (uc ∘ colCutEquiv k n) v (Sum.inr (Fin.last n)) (FC z) hMG hzG
  rw [←hcore,hcol,hrow] at hg
  have href := WrapTransport.response_reindex Q (rowCutEquiv k n) (colCutEquiv k n) ur uc
  rw [hrow] at href
  exact hg.trans (congrArg (WrapDeform.residue p) href)


/-- Lower-count reference before its top-extension pair. -/
noncomputable def baseCutCore (q o gamma k n : ℕ) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ))*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ)+1)*p)

/-- Independently ordered actual upper-count matrix for top extension. -/
noncomputable def topCutCore (q o gamma k n : ℕ) (s u : GaussLoc p) :=
  (upperCutCore (p:=p) q o gamma k n s u).submatrix
    (fun i => rowCutEquiv k n (appendEquiv k n i))
    (fun i => colCutEquiv k n (appendEquiv k n i))

/-- All old columns agree with the original n+1-pair profile; only the
new common column differs. -/
theorem top_cut_old_column (q o gamma k n : ℕ) (s u : GaussLoc p)
    (i : (Fin k ⊕ Fin n) ⊕ Unit) (j : Fin k ⊕ Fin n) :
    topCutCore (p:=p) q o gamma k n s u i (Sum.inl j)=
      (lowerCutCore (p:=p) q o gamma k n s u)
        (appendEquiv k n i) (appendEquiv k n (Sum.inl j)) := by
  classical
  have hne : appendEquiv k n (Sum.inl j)≠Sum.inr (Fin.last n) := by
    cases j <;> simp [appendEquiv,Fin.castSucc_ne_last]
  have he := congrFun (congrFun (cut_core_updateCol (p:=p) q o gamma k n s u)
    (appendEquiv k n i)) (appendEquiv k n (Sum.inl j))
  rw [Matrix.updateCol_ne hne] at he
  exact he.symm

/-- The original common spectral block restricts literally to the
lower-count reference after the top-extension reindexing. -/
theorem top_cut_block (q o gamma k n : ℕ) (s u : GaussLoc p) :
    (topCutCore (p:=p) q o gamma k n s u).toBlocks₁₁=
      baseCutCore (p:=p) q o gamma k n s u := by
  ext i j
  change topCutCore (p:=p) q o gamma k n s u (Sum.inl i) (Sum.inl j)=_
  rw [top_cut_old_column]
  cases i <;> cases j <;> rfl

/-- The new actual row is the reference zone row. Its opposite column
can be arbitrary, exactly as allowed by the mixed-border identity. -/
theorem top_cut_row (q o gamma k n : ℕ) (s u : GaussLoc p) (j : Fin k ⊕ Fin n) :
    topCutCore (p:=p) q o gamma k n s u (Sum.inr ()) (Sum.inl j)=
      WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p)
        (Sum.elim (fun i:Fin k => gamma+(i:ℕ)*p)
          (fun i:Fin n => gamma+(k+2*(i:ℕ)+1)*p) j) := by
  rw [top_cut_old_column]
  cases j <;> simp [lowerCutCore,WrapFibreCore.core,appendEquiv]

/-- The mixed top extension's whole row node family is literal. -/
theorem top_cut_rows (gamma k n : ℕ) (i : (Fin k ⊕ Fin n) ⊕ Unit) :
    Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) (rowCutEquiv k n (appendEquiv k n i))=
    Sum.elim (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+2*(j:ℕ))*p)) (fun _:Unit => gamma+(k+2*n)*p) i := by
  rw [←rowCut_nodes (p:=p) gamma k n (appendEquiv k n i)]
  rcases i with (i|i)|i <;> rfl

/-- The new column is the original common node, while every previous
column is retained in its independent original ordering. -/
theorem top_cut_cols (gamma k n : ℕ) (i : (Fin k ⊕ Fin n) ⊕ Unit) :
    Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) (colCutEquiv k n (appendEquiv k n i))=
    Sum.elim (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
      (fun j:Fin n => gamma+(k+2*(j:ℕ)+1)*p)) (fun _:Unit => gamma+k*p) i := by
  rcases i with (i|i)|i
  · rfl
  · simp [appendEquiv,colCutEquiv]
    congr 1
    omega
  · simp [appendEquiv,colCutEquiv]

/-- Actual top extension preserves the reduced mixed moment. This
uses the true new row, the true common column and independent loads. -/
theorem top_cut_response (q o gamma k n : ℕ) (s u : GaussLoc p)
    (FR FC : ℕ → WrapDeform.Extension p)
    (hQ : IsUnit (baseCutCore (p:=p) q o gamma k n s u).det)
    (hM : IsUnit (upperCutCore (p:=p) q o gamma k n s u).det)
    (hz : WrapDeform.residue p (FR (gamma+(k+2*n)*p)-
      (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p)
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
          (fun j:Fin n => gamma+(k+2*(j:ℕ)+1)*p) i)) ⬝ᵥ
      (baseCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => FR (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+2*(j:ℕ))*p) i)))=0) :
    WrapDeform.residue p ((fun i => FC (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p) i)) ⬝ᵥ
      (upperCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => FR (Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p) i)))=
    WrapDeform.residue p ((fun i => FC (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+2*(j:ℕ)+1)*p) i)) ⬝ᵥ
      (baseCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => FR (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
        (fun j:Fin n => gamma+(k+2*(j:ℕ))*p) i))) := by
  classical
  let R0 := Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+2*(j:ℕ))*p)
  let C0 := Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+2*(j:ℕ)+1)*p)
  let R1 := Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+2+2*(j:ℕ))*p)
  let C1 := Sum.elim (fun j:Fin (k+1) => gamma+(j:ℕ)*p)
    (fun j:Fin n => gamma+(k+1+2*(j:ℕ))*p)
  let ER := (appendEquiv k n).trans (rowCutEquiv k n)
  let EC := (appendEquiv k n).trans (colCutEquiv k n)
  let M := topCutCore (p:=p) q o gamma k n s u
  let Q := baseCutCore (p:=p) q o gamma k n s u
  let sx := fun j => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (C0 j)
  let sy := fun i => M (Sum.inl i) (Sum.inr ())
  let h := M (Sum.inr ()) (Sum.inr ())
  have hd : M=Matrix.fromBlocks Q (Matrix.of fun i (_:Unit) => sy i)
      (Matrix.of fun (_:Unit) j => sx j) (Matrix.of fun (_ _:Unit) => h) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · exact congrFun (congrFun (top_cut_block (p:=p) q o gamma k n s u) i) j
    · cases j; rfl
    · cases i; exact top_cut_row (p:=p) q o gamma k n s u j
    · cases i; cases j; rfl
  have hunit : IsUnit M.det := by
    apply (Matrix.isUnit_iff_isUnit_det M).mp
    apply (Matrix.isUnit_submatrix_equiv ER EC).mpr
    exact (Matrix.isUnit_iff_isUnit_det _).mpr hM
  rw [hd] at hunit
  have hm := mixedBorder_response_mod (WrapDeform.residue p) Q hQ (FR ∘ R0) (FC ∘ C0)
    sx sy h (FR (gamma+(k+2*n)*p)) (FC (gamma+k*p)) hz hunit
  have he := WrapTransport.response_reindex (upperCutCore (p:=p) q o gamma k n s u)
    ER EC (FR ∘ R1) (FC ∘ C1)
  have hr : (FR ∘ R1) ∘ ER=Sum.elim (FR ∘ R0) (fun _:Unit => FR (gamma+(k+2*n)*p)) := by
    funext i
    have hh := congrArg FR (top_cut_rows (p:=p) gamma k n i)
    rcases i with i|i <;> exact hh
  have hc : (FC ∘ C1) ∘ EC=Sum.elim (FC ∘ C0) (fun _:Unit => FC (gamma+k*p)) := by
    funext i
    have hh := congrArg FC (top_cut_cols (p:=p) gamma k n i)
    rcases i with i|i <;> exact hh
  rw [hr,hc] at he
  change _ ⬝ᵥ M⁻¹ *ᵥ _=_ at he
  rw [hd] at he
  exact (congrArg (WrapDeform.residue p) he.symm).trans hm

end CommonCut

section ProfileArithmetic

/-- The first original representative of a colour determines its
common count uniquely. -/
theorem count_eq_of_first (p r gamma k : ℕ) (hp : 0<p) (hg : gamma<p)
    (hlo : r≤gamma+k*p) (hhi : gamma+k*p<r+p) :
    WrapJointProfile.count p r gamma=k := by
  have hb := WrapJointProfile.lower_bounds p r gamma hp hg
  have hle : WrapJointProfile.count p r gamma≤k := by
    have hn : ¬k<WrapJointProfile.count p r gamma := by
      intro hh
      exact (not_lt_of_ge hlo) ((WrapJointProfile.common_bound p r gamma k hp hg).mpr hh)
    omega
  have hge : k≤WrapJointProfile.count p r gamma := by
    by_contra hn
    have hm := Nat.mul_le_mul_right p (show WrapJointProfile.count p r gamma+1≤k by omega)
    unfold WrapJointProfile.lower at hb
    nlinarith
  omega

/-- Restoring complete original periods adds that number to the common
count without changing the physical residue. -/
theorem count_add_periods (p r gamma n : ℕ) (hp : 0<p) (hg : gamma<p) :
    WrapJointProfile.count p (r+n*p) gamma=WrapJointProfile.count p r gamma+n := by
  have hb := WrapJointProfile.lower_bounds p r gamma hp hg
  unfold WrapJointProfile.lower at hb
  apply count_eq_of_first p (r+n*p) gamma (WrapJointProfile.count p r gamma+n) hp hg <;> nlinarith

/-- A residual interval of length at most one period adds exactly the
colour whose first original representative lies in that interval. -/
theorem count_add_residual (p r gamma b : ℕ) (hp : 0<p) (hg : gamma<p) (hbp : b≤p) :
    WrapJointProfile.count p (r+b) gamma=WrapJointProfile.count p r gamma+
      if WrapJointProfile.lower p r gamma<r+b then 1 else 0 := by
  have hb := WrapJointProfile.lower_bounds p r gamma hp hg
  by_cases hc : WrapJointProfile.lower p r gamma<r+b
  · rw [if_pos hc]
    apply count_eq_of_first p (r+b) gamma (WrapJointProfile.count p r gamma+1) hp hg
    · unfold WrapJointProfile.lower at hb hc
      nlinarith
    · unfold WrapJointProfile.lower at hc
      nlinarith
  · rw [if_neg hc,Nat.add_zero]
    apply count_eq_of_first p (r+b) gamma (WrapJointProfile.count p r gamma) hp hg
    · unfold WrapJointProfile.lower at hc
      omega
    · unfold WrapJointProfile.lower at hb
      omega

/-- A colour belongs to a short original residual interval precisely
when its first original representative lies below the interval's end. -/
theorem residual_interval_iff (p r b : ℕ) [Fact p.Prime] (hp : 0<p) (hbp : b≤p) (gamma : ZMod p) :
    (∃ i:Fin b,((r+(i:ℕ):ℕ):ZMod p)=gamma) ↔ WrapJointProfile.lower p r gamma.val<r+b := by
  constructor
  · rintro ⟨i,hi⟩
    have hnode := WrapFibreIndex.node_eq p (r+(i:ℕ)) gamma hi
    have hc := count_eq_of_first p r gamma.val ((r+(i:ℕ))/p) hp (ZMod.val_lt gamma)
      (by rw [←hnode]; omega) (by rw [←hnode]; have := i.2; omega)
    have he : WrapJointProfile.lower p r gamma.val=r+(i:ℕ) := by
      unfold WrapJointProfile.lower
      rw [hc]
      exact hnode.symm
    rw [he]
    have := i.2
    omega
  · intro hi
    have hb := WrapJointProfile.lower_bounds p r gamma.val hp (ZMod.val_lt gamma)
    refine ⟨⟨WrapJointProfile.lower p r gamma.val-r,by omega⟩,?_⟩
    have he : r+(WrapJointProfile.lower p r gamma.val-r)=WrapJointProfile.lower p r gamma.val := by omega
    rw [he]
    simp [WrapJointProfile.lower]

/-- The compressed virtual common count is the original common count
plus the full-period count and the single residual-colour indicator. -/
theorem virtual_count (p r n b gamma : ℕ) (hp : 0<p) (hg : gamma<p) (hbp : b≤p) :
    WrapJointProfile.count p (r+n*p+b) gamma=WrapJointProfile.count p r gamma+n+
      if WrapJointProfile.lower p r gamma<r+b then 1 else 0 := by
  rw [show r+n*p+b=(r+b)+n*p by omega,count_add_periods p (r+b) gamma n hp hg,
    count_add_residual p r gamma b hp hg hbp]
  omega


end ProfileArithmetic

section VirtualProfile

/-- Mixed profile with a fixed original common count. This also names
virtual credited nodes whose count differs from their original fibre. -/
def profileRows (p k n gamma bit : ℕ) : Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ)+bit)*p)

def profileCols (p k n gamma bit : ℕ) : Fin k ⊕ Fin n → ℕ :=
  Sum.elim (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ)+(1-bit))*p)

noncomputable def profileCore (q o k n gamma bit : ℕ) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (fun i:Fin k => gamma+(i:ℕ)*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ)+bit)*p)
    (fun i:Fin n => gamma+(k+2*(i:ℕ)+(1-bit))*p)

noncomputable def profileMoment (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) :=
  WrapDeform.residue p ((fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (profileCols p k n gamma bit i)-direction) ⬝ᵥ
    (profileCore (p:=p) q o k n gamma bit s u)⁻¹ *ᵥ
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o
      (profileRows p k n gamma bit i)-direction))

/-- Bind the virtual notation to the actual canonical profile whenever
its common count and parity are the original ones. -/
theorem profile_core_eq (q o r k n gamma bit : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit) :
    WrapPrefixType.core p q o r k n gamma s u=profileCore (p:=p) q o k n gamma bit s u := by
  have hr : (fun i:Fin n => WrapJointProfile.rowProfile p r gamma i)=
      fun i:Fin n => gamma+(k+2*(i:ℕ)+bit)*p := by
    funext i
    simp only [WrapJointProfile.rowProfile,WrapJointProfile.lower,hk,hb]
    ring
  have hc : (fun i:Fin n => WrapJointProfile.colProfile p r gamma i)=
      fun i:Fin n => gamma+(k+2*(i:ℕ)+(1-bit))*p := by
    funext i
    simp only [WrapJointProfile.colProfile,WrapJointProfile.lower,hk,hb]
    ring
  unfold WrapPrefixType.core profileCore
  rw [hr,hc]

/-- Transposing the actual mixed profile exchanges its two parity bits
and its independent row/column loads. -/
theorem profile_core_transpose (q o k n gamma : ℕ) (s u : GaussLoc p) :
    profileCore (p:=p) q o k n gamma 1 s u=
      (profileCore (p:=p) q o k n gamma 0 s u)ᵀ := by
  classical
  ext i j
  simp only [profileCore,WrapFibreCore.core,Matrix.add_apply,Matrix.of_apply,Matrix.transpose_apply,
    Nat.sub_zero,Nat.sub_self,Nat.add_zero]
  rw [WrapEntryRelation.entry_symm]
  congr 1
  cases i <;> cases j <;> simp [Matrix.one_apply,eq_comm]

/-- The reduced mixed moment is invariant under the independent-axis
transpose, without a symmetry assumption on the balanced block. -/
theorem profile_moment_transpose (q o k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) :
    profileMoment (p:=p) q o k n gamma 1 s u direction=
      profileMoment (p:=p) q o k n gamma 0 s u direction := by
  have hr : profileRows p k n gamma 1=profileCols p k n gamma 0 := by
    funext i; cases i <;> rfl
  have hc : profileCols p k n gamma 1=profileRows p k n gamma 0 := by
    funext i; cases i <;> rfl
  unfold profileMoment
  rw [profile_core_transpose,hr,hc]
  exact congrArg (WrapDeform.residue p) (WrapTransport.response_transpose
    (profileCore (p:=p) q o k n gamma 0 s u) _ _).symm

theorem profile_rows_eq (r k n gamma bit : ℕ)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit) :
    WrapPrefixType.rows p r k n gamma=profileRows p k n gamma bit := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.rows,profileRows,Sum.elim_inr,WrapJointProfile.rowProfile,
      WrapJointProfile.lower,hk,hb]
    ring

theorem profile_cols_eq (r k n gamma bit : ℕ)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit) :
    WrapPrefixType.cols p r k n gamma=profileCols p k n gamma bit := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.cols,profileCols,Sum.elim_inr,WrapJointProfile.colProfile,
      WrapJointProfile.lower,hk,hb]
    ring

theorem profile_moment_eq (q o r k n gamma bit : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit)
    (direction : WrapDeform.Extension p) :
    WrapPrefixType.moment p q o r k n gamma s u direction=
      profileMoment (p:=p) q o k n gamma bit s u direction := by
  unfold WrapPrefixType.moment profileMoment
  rw [profile_core_eq q o r k n gamma bit s u hk hb,
    profile_rows_eq r k n gamma bit hk hb,profile_cols_eq r k n gamma bit hk hb]

end VirtualProfile

section ActualProfiles
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Presence of the original unique residual balanced pair. -/
def hasResidual (gamma : ZMod p) : Prop := ∃ j:Fin b,(H.xs (Sum.inr j):ZMod p)=gamma

noncomputable def fibrePairs (gamma : ZMod p) : ℕ := by
  classical
  exact n+if hasResidual H gamma then 1 else 0

theorem fibrePairs_present (gamma : ZMod p) (hj : hasResidual H gamma) : fibrePairs H gamma=n+1 := by
  classical
  simp only [fibrePairs,if_pos hj]

theorem fibrePairs_absent (gamma : ZMod p) (hj : ¬hasResidual H gamma) : fibrePairs H gamma=n := by
  classical
  simp only [fibrePairs,if_neg hj,Nat.add_zero]

/-- Every original fibre moment is its concrete mixed quotient profile,
with exactly n or n+1 actual balanced pairs. -/
theorem actual_profile_moment (gamma : ZMod p) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    H.moment s u gamma=profileMoment (p:=p) q o
      (WrapJointProfile.count p r gamma.val) (fibrePairs H gamma) gamma.val
      (WrapJointProfile.bit p r gamma.val) s u (H.anchor s u) := by
  classical
  by_cases hj : hasResidual H gamma
  · rw [fibrePairs_present H gamma hj]
    obtain ⟨j,hjval⟩ := hj
    have he := residual_profile_moment H gamma j hjval s u hs hu huc
    have ht := profile_moment_eq q o r (WrapJointProfile.count p r gamma.val)
      (n+1) gamma.val (WrapJointProfile.bit p r gamma.val) s u rfl rfl (H.anchor s u)
    exact he.trans ht
  · rw [fibrePairs_absent H gamma hj]
    have hres : ∀ j:Fin b,(H.xs (Sum.inr j):ZMod p)≠gamma := by
      intro j he
      exact hj ⟨j,he⟩
    have he := WrapPrefixWindow.mixed_moment p r n e b d shift q o H.hp H.hp2 s u H.er H.ec
      gamma hres (H.anchor s u) (H.own_unit s u hs hu huc)
    have ht := profile_moment_eq q o r (WrapJointProfile.count p r gamma.val)
      n gamma.val (WrapJointProfile.bit p r gamma.val) s u rfl rfl (H.anchor s u)
    exact he.trans ht

/-- The concrete original own-colour block is a unit for every colour. -/
theorem own_colour_unit (gamma : ZMod p) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit ((H.core s u).toSquareBlock H.colour gamma).det := by
  classical
  have hb : ∀ a b,H.colour a≠H.colour b → H.own s u a b=0 := by
    intro a b hab
    exact if_neg hab
  have he : blk (H.own s u) H.colour gamma=(H.core s u).toSquareBlock H.colour gamma := by
    ext i j
    change (if H.colour i.1=H.colour j.1 then H.core s u i.1 j.1 else 0)=H.core s u i.1 j.1
    rw [if_pos (i.2.trans j.2.symm)]
  rw [←he]
  exact (inv_restrict (H.own s u) H.colour (H.own_unit s u hs hu huc) hb gamma).1

/-- All actual quotient profile units come from the original own blocks,
including residual-present colours. -/
theorem actual_profile_unit (gamma : ZMod p) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit (profileCore (p:=p) q o (WrapJointProfile.count p r gamma.val)
      (fibrePairs H gamma) gamma.val (WrapJointProfile.bit p r gamma.val) s u).det := by
  classical
  by_cases hj : hasResidual H gamma
  · rw [fibrePairs_present H gamma hj]
    obtain ⟨j,hjval⟩ := hj
    have he := residual_profile_unit H gamma j hjval s u hs hu huc
    rw [profile_core_eq q o r (WrapJointProfile.count p r gamma.val) (n+1)
      gamma.val (WrapJointProfile.bit p r gamma.val) s u rfl rfl] at he
    exact he
  · rw [fibrePairs_absent H gamma hj]
    have hres : ∀ j:Fin b,(H.xs (Sum.inr j):ZMod p)≠gamma := by
      intro j he
      exact hj ⟨j,he⟩
    have he := WrapJointProfile.whole_core_unit p r n e b d shift q o H.hp H.hp2 s u H.er H.ec
      gamma hres (own_colour_unit H gamma s u hs hu huc)
    change IsUnit (WrapPrefixType.core p q o r (WrapJointProfile.count p r gamma.val) n gamma.val s u).det at he
    rw [profile_core_eq q o r (WrapJointProfile.count p r gamma.val) n
      gamma.val (WrapJointProfile.bit p r gamma.val) s u rfl rfl] at he
    exact he

end ActualProfiles

section VirtualProfile


theorem profile_as_entries (q o k n gamma bit : ℕ) (s u : GaussLoc p) :
    profileCore (p:=p) q o k n gamma bit s u=
      Matrix.of (fun i j => WrapDeformedEntry.entry p q o u
        (profileRows p k n gamma bit i) (profileCols p k n gamma bit j))+
        WrapPrefixType.spectral p k n s := rfl

theorem profile_rows_colour (k n gamma bit : ℕ) (i : Fin k ⊕ Fin n) :
    (profileRows p k n gamma bit i:ZMod p)=(gamma:ZMod p) := by
  cases i <;> simp [profileRows]

theorem profile_cols_colour (k n gamma bit : ℕ) (i : Fin k ⊕ Fin n) :
    (profileCols p k n gamma bit i:ZMod p)=(gamma:ZMod p) := by
  cases i <;> simp [profileCols]

theorem profile_rows_shift (k n gamma delta bit : ℕ) (hgd : gamma≤delta) (i : Fin k ⊕ Fin n) :
    profileRows p k n delta bit i=profileRows p k n gamma bit i+(delta-gamma) := by
  cases i <;> simp only [profileRows,Sum.elim_inl,Sum.elim_inr] <;> omega

theorem profile_cols_shift (k n gamma delta bit : ℕ) (hgd : gamma≤delta) (i : Fin k ⊕ Fin n) :
    profileCols p k n delta bit i=profileCols p k n gamma bit i+(delta-gamma) := by
  cases i <;> simp only [profileCols,Sum.elim_inl,Sum.elim_inr] <;> omega

/-- A fixed original common-count profile translates beyond the actual
node bound without changing its reduced matrix. -/
theorem profile_core_shift (q o k n gamma delta bit t : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta) (ht : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    (profileCore (p:=p) q o k n delta bit s u).map (WrapDeform.residue p)=
      (profileCore (p:=p) q o k n gamma bit s u).map (WrapDeform.residue p) := by
  rw [profile_as_entries,profile_as_entries]
  simp_rw [profile_rows_shift (p:=p) k n gamma delta bit hgd,profile_cols_shift (p:=p) k n gamma delta bit hgd]
  exact translated_matrix_map q o t (delta-gamma) u (profileRows p k n gamma bit)
    (profileCols p k n gamma bit) (WrapPrefixType.spectral p k n s)
    (fun i => (profile_rows_colour (p:=p) k n gamma bit i).trans ht.symm)
    (fun i => (profile_cols_colour (p:=p) k n gamma bit i).trans ht.symm) hw

/-- Fixed-profile moments are constant on a regular pole arc. -/
theorem profile_moment_shift (q o k n gamma delta bit t : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta) (ht : (t:ZMod p)=(gamma:ZMod p))
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma bit s u).det)
    (direction : WrapDeform.Extension p) :
    profileMoment (p:=p) q o k n delta bit s u direction=
      profileMoment (p:=p) q o k n gamma bit s u direction := by
  unfold profileMoment
  rw [profile_as_entries,profile_as_entries]
  simp_rw [profile_rows_shift (p:=p) k n gamma delta bit hgd,profile_cols_shift (p:=p) k n gamma delta bit hgd]
  exact translated_moment q o t (delta-gamma) s u (profileRows p k n gamma bit)
    (profileCols p k n gamma bit) (WrapPrefixType.spectral p k n s)
    (fun i => (profile_rows_colour (p:=p) k n gamma bit i).trans ht.symm)
    (fun i => (profile_cols_colour (p:=p) k n gamma bit i).trans ht.symm) hw
    (by rwa [←profile_as_entries]) direction

/-- The same original mixed moment may be evaluated in either parity
ordering. -/
theorem profile_moment_bit (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (hbit : bit≤1) (direction : WrapDeform.Extension p) :
    profileMoment (p:=p) q o k n gamma bit s u direction=
      profileMoment (p:=p) q o k n gamma 0 s u direction := by
  interval_cases bit
  · rfl
  · exact profile_moment_transpose q o k n gamma s u direction

noncomputable def profileRowOwn (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) :=
  (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+(k+2*n)*p)-direction)-
    (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (profileCols p k n gamma bit i)) ⬝ᵥ
    (profileCore (p:=p) q o k n gamma bit s u)⁻¹ *ᵥ
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (profileRows p k n gamma bit i)-direction)

noncomputable def profileColOwn (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) :=
  (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+(k+2*n)*p)-direction)-
    (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (profileRows p k n gamma bit i)) ⬝ᵥ
    (profileCore (p:=p) q o k n gamma bit s u)ᵀ⁻¹ *ᵥ
    (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (profileCols p k n gamma bit i)-direction)

theorem profile_row_one (q o k n gamma : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p) :
    profileRowOwn (p:=p) q o k n gamma 1 s u direction=
      profileColOwn (p:=p) q o k n gamma 0 s u direction := by
  have hr : profileRows p k n gamma 1=profileCols p k n gamma 0 := by funext i; cases i <;> rfl
  have hc : profileCols p k n gamma 1=profileRows p k n gamma 0 := by funext i; cases i <;> rfl
  unfold profileRowOwn profileColOwn
  rw [profile_core_transpose,hr,hc]

theorem profile_col_one (q o k n gamma : ℕ) (s u : GaussLoc p) (direction : WrapDeform.Extension p) :
    profileColOwn (p:=p) q o k n gamma 1 s u direction=
      profileRowOwn (p:=p) q o k n gamma 0 s u direction := by
  have hr : profileRows p k n gamma 1=profileCols p k n gamma 0 := by funext i; cases i <;> rfl
  have hc : profileCols p k n gamma 1=profileRows p k n gamma 0 := by funext i; cases i <;> rfl
  unfold profileRowOwn profileColOwn
  rw [profile_core_transpose,Matrix.transpose_transpose,hr,hc]

/-- Either actual parity gives the same unit bit-zero reference. -/
theorem profile_unit_zero (q o k n gamma bit : ℕ) (s u : GaussLoc p) (hbit : bit≤1)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma bit s u).det) :
    IsUnit (profileCore (p:=p) q o k n gamma 0 s u).det := by
  interval_cases bit
  · exact hQ
  · rwa [profile_core_transpose,Matrix.det_transpose] at hQ

/-- Both independent own-source zeros pass to the bit-zero ordering. -/
theorem profile_sources_zero (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (hbit : bit≤1) (direction : WrapDeform.Extension p)
    (hr : WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma bit s u direction)=0)
    (hc : WrapDeform.residue p (profileColOwn (p:=p) q o k n gamma bit s u direction)=0) :
    WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma 0 s u direction)=0 ∧
      WrapDeform.residue p (profileColOwn (p:=p) q o k n gamma 0 s u direction)=0 := by
  interval_cases bit
  · exact ⟨hr,hc⟩
  · rw [profile_row_one] at hr
    rw [profile_col_one] at hc
    exact ⟨hc,hr⟩

/-- The virtual zone own source translates with the entire original
mixed profile, without an artificial virtual-node size bound. -/
theorem profile_row_shift (q o k n gamma delta bit : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta)
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((gamma+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (gamma+(k+2*n)*p+h))≠0)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma bit s u).det)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p (profileRowOwn (p:=p) q o k n delta bit s u direction)=
      WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma bit s u direction) := by
  unfold profileRowOwn
  rw [profile_as_entries,profile_as_entries]
  simp_rw [profile_rows_shift (p:=p) k n gamma delta bit hgd,
    profile_cols_shift (p:=p) k n gamma delta bit hgd]
  rw [show delta+(k+2*n)*p=(gamma+(k+2*n)*p)+(delta-gamma) by omega]
  exact translated_own_source q o (gamma+(k+2*n)*p) (delta-gamma) u
    (profileRows p k n gamma bit) (profileCols p k n gamma bit) (WrapPrefixType.spectral p k n s)
    (fun i => by cases i <;> simp [profileRows]) (fun i => by cases i <;> simp [profileCols]) hw
    (by rwa [←profile_as_entries]) direction

/-- The independent column own source obeys the same virtual transport. -/
theorem profile_col_shift (q o k n gamma delta : ℕ) (s u : GaussLoc p)
    (hgd : gamma≤delta)
    (hw : ∀ h∈Icc 1 (delta-gamma),res p ((gamma+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (gamma+(k+2*n)*p+h))≠0)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma 0 s u).det)
    (direction : WrapDeform.Extension p) :
    WrapDeform.residue p (profileColOwn (p:=p) q o k n delta 0 s u direction)=
      WrapDeform.residue p (profileColOwn (p:=p) q o k n gamma 0 s u direction) := by
  rw [←profile_row_one,←profile_row_one]
  exact profile_row_shift q o k n gamma delta 1 s u hgd hw
    (by rwa [profile_core_transpose,Matrix.det_transpose]) direction

/-- A virtual reference transfers to either side of its original
representative inside a regular arc. All target units are derived. -/
theorem profile_arc_transfer (q o k n gamma delta : ℕ) (s u : GaussLoc p)
    (hw : ∀ h∈Icc 1 (max gamma delta-min gamma delta),
      res p ((min gamma delta+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (min gamma delta+(k+2*n)*p+h))≠0)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma 0 s u).det)
    (direction : WrapDeform.Extension p)
    (hr : WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma 0 s u direction)=0)
    (hc : WrapDeform.residue p (profileColOwn (p:=p) q o k n gamma 0 s u direction)=0) :
    IsUnit (profileCore (p:=p) q o k n delta 0 s u).det ∧
      WrapDeform.residue p (profileRowOwn (p:=p) q o k n delta 0 s u direction)=0 ∧
      WrapDeform.residue p (profileColOwn (p:=p) q o k n delta 0 s u direction)=0 ∧
      profileMoment (p:=p) q o k n delta 0 s u direction=
        profileMoment (p:=p) q o k n gamma 0 s u direction := by
  by_cases hgd : gamma≤delta
  · have hw' : ∀ h∈Icc 1 (delta-gamma),res p ((gamma+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
        res p (WrapIncrement.argument p q o (gamma+(k+2*n)*p+h))≠0 := by
      simpa only [min_eq_left hgd,max_eq_right hgd] using hw
    have hm := profile_core_shift q o k n gamma delta 0 (gamma+(k+2*n)*p) s u hgd (by simp) hw'
    exact ⟨unit_of_same_reduction _ _ hQ hm,
      (profile_row_shift q o k n gamma delta 0 s u hgd hw' hQ direction).trans hr,
      (profile_col_shift q o k n gamma delta s u hgd hw' hQ direction).trans hc,
      profile_moment_shift q o k n gamma delta 0 (gamma+(k+2*n)*p) s u hgd (by simp) hw' hQ direction⟩
  · have hdg : delta≤gamma := by omega
    have hw' : ∀ h∈Icc 1 (gamma-delta),res p ((delta+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
        res p (WrapIncrement.argument p q o (delta+(k+2*n)*p+h))≠0 := by
      simpa only [min_eq_right hdg,max_eq_left hdg] using hw
    have hm := profile_core_shift q o k n delta gamma 0 (delta+(k+2*n)*p) s u hdg (by simp) hw'
    have hQ' := unit_of_same_reduction _ _ hQ hm.symm
    exact ⟨hQ',
      (profile_row_shift q o k n delta gamma 0 s u hdg hw' hQ' direction).symm.trans hr,
      (profile_col_shift q o k n delta gamma s u hdg hw' hQ' direction).symm.trans hc,
      (profile_moment_shift q o k n delta gamma 0 (delta+(k+2*n)*p) s u hdg (by simp) hw' hQ' direction).symm⟩

/-- The same regular arc also preserves the two-term cyclic weight. -/
theorem arc_cyclic_weight (q o k n gamma delta : ℕ)
    (ho : (o:ZMod p)≠0) (hq : (q:ZMod p)≠0)
    (hw : ∀ h∈Icc 1 (max gamma delta-min gamma delta),
      res p ((min gamma delta+(k+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (min gamma delta+(k+2*n)*p+h))≠0) :
    wT p q o (delta:ZMod p)=wT p q o (gamma:ZMod p) := by
  have he := WrapPrefixType.cyclic_weight_const p q o (min gamma delta+(k+2*n)*p)
    (max gamma delta-min gamma delta) ho hq hw
  have hlast : min gamma delta+(k+2*n)*p+(max gamma delta-min gamma delta)=
      max gamma delta+(k+2*n)*p := by omega
  rw [hlast] at he
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] at he
  by_cases hgd : gamma≤delta
  · simpa only [min_eq_left hgd,max_eq_right hgd] using he
  · have hdg : delta≤gamma := by omega
    simpa only [min_eq_right hdg,max_eq_left hdg] using he.symm

theorem profile_row_prefix (q o r k n gamma bit : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit)
    (direction : WrapDeform.Extension p) :
    profileRowOwn (p:=p) q o k n gamma bit s u direction=
      WrapPrefixWindow.rowOwn p q o r k n gamma (gamma+(k+2*n)*p) s u direction := by
  unfold profileRowOwn WrapPrefixWindow.rowOwn
  rw [profile_core_eq q o r k n gamma bit s u hk hb,
    profile_rows_eq r k n gamma bit hk hb,profile_cols_eq r k n gamma bit hk hb]


theorem profile_fake_count (k gamma : ℕ) (hg : gamma<p) :
    WrapJointProfile.count p (gamma+k*p) gamma=k :=
  count_eq_of_first p (gamma+k*p) gamma k (Fact.out:p.Prime).pos hg le_rfl (by have := (Fact.out:p.Prime).pos; omega)

theorem profile_fake_bit (k gamma : ℕ) (hg : gamma<p) :
    WrapJointProfile.bit p (gamma+k*p) gamma=0 := by
  unfold WrapJointProfile.bit WrapJointProfile.lower
  rw [profile_fake_count k gamma hg]
  simp

/-- The original next-pair identity applies to a virtual fixed-count
profile using only its derived units and reduced own-source zero. -/
theorem profile_append_moment (q o k n gamma : ℕ) (s u : GaussLoc p) (hg : gamma<p)
    (direction : WrapDeform.Extension p)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma 0 s u).det)
    (hM : IsUnit (profileCore (p:=p) q o k (n+1) gamma 0 s u).det)
    (hz : WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma 0 s u direction)=0) :
    profileMoment (p:=p) q o k (n+1) gamma 0 s u direction=
      profileMoment (p:=p) q o k n gamma 0 s u direction := by
  let r0 := gamma+k*p
  have hc : WrapJointProfile.count p r0 gamma=k := profile_fake_count k gamma hg
  have hb : WrapJointProfile.bit p r0 gamma=0 := profile_fake_bit k gamma hg
  have hnode : WrapJointProfile.rowProfile p r0 gamma n=gamma+(k+2*n)*p := by
    unfold WrapJointProfile.rowProfile WrapJointProfile.lower
    rw [hc,hb]
    ring
  have hQ0 : IsUnit (WrapPrefixType.core p q o r0 k n gamma s u).det := by
    rwa [profile_core_eq q o r0 k n gamma 0 s u hc hb]
  have hM0 : IsUnit (WrapPrefixType.core p q o r0 k (n+1) gamma s u).det := by
    rwa [profile_core_eq q o r0 k (n+1) gamma 0 s u hc hb]
  have hzero : WrapDeform.residue p (WrapPrefixWindow.rowOwn p q o r0 k n gamma
      (WrapJointProfile.rowProfile p r0 gamma n) s u direction)=0 := by
    rw [hnode,←profile_row_prefix q o r0 k n gamma 0 s u hc hb direction]
    exact hz
  have he := append_moment_mod q o r0 k n gamma s u direction hQ0 hM0 hzero
  rw [profile_moment_eq q o r0 k (n+1) gamma 0 s u hc hb direction,
    profile_moment_eq q o r0 k n gamma 0 s u hc hb direction] at he
  exact he

/-- The column own source in independent load-response orientation. -/
theorem profile_col_response (q o k n gamma bit : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p) :
    profileColOwn (p:=p) q o k n gamma bit s u direction=
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o (gamma+(k+2*n)*p)-direction)-
      (fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (profileCols p k n gamma bit i)-direction) ⬝ᵥ
      (profileCore (p:=p) q o k n gamma bit s u)⁻¹ *ᵥ
      (fun i => WrapDeformedEntry.entry p q o u (profileRows p k n gamma bit i) (gamma+(k+2*n)*p)) := by
  have he : (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p) (profileRows p k n gamma bit i))=
      fun i => WrapDeformedEntry.entry p q o u (profileRows p k n gamma bit i) (gamma+(k+2*n)*p) := by
    funext i
    exact WrapEntryRelation.entry_symm p q o u _ _
  unfold profileColOwn
  rw [he,←WrapTransport.response_transpose]

/-- Bind the independent upper-cut rows to the bit-one virtual profile. -/
theorem upper_cut_profile_rows (k n gamma : ℕ) :
    Sum.elim (fun i:Fin (k+1) => gamma+(i:ℕ)*p)
      (fun i:Fin n => gamma+(k+2+2*(i:ℕ))*p)=profileRows p (k+1) n gamma 1 := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => simp only [Sum.elim_inr,profileRows]; ring

theorem upper_cut_profile_cols (k n gamma : ℕ) :
    Sum.elim (fun i:Fin (k+1) => gamma+(i:ℕ)*p)
      (fun i:Fin n => gamma+(k+1+2*(i:ℕ))*p)=profileCols p (k+1) n gamma 1 := rfl

theorem upper_cut_profile_core (q o k n gamma : ℕ) (s u : GaussLoc p) :
    upperCutCore (p:=p) q o gamma k n s u=profileCore (p:=p) q o (k+1) n gamma 1 s u := by
  have hr : (fun i:Fin n => gamma+(k+2+2*(i:ℕ))*p)=
      fun i:Fin n => gamma+(k+1+2*(i:ℕ)+1)*p := by
    funext i
    ring
  unfold upperCutCore profileCore
  rw [hr]
  simp only [Nat.sub_self,Nat.add_zero]

/-- The actual residual-present lower-count moment equals its
regularly transported upper-count reference moment. -/
theorem profile_cut_moment (q o k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p)
    (hQ : IsUnit (profileCore (p:=p) q o (k+1) n gamma 0 s u).det)
    (hM : IsUnit (profileCore (p:=p) q o k (n+1) gamma 0 s u).det)
    (hz : WrapDeform.residue p (profileRowOwn (p:=p) q o (k+1) n gamma 0 s u direction)=0) :
    profileMoment (p:=p) q o k (n+1) gamma 0 s u direction=
      profileMoment (p:=p) q o (k+1) n gamma 0 s u direction := by
  let L := fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-direction
  have hQ1 : IsUnit (upperCutCore (p:=p) q o gamma k n s u).det := by
    rwa [upper_cut_profile_core,profile_core_transpose,Matrix.det_transpose]
  have hM0 : IsUnit (lowerCutCore (p:=p) q o gamma k n s u).det := hM
  have hz1 : WrapDeform.residue p (profileColOwn (p:=p) q o (k+1) n gamma 1 s u direction)=0 := by
    rwa [profile_col_one]
  rw [profile_col_response,←upper_cut_profile_core,←upper_cut_profile_rows,←upper_cut_profile_cols] at hz1
  have hnode : gamma+(k+1+2*n)*p=gamma+(k+2*n+1)*p := by ring
  rw [hnode] at hz1
  have he := cut_response q o gamma k n s u L L hQ1 hM0 hz1
  rw [upper_cut_profile_core,upper_cut_profile_rows,upper_cut_profile_cols] at he
  change profileMoment (p:=p) q o k (n+1) gamma 0 s u direction=
    profileMoment (p:=p) q o (k+1) n gamma 1 s u direction at he
  exact he.trans (profile_moment_transpose q o (k+1) n gamma s u direction)

/-- The actual higher common count in a virtual top extension adds
no mixed moment beyond the transported lower-count reference. -/
theorem profile_top_moment (q o k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p)
    (hQ : IsUnit (profileCore (p:=p) q o k n gamma 0 s u).det)
    (hM : IsUnit (profileCore (p:=p) q o (k+1) n gamma 0 s u).det)
    (hz : WrapDeform.residue p (profileRowOwn (p:=p) q o k n gamma 0 s u direction)=0) :
    profileMoment (p:=p) q o (k+1) n gamma 0 s u direction=
      profileMoment (p:=p) q o k n gamma 0 s u direction := by
  let L := fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a-direction
  have hQ0 : IsUnit (baseCutCore (p:=p) q o gamma k n s u).det := hQ
  have hM1 : IsUnit (upperCutCore (p:=p) q o gamma k n s u).det := by
    rwa [upper_cut_profile_core,profile_core_transpose,Matrix.det_transpose]
  have hz0 : WrapDeform.residue p (L (gamma+(k+2*n)*p)-
      (fun i => WrapDeformedEntry.entry p q o u (gamma+(k+2*n)*p)
        (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p) (fun j:Fin n => gamma+(k+2*(j:ℕ)+1)*p) i)) ⬝ᵥ
      (baseCutCore (p:=p) q o gamma k n s u)⁻¹ *ᵥ
      (fun i => L (Sum.elim (fun j:Fin k => gamma+(j:ℕ)*p) (fun j:Fin n => gamma+(k+2*(j:ℕ))*p) i)))=0 := hz
  have he := top_cut_response q o gamma k n s u L L hQ0 hM1 hz0
  rw [upper_cut_profile_core,upper_cut_profile_rows,upper_cut_profile_cols] at he
  change profileMoment (p:=p) q o (k+1) n gamma 1 s u direction=
    profileMoment (p:=p) q o k n gamma 0 s u direction at he
  exact (profile_moment_transpose q o (k+1) n gamma s u direction).symm.trans he

end VirtualProfile

section ResidualColours

/-- The wrapped residual slot t has original colour r+t after restoring
all full periods, irrespective of which end of its pair is the row. -/
theorem wrapped_residual_colour (r n shift l : ℕ) (hl : 1≤l) (hls : l≤shift)
    (hp : p=2*shift+1) (i : Fin (2*l-1)) :
    (WrapPrefixCoreGeometry.xs p (n:=n) r (WrapGeometry.rowEquiv shift l hl hls) (Sum.inr i):ZMod p)=
      ((r+(i:ℕ):ℕ):ZMod p) := by
  change ((r+2*(n*p+WrapGeometry.rowBalanced shift i):ℕ):ZMod p)=_
  have he := WrapGeometry.rowBalanced_node r shift i
  rw [←hp] at he
  rw [show r+2*(n*p+WrapGeometry.rowBalanced shift i)=
    (r+2*WrapGeometry.rowBalanced shift i)+2*n*p by ring,he]
  by_cases hi : (i:ℕ)%2=0 <;> simp [hi]

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The actual residual-colour indicator gives the compressed virtual
common count; no balanced cycle is made into a spectral common node. -/
theorem actual_virtual_count (hb : b≤p)
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (gamma : ZMod p) :
    WrapJointProfile.count p (r+n*p+b) gamma.val=
      WrapJointProfile.count p r gamma.val+fibrePairs H gamma := by
  classical
  have hi : hasResidual H gamma ↔ WrapJointProfile.lower p r gamma.val<r+b := by
    unfold hasResidual
    simp_rw [hcolour]
    exact residual_interval_iff p r b (Fact.out:p.Prime).pos hb gamma
  unfold fibrePairs
  rw [virtual_count p r n b gamma.val (Fact.out:p.Prime).pos (ZMod.val_lt gamma) hb]
  by_cases hh : hasResidual H gamma
  · rw [if_pos hh,if_pos (hi.mp hh)]
    omega
  · rw [if_neg hh,if_neg (fun h => hh (hi.mpr h))]
    omega

/-- The original selected representative has no residual balanced pair. -/
theorem anchor_no_residual : ¬hasResidual H (H.t0:ZMod p) := by
  rintro ⟨j,hj⟩
  exact H.hfree H.t0 (mem_Icc.mpr ⟨le_rfl,H.hle⟩) j hj

/-- The credited virtual cell yields exactly the four actual source
profiles, with every residual indicator derived from original nodes. -/
theorem actual_profile_count_cases (hb : b≤p)
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (gamma : ZMod p)
    (hcell : WrapJointProfile.count p (r+n*p+b) gamma.val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val ∨
      WrapJointProfile.count p (r+n*p+b) gamma.val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val+1) :
    (¬hasResidual H gamma ∧ WrapJointProfile.count p r gamma.val=H.commonCount) ∨
    (hasResidual H gamma ∧ WrapJointProfile.count p r gamma.val+1=H.commonCount) ∨
    (¬hasResidual H gamma ∧ WrapJointProfile.count p r gamma.val=H.commonCount+1) ∨
    (hasResidual H gamma ∧ WrapJointProfile.count p r gamma.val=H.commonCount) := by
  classical
  have h0 := actual_virtual_count H hb hcolour (H.t0:ZMod p)
  rw [fibrePairs_absent H _ (anchor_no_residual H)] at h0
  have ht := actual_virtual_count H hb hcolour gamma
  change WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val=H.commonCount+n at h0
  by_cases hj : hasResidual H gamma
  · rw [fibrePairs_present H gamma hj] at ht
    rcases hcell with hc|hc
    · exact Or.inr (Or.inl ⟨hj,by omega⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hj,by omega⟩))
  · rw [fibrePairs_absent H gamma hj] at ht
    rcases hcell with hc|hc
    · exact Or.inl ⟨hj,by omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hj,by omega⟩))

end ResidualColours

section AnchorProfiles
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The original arithmetic constructs exact zeros of both independent
own sources in the original anchor direction. -/
theorem anchor_original_sources (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    WrapPrefixWindow.rowOwn p q o r H.commonCount n (H.t0:ZMod p).val H.t0 s u (H.anchor s u)=0 ∧
      WrapPrefixWindow.colOwn p q o r H.commonCount n (H.t0:ZMod p).val H.t0 s u (H.anchor s u)=0 := by
  have hmem : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have htip := H.tip H.t0 hmem
  obtain ⟨direction,hr,hc,hB,hBC⟩ := WrapPrefixType.anchor p (H.profile_hyp H.t0 hmem)
    (H.count_eq H.t0 hmem) s u hs hu huc (H.profile_common_bound H.t0 hmem)
    (by rw [←htip]; exact lt_of_le_of_lt H.hle H.htvN)
  change WrapPrefixWindow.rowOwn p q o r H.commonCount n (H.t0:ZMod p).val
    ((H.t0:ZMod p).val+(H.commonCount+2*n)*p) s u direction=0 at hr
  change WrapPrefixWindow.colOwn p q o r H.commonCount n (H.t0:ZMod p).val
    ((H.t0:ZMod p).val+(H.commonCount+2*n)*p) s u direction=0 at hc
  change IsUnit (WrapPrefixWindow.reference p q o r H.commonCount n (H.t0:ZMod p).val
    ((H.t0:ZMod p).val+(H.commonCount+2*n)*p) s u) at hB
  rw [←htip] at hr hc hB
  have hd := WrapPrefixWindow.row_own_unique p q o r H.commonCount n (H.t0:ZMod p).val
    H.t0 s u direction hr hB
  change direction=H.anchor s u at hd
  rw [hd] at hr hc
  exact ⟨hr,hc⟩

/-- The actual anchor's moment may be evaluated in the bit-zero
reference ordering with its original common count and all n pairs. -/
theorem anchor_profile_moment (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    H.moment s u (H.t0:ZMod p)=profileMoment (p:=p) q o H.commonCount n
      (H.t0:ZMod p).val 0 s u (H.anchor s u) := by
  have hmem : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have hb : WrapJointProfile.bit p r (H.t0:ZMod p).val≤1 := by
    have := WrapJointProfile.bit_lt p r (H.t0:ZMod p).val
    omega
  exact (H.profile_moment H.t0 hmem s u hs hu huc).trans
    ((profile_moment_eq q o r H.commonCount n (H.t0:ZMod p).val
      (WrapJointProfile.bit p r (H.t0:ZMod p).val) s u (H.count_eq H.t0 hmem) rfl (H.anchor s u)).trans
      (profile_moment_bit q o H.commonCount n (H.t0:ZMod p).val _ s u hb (H.anchor s u)))

/-- The original anchor supplies the virtual bit-zero unit and both
source zeros, without a new source-certificate hypothesis. -/
theorem anchor_profile_sources (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit (profileCore (p:=p) q o H.commonCount n (H.t0:ZMod p).val 0 s u).det ∧
      WrapDeform.residue p (profileRowOwn (p:=p) q o H.commonCount n (H.t0:ZMod p).val 0 s u (H.anchor s u))=0 ∧
      WrapDeform.residue p (profileColOwn (p:=p) q o H.commonCount n (H.t0:ZMod p).val 0 s u (H.anchor s u))=0 := by
  let gamma := (H.t0:ZMod p).val
  let bit := WrapJointProfile.bit p r gamma
  have hmem : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have hb : bit≤1 := by have := WrapJointProfile.bit_lt p r gamma; omega
  have hcount : WrapJointProfile.count p r gamma=H.commonCount := H.count_eq H.t0 hmem
  have htip : H.t0=gamma+(H.commonCount+2*n)*p := H.tip H.t0 hmem
  have hQ := WrapPrefixType.core_unit p (H.profile_hyp H.t0 hmem) hcount s u hs hu huc
    (H.profile_common_bound H.t0 hmem)
  rw [profile_core_eq q o r H.commonCount n gamma bit s u hcount rfl] at hQ
  have hR : profileRowOwn (p:=p) q o H.commonCount n gamma bit s u (H.anchor s u)=
      WrapPrefixWindow.rowOwn p q o r H.commonCount n gamma H.t0 s u (H.anchor s u) := by
    unfold profileRowOwn WrapPrefixWindow.rowOwn
    rw [profile_core_eq q o r H.commonCount n gamma bit s u hcount rfl,
      profile_rows_eq r H.commonCount n gamma bit hcount rfl,
      profile_cols_eq r H.commonCount n gamma bit hcount rfl,htip]
  have hC : profileColOwn (p:=p) q o H.commonCount n gamma bit s u (H.anchor s u)=
      WrapPrefixWindow.colOwn p q o r H.commonCount n gamma H.t0 s u (H.anchor s u) := by
    unfold profileColOwn WrapPrefixWindow.colOwn
    rw [profile_core_eq q o r H.commonCount n gamma bit s u hcount rfl,
      profile_rows_eq r H.commonCount n gamma bit hcount rfl,
      profile_cols_eq r H.commonCount n gamma bit hcount rfl,htip]
  have hsource := anchor_original_sources H s u hs hu huc
  have hr : WrapDeform.residue p (profileRowOwn (p:=p) q o H.commonCount n gamma bit s u (H.anchor s u))=0 := by
    rw [hR,hsource.1,map_zero]
  have hc : WrapDeform.residue p (profileColOwn (p:=p) q o H.commonCount n gamma bit s u (H.anchor s u))=0 := by
    rw [hC,hsource.2,map_zero]
  exact ⟨profile_unit_zero q o H.commonCount n gamma bit s u hb hQ,
    profile_sources_zero q o H.commonCount n gamma bit s u hb (H.anchor s u) hr hc⟩

/-- Equal cyclic weight and actual mixed moment give the original
source zero at any credited colour. -/
theorem weight_zero_of_moment (s u : GaussLoc p) (gamma : ZMod p)
    (hw : wT p q o gamma=wT p q o (H.t0:ZMod p))
    (hm : H.moment s u gamma=H.moment s u (H.t0:ZMod p)) : H.weight s u gamma=0 := by
  unfold WrapPrefixWindow.Setup.weight WrapPrefixWindow.Setup.sourceConstant
  rw [hw,hm]
  ring

end AnchorProfiles

section CreditedProfiles
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Actual credited-colour cancellation for every original prefix
fibre shape. Every matrix unit and both source zeros are constructed
from the original arithmetic anchor. -/
theorem credited_weight_zero (hb : b≤p)
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (gamma : ZMod p)
    (hcell : WrapJointProfile.count p (r+n*p+b) gamma.val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val ∨
      WrapJointProfile.count p (r+n*p+b) gamma.val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val+1)
    (hw : ∀ h∈Icc 1 (max (H.t0:ZMod p).val gamma.val-min (H.t0:ZMod p).val gamma.val),
      res p ((min (H.t0:ZMod p).val gamma.val+(H.commonCount+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (min (H.t0:ZMod p).val gamma.val+(H.commonCount+2*n)*p+h))≠0)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : H.weight s u gamma=0 := by
  classical
  have ha := anchor_profile_sources H s u hs hu huc
  obtain ⟨hv,hvr,hvc,hvm⟩ := profile_arc_transfer q o H.commonCount n (H.t0:ZMod p).val gamma.val
    s u hw ha.1 (H.anchor s u) ha.2.1 ha.2.2
  have hb0 : WrapJointProfile.bit p r gamma.val≤1 := by
    have := WrapJointProfile.bit_lt p r gamma.val
    omega
  have hua := profile_unit_zero q o (WrapJointProfile.count p r gamma.val) (fibrePairs H gamma)
    gamma.val (WrapJointProfile.bit p r gamma.val) s u hb0 (actual_profile_unit H gamma s u hs hu huc)
  have hma := (actual_profile_moment H gamma s u hs hu huc).trans
    (profile_moment_bit q o (WrapJointProfile.count p r gamma.val) (fibrePairs H gamma)
      gamma.val (WrapJointProfile.bit p r gamma.val) s u hb0 (H.anchor s u))
  have hm : H.moment s u gamma=profileMoment (p:=p) q o H.commonCount n gamma.val 0 s u (H.anchor s u) := by
    rw [hma]
    rcases actual_profile_count_cases H hb hcolour gamma hcell with h|h|h|h
    · rw [fibrePairs_absent H gamma h.1,h.2]
    · rw [fibrePairs_present H gamma h.1] at hua ⊢
      rw [←h.2] at hv hvr ⊢
      exact profile_cut_moment q o (WrapJointProfile.count p r gamma.val) n gamma.val
        s u (H.anchor s u) hv hua hvr
    · rw [fibrePairs_absent H gamma h.1,h.2] at hua ⊢
      exact profile_top_moment q o H.commonCount n gamma.val s u (H.anchor s u) hv hua hvr
    · rw [fibrePairs_present H gamma h.1,h.2] at hua ⊢
      exact profile_append_moment q o H.commonCount n gamma.val s u (ZMod.val_lt gamma)
        (H.anchor s u) hv hua hvr
  have hq : (q:ZMod p)≠0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff q p).mp he
    have hle := Nat.le_of_dvd H.hq0 hd
    have := H.hqp
    omega
  have hwT := arc_cyclic_weight q o H.commonCount n (H.t0:ZMod p).val gamma.val H.ho hq hw
  apply weight_zero_of_moment H s u gamma
  · simpa only [ZMod.natCast_zmod_val] using hwT
  · exact (hm.trans hvm).trans (anchor_profile_moment H s u hs hu huc).symm

end CreditedProfiles

section CreditedIntervals

/-- In one quotient cell, a representative at or above the common
start has the least common count; every earlier colour adds one. -/
theorem count_cell_cases (p a t0 t : ℕ) (hp : 0<p)
    (ha : a≤t0) (ht0 : t0<a+p) (ht : t<a+p) (hdiv : t/p=t0/p) :
    WrapJointProfile.count p a (t%p)=WrapJointProfile.count p a (t0%p) ∨
      WrapJointProfile.count p a (t%p)=WrapJointProfile.count p a (t0%p)+1 := by
  have h0 : t0%p+(t0/p)*p=t0 := by have he := Nat.mod_add_div t0 p; nlinarith
  have h1 : t%p+(t/p)*p=t := by have he := Nat.mod_add_div t p; nlinarith
  have hc0 : WrapJointProfile.count p a (t0%p)=t0/p :=
    count_eq_of_first p a (t0%p) (t0/p) hp (Nat.mod_lt t0 hp)
      (by rw [h0]; exact ha) (by rw [h0]; exact ht0)
  by_cases hat : a≤t
  · left
    have hc1 : WrapJointProfile.count p a (t%p)=t/p :=
      count_eq_of_first p a (t%p) (t/p) hp (Nat.mod_lt t hp)
        (by rw [h1]; exact hat) (by rw [h1]; exact ht)
    rw [hc1,hc0,hdiv]
  · right
    have htp : a≤t+p := by
      have hm := Nat.mod_lt t0 hp
      rw [hdiv] at h1
      omega
    have he : t%p+(t/p+1)*p=t+p := by nlinarith
    have hc1 : WrapJointProfile.count p a (t%p)=t/p+1 :=
      count_eq_of_first p a (t%p) (t/p+1) hp (Nat.mod_lt t hp)
        (by rw [he]; exact htp) (by rw [he]; omega)
    rw [hc1,hc0,hdiv]

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The actual free anchor lies after the entire residual balanced arc. -/
theorem anchor_after_residual
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p)) :
    r+2*n*p+b≤H.t0 := by
  by_contra hn
  have hlo := H.hlo
  have hj : H.t0-(r+2*n*p)<b := by omega
  let j : Fin b := ⟨H.t0-(r+2*n*p),hj⟩
  have he : r+(j:ℕ)+2*n*p=H.t0 := by dsimp only [j]; omega
  have hv := congrArg (fun a:ℕ => (a:ZMod p)) he
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] at hv
  exact H.hfree H.t0 (mem_Icc.mpr ⟨le_rfl,H.hle⟩) j ((hcolour j).trans (by simpa only [Nat.cast_add] using hv))

/-- The virtual common-count alternative is a consequence of the
physical credited interval, with all original n periods restored. -/
theorem credited_count_cases
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (t : ℕ) (ht : t<r+2*n*p+b+p) (hdiv : t/p=H.t0/p) :
    WrapJointProfile.count p (r+n*p+b) (t:ZMod p).val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val ∨
      WrapJointProfile.count p (r+n*p+b) (t:ZMod p).val=
        WrapJointProfile.count p (r+n*p+b) (H.t0:ZMod p).val+1 := by
  have hA := anchor_after_residual H hcolour
  have h0 := H.hhi
  have hle := H.hle
  have hc := count_cell_cases p (r+2*n*p+b) H.t0 t (Fact.out:p.Prime).pos hA (by omega) ht hdiv
  have he : r+2*n*p+b=(r+n*p+b)+n*p := by ring
  have hp0 := (Fact.out:p.Prime).pos
  have hg0 := Nat.mod_lt H.t0 hp0
  have hg := Nat.mod_lt t hp0
  rw [he,count_add_periods p (r+n*p+b) (t%p) n hp0 hg,
    count_add_periods p (r+n*p+b) (H.t0%p) n hp0 hg0] at hc
  simp only [ZMod.val_natCast]
  omega

/-- Equal physical quotient cells identify the source's actual zone
nodes exactly; no virtual source-size assumption is introduced. -/
theorem credited_regular_arc (w0 w1 t : ℕ)
    (h0 : H.t0∈Icc w0 w1) (ht : t∈Icc w0 w1) (hdiv : t/p=H.t0/p)
    (hw : ∀ v∈Ioc w0 w1,res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0) :
    ∀ h∈Icc 1 (max (H.t0:ZMod p).val (t:ZMod p).val-min (H.t0:ZMod p).val (t:ZMod p).val),
      res p ((min (H.t0:ZMod p).val (t:ZMod p).val+(H.commonCount+2*n)*p+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (min (H.t0:ZMod p).val (t:ZMod p).val+(H.commonCount+2*n)*p+h))≠0 := by
  have hmem : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have htip := H.tip H.t0 hmem
  have hp0 := (Fact.out:p.Prime).pos
  have hquot : H.t0/p=H.commonCount+2*n := by
    rw [htip,Nat.add_mul_div_right _ _ hp0,Nat.div_eq_of_lt (ZMod.val_lt (H.t0:ZMod p)),zero_add]
  have htipT := WrapFibreIndex.node_eq p t (t:ZMod p) rfl
  rw [hdiv,hquot] at htipT
  intro h hh
  apply hw _
  have ht0 := mem_Icc.mp h0
  have htt := mem_Icc.mp ht
  have hhh := mem_Icc.mp hh
  simp only [mem_Ioc]
  omega

/-- Every credited interval colour vanishes in the actual source, from
original arithmetic alone, including virtual targets beyond N. -/
theorem credited_interval_zero (hb : b≤p)
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (w0 w1 : ℕ) (h0 : H.t0∈Icc w0 w1) (hhi : w1<r+2*n*p+b+p)
    (hdiv : w1/p=w0/p)
    (hw : ∀ v∈Ioc w0 w1,res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t∈Icc w0 w1) :
    H.weight s u (t:ZMod p)=0 := by
  have hd : t/p=H.t0/p := by
    have ht0 := mem_Icc.mp h0
    have htt := mem_Icc.mp ht
    have hL := Nat.div_le_div_right (c:=p) htt.1
    have hU := Nat.div_le_div_right (c:=p) htt.2
    have hL0 := Nat.div_le_div_right (c:=p) ht0.1
    have hU0 := Nat.div_le_div_right (c:=p) ht0.2
    omega
  exact credited_weight_zero H hb hcolour (t:ZMod p)
    (credited_count_cases H hcolour t (lt_of_le_of_lt (mem_Icc.mp ht).2 hhi) hd)
    (credited_regular_arc H w0 w1 t h0 ht hd hw) s u hs hu huc

end CreditedIntervals

section Baseline
variable {Fr : Frame} {q o r m N : ℕ}

/-- Universal original-member baseline, including exact whole-period
borders with no residual surplus. -/
theorem trivial_member_gle (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hqp : q<p) (hN : N<p*p) (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (hsize : r+2*m≤N) (K : Finset (Fin r)) :
    GLE p (2*(r+m))
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K)
        (fun i:Fin m => r+2*(i:ℕ)) (fun i:Fin m => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  classical
  have hc : ∀ i:WrapKeep.Keep K,WrapPrefixMember.common K i<N := by
    intro i
    change (i.1:ℕ)<N
    have := i.1.2
    omega
  have hx : ∀ i:Fin m,r+2*(i:ℕ)<N := by intro i; have := i.2; omega
  have hy : ∀ i:Fin m,r+2*(i:ℕ)+1<N := by intro i; have := i.2; omega
  have hg := WrapDeformedFamily.original_gle p T D hqp hN hsq (WrapPrefixMember.common K)
    (fun i:Fin m => r+2*(i:ℕ)) (fun i:Fin m => r+2*(i:ℕ)+1) hc hx hy 0 (by simp)
  have hk : Fintype.card (WrapKeep.Keep K)≤r := by
    have he := Fintype.card_le_of_injective (fun i:WrapKeep.Keep K => i.1) Subtype.val_injective
    simpa only [Fintype.card_fin] using he
  apply hg.mono
  simp only [Fintype.card_sum,Fintype.card_fin,Nat.sub_zero]
  omega

variable {n e b d shift : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- A nonempty original surplus uses the d first-level savings even
when a closed candidate selects no kernel coordinates. -/
theorem window_baseline_gle (T : TwoTermData Fr q o) (D : PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (K : Finset (Fin r)) :
    GLE p (2*(r+n*p+e)-d)
      (CatalanCore.Rect.FullN Fr (WrapPrefixMember.common K)
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  have hg := window_price_gle H T D hsq ∅ ∅ hinj
    (fun _ h => False.elim (notMem_empty _ h)) (fun _ h => False.elim (notMem_empty _ h)) K
  simpa only [card_empty,Nat.zero_add,Nat.zero_sub,WrapCount.gain,Nat.add_zero] using hg

end Baseline

section RectangularCauchy
variable {K : Type*} [Field K] {n : ℕ}

/-- The one-dimensional rectangular Cauchy kernel has nonzero coordinate
sum. The square reference theorem supplies the required normalization. -/
theorem rectangular_cauchy_kernel_sum (x : Fin n → K) (y : Fin (n+1) → K)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j,x i≠y j)
    (b : Fin (n+1) → K) (hb : b≠0)
    (hker : ∀ i,∑ j,(1/(x i-y j))*b j=0) : ∑ j,b j≠0 := by
  classical
  let y0 := fun j:Fin n => y j.castSucc
  let Q := WrapCauchy.matrix x y0
  let v := fun i:Fin n => 1/(x i-y (Fin.last n))
  let b0 := fun j:Fin n => b j.castSucc
  have hy0 : Function.Injective y0 := hy.comp (Fin.castSucc_injective n)
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr
    (WrapCauchy.det_ne x y0 hx hy0 (fun i j => hxy i j.castSucc))
  have hsolve : Q *ᵥ b0=-(b (Fin.last n)) • v := by
    funext i
    have he := hker i
    rw [Fin.sum_univ_castSucc] at he
    change (∑ j:Fin n,(1/(x i-y j.castSucc))*b j.castSucc)=-(b (Fin.last n))*(1/(x i-y (Fin.last n)))
    linear_combination he
  have hload : b0=-(b (Fin.last n)) • (Q⁻¹ *ᵥ v) := by
    calc
      b0=Q⁻¹ *ᵥ (Q *ᵥ b0) := by
        rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q hQ,Matrix.one_mulVec]
      _=_ := by rw [hsolve,Matrix.mulVec_smul]
  have hlast : b (Fin.last n)≠0 := by
    intro hz
    apply hb
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hz
    · have he := congrFun hload j
      simpa only [hz,neg_zero,zero_smul,Pi.zero_apply,b0] using he
  have href : 1-(1:Fin n → K) ⬝ᵥ Q⁻¹ *ᵥ v≠0 := by
    have hr := WrapCauchy.reference_ne y0 x hy0 hx (fun i j => (hxy j i.castSucc).symm)
      (y (Fin.last n)) (fun i he => Fin.castSucc_ne_last i (hy he))
      (fun j => (hxy j (Fin.last n)).symm)
    have hm : WrapCauchy.matrix y0 x=-Qᵀ := by
      ext i j
      simp only [WrapCauchy.matrix,Matrix.of_apply,Matrix.neg_apply,Matrix.transpose_apply,Q,y0]
      simpa only [one_div] using
        (congrArg (fun z:K => z⁻¹) (show y i.castSucc-x j=-(x j-y i.castSucc) by ring)).trans inv_neg
    have hv : (fun j:Fin n => 1/(y (Fin.last n)-x j))=-v := by
      funext j
      change 1/(y (Fin.last n)-x j)=-(1/(x j-y (Fin.last n)))
      simpa only [one_div] using
        (congrArg (fun z:K => z⁻¹) (show y (Fin.last n)-x j=-(x j-y (Fin.last n)) by ring)).trans inv_neg
    rw [hm,hv,WrapHarmonic.neg_reference Qᵀ v (by rwa [Matrix.det_transpose])] at hr
    rw [←WrapTransport.response_transpose Q v (1:Fin n → K)] at hr
    exact hr
  have hsum : (∑ j,b j)=b (Fin.last n)*(1-(1:Fin n → K) ⬝ᵥ Q⁻¹ *ᵥ v) := by
    rw [Fin.sum_univ_castSucc]
    have he : (∑ j:Fin n,b j.castSucc)=-(b (Fin.last n))*(∑ j:Fin n,(Q⁻¹ *ᵥ v) j) := by
      calc
        _=∑ j:Fin n,(-(b (Fin.last n)) • (Q⁻¹ *ᵥ v)) j := by
          apply Finset.sum_congr rfl
          intro j _
          exact congrFun hload j
        _=_ := by simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    rw [he]
    simp only [dotProduct,Pi.one_apply,one_mul]
    ring
  rw [hsum]
  exact mul_ne_zero hlast href

end RectangularCauchy

section CauchyAugmented
variable {K : Type*} [Field K] {n : ℕ}

/-- Append the constant row to a rectangular Cauchy matrix. -/
noncomputable def cauchyWithOnes (x : Fin n → K) (y : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.of fun i j => Fin.lastCases (1:K) (fun a:Fin n => 1/(x a-y j)) i

/-- The rectangular-kernel normalization makes the appended constant
row nonsingular, with no assumption on a square Gram compression. -/
theorem cauchyWithOnes_det_ne (x : Fin n → K) (y : Fin (n+1) → K)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j,x i≠y j) :
    (cauchyWithOnes x y).det≠0 := by
  classical
  let M := cauchyWithOnes x y
  have hzero : ∀ b:Fin (n+1) → K,M *ᵥ b=0 → b=0 := by
    intro b hb
    by_contra hn
    have hker : ∀ i,∑ j,(1/(x i-y j))*b j=0 := by
      intro i
      have he := congrFun hb i.castSucc
      simpa only [M,cauchyWithOnes,Matrix.mulVec,dotProduct,Matrix.of_apply,Fin.lastCases_castSucc,Pi.zero_apply] using he
    have hsum : ∑ j,b j=0 := by
      have he := congrFun hb (Fin.last n)
      simpa only [M,cauchyWithOnes,Matrix.mulVec,dotProduct,Matrix.of_apply,Fin.lastCases_last,one_mul,Pi.zero_apply] using he
    exact rectangular_cauchy_kernel_sum x y hx hy hxy b hn hker hsum
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have he : M *ᵥ (u-v)=0 := by rw [Matrix.mulVec_sub,huv,sub_self]
    exact sub_eq_zero.mp (hzero _ he)
  have hu := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero


/-- A rectangular Cauchy system with a constant column forces its
constant unknown to equal the constant right-hand side. This is the
normalization step in both central-threshold direction tests. -/
theorem rectangular_cauchy_constant (x : Fin (n+1) → K) (y : Fin n → K)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j,x i≠y j)
    (v : Fin n → K) (d c : K)
    (he : ∀ i,(∑ j,(1/(x i-y j))*v j)+d=c) : d=c ∧ v=0 := by
  classical
  let M := (cauchyWithOnes y x)ᵀ
  let w : Fin (n+1) → K := Fin.lastCases (d-c) (fun j => -v j)
  have hM : IsUnit M.det := by
    rw [show M=(cauchyWithOnes y x)ᵀ from rfl,Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (cauchyWithOnes_det_ne y x hy hx (fun i j => (hxy j i).symm))
  have hzero : M *ᵥ w=0 := by
    funext i
    change (∑ j,(cauchyWithOnes y x) j i*w j)=0
    rw [Fin.sum_univ_castSucc]
    simp only [cauchyWithOnes,Matrix.of_apply,w,Fin.lastCases_castSucc,
      Fin.lastCases_last,one_mul]
    have hs : (∑ j:Fin n,(1/(y j-x i))*(-v j))=
        ∑ j:Fin n,(1/(x i-y j))*v j := by
      apply Finset.sum_congr rfl
      intro j _
      have hr : 1/(y j-x i)=-(1/(x i-y j)) := by
        simpa only [one_div] using
          (congrArg (fun z:K => z⁻¹) (show y j-x i=-(x i-y j) by ring)).trans inv_neg
      rw [hr,neg_mul_neg]
    rw [hs]
    linear_combination he i
  have hw : w=0 := by
    calc
      w=M⁻¹ *ᵥ (M *ᵥ w) := by
        rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M hM,Matrix.one_mulVec]
      _=0 := by rw [hzero,Matrix.mulVec_zero]
  constructor
  · exact sub_eq_zero.mp (by simpa only [w,Fin.lastCases_last,Pi.zero_apply] using congrFun hw (Fin.last n))
  · funext j
    have hj := congrFun hw j.castSucc
    simpa only [w,Fin.lastCases_castSucc,Pi.zero_apply,neg_eq_zero] using hj

/-- The actual constant COLUMN completion of a rectangular Cauchy
matrix; its last column is the direction unknown in the bordered test. -/
noncomputable def cauchyConstantColumn (x : Fin (n+1) → K) (y : Fin n → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.of fun i j => Fin.lastCases (1:K) (fun a => 1/(x i-y a)) j

theorem cauchyConstantColumn_det_ne (x : Fin (n+1) → K) (y : Fin n → K)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j,x i≠y j) :
    (cauchyConstantColumn x y).det≠0 := by
  classical
  let M := cauchyConstantColumn x y
  have hzero : ∀ v:Fin (n+1) → K,M *ᵥ v=0 → v=0 := by
    intro v hv
    have he : ∀ i,(∑ j:Fin n,(1/(x i-y j))*v j.castSucc)+v (Fin.last n)=0 := by
      intro i
      have hi := congrFun hv i
      simpa only [M,cauchyConstantColumn,Matrix.mulVec,dotProduct,Matrix.of_apply,
        Fin.sum_univ_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last,
        one_mul,Pi.zero_apply] using hi
    obtain ⟨hd,hv0⟩ := rectangular_cauchy_constant x y hx hy hxy
      (fun j => v j.castSucc) (v (Fin.last n)) 0 he
    funext j
    refine Fin.lastCases ?_ (fun a => ?_) j
    · exact hd
    · exact congrFun hv0 a
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have he : M *ᵥ (u-v)=0 := by rw [Matrix.mulVec_sub,huv,sub_self]
    exact sub_eq_zero.mp (hzero _ he)
  exact ((Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

end CauchyAugmented

section StepLoewner
variable {K : Type*} [Field K]

noncomputable def stepValue (cut a : ℕ) : K := if a<cut then 0 else 1
noncomputable def stepEntry (cut a b : ℕ) : K :=
  (stepValue (K:=K) cut b-stepValue (K:=K) cut a)/((b:K)-(a:K))

theorem one_div_reverse (a b : K) : 1/(b-a)=-(1/(a-b)) := by
  simpa only [one_div] using
    (congrArg (fun z:K => z⁻¹) (show b-a=-(a-b) by ring)).trans inv_neg


/-- Central step system when the HIGH rectangular block has one
extra row. The final column carries the normalized direction. -/
noncomputable def centralStepBorderOne {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH : Fin (h+1) → ℕ) (yL : Fin h → ℕ) :
    Matrix (Fin l ⊕ Fin (h+1)) (Fin l ⊕ Fin (h+1)) K :=
  Matrix.of fun i j => Sum.elim
    (fun a => stepEntry (K:=K) cut (Sum.elim xL xH i) (yH a))
    (fun a => Fin.lastCases (1:K)
      (fun b => stepEntry (K:=K) cut (Sum.elim xL xH i) (yL b)) a) j

theorem centralStepBorderOne_eq {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH : Fin (h+1) → ℕ) (yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut) :
    centralStepBorderOne (K:=K) cut xL yH xH yL=
      Matrix.fromBlocks
        (-(WrapCauchy.matrix (fun i => (xL i:K)) (fun j => (yH j:K))))
        (Matrix.of fun (_:Fin l) (j:Fin (h+1)) => Fin.lastCases (1:K) (fun _ => 0) j)
        0 (cauchyConstantColumn (fun i => (xH i:K)) (fun j => (yL j:K))) := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inl,
      Matrix.fromBlocks_apply₁₁,Matrix.neg_apply,WrapCauchy.matrix,
      stepEntry,stepValue,if_pos (hxL i),if_neg (not_lt_of_ge (hyH j)),sub_zero]
    exact one_div_reverse _ _
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩|rfl
    · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
        Fin.lastCases_castSucc,Matrix.fromBlocks_apply₁₂,stepEntry,stepValue,
        if_pos (hxL i),if_pos (hyL j),sub_self,zero_div]
    · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
        Fin.lastCases_last,Matrix.fromBlocks_apply₁₂]
  · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,stepEntry,stepValue,
      if_neg (not_lt_of_ge (hxH i)),if_neg (not_lt_of_ge (hyH j)),sub_self,zero_div]
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩|rfl
    · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inr,
        Fin.lastCases_castSucc,Matrix.fromBlocks_apply₂₂,cauchyConstantColumn,
        stepEntry,stepValue,if_neg (not_lt_of_ge (hxH i)),if_pos (hyL j),
        zero_sub,neg_div]
      rw [one_div_reverse,neg_neg]
    · simp only [centralStepBorderOne,Matrix.of_apply,Sum.elim_inr,
        Fin.lastCases_last,Matrix.fromBlocks_apply₂₂,cauchyConstantColumn]

theorem centralStepBorderOne_det_ne {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH : Fin (h+1) → ℕ) (yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut)
    (hxiL : Function.Injective (fun i => (xL i:K)))
    (hyiH : Function.Injective (fun i => (yH i:K)))
    (hxiH : Function.Injective (fun i => (xH i:K)))
    (hyiL : Function.Injective (fun i => (yL i:K)))
    (hxy0 : ∀ i j,(xL i:K)≠(yH j:K)) (hxy1 : ∀ i j,(xH i:K)≠(yL j:K)) :
    (centralStepBorderOne (K:=K) cut xL yH xH yL).det≠0 := by
  rw [centralStepBorderOne_eq cut xL yH xH yL hxL hyH hxH hyL,
    Matrix.det_fromBlocks_zero₂₁,Matrix.det_neg]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (WrapCauchy.det_ne _ _ hxiL hyiH hxy0))
    (cauchyConstantColumn_det_ne _ _ hxiH hyiL hxy1)

/-- The complementary central step system has one extra LOW row;
its constant direction column is placed with the high-column group. -/
noncomputable def centralStepBorderZero {l h : ℕ} (cut : ℕ)
    (xL : Fin (l+1) → ℕ) (yH : Fin l → ℕ) (xH yL : Fin h → ℕ) :
    Matrix (Fin (l+1) ⊕ Fin h) (Fin (l+1) ⊕ Fin h) K :=
  Matrix.of fun i j => Sum.elim
    (fun a => Fin.lastCases (1:K)
      (fun b => stepEntry (K:=K) cut (Sum.elim xL xH i) (yH b)) a)
    (fun a => stepEntry (K:=K) cut (Sum.elim xL xH i) (yL a)) j

theorem centralStepBorderZero_eq {l h : ℕ} (cut : ℕ)
    (xL : Fin (l+1) → ℕ) (yH : Fin l → ℕ) (xH yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut) :
    centralStepBorderZero (K:=K) cut xL yH xH yL=
      Matrix.fromBlocks
        ((cauchyWithOnes (fun j => (yH j:K)) (fun i => (xL i:K)))ᵀ) 0
        (Matrix.of fun (_:Fin h) (j:Fin (l+1)) => Fin.lastCases (1:K) (fun _ => 0) j)
        (WrapCauchy.matrix (fun i => (xH i:K)) (fun j => (yL j:K))) := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩|rfl
    · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inl,
        Fin.lastCases_castSucc,Matrix.fromBlocks_apply₁₁,Matrix.transpose_apply,
        cauchyWithOnes,stepEntry,stepValue,if_pos (hxL i),
        if_neg (not_lt_of_ge (hyH j)),sub_zero]
    · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inl,
        Fin.lastCases_last,Matrix.fromBlocks_apply₁₁,Matrix.transpose_apply,cauchyWithOnes]
  · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,stepEntry,stepValue,
      if_pos (hxL i),if_pos (hyL j),sub_self,zero_div]
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩|rfl
    · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
        Fin.lastCases_castSucc,Matrix.fromBlocks_apply₂₁,stepEntry,stepValue,
        if_neg (not_lt_of_ge (hxH i)),if_neg (not_lt_of_ge (hyH j)),sub_self,zero_div]
    · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
        Fin.lastCases_last,Matrix.fromBlocks_apply₂₁]
  · simp only [centralStepBorderZero,Matrix.of_apply,Sum.elim_inr,
      Matrix.fromBlocks_apply₂₂,WrapCauchy.matrix,stepEntry,stepValue,
      if_neg (not_lt_of_ge (hxH i)),if_pos (hyL j),zero_sub,neg_div]
    rw [one_div_reverse,neg_neg]

theorem centralStepBorderZero_det_ne {l h : ℕ} (cut : ℕ)
    (xL : Fin (l+1) → ℕ) (yH : Fin l → ℕ) (xH yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut)
    (hxiL : Function.Injective (fun i => (xL i:K)))
    (hyiH : Function.Injective (fun i => (yH i:K)))
    (hxiH : Function.Injective (fun i => (xH i:K)))
    (hyiL : Function.Injective (fun i => (yL i:K)))
    (hxy0 : ∀ i j,(xL i:K)≠(yH j:K)) (hxy1 : ∀ i j,(xH i:K)≠(yL j:K)) :
    (centralStepBorderZero (K:=K) cut xL yH xH yL).det≠0 := by
  rw [centralStepBorderZero_eq cut xL yH xH yL hxL hyH hxH hyL,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_transpose]
  exact mul_ne_zero
    (cauchyWithOnes_det_ne _ _ hyiH hxiL (fun i j => (hxy0 j i).symm))
    (WrapCauchy.det_ne _ _ hxiH hyiL hxy1)

/-- The HIGH rectangular block forces direction one in the actual
bordered step system; no inverse of its potential square block is used. -/
theorem centralStepBorderOne_direction {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH : Fin (h+1) → ℕ) (yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut)
    (hxiH : Function.Injective (fun i => (xH i:K)))
    (hyiL : Function.Injective (fun i => (yL i:K)))
    (hxy : ∀ i j,(xH i:K)≠(yL j:K))
    (v : Fin l ⊕ Fin (h+1) → K)
    (hv : centralStepBorderOne (K:=K) cut xL yH xH yL *ᵥ v=
      fun i => stepValue (K:=K) cut (Sum.elim xL xH i)) :
    v (Sum.inr (Fin.last h))=1 := by
  classical
  rw [centralStepBorderOne_eq cut xL yH xH yL hxL hyH hxH hyL] at hv
  have he : ∀ i,(∑ j:Fin h,(1/((xH i:K)-(yL j:K)))*v (Sum.inr j.castSucc))+
      v (Sum.inr (Fin.last h))=1 := by
    intro i
    have hi := congrFun hv (Sum.inr i)
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,zero_add,cauchyConstantColumn,Matrix.of_apply,
      Fin.sum_univ_castSucc,Fin.lastCases_castSucc,Fin.lastCases_last,one_mul,
      Sum.elim_inr,stepValue,if_neg (not_lt_of_ge (hxH i))] using hi
  exact (rectangular_cauchy_constant (fun i => (xH i:K)) (fun j => (yL j:K))
    hxiH hyiL hxy (fun j => v (Sum.inr j.castSucc))
    (v (Sum.inr (Fin.last h))) 1 he).1

/-- The LOW rectangular block forces direction zero in the
complementary bordered step system. -/
theorem centralStepBorderZero_direction {l h : ℕ} (cut : ℕ)
    (xL : Fin (l+1) → ℕ) (yH : Fin l → ℕ) (xH yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut)
    (hxiL : Function.Injective (fun i => (xL i:K)))
    (hyiH : Function.Injective (fun i => (yH i:K)))
    (hxy : ∀ i j,(xL i:K)≠(yH j:K))
    (v : Fin (l+1) ⊕ Fin h → K)
    (hv : centralStepBorderZero (K:=K) cut xL yH xH yL *ᵥ v=
      fun i => stepValue (K:=K) cut (Sum.elim xL xH i)) :
    v (Sum.inl (Fin.last l))=0 := by
  classical
  rw [centralStepBorderZero_eq cut xL yH xH yL hxL hyH hxH hyL] at hv
  have he : ∀ i,(∑ j:Fin l,(1/((xL i:K)-(yH j:K)))*(-v (Sum.inl j.castSucc)))+
      v (Sum.inl (Fin.last l))=0 := by
    intro i
    have hi := congrFun hv (Sum.inl i)
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,
      zero_mul,Finset.sum_const_zero,add_zero,Matrix.transpose_apply,
      cauchyWithOnes,Matrix.of_apply,Fin.sum_univ_castSucc,
      Fin.lastCases_castSucc,Fin.lastCases_last,one_mul,Sum.elim_inl,
      stepValue,if_pos (hxL i)] at hi
    have hs : (∑ j:Fin l,(1/((xL i:K)-(yH j:K)))*(-v (Sum.inl j.castSucc)))=
        ∑ j:Fin l,(1/((yH j:K)-(xL i:K)))*v (Sum.inl j.castSucc) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [one_div_reverse]
      ring
    rw [hs]
    exact hi
  exact (rectangular_cauchy_constant (fun i => (xL i:K)) (fun j => (yH j:K))
    hxiL hyiH hxy (fun j => -v (Sum.inl j.castSucc))
    (v (Sum.inl (Fin.last l))) 0 he).1

end StepLoewner

section SpectralOrder
variable {K : Type*} [Field K]


/-- The ORIGINAL cleared three-variable expression embeds faithfully in
the actual nested residue field, without evaluating a generic pivot. -/
noncomputable def embedThree : K[X][X][X] →+* RatFunc (RatFunc (RatFunc K)) :=
  (algebraMap (RatFunc (RatFunc K))[X] (RatFunc (RatFunc (RatFunc K)))).comp
    (Polynomial.mapRingHom (WrapBivariate.embed (K:=K)))


end SpectralOrder


theorem rational_div_eq_mul_inv {S : Type*} [CommRing S] [IsDomain S]
    (a b : RatFunc S) : a/b=a*b⁻¹ := div_eq_mul_inv a b


section TwoParameterDescent
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable (phi : R →+* K)


end TwoParameterDescent

namespace TwoTermDeformation
variable (p : ℕ) [Fact p.Prime]


variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


abbrev Residue := RatFunc (WrapPoleResidue.Residue p)


section ActualPrefix
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)


end ActualPrefix

end TwoTermDeformation

section CentralPole


end CentralPole

section ClosedRetainedCount
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The original nonzero row coupling supplies its actual killed colour. -/
theorem row_killed_colour (s u : GaussLoc p) (z : Fin d)
    (hl : WrapPrefixSchur.rowCoupling H s u z≠0)
    (hw : H.weight s u (WrapPrefixSchur.surplusRow H z:ZMod p)≠0) :
    (WrapPrefixSchur.surplusRow H z:ZMod p)∈WrapPrefixSchur.killedRows H s u := by
  classical
  apply mem_image.mpr
  exact ⟨z,mem_filter.mpr ⟨mem_univ z,hl,hw⟩,rfl⟩

/-- The original nonzero column coupling supplies its actual killed colour. -/
theorem col_killed_colour (s u : GaussLoc p) (y : Fin d)
    (hl : WrapPrefixSchur.colCoupling H s u y≠0) :
    (WrapPrefixSchur.surplusCol H y:ZMod p)∈WrapPrefixSchur.killedColumns H s u := by
  classical
  apply mem_image.mpr
  exact ⟨y,mem_filter.mpr ⟨mem_univ y,hl⟩,rfl⟩

/-- Original credited source zeros and actual outside coupling kills
feed exactly the existing three-translate closed residue count. -/
theorem retained_closed_bound (hb : b≤p)
    (hcolour : ∀ i:Fin b,(H.xs (Sum.inr i):ZMod p)=((r+(i:ℕ):ℕ):ZMod p))
    (w0 w1 : ℕ) (h0 : H.t0∈Icc w0 w1) (hhi : w1<r+2*n*p+b+p)
    (hdiv : w1/p=w0/p)
    (hw : ∀ v∈Ioc w0 w1,res p (v:GaussLoc p)≠0 ∧ res p (WrapIncrement.argument p q o v)≠0)
    (hcover : ∀ v∈Ico (r+2*n*p+b) (r+2*n*p+b+2*d),
      (∃ z:Fin d,WrapPrefixSchur.surplusRow H z=v) ∨
      (∃ y:Fin d,WrapPrefixSchur.surplusCol H y=v))
    (hwidth : 2*d≤p) (hwin : w1<w0+p)
    (hR : r+2*n*p+b+2*d≤w0+2*p) (hW : w1<r+2*n*p+b+2*p)
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hrow : ∀ z:Fin d,
      (¬∃ w∈Icc w0 w1,(WrapPrefixSchur.surplusRow H z:ZMod p)=(w:ZMod p)) →
      H.weight s u (WrapPrefixSchur.surplusRow H z:ZMod p)=0 ∨ WrapPrefixSchur.rowCoupling H s u z≠0)
    (hcol : ∀ y:Fin d,
      (¬∃ w∈Icc w0 w1,(WrapPrefixSchur.surplusCol H y:ZMod p)=(w:ZMod p)) →
      H.weight s u (WrapPrefixSchur.surplusCol H y:ZMod p)=0 ∨ WrapPrefixSchur.colCoupling H s u y≠0) :
    (WrapPrefixMember.fullRetained H s u).card≤
      p-((w1+1-w0)+(2*d-beta3 d (r+2*n*p+b) p w0 w1)) := by
  classical
  let I := (Icc w0 w1).image (fun v:ℕ => (v:ZMod p))
  let O := (outNodes p (r+2*n*p+b) d w0 w1).image (fun v:ℕ => (v:ZMod p))
  have hI : ∀ gamma∈I,H.weight s u gamma=0 := by
    intro gamma hg
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hg
    exact credited_interval_zero H hb hcolour w0 w1 h0 hhi hdiv hw s u hs hu huc t ht
  have hO : ∀ gamma∈O,H.weight s u gamma=0 ∨
      gamma∈WrapPrefixSchur.killedColumns H s u∪WrapPrefixSchur.killedRows H s u := by
    intro gamma hg
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hg
    have hvo := mem_outNodes.mp hv
    rcases hcover v (mem_Ico.mpr hvo.1) with ⟨z,hz⟩|⟨y,hy⟩
    · rcases hrow z (by simpa only [hz] using hvo.2) with hz0|hz1
      · exact Or.inl (by simpa only [hz] using hz0)
      · by_cases hwv : H.weight s u (v:ZMod p)=0
        · exact Or.inl hwv
        · have hk := row_killed_colour H s u z hz1 (by simpa only [hz] using hwv)
          exact Or.inr (mem_union_right _ (by simpa only [hz] using hk))
    · rcases hcol y (by simpa only [hy] using hvo.2) with hy0|hy1
      · exact Or.inl (by simpa only [hy] using hy0)
      · have hk := col_killed_colour H s u y hy1
        exact Or.inr (mem_union_left _ (by simpa only [hy] using hk))
  have hc := retained_credit_bound H s u I O hI hO
  have hcount := WrapCell.residue_union_count (p:=p) (r+2*n*p+b) d w0 w1 hwin hwidth hR hW
  exact hc.trans (Nat.sub_le_sub_left hcount p)

end ClosedRetainedCount


end CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed

-- Section 8.2-8.3 separation and two-parameter transport (moved verbatim from WrapPrefixLayer, 31 Oct).
open CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section SpectralTop
variable {F : Type*} [Field F] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Original cleared spectral system: only the original common
coordinates carry the spectral variable, with scalar `c`. -/
noncomputable def spectralBlocks (c : F) (A : Matrix ι ι F) (B : Matrix ι κ F)
    (E : Matrix κ ι F) (D : Matrix κ κ F) : Matrix (ι ⊕ κ) (ι ⊕ κ) F[X] :=
  Matrix.fromBlocks ((X*Polynomial.C c) • (1:Matrix ι ι F[X])+A.map Polynomial.C)
    (B.map Polynomial.C) (E.map Polynomial.C) (D.map Polynomial.C)

/-- The same system after the substitution of the reciprocal spectral
variable, with the common columns divided by the spectral variable. -/
noncomputable def reversedBlocks (c : F) (A : Matrix ι ι F) (B : Matrix ι κ F)
    (E : Matrix κ ι F) (D : Matrix κ κ F) : Matrix (ι ⊕ κ) (ι ⊕ κ) F[X] :=
  Matrix.fromBlocks (Polynomial.C c • (1:Matrix ι ι F[X])+(X:F[X]) • A.map Polynomial.C)
    (B.map Polynomial.C) ((X:F[X]) • E.map Polynomial.C) (D.map Polynomial.C)

theorem reversedBlocks_zero (c : F) (A : Matrix ι ι F) (B : Matrix ι κ F)
    (E : Matrix κ ι F) (D : Matrix κ κ F) :
    (reversedBlocks c A B E D).det.eval 0=c^Fintype.card ι*D.det := by
  have he : (reversedBlocks c A B E D).map (Polynomial.evalRingHom (0:F))=
      Matrix.fromBlocks (c • (1:Matrix ι ι F)) B 0 D := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;>
      simp only [reversedBlocks,Matrix.map_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.add_apply,Matrix.smul_apply,
        Matrix.one_apply,Matrix.zero_apply,smul_eq_mul,Polynomial.coe_evalRingHom,
        Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,zero_mul,add_zero]
    all_goals (try split_ifs) <;> simp
  have hd := RingHom.map_det (Polynomial.evalRingHom (0:F)) (reversedBlocks c A B E D)
  rw [show (reversedBlocks c A B E D).det.eval 0=
    (Polynomial.evalRingHom (0:F)) (reversedBlocks c A B E D).det from rfl,hd]
  change ((reversedBlocks c A B E D).map (Polynomial.evalRingHom (0:F))).det=_
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_smul,Matrix.det_one,mul_one]

/-- Highest original spectral coefficient: the cleared determinant has
degree at most the number of original common coordinates, and its top
coefficient is the determinant of the non-common block. No pivot is used. -/
theorem spectral_top (c : F) (A : Matrix ι ι F) (B : Matrix ι κ F)
    (E : Matrix κ ι F) (D : Matrix κ κ F) :
    (spectralBlocks c A B E D).det.natDegree≤Fintype.card ι ∧
      (spectralBlocks c A B E D).det.coeff (Fintype.card ι)=c^Fintype.card ι*D.det := by
  classical
  let L := RatFunc F
  let φ : F[X] →+* L := algebraMap F[X] L
  have hφ : Function.Injective φ := IsFractionRing.injective F[X] L
  let x : L := φ X
  have hx : x≠0 := by
    intro h
    exact Polynomial.X_ne_zero (hφ (by simpa only [map_zero] using h))
  have hx' : (algebraMap F[X] L) X≠0 := hx
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have hφC : ∀ a : F,φ (Polynomial.C a)=algebraMap F L a := by
    intro a
    rw [IsScalarTower.algebraMap_apply F F[X] L,Polynomial.algebraMap_eq]
  have hev : φ=Polynomial.eval₂RingHom (algebraMap F L) x := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [hφC]
      simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,x]
  let M := spectralBlocks c A B E D
  let S := reversedBlocks c A B E D
  let ψ : F[X] →+* L := Polynomial.eval₂RingHom (algebraMap F L) x⁻¹
  let v : ι ⊕ κ → L := Sum.elim (fun _ => x) (fun _ => 1)
  have hcol : M.map φ=Matrix.of fun i j => v j*(S.map ψ) i j := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j
      · subst hij
        simp only [M,S,spectralBlocks,reversedBlocks,Matrix.map_apply,Matrix.of_apply,
          Matrix.fromBlocks_apply₁₁,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,
          smul_eq_mul,mul_one,v,Sum.elim_inl,ψ,map_add,map_mul,Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,hφC]
        change x*_+_=x*_
        rw [mul_add,← mul_assoc,mul_inv_cancel₀ hx,one_mul]
      · simp only [M,S,spectralBlocks,reversedBlocks,Matrix.map_apply,Matrix.of_apply,
          Matrix.fromBlocks_apply₁₁,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_ne hij,
          smul_eq_mul,mul_zero,zero_add,v,Sum.elim_inl,ψ,Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,hφC,map_zero]
        rw [← mul_assoc,mul_inv_cancel₀ hx,one_mul]
    · simp only [M,S,spectralBlocks,reversedBlocks,Matrix.map_apply,Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂,v,Sum.elim_inr,one_mul,ψ,Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C,hφC]
    · simp only [M,S,spectralBlocks,reversedBlocks,Matrix.map_apply,Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁,Matrix.smul_apply,smul_eq_mul,v,Sum.elim_inl,ψ,
        Polynomial.coe_eval₂RingHom,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_X,hφC]
      rw [← mul_assoc,mul_inv_cancel₀ hx,one_mul]
    · simp only [M,S,spectralBlocks,reversedBlocks,Matrix.map_apply,Matrix.of_apply,
        Matrix.fromBlocks_apply₂₂,v,Sum.elim_inr,one_mul,ψ,Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C,hφC]
  have hdet : φ M.det=x^Fintype.card ι*ψ S.det := by
    rw [RingHom.map_det,RingHom.mapMatrix_apply,hcol,Matrix.det_mul_row,
      ← RingHom.mapMatrix_apply,← RingHom.map_det]
    congr 1
    simp only [v,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.prod_const_one,mul_one,
      Finset.prod_const,Finset.card_univ]
  let Nd := S.det.natDegree
  have href := Polynomial.eval₂_reflect_mul_pow (algebraMap F L) x⁻¹ Nd S.det le_rfl
  have hinv : ⅟(x⁻¹)=x := by
    rw [invOf_eq_inv,inv_inv]
  rw [hinv] at href
  have hxN : x⁻¹^Nd*x^Nd=1 := by rw [inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hx)]
  have hpoly : M.det*X^Nd=X^Fintype.card ι*Polynomial.reflect Nd S.det := by
    apply hφ
    have hr : φ (Polynomial.reflect Nd S.det)=
        Polynomial.eval₂ (algebraMap F L) x (Polynomial.reflect Nd S.det) := by
      rw [hev]; rfl
    have hS : ψ S.det=Polynomial.eval₂ (algebraMap F L) x⁻¹ S.det := rfl
    rw [map_mul,map_mul,hdet,map_pow,map_pow,hr,hS,← href]
    change x^Fintype.card ι*(_*x⁻¹^Nd)*x^Nd=x^Fintype.card ι*_
    rw [mul_assoc,mul_assoc,hxN,mul_one]
  have hrdeg : (Polynomial.reflect Nd S.det).natDegree≤Nd := by
    have := Polynomial.natDegree_reflect_le (N:=Nd) (p:=S.det)
    simpa [Nd] using this
  constructor
  · by_cases hM : M.det=0
    · change M.det.natDegree≤_
      rw [hM,Polynomial.natDegree_zero]
      exact Nat.zero_le _
    · have h1 := congrArg Polynomial.natDegree hpoly
      rw [Polynomial.natDegree_mul hM (pow_ne_zero _ Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow] at h1
      have h2 : (X^Fintype.card ι*Polynomial.reflect Nd S.det).natDegree≤Fintype.card ι+Nd := by
        calc _≤(X^Fintype.card ι:F[X]).natDegree+(Polynomial.reflect Nd S.det).natDegree :=
              Polynomial.natDegree_mul_le
          _≤_ := by rw [Polynomial.natDegree_X_pow]; omega
      change M.det.natDegree≤_
      omega
  · have h1 : (M.det*X^Nd).coeff (Fintype.card ι+Nd)=
        (X^Fintype.card ι*Polynomial.reflect Nd S.det).coeff (Fintype.card ι+Nd) := by
      rw [hpoly]
    rw [Polynomial.coeff_mul_X_pow,Polynomial.coeff_X_pow_mul',if_pos (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left,Polynomial.coeff_reflect,Polynomial.revAt_le le_rfl,Nat.sub_self,
      Polynomial.coeff_zero_eq_eval_zero,reversedBlocks_zero] at h1
    exact h1

end SpectralTop


section StepFibre
variable {K : Type*} [Field K]

theorem submatrix_det_ne_iff {R ι τ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ] (A : Matrix ι ι R) (er ec : τ ≃ ι) :
    (A.submatrix er ec).det≠0 ↔ A.det≠0 := by
  have he : (A.submatrix er ec).det=((Equiv.Perm.sign (ec.symm.trans er):ℤ):R)*A.det := by
    simpa only [Matrix.reindex_apply,Equiv.symm_symm] using Matrix.det_reindex er.symm ec.symm A
  have hu : IsUnit (((Equiv.Perm.sign (ec.symm.trans er):ℤ):R)) :=
    (Equiv.Perm.sign (ec.symm.trans er)).isUnit.map (Int.castRingHom R)
  rw [he]
  constructor
  · intro h hz
    exact h (by rw [hz,mul_zero])
  · intro h hz
    exact h ((hu.mul_right_eq_zero).mp hz)

/-- Bordered central step system of one actual fibre at its highest
spectral degree: balanced rows then the zone; balanced columns then the
constant direction column (never multiplied by the central factor). -/
noncomputable def stepBordered (cut : ℕ) {n : ℕ} (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.of fun i j => if h : (j:ℕ)<n then stepEntry (K:=K) cut (rowQ i) (colQ ⟨j,h⟩) else 1

/-- Lower adjacent type: `n+1` low nodes. The bordered system is
nonsingular and its direction coordinate is zero. -/
theorem stepBordered_zero (cut n LR h : ℕ) (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ)
    (hR : ∀ i,rowQ i<cut ↔ (i:ℕ)<LR) (hC : ∀ c,colQ c<cut ↔ (c:ℕ)<h)
    (hsum : LR+h=n+1) (hLR : 1≤LR)
    (hri : Function.Injective (fun i => (rowQ i:K)))
    (hci : Function.Injective (fun c => (colQ c:K)))
    (hrc : ∀ i c,(rowQ i:K)≠(colQ c:K)) :
    (stepBordered (K:=K) cut rowQ colQ).det≠0 ∧
      ∀ w,stepBordered (K:=K) cut rowQ colQ *ᵥ w=(fun i => stepValue (K:=K) cut (rowQ i)) →
        w (Fin.last n)=0 := by
  classical
  obtain ⟨l,rfl⟩ : ∃ l,LR=l+1 := ⟨LR-1,by omega⟩
  have hcard : l+1+h=n+1 := by omega
  let eR : Fin (l+1) ⊕ Fin h ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr hcard)
  let fC : Fin (l+1) ⊕ Fin h → Fin (n+1) := fun j => Sum.elim
    (fun a:Fin (l+1) => if (a:ℕ)<l then (⟨h+(a:ℕ),by omega⟩:Fin (n+1)) else Fin.last n)
    (fun a:Fin h => (⟨(a:ℕ),by omega⟩:Fin (n+1))) j
  have hfC : Function.Bijective fC := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_,by simp only [Fintype.card_sum,Fintype.card_fin]; omega⟩
    intro x y hxy
    have hv := congrArg Fin.val hxy
    rcases x with a|a <;> rcases y with b|b <;>
      simp only [fC,Sum.elim_inl,Sum.elim_inr] at hv
    · have ha := a.2; have hb := b.2
      split_ifs at hv with h1 h2 h2 <;> simp only [Fin.val_last] at hv
      · exact congrArg Sum.inl (Fin.ext (by omega))
      · omega
      · omega
      · exact congrArg Sum.inl (Fin.ext (by omega))
    · have hb := b.2
      split_ifs at hv with h1 <;> simp only [Fin.val_last] at hv <;> omega
    · have ha := a.2
      split_ifs at hv with h1 <;> simp only [Fin.val_last] at hv <;> omega
    · exact congrArg Sum.inr (Fin.ext hv)
  let eC : Fin (l+1) ⊕ Fin h ≃ Fin (n+1) := Equiv.ofBijective fC hfC
  let xL : Fin (l+1) → ℕ := fun a => rowQ (eR (Sum.inl a))
  let xH : Fin h → ℕ := fun a => rowQ (eR (Sum.inr a))
  let yH : Fin l → ℕ := fun b => colQ ⟨h+(b:ℕ),by omega⟩
  let yL : Fin h → ℕ := fun a => colQ ⟨(a:ℕ),by omega⟩
  have heR (i : Fin (l+1) ⊕ Fin h) : rowQ (eR i)=Sum.elim xL xH i := by cases i <;> rfl
  have hM : (stepBordered (K:=K) cut rowQ colQ).submatrix eR eC=
      centralStepBorderZero (K:=K) cut xL yH xH yL := by
    ext i j
    rcases j with a|a
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨b,rfl⟩|rfl
      · have hb : (b:ℕ)<l := b.2
        have hc : ((eC (Sum.inl b.castSucc)):ℕ)=h+(b:ℕ) := by
          simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inl,Fin.coe_castSucc,if_pos hb]
        have hlt : ((eC (Sum.inl b.castSucc)):ℕ)<n := by omega
        simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderZero,
          Sum.elim_inl,Fin.lastCases_castSucc,dif_pos hlt,heR]
        congr 2
        try exact Fin.ext hc
      · have hc : eC (Sum.inl (Fin.last l))=Fin.last n := by
          simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inl,Fin.val_last,lt_irrefl,if_false]
        simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderZero,
          Sum.elim_inl,Fin.lastCases_last,hc,Fin.val_last,lt_irrefl,dite_false]
    · have hc : ((eC (Sum.inr a)):ℕ)=(a:ℕ) := by
        simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inr]
      have hlt : ((eC (Sum.inr a)):ℕ)<n := by have := a.2; omega
      simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderZero,
        Sum.elim_inr,dif_pos hlt,heR]
      congr 2
      try exact Fin.ext hc
  have hxL : ∀ i,xL i<cut := by
    intro i; apply (hR _).mpr
    have := i.2
    simp only [eR,Equiv.trans_apply,finSumFinEquiv_apply_left,finCongr_apply,Fin.coe_cast,
      Fin.coe_castAdd]
    omega
  have hxH : ∀ i,cut≤xH i := by
    intro i; apply le_of_not_gt; intro hc
    have := (hR _).mp hc
    simp only [eR,Equiv.trans_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.coe_cast,
      Fin.coe_natAdd] at this
    omega
  have hyH : ∀ i,cut≤yH i := by
    intro i; apply le_of_not_gt; intro hc
    have := (hC _).mp hc
    change h+(i:ℕ)<h at this
    omega
  have hyL : ∀ i,yL i<cut := by
    intro i; apply (hC _).mpr
    exact i.2
  have hinjR : Function.Injective (fun a => (xL a:K)) := fun a b hab =>
    Sum.inl_injective (eR.injective (hri hab))
  have hinjH : Function.Injective (fun a => (xH a:K)) := fun a b hab =>
    Sum.inr_injective (eR.injective (hri hab))
  have hinjyH : Function.Injective (fun a => (yH a:K)) := by
    intro a b hab
    have := congrArg Fin.val (hci hab)
    exact Fin.ext (by simp only at this; omega)
  have hinjyL : Function.Injective (fun a => (yL a:K)) := by
    intro a b hab
    have := congrArg Fin.val (hci hab)
    exact Fin.ext this
  constructor
  · rw [← submatrix_det_ne_iff _ eR eC,hM]
    exact centralStepBorderZero_det_ne cut xL yH xH yL hxL hyH hxH hyL hinjR hinjyH hinjH hinjyL
      (fun i j => hrc _ _) (fun i j => hrc _ _)
  · intro w hw
    have hv := centralStepBorderZero_direction (K:=K) cut xL yH xH yL hxL hyH hxH hyL hinjR hinjyH
      (fun i j => hrc _ _) (w ∘ eC) (by
        rw [← hM,Matrix.submatrix_mulVec_equiv]
        have hw2 : (w ∘ eC) ∘ eC.symm=w := by funext x; simp
        rw [hw2,hw]
        funext i
        simp only [Function.comp_apply]
        rw [heR])
    have hc : eC (Sum.inl (Fin.last l))=Fin.last n := by
      simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inl,Fin.val_last,lt_irrefl,if_false]
    simpa only [Function.comp_apply,hc] using hv

/-- Upper adjacent type: `n` low nodes. The bordered system is
nonsingular and its direction coordinate is one. -/
theorem stepBordered_one (cut n l h : ℕ) (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ)
    (hR : ∀ i,rowQ i<cut ↔ (i:ℕ)<l) (hC : ∀ c,colQ c<cut ↔ (c:ℕ)<h)
    (hsum : l+h=n)
    (hri : Function.Injective (fun i => (rowQ i:K)))
    (hci : Function.Injective (fun c => (colQ c:K)))
    (hrc : ∀ i c,(rowQ i:K)≠(colQ c:K)) :
    (stepBordered (K:=K) cut rowQ colQ).det≠0 ∧
      ∀ w,stepBordered (K:=K) cut rowQ colQ *ᵥ w=(fun i => stepValue (K:=K) cut (rowQ i)) →
        w (Fin.last n)=1 := by
  classical
  have hcard : l+(h+1)=n+1 := by omega
  let eR : Fin l ⊕ Fin (h+1) ≃ Fin (n+1) := finSumFinEquiv.trans (finCongr hcard)
  let fC : Fin l ⊕ Fin (h+1) → Fin (n+1) := fun j => Sum.elim
    (fun a:Fin l => (⟨h+(a:ℕ),by omega⟩:Fin (n+1)))
    (fun a:Fin (h+1) => if (a:ℕ)<h then (⟨(a:ℕ),by omega⟩:Fin (n+1)) else Fin.last n) j
  have hfC : Function.Bijective fC := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_,by simp only [Fintype.card_sum,Fintype.card_fin]; omega⟩
    intro x y hxy
    have hv := congrArg Fin.val hxy
    rcases x with a|a <;> rcases y with b|b <;>
      simp only [fC,Sum.elim_inl,Sum.elim_inr] at hv
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · have ha := a.2; have hb := b.2
      split_ifs at hv with h1 <;> simp only [Fin.val_last] at hv <;> omega
    · have ha := a.2; have hb := b.2
      split_ifs at hv with h1 <;> simp only [Fin.val_last] at hv <;> omega
    · have ha := a.2; have hb := b.2
      split_ifs at hv with h1 h2 h2 <;> simp only [Fin.val_last] at hv
      · exact congrArg Sum.inr (Fin.ext (by omega))
      · omega
      · omega
      · exact congrArg Sum.inr (Fin.ext (by omega))
  let eC : Fin l ⊕ Fin (h+1) ≃ Fin (n+1) := Equiv.ofBijective fC hfC
  let xL : Fin l → ℕ := fun a => rowQ (eR (Sum.inl a))
  let xH : Fin (h+1) → ℕ := fun a => rowQ (eR (Sum.inr a))
  let yH : Fin l → ℕ := fun b => colQ ⟨h+(b:ℕ),by omega⟩
  let yL : Fin h → ℕ := fun a => colQ ⟨(a:ℕ),by omega⟩
  have heR (i : Fin l ⊕ Fin (h+1)) : rowQ (eR i)=Sum.elim xL xH i := by cases i <;> rfl
  have hM : (stepBordered (K:=K) cut rowQ colQ).submatrix eR eC=
      centralStepBorderOne (K:=K) cut xL yH xH yL := by
    ext i j
    rcases j with a|a
    · have hc : ((eC (Sum.inl a)):ℕ)=h+(a:ℕ) := by
        simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inl]
      have hlt : ((eC (Sum.inl a)):ℕ)<n := by have := a.2; omega
      simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderOne,
        Sum.elim_inl,dif_pos hlt,heR]
      congr 2
      try exact Fin.ext hc
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨b,rfl⟩|rfl
      · have hb : (b:ℕ)<h := b.2
        have hc : ((eC (Sum.inr b.castSucc)):ℕ)=(b:ℕ) := by
          simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inr,Fin.coe_castSucc,if_pos hb]
        have hlt : ((eC (Sum.inr b.castSucc)):ℕ)<n := by omega
        simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderOne,
          Sum.elim_inr,Fin.lastCases_castSucc,dif_pos hlt,heR]
        congr 2
        try exact Fin.ext hc
      · have hc : eC (Sum.inr (Fin.last h))=Fin.last n := by
          simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inr,Fin.val_last,lt_irrefl,if_false]
        simp only [Matrix.submatrix_apply,stepBordered,Matrix.of_apply,centralStepBorderOne,
          Sum.elim_inr,Fin.lastCases_last,hc,Fin.val_last,lt_irrefl,dite_false]
  have hxL : ∀ i,xL i<cut := by
    intro i; apply (hR _).mpr
    have := i.2
    simp only [eR,Equiv.trans_apply,finSumFinEquiv_apply_left,finCongr_apply,Fin.coe_cast,
      Fin.coe_castAdd]
    omega
  have hxH : ∀ i,cut≤xH i := by
    intro i; apply le_of_not_gt; intro hc
    have := (hR _).mp hc
    simp only [eR,Equiv.trans_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.coe_cast,
      Fin.coe_natAdd] at this
    omega
  have hyH : ∀ i,cut≤yH i := by
    intro i; apply le_of_not_gt; intro hc
    have := (hC _).mp hc
    change h+(i:ℕ)<h at this
    omega
  have hyL : ∀ i,yL i<cut := by
    intro i; apply (hC _).mpr
    exact i.2
  have hinjR : Function.Injective (fun a => (xL a:K)) := fun a b hab =>
    Sum.inl_injective (eR.injective (hri hab))
  have hinjH : Function.Injective (fun a => (xH a:K)) := fun a b hab =>
    Sum.inr_injective (eR.injective (hri hab))
  have hinjyH : Function.Injective (fun a => (yH a:K)) := by
    intro a b hab
    have := congrArg Fin.val (hci hab)
    exact Fin.ext (by simp only at this; omega)
  have hinjyL : Function.Injective (fun a => (yL a:K)) := by
    intro a b hab
    have := congrArg Fin.val (hci hab)
    exact Fin.ext this
  constructor
  · rw [← submatrix_det_ne_iff _ eR eC,hM]
    exact centralStepBorderOne_det_ne cut xL yH xH yL hxL hyH hxH hyL hinjR hinjyH hinjH hinjyL
      (fun i j => hrc _ _) (fun i j => hrc _ _)
  · intro w hw
    have hv := centralStepBorderOne_direction (K:=K) cut xL yH xH yL hxL hyH hxH hyL hinjH hinjyL
      (fun i j => hrc _ _) (w ∘ eC) (by
        rw [← hM,Matrix.submatrix_mulVec_equiv]
        have hw2 : (w ∘ eC) ∘ eC.symm=w := by funext x; simp
        rw [hw2,hw]
        funext i
        simp only [Function.comp_apply]
        rw [heR])
    have hc : eC (Sum.inr (Fin.last h))=Fin.last n := by
      simp only [eC,Equiv.ofBijective_apply,fC,Sum.elim_inr,Fin.val_last,lt_irrefl,if_false]
    simpa only [Function.comp_apply,hc] using hv

end StepFibre

section ProfileStep
variable {K : Type*} [Field K]

/-- Highest-degree quotient nodes of an actual surplus fibre: balanced
rows `κ+2c+η`, then the zone `κ+2n`; balanced columns `κ+2c+1-η`. -/
def profileRowQ (κ η n : ℕ) (i : Fin (n+1)) : ℕ := if (i:ℕ)<n then κ+2*(i:ℕ)+η else κ+2*n
def profileColQ (κ η n : ℕ) (c : Fin n) : ℕ := κ+2*(c:ℕ)+(1-η)

theorem profile_nodes_distinct (κ η n : ℕ) (hη : η≤1)
    (hK : ∀ a b : ℕ,a≤κ+2*n → b≤κ+2*n → (a:K)=(b:K) → a=b) :
    Function.Injective (fun i => (profileRowQ κ η n i:K)) ∧
      Function.Injective (fun c => (profileColQ κ η n c:K)) ∧
      ∀ i c,(profileRowQ κ η n i:K)≠(profileColQ κ η n c:K) := by
  have hr (i : Fin (n+1)) : profileRowQ κ η n i≤κ+2*n := by
    have := i.2; unfold profileRowQ; split_ifs <;> omega
  have hc (c : Fin n) : profileColQ κ η n c≤κ+2*n := by
    have := c.2; unfold profileColQ; omega
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    have he := hK _ _ (hr i) (hr j) hij
    have := i.2; have := j.2
    unfold profileRowQ at he
    apply Fin.ext
    split_ifs at he <;> omega
  · intro i j hij
    have he := hK _ _ (hc i) (hc j) hij
    have := i.2; have := j.2
    unfold profileColQ at he
    exact Fin.ext (by omega)
  · intro i c hic
    have he := hK _ _ (hr i) (hc c) hic
    have := i.2; have := c.2
    unfold profileRowQ profileColQ at he
    split_ifs at he <;> omega

/-- Column scaling: the constant direction column is never scaled. -/
noncomputable def scaledStep (g : K) (cut : ℕ) {n : ℕ} (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.of fun i j => if h : (j:ℕ)<n then g*stepEntry (K:=K) cut (rowQ i) (colQ ⟨j,h⟩) else 1

/-- The same system with the normalized central load in the direction column. -/
noncomputable def scaledStepLoad (g : K) (cut : ℕ) {n : ℕ} (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Matrix.of fun i j => if h : (j:ℕ)<n then g*stepEntry (K:=K) cut (rowQ i) (colQ ⟨j,h⟩)
    else g*stepValue (K:=K) cut (rowQ i)

theorem scaledStep_det (g : K) (cut : ℕ) {n : ℕ} (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ) :
    (scaledStep g cut rowQ colQ).det=g^n*(stepBordered (K:=K) cut rowQ colQ).det := by
  have he : scaledStep g cut rowQ colQ=Matrix.of fun i j =>
      (fun j:Fin (n+1) => if (j:ℕ)<n then g else 1) j*stepBordered (K:=K) cut rowQ colQ i j := by
    ext i j
    simp only [scaledStep,stepBordered,Matrix.of_apply]
    split_ifs <;> simp
  rw [he,Matrix.det_mul_row]
  congr 1
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.coe_castSucc,Fin.is_lt,if_true,Fin.val_last,lt_irrefl,if_false,mul_one,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem scaledStepLoad_det (g : K) (cut : ℕ) {n : ℕ} (rowQ : Fin (n+1) → ℕ) (colQ : Fin n → ℕ) :
    (scaledStepLoad g cut rowQ colQ).det=g^(n+1)*((stepBordered (K:=K) cut rowQ colQ).updateCol
      (Fin.last n) (fun i => stepValue (K:=K) cut (rowQ i))).det := by
  have he : scaledStepLoad g cut rowQ colQ=Matrix.of fun i j =>
      (fun _:Fin (n+1) => g) j*((stepBordered (K:=K) cut rowQ colQ).updateCol
        (Fin.last n) (fun i => stepValue (K:=K) cut (rowQ i))) i j := by
    ext i j
    simp only [scaledStepLoad,stepBordered,Matrix.of_apply,Matrix.updateCol_apply]
    by_cases hj : (j:ℕ)<n
    · have hne : j≠Fin.last n := fun h => by rw [h,Fin.val_last] at hj; omega
      simp only [dif_pos hj,if_neg hne]
    · have heq : j=Fin.last n := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
      simp only [dif_neg hj,if_pos heq]
  rw [he,Matrix.det_mul_row]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Cramer's rule at the direction coordinate. -/
theorem cramer_direction {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m K) (hA : A.det≠0) (b : m → K) (j : m) (d : K)
    (hd : ∀ w,A *ᵥ w=b → w j=d) : (A.updateCol j b).det=d*A.det := by
  let w := A.det⁻¹ • Matrix.cramer A b
  have hw : A *ᵥ w=b := by
    simp only [w,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hA,one_smul]
  have h1 := hd w hw
  simp only [w,Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply] at h1
  rw [← h1]
  field_simp

/-- Two adjacent actual central tests with the same balanced count and
the same nonzero central weight give different directions; the cleared
cross product is therefore nonzero. -/
theorem scaled_cross_ne (g : K) (hg : g≠0) (n cut1 cut2 : ℕ)
    (r1 r2 : Fin (n+1) → ℕ) (c1 c2 : Fin n → ℕ) (d1 d2 : K) (hd : d1≠d2)
    (hE1 : (stepBordered (K:=K) cut1 r1 c1).det≠0) (hE2 : (stepBordered (K:=K) cut2 r2 c2).det≠0)
    (hD1 : ∀ w,stepBordered (K:=K) cut1 r1 c1 *ᵥ w=(fun i => stepValue (K:=K) cut1 (r1 i)) →
      w (Fin.last n)=d1)
    (hD2 : ∀ w,stepBordered (K:=K) cut2 r2 c2 *ᵥ w=(fun i => stepValue (K:=K) cut2 (r2 i)) →
      w (Fin.last n)=d2) :
    (scaledStepLoad g cut1 r1 c1).det*(scaledStep g cut2 r2 c2).det≠
      (scaledStepLoad g cut2 r2 c2).det*(scaledStep g cut1 r1 c1).det := by
  rw [scaledStepLoad_det,scaledStepLoad_det,scaledStep_det,scaledStep_det,
    cramer_direction _ hE1 _ _ d1 hD1,cramer_direction _ hE2 _ _ d2 hD2]
  intro he
  have hz : g^(2*n+1)*(stepBordered (K:=K) cut1 r1 c1).det*
      (stepBordered (K:=K) cut2 r2 c2).det*(d1-d2)=0 := by
    linear_combination he
  rcases mul_eq_zero.mp hz with h|h
  · rcases mul_eq_zero.mp h with h|h
    · rcases mul_eq_zero.mp h with h|h
      · exact hg (pow_eq_zero_iff (by omega) |>.mp h)
      · exact hE1 h
    · exact hE2 h
  · exact hd (sub_eq_zero.mp h)

/-- Lower adjacent fibre (`n+1` low nodes): direction zero. -/
theorem profile_lower (κ η n : ℕ) (hη : η≤1) (hn : 1≤n)
    (hK : ∀ a b : ℕ,a≤κ+2*n → b≤κ+2*n → (a:K)=(b:K) → a=b) :
    (stepBordered (K:=K) (κ+n+1) (profileRowQ κ η n) (profileColQ κ η n)).det≠0 ∧
      ∀ w,stepBordered (K:=K) (κ+n+1) (profileRowQ κ η n) (profileColQ κ η n) *ᵥ w=
        (fun i => stepValue (K:=K) (κ+n+1) (profileRowQ κ η n i)) → w (Fin.last n)=0 := by
  obtain ⟨hri,hci,hrc⟩ := profile_nodes_distinct (K:=K) κ η n hη hK
  apply stepBordered_zero (κ+n+1) n ((n-η)/2+1) (n-(n-η)/2) _ _ _ _ (by omega) (by omega)
    hri hci hrc
  · intro i
    have := i.2
    unfold profileRowQ
    split_ifs <;> omega
  · intro c
    have := c.2
    unfold profileColQ
    omega

/-- Upper adjacent fibre (`n` low nodes): direction one. -/
theorem profile_upper (κ η n : ℕ) (hη : η≤1) (hn : 1≤n)
    (hK : ∀ a b : ℕ,a≤κ+2*n → b≤κ+2*n → (a:K)=(b:K) → a=b) :
    (stepBordered (K:=K) (κ+n) (profileRowQ κ η n) (profileColQ κ η n)).det≠0 ∧
      ∀ w,stepBordered (K:=K) (κ+n) (profileRowQ κ η n) (profileColQ κ η n) *ᵥ w=
        (fun i => stepValue (K:=K) (κ+n) (profileRowQ κ η n i)) → w (Fin.last n)=1 := by
  obtain ⟨hri,hci,hrc⟩ := profile_nodes_distinct (K:=K) κ η n hη hK
  apply stepBordered_one (κ+n) n ((n+1-η)/2) (n-(n+1-η)/2) _ _ _ _ (by omega) hri hci hrc
  · intro i
    have := i.2
    unfold profileRowQ
    split_ifs <;> omega
  · intro c
    have := c.2
    unfold profileColQ
    omega

end ProfileStep


section SpectralOuter
variable {K : Type*} [Field K]

/-- Constants and the two pole parameters, in the ORIGINAL embedding order. -/
noncomputable def poleCoefficients : K[X][X] →+* K[X][X][X] :=
  Polynomial.eval₂RingHom (R:=K[X]) (S:=K[X][X][X])
    (Polynomial.eval₂RingHom (R:=K) (S:=K[X][X][X])
      ((Polynomial.C:K[X][X] →+* K[X][X][X]).comp
        ((Polynomial.C:K[X] →+* K[X][X]).comp (Polynomial.C:K →+* K[X])))
      (Polynomial.C (Polynomial.X:K[X][X])))
    (Polynomial.X:K[X][X][X])

/-- Return a spectral-OUTER cleared polynomial to the original variable
order: spectral innermost, fractional middle, integer outermost. -/
noncomputable def spectralFirst : K[X][X][X] →+* K[X][X][X] :=
  Polynomial.eval₂RingHom (R:=K[X][X]) (S:=K[X][X][X]) (poleCoefficients (K:=K))
    (Polynomial.C (Polynomial.C (Polynomial.X:K[X])))


/-- Faithful embedding of spectral-outer cleared polynomials in the actual
two-parameter residue field: outer variable = original spectral `U`. -/
noncomputable def embedU : K[X][X][X] →+* RatFunc (RatFunc (RatFunc K)) :=
  (embedThree (K:=K)).comp (spectralFirst (K:=K))


end SpectralOuter


section ClearedWorld
variable (p : ℕ) [Fact p.Prime]


/-- The two ORIGINAL pole parameters and the constants, as cleared
polynomials with the integer parameter outermost. -/
noncomputable def bconst (k : ZMod p) : (ZMod p)[X][X] := Polynomial.C (Polynomial.C k)
noncomputable def bInt : (ZMod p)[X][X] := Polynomial.X
noncomputable def bFrac : (ZMod p)[X][X] := Polynomial.C Polynomial.X

noncomputable def embedB : (ZMod p)[X][X] →+* TwoTermDeformation.Residue p :=
  (embedU (K:=ZMod p)).comp Polynomial.C


variable (q o : ℕ)

/-- The elementary ORIGINAL pole denominator at node `t`, or one. -/
noncomputable def dfac (t : ℕ) : (ZMod p)[X][X] :=
  if p∣t then bconst p ((t/p:ℕ):ZMod p)+bInt p
  else if p∣q*t-o then bconst p (((q*t-o)/p:ℕ):ZMod p)+bconst p (q:ZMod p)*bFrac p else 1

noncomputable def clearing (M : ℕ) : (ZMod p)[X][X] := ∏ t∈Icc 1 M,dfac p q o t
noncomputable def cofactor (M t : ℕ) : (ZMod p)[X][X] := ∏ t'∈(Icc 1 M).erase t,dfac p q o t'

noncomputable def deltaWeight (t : ℕ) : (ZMod p)[X][X] :=
  if p∣t then 1 else if p∣q*t-o then -bconst p (q:ZMod p) else 0
noncomputable def squareWeight (t : ℕ) : (ZMod p)[X][X] :=
  if p∣t then 1 else if p∣q*t-o then -bconst p ((q:ZMod p)^2) else 0

noncomputable def clearedDelta (M t : ℕ) : (ZMod p)[X][X] := deltaWeight p q o t*cofactor p q o M t
noncomputable def clearedLoad (M a : ℕ) : (ZMod p)[X][X] := ∑ t∈Icc 1 a,clearedDelta p q o M t
noncomputable def clearedSquare (M t : ℕ) : (ZMod p)[X][X] := squareWeight p q o t*cofactor p q o M t^2

theorem not_both (t : ℕ) (hq : q<p) (ho0 : 0<o) (hoq : o<q) (hle : o≤q*t) (hd : p∣t) : ¬p∣q*t-o := by
  intro hf
  have h1 : p∣q*t := Dvd.dvd.mul_left hd q
  have h2 : p∣o := by
    have := Nat.dvd_sub h1 hf
    rwa [Nat.sub_sub_self hle] at this
  have := Nat.le_of_dvd ho0 h2
  omega


theorem cofactor_mul (M t : ℕ) (ht : t∈Icc 1 M) :
    cofactor p q o M t*dfac p q o t=clearing p q o M := by
  unfold cofactor clearing
  exact Finset.prod_erase_mul _ _ ht


theorem load_terms (M a : ℕ) (haM : a≤M) (hM : M<p*p) (hq0 : 0<q) (hoq : o<q) (t : ℕ)
    (ht : t∈Icc 1 a) : t∈Icc 1 M ∧ o≤q*t ∧ ¬p^2∣t := by
  have h := mem_Icc.mp ht
  refine ⟨mem_Icc.mpr ⟨h.1,h.2.trans haM⟩,?_,Smith.not_sq_dvd_of_lt (by omega) (by omega)⟩
  have := Nat.le_mul_of_pos_right q h.1
  omega


theorem nat_cast_eq_of_lt (a b : ℕ) (ha : a<p) (hb : b<p) (h : (a:ZMod p)=(b:ZMod p)) : a=b := by
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at this


section Evaluated
variable {L : Type*} [Field L] (ev : (ZMod p)[X][X] →+* L) (M ts : ℕ)
variable (htsM : ts∈Icc 1 M) (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
include htsM hz

theorem ev_cofactor_other (t : ℕ) (ht : t≠ts) : ev (cofactor p q o M t)=0 := by
  unfold cofactor
  rw [map_prod]
  apply Finset.prod_eq_zero (i:=ts) (Finset.mem_erase.mpr ⟨fun h => ht h.symm,htsM⟩)
  exact (hz ts htsM).mpr rfl

theorem ev_cofactor_self : ev (cofactor p q o M ts)≠0 := by
  unfold cofactor
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  have h := Finset.mem_erase.mp ht
  intro h0
  exact h.1 ((hz t h.2).mp h0)

/-- Only the central original pole survives in a cleared cumulative load. -/
theorem ev_clearedLoad (a : ℕ) :
    ev (clearedLoad p q o M a)=
      if ts≤a then ev (deltaWeight p q o ts)*ev (cofactor p q o M ts) else 0 := by
  classical
  unfold clearedLoad clearedDelta
  rw [map_sum]
  have he : ∀ t∈Icc 1 a,ev (deltaWeight p q o t*cofactor p q o M t)=
      if t=ts then ev (deltaWeight p q o ts)*ev (cofactor p q o M ts) else 0 := by
    intro t _
    by_cases h : t=ts
    · subst h; rw [if_pos rfl,map_mul]
    · rw [if_neg h,map_mul,ev_cofactor_other p q o ev M ts htsM hz t h,mul_zero]
  rw [Finset.sum_congr rfl he,Finset.sum_ite_eq']
  have h1 := (mem_Icc.mp htsM).1
  by_cases ha : ts≤a
  · rw [if_pos (mem_Icc.mpr ⟨h1,ha⟩),if_pos ha]
  · rw [if_neg (fun h => ha (mem_Icc.mp h).2),if_neg ha]

end Evaluated

/-- Cleared off-diagonal entry at ORIGINAL nodes `a`,`b` of one colour:
the residue times the clearing factor. Quotients are the original node
quotients. -/
noncomputable def clearedEntry (M : ℕ) (u0 : ZMod p) (a b : ℕ) : (ZMod p)[X][X] :=
  bconst p (u0/(((b/p:ℕ):ZMod p)-((a/p:ℕ):ZMod p)))*(clearedLoad p q o M b-clearedLoad p q o M a)

noncomputable def clearedLoadRow (M : ℕ) (u0 : ZMod p) (a : ℕ) : (ZMod p)[X][X] :=
  bconst p u0*clearedLoad p q o M a

/-- Central evaluation of cleared entries is the actual central step
system, scaled by one nonzero common factor. -/
theorem ev_clearedEntry {L : Type*} [Field L] [Algebra (ZMod p) L] (ev : (ZMod p)[X][X] →+* L) (M ts : ℕ)
    (htsM : ts∈Icc 1 M) (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,ev (bconst p k)=algebraMap (ZMod p) L k) (u0 : ZMod p) (cut a b : ℕ)
    (hab : ((b/p:ℕ):L)≠((a/p:ℕ):L))
    (ha : ts≤a ↔ cut≤a/p) (hb : ts≤b ↔ cut≤b/p) :
    ev (clearedEntry p q o M u0 a b)=
      (algebraMap (ZMod p) L u0*ev (deltaWeight p q o ts)*ev (cofactor p q o M ts))*
        stepEntry (K:=L) cut (a/p) (b/p) := by
  unfold clearedEntry stepEntry stepValue
  rw [map_mul,map_sub,ev_clearedLoad p q o ev M ts htsM hz,ev_clearedLoad p q o ev M ts htsM hz,hev]
  simp only [map_div₀,map_sub,map_natCast]
  have hd : ((b/p:ℕ):L)-((a/p:ℕ):L)≠0 := sub_ne_zero.mpr hab
  by_cases h1 : ts≤a <;> by_cases h2 : ts≤b
  · rw [if_pos h1,if_pos h2,if_neg (not_lt.mpr (ha.mp h1)),if_neg (not_lt.mpr (hb.mp h2))]
    simp
  · rw [if_pos h1,if_neg h2,if_neg (not_lt.mpr (ha.mp h1)),if_pos (not_le.mp (fun h => h2 (hb.mpr h)))]
    field_simp
    ring
  · rw [if_neg h1,if_pos h2,if_pos (not_le.mp (fun h => h1 (ha.mpr h))),if_neg (not_lt.mpr (hb.mp h2))]
    field_simp
    ring
  · rw [if_neg h1,if_neg h2,if_pos (not_le.mp (fun h => h1 (ha.mpr h))),
      if_pos (not_le.mp (fun h => h2 (hb.mpr h)))]
    simp

theorem ev_clearedLoadRow {L : Type*} [Field L] [Algebra (ZMod p) L] (ev : (ZMod p)[X][X] →+* L) (M ts : ℕ)
    (htsM : ts∈Icc 1 M) (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,ev (bconst p k)=algebraMap (ZMod p) L k) (u0 : ZMod p) (cut a : ℕ)
    (ha : ts≤a ↔ cut≤a/p) :
    ev (clearedLoadRow p q o M u0 a)=
      (algebraMap (ZMod p) L u0*ev (deltaWeight p q o ts)*ev (cofactor p q o M ts))*
        stepValue (K:=L) cut (a/p) := by
  unfold clearedLoadRow stepValue
  rw [map_mul,ev_clearedLoad p q o ev M ts htsM hz,hev]
  by_cases h1 : ts≤a
  · rw [if_pos h1,if_neg (not_lt.mpr (ha.mp h1))]; ring
  · rw [if_neg h1,if_pos (not_le.mp (fun h => h1 (ha.mpr h)))]; ring

theorem rational_inv_mul_cancel {S : Type*} [CommRing S] [IsDomain S] (a : RatFunc S) (ha : a≠0) :
    a⁻¹*a=1 := inv_mul_cancel₀ ha


noncomputable def clearedDiag (M : ℕ) (u0 : ZMod p) (a : ℕ) : (ZMod p)[X][X] :=
  -(bconst p u0*∑ t∈Icc 1 a,clearedSquare p q o M t)


end ClearedWorld

section SpectralDomain
variable {R : Type*} [CommRing R] [IsDomain R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

noncomputable def spectralSystem (c : R) (A : Matrix ι ι R) (B : Matrix ι κ R)
    (E : Matrix κ ι R) (D : Matrix κ κ R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R[X] :=
  Matrix.fromBlocks ((X*Polynomial.C c) • (1:Matrix ι ι R[X])+A.map Polynomial.C)
    (B.map Polynomial.C) (E.map Polynomial.C) (D.map Polynomial.C)

/-- Highest original spectral coefficient over any integral domain of
cleared coefficients. -/
theorem spectral_top_domain (c : R) (A : Matrix ι ι R) (B : Matrix ι κ R)
    (E : Matrix κ ι R) (D : Matrix κ κ R) :
    (spectralSystem c A B E D).det.natDegree≤Fintype.card ι ∧
      (spectralSystem c A B E D).det.coeff (Fintype.card ι)=c^Fintype.card ι*D.det := by
  classical
  let F := FractionRing R
  let f : R →+* F := algebraMap R F
  have hf : Function.Injective f := IsFractionRing.injective R F
  have hm : (spectralSystem c A B E D).map (Polynomial.mapRingHom f)=
      spectralBlocks (f c) (A.map f) (B.map f) (E.map f) (D.map f) := by
    ext i j
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j
      · subst hij; simp [spectralSystem,spectralBlocks,Matrix.one_apply]
      · simp [spectralSystem,spectralBlocks,Matrix.one_apply,hij]
    · simp [spectralSystem,spectralBlocks]
    · simp [spectralSystem,spectralBlocks]
    · simp [spectralSystem,spectralBlocks]
  have hdet : Polynomial.map f (spectralSystem c A B E D).det=
      (spectralBlocks (f c) (A.map f) (B.map f) (E.map f) (D.map f)).det := by
    rw [← hm]
    change (Polynomial.mapRingHom f) _=_
    rw [RingHom.map_det]
    rfl
  obtain ⟨h1,h2⟩ := spectral_top (f c) (A.map f) (B.map f) (E.map f) (D.map f)
  rw [← hdet] at h1 h2
  refine ⟨?_,?_⟩
  · rwa [Polynomial.natDegree_map_eq_of_injective hf] at h1
  · rw [Polynomial.coeff_map] at h2
    apply hf
    rw [h2,map_mul,map_pow]
    congr 1
    exact (RingHom.map_det f D).symm

/-- Distinct highest spectral cross coefficients separate two cleared
directions. -/
theorem cross_ne_of_top (a b : ℕ) (Nv Dv N0 D0 : R[X])
    (hNv : Nv.natDegree≤a) (hDv : Dv.natDegree≤a) (hN0 : N0.natDegree≤b) (hD0 : D0.natDegree≤b)
    (h : Nv.coeff a*D0.coeff b≠N0.coeff b*Dv.coeff a) : Nv*D0≠N0*Dv := by
  intro he
  apply h
  have h1 := Polynomial.coeff_mul_add_eq_of_natDegree_le hNv hD0
  rw [he,mul_comm N0,Polynomial.coeff_mul_add_eq_of_natDegree_le hDv hN0] at h1
  rw [← h1]
  ring

end SpectralDomain


section FibreSystem
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)


/-- Determinants commute with evaluation of a cleared spectral polynomial
system; stated generically so no concrete instance unfolding is needed. -/
theorem eval₂_det {B K m : Type*} [CommRing B] [CommRing K] [Fintype m] [DecidableEq m]
    (ι : B →+* K) (U : K) (C : Matrix m m B[X]) :
    Polynomial.eval₂RingHom ι U C.det=(C.map (Polynomial.eval₂RingHom ι U)).det :=
  RingHom.map_det _ _

variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)

/-- Bordered row nodes of an actual fibre: balanced rows, then the zone. -/
def bordRow (i : Fin (n+1)) : ℕ := if h : (i:ℕ)<n then xr ⟨i,h⟩ else z


noncomputable def clearedA (M : ℕ) (u0 : ZMod p) : Matrix (Fin k) (Fin k) (ZMod p)[X][X] :=
  Matrix.of fun i j => if i=j then clearedDiag p q o M u0 (cn i)
    else clearing p q o M*clearedEntry p q o M u0 (cn i) (cn j)

noncomputable def clearedB (M : ℕ) (u0 : ZMod p) (load : Bool) : Matrix (Fin k) (Fin (n+1)) (ZMod p)[X][X] :=
  Matrix.of fun i j => if h : (j:ℕ)<n then clearing p q o M*clearedEntry p q o M u0 (cn i) (yc ⟨j,h⟩)
    else if load then clearing p q o M*clearedLoadRow p q o M u0 (cn i) else clearing p q o M

noncomputable def clearedE (M : ℕ) (u0 : ZMod p) : Matrix (Fin (n+1)) (Fin k) (ZMod p)[X][X] :=
  Matrix.of fun i j => clearedEntry p q o M u0 (bordRow xr z i) (cn j)

noncomputable def clearedD (M : ℕ) (u0 : ZMod p) (load : Bool) : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)[X][X] :=
  Matrix.of fun i j => if h : (j:ℕ)<n then clearedEntry p q o M u0 (bordRow xr z i) (yc ⟨j,h⟩)
    else if load then clearedLoadRow p q o M u0 (bordRow xr z i) else 1

noncomputable def clearedSystem (M : ℕ) (u0 : ZMod p) (load : Bool) :=
  spectralSystem (clearing p q o M^2) (clearedA p q o cn M u0) (clearedB p q o cn yc M u0 load)
    (clearedE p q o cn xr z M u0) (clearedD p q o xr yc z M u0 load)

/-- Arithmetic hypotheses of one actual fibre: one colour, original
bounds, and distinct original quotients at every off-diagonal pair. -/
structure FibreHyp (M : ℕ) where
  hM : q*M<p*p
  hq0 : 0<q
  hqp : q<p
  ho0 : 0<o
  hoq : o<q
  hcn : ∀ i,cn i≤M
  hxr : ∀ c,xr c≤M
  hyc : ∀ c,yc c≤M
  hz : z≤M
  colour : ZMod p
  ccn : ∀ i,(cn i:ZMod p)=colour
  cxr : ∀ c,(xr c:ZMod p)=colour
  cyc : ∀ c,(yc c:ZMod p)=colour
  cz : (z:ZMod p)=colour
  qcc : ∀ i j,i≠j → ((cn j/p:ℕ):ZMod p)≠((cn i/p:ℕ):ZMod p)
  qcb : ∀ i c,((yc c/p:ℕ):ZMod p)≠((cn i/p:ℕ):ZMod p)
  qbc : ∀ i j,((cn j/p:ℕ):ZMod p)≠((bordRow xr z i/p:ℕ):ZMod p)
  qbb : ∀ i c,((yc c/p:ℕ):ZMod p)≠((bordRow xr z i/p:ℕ):ZMod p)

variable {p q o cn xr yc z}

theorem FibreHyp.bord_le {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (i : Fin (n+1)) : bordRow xr z i≤M := by
  unfold bordRow; split_ifs; exacts [H.hxr _,H.hz]

theorem FibreHyp.bord_colour {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (i : Fin (n+1)) :
    (bordRow xr z i:ZMod p)=H.colour := by
  unfold bordRow; split_ifs; exacts [H.cxr _,H.cz]


theorem det_scaled {R m : Type*} [CommRing R] [Fintype m] [DecidableEq m] (r c : m → R) (A : Matrix m m R) :
    (Matrix.of fun i j => r i*A i j*c j).det=(∏ i,r i)*(∏ j,c j)*A.det := by
  have h1 : (Matrix.of fun i j => r i*A i j*c j)=Matrix.of fun i j => c j*(Matrix.of fun i j => r i*A i j) i j := by
    ext i j; simp only [Matrix.of_apply]; ring
  rw [h1,Matrix.det_mul_row,Matrix.det_mul_column]
  ring


/-- Central evaluation of the cleared bordered block is the actual
central step system with one common nonzero factor. -/
theorem ev_clearedD {L : Type*} [Field L] [Algebra (ZMod p) L] (ev : (ZMod p)[X][X] →+* L) (M ts : ℕ)
    (htsM : ts∈Icc 1 M) (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,ev (bconst p k)=algebraMap (ZMod p) L k) (u0 : ZMod p) (cut : ℕ)
    (hrow : ∀ i,ts≤bordRow xr z i ↔ cut≤bordRow xr z i/p)
    (hcolc : ∀ c,ts≤yc c ↔ cut≤yc c/p)
    (hq : ∀ i c,((yc c/p:ℕ):L)≠((bordRow xr z i/p:ℕ):L)) (load : Bool) :
    (clearedD p q o xr yc z M u0 load).map ev=
      (if load then scaledStepLoad else scaledStep)
        (algebraMap (ZMod p) L u0*ev (deltaWeight p q o ts)*ev (cofactor p q o M ts)) cut
        (fun i => bordRow xr z i/p) (fun c => yc c/p) := by
  ext i j
  simp only [Matrix.map_apply,clearedD,Matrix.of_apply]
  by_cases hj : (j:ℕ)<n
  · cases load <;>
    · simp only [dif_pos hj,Bool.false_eq_true,↓reduceIte,scaledStep,scaledStepLoad,Matrix.of_apply]
      exact ev_clearedEntry p q o ev M ts htsM hz hev u0 cut _ _ (hq i _) (hrow i) (hcolc _)
  · cases load
    · simp only [dif_neg hj,Bool.false_eq_true,↓reduceIte,scaledStep,Matrix.of_apply,map_one]
    · simp only [dif_neg hj,↓reduceIte,scaledStepLoad,Matrix.of_apply]
      exact ev_clearedLoadRow p q o ev M ts htsM hz hev u0 cut _ (hrow i)

end FibreSystem


section ProfileSeparation
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)


/-- The common nonzero central factor of the evaluated cleared systems. -/
noncomputable def centralWeight (ev : (ZMod p)[X][X] →+* RatFunc (ZMod p)) (u0 : ZMod p) (M ts : ℕ) :
    RatFunc (ZMod p) :=
  algebraMap (ZMod p) (RatFunc (ZMod p)) u0*ev (deltaWeight p q o ts)*ev (cofactor p q o M ts)


/-- Actual fibre nodes of colour `γ`: `k` original common nodes, `n`
balanced pairs with bit `η`, and the zone at quotient `k+2n`. -/
def pcn (γ k : ℕ) (i : Fin k) : ℕ := γ+(i:ℕ)*p
def pxr (γ k η n : ℕ) (c : Fin n) : ℕ := γ+(k+2*(c:ℕ)+η)*p
def pyc (γ k η n : ℕ) (c : Fin n) : ℕ := γ+(k+2*(c:ℕ)+(1-η))*p
def pz (γ k n : ℕ) : ℕ := γ+(k+2*n)*p

theorem node_quot (γ j : ℕ) (hγ : γ<p) : (γ+j*p)/p=j := by
  have hp := (Fact.out:p.Prime).pos
  rw [Nat.add_mul_div_right _ _ hp,Nat.div_eq_of_lt hγ,zero_add]

theorem bord_quot (γ k η n : ℕ) (hγ : γ<p) (i : Fin (n+1)) :
    bordRow (pxr p γ k η n) (pz p γ k n) i/p=profileRowQ k η n i := by
  unfold bordRow profileRowQ pxr pz
  split_ifs <;> exact node_quot p _ _ hγ

theorem col_quot (γ k η n : ℕ) (hγ : γ<p) (c : Fin n) :
    pyc p γ k η n c/p=profileColQ k η n c := by
  unfold pyc profileColQ
  exact node_quot p _ _ hγ

theorem bord_node (γ k η n : ℕ) (i : Fin (n+1)) :
    bordRow (pxr p γ k η n) (pz p γ k n) i=γ+profileRowQ k η n i*p := by
  unfold bordRow profileRowQ pxr pz
  split_ifs <;> rfl

theorem zmod_cast_ne (a b : ℕ) (ha : a<p) (hb : b<p) (hab : a≠b) : (a:ZMod p)≠(b:ZMod p) :=
  fun h => hab (nat_cast_eq_of_lt p a b ha hb h)

/-- The actual profile satisfies every fibre arithmetic hypothesis. -/
def profileHyp (γ k η n M : ℕ) (hγ : γ<p) (hη : η≤1) (hkn : k+2*n<p)
    (hzM : pz p γ k n≤M) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q) :
    FibreHyp p q o (pcn p γ k) (pxr p γ k η n) (pyc p γ k η n) (pz p γ k n) M where
  hM := hM
  hq0 := hq0
  hqp := hqp
  ho0 := ho0
  hoq := hoq
  hcn := fun i => by
    unfold pcn; unfold pz at hzM
    have := i.2
    nlinarith
  hxr := fun c => by
    unfold pxr; unfold pz at hzM
    have := c.2
    nlinarith
  hyc := fun c => by
    unfold pyc; unfold pz at hzM
    have := c.2
    have : 1-η≤1 := by omega
    nlinarith
  hz := hzM
  colour := (γ:ZMod p)
  ccn := fun i => by simp [pcn]
  cxr := fun c => by simp [pxr]
  cyc := fun c => by simp [pyc]
  cz := by simp [pz]
  qcc := fun i j hij => by
    rw [pcn,pcn,node_quot p _ _ hγ,node_quot p _ _ hγ]
    exact zmod_cast_ne p _ _ (by have := j.2; omega) (by have := i.2; omega)
      (fun h => hij (Fin.ext h.symm))
  qcb := fun i c => by
    rw [col_quot p _ _ _ _ hγ,pcn,node_quot p _ _ hγ]
    unfold profileColQ
    exact zmod_cast_ne p _ _ (by have := c.2; omega) (by have := i.2; omega)
      (by have := i.2; omega)
  qbc := fun i j => by
    rw [bord_quot p _ _ _ _ hγ,pcn,node_quot p _ _ hγ]
    unfold profileRowQ
    have := j.2; have := i.2
    split_ifs <;> exact zmod_cast_ne p _ _ (by omega) (by omega) (by omega)
  qbb := fun i c => by
    rw [bord_quot p _ _ _ _ hγ,col_quot p _ _ _ _ hγ]
    unfold profileRowQ profileColQ
    have := c.2; have := i.2
    split_ifs <;> exact zmod_cast_ne p _ _ (by omega) (by omega) (by omega)

theorem rat_cast_ne (a b : ℕ) (ha : a<p) (hb : b<p) (hab : a≠b) :
    (a:RatFunc (ZMod p))≠(b:RatFunc (ZMod p)) := by
  intro h
  apply zmod_cast_ne p a b ha hb hab
  apply (algebraMap (ZMod p) (RatFunc (ZMod p))).injective
  simpa only [map_natCast] using h

theorem central_cut (γ c ts j : ℕ) (hc : 1≤c) (h1 : γ+(c-1)*p<ts) (h2 : ts≤γ+c*p) :
    ts≤γ+j*p ↔ c≤j := by
  constructor
  · intro h
    by_contra hj
    have : j*p≤(c-1)*p := Nat.mul_le_mul_right p (by omega)
    omega
  · intro h
    have : c*p≤j*p := Nat.mul_le_mul_right p h
    omega

theorem rat_cast_inj (B : ℕ) (hB : B<p) (a b : ℕ) (ha : a≤B) (hb : b≤B)
    (h : (a:RatFunc (ZMod p))=(b:RatFunc (ZMod p))) : a=b := by
  by_contra hab
  exact rat_cast_ne p a b (by omega) (by omega) hab h


end ProfileSeparation

section FieldFibre
variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] {α : Type*} [Fintype α] [DecidableEq α]

/-- Over the residue field, a colour-block-diagonal response of a border
supported on one colour is computed in that colour block. -/
theorem fibre_response (Q : Matrix α α K) (col : α → ZMod p) (hQ : Q.det≠0)
    (hb : ∀ a b,col a≠col b → Q a b=0) (τ : ZMod p) (σ y : α → K)
    (hs : ∀ a,col a≠τ → σ a=0) :
    σ ⬝ᵥ Q⁻¹ *ᵥ y=(fun i:{a // col a=τ} => σ i.1) ⬝ᵥ (UFMoments.blk Q col τ)⁻¹ *ᵥ (fun i => y i.1) := by
  have he := UFMoments.own_fiber_form Q col (isUnit_iff_ne_zero.mpr hQ) hb τ σ y hs
  rw [Matrix.dotProduct_mulVec,he,Matrix.dotProduct_mulVec]
  rfl

/-- Schur form of a bordered determinant over a field. -/
theorem bordered_det {β : Type*} [Fintype β] [DecidableEq β]
    (P : Matrix β β K) (hP : P.det≠0) (L σ : β → K) (c : K) :
    (Matrix.fromBlocks P (Matrix.of fun i (_:Unit) => L i) (Matrix.of fun (_:Unit) j => σ j)
      (Matrix.of fun (_:Unit) (_:Unit) => c)).det=P.det*(c-σ ⬝ᵥ P⁻¹ *ᵥ L) := by
  letI : Invertible P := Matrix.invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply,Matrix.of_apply,Matrix.mul_apply,Matrix.invOf_eq_nonsing_inv,
    dotProduct,Matrix.mulVec]
  congr 1
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cross-multiplied coupling identity: the residue coupling, times the
nonzero anchor reference and the two fibre determinants, is the cleared
cross product of ORIGINAL bordered determinants. -/
theorem coupling_cross {S : Type*} [CommRing S] [IsDomain S] (detv det0 momv mom0 refv ref0 : RatFunc S) (h0 : ref0≠0) :
    (momv-mom0*ref0⁻¹*refv)*ref0*detv*det0=
      (detv*momv)*(det0*ref0)-(det0*mom0)*(detv*refv) := by
  field_simp

end FieldFibre

section BorderedFibre
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)


/-- Separate the zone row and direction column of a bordered fibre system. -/
noncomputable def bordEquiv (k n : ℕ) : (Fin k ⊕ Fin n) ⊕ Unit ≃ Fin k ⊕ Fin (n+1) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv.symm).trans finSumFinEquiv))

variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)

theorem bordEquiv_inl_inl (i : Fin k) : bordEquiv k n (Sum.inl (Sum.inl i))=Sum.inl i := rfl
theorem bordEquiv_inl_inr (c : Fin n) : bordEquiv k n (Sum.inl (Sum.inr c))=Sum.inr (Fin.castAdd 1 c) := rfl
theorem bordEquiv_inr (w : Unit) : bordEquiv k n (Sum.inr w)=Sum.inr (Fin.last n) := by
  cases w
  simp [bordEquiv,Fin.ext_iff]


end BorderedFibre

section TwoParameterCoupling
variable {p : ℕ} [Fact p.Prime]


theorem residue_response {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]
    (f : R →+* K) (Q : Matrix α α R) (hQ : IsUnit Q.det) (σ y : α → R) :
    f (σ ⬝ᵥ Q⁻¹ *ᵥ y)=(fun i => f (σ i)) ⬝ᵥ (Q.map f)⁻¹ *ᵥ (fun i => f (y i)) := by
  rw [UFMoments.map_inv_of_unit f Q hQ]
  simp only [dotProduct,Matrix.mulVec,map_sum,map_mul,Matrix.map_apply]


variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)


include H in
theorem single_bound : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN

theorem colNode_colour (j : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    ((Sum.elim (fun i:Fin r => (i:ℕ)) H.ys j:ℕ):ZMod p)=H.colour j := by
  cases j with
  | inl j => rfl
  | inr j => exact (H.same_colour j).symm

theorem rowNode_colour (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    ((Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i:ℕ):ZMod p)=H.colour i := by
  cases i <;> rfl


end TwoParameterCoupling

section BorderedResidue

/-- Schur form of the image of a bordered determinant under a ring map to a
field (stated generically: no concrete residue instances are unfolded). -/
theorem map_bordered_det {R K β : Type*} [CommRing R] [Field K] [Fintype β] [DecidableEq β]
    (f : R →+* K) (P : Matrix β β R) (L σ : β → R) (c : R) (hP : (P.map f).det≠0) :
    f (Matrix.fromBlocks P (Matrix.of fun i (_:Unit) => L i) (Matrix.of fun (_:Unit) j => σ j)
      (Matrix.of fun (_:Unit) (_:Unit) => c)).det=
      (P.map f).det*(f c-(fun j => f (σ j)) ⬝ᵥ (P.map f)⁻¹ *ᵥ (fun i => f (L i))) := by
  rw [RingHom.map_det,RingHom.mapMatrix_apply,Matrix.fromBlocks_map]
  have h1 : (Matrix.of fun i (_:Unit) => L i).map f=Matrix.of fun i (_:Unit) => f (L i) := by
    ext i j; rfl
  have h2 : (Matrix.of fun (_:Unit) j => σ j).map f=Matrix.of fun (_:Unit) j => f (σ j) := by
    ext i j; rfl
  have h3 : (Matrix.of fun (_:Unit) (_:Unit) => c).map f=Matrix.of fun (_:Unit) (_:Unit) => f c := by
    ext i j; rfl
  rw [h1,h2,h3]
  exact bordered_det _ hP _ _ _

end BorderedResidue

section BorderedResidueActual
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)


variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)


end BorderedResidueActual

section FibreBinding
variable {p : ℕ} [Fact p.Prime]


variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

include H in
theorem hodd : p%2=1 := by have := H.hp; omega

/-- The actual whole-fibre equivalence, typed by the setup colour. -/
noncomputable def fibreEquiv (γ : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠γ) :
    (Fin (WrapJointProfile.count p r γ.val) ⊕ Fin n) ≃ {a // H.colour a=γ} :=
  WrapJointProfile.wholeEquiv p r n e b d H.hp2 H.er γ hres

theorem fibre_row (γ : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠γ)
    (i : Fin (WrapJointProfile.count p r γ.val) ⊕ Fin n) :
    Sum.elim (fun j:Fin r => (j:ℕ)) H.xs (fibreEquiv H γ hres i).1=
      Sum.elim (fun j:Fin (WrapJointProfile.count p r γ.val) => γ.val+(j:ℕ)*p)
        (fun c:Fin n => WrapJointProfile.rowProfile p r γ.val c) i :=
  WrapJointProfile.whole_row p r n e b d H.hp2 (hodd H) H.er γ hres i

theorem fibre_col (γ : ZMod p)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠γ)
    (i : Fin (WrapJointProfile.count p r γ.val) ⊕ Fin n) :
    Sum.elim (fun j:Fin r => (j:ℕ)) H.ys (fibreEquiv H γ hres i).1=
      Sum.elim (fun j:Fin (WrapJointProfile.count p r γ.val) => γ.val+(j:ℕ)*p)
        (fun c:Fin n => WrapJointProfile.colProfile p r γ.val c) i :=
  WrapJointProfile.whole_col p r n e b d shift H.hp H.hp2 H.er H.ec γ hres i


theorem rowProfile_eq (γ : ℕ) (c : Fin n) :
    WrapJointProfile.rowProfile p r γ c=pxr p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n c := by
  unfold WrapJointProfile.rowProfile WrapJointProfile.lower pxr
  ring

theorem colProfile_eq (γ : ℕ) (c : Fin n) :
    WrapJointProfile.colProfile p r γ c=pyc p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n c := by
  unfold WrapJointProfile.colProfile WrapJointProfile.lower pyc
  ring

end FibreBinding


section RowSeparation
variable {p : ℕ} [Fact p.Prime]


variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)


end RowSeparation


section RowSeparationFinal
variable {p : ℕ} [Fact p.Prime]


theorem rfH_eq (z : ZMod p) : CatalanCore.Uniform.Content.Hybrid.rfH p z=RatFunc.C z := by
  simp [CatalanCore.Uniform.Content.Hybrid.rfH,RatFunc.algebraMap_C]


theorem lower_window (A K n p t k : ℕ) (htip : t=A+(K+2*n)*p) (h1 : t<k) (h2 : k≤t+p) :
    A+((K+n+1)-1)*p<k-n*p ∧ k-n*p≤A+(K+n+1)*p := by
  have e1 : (K+2*n)*p=(K+n)*p+n*p := by ring
  have e2 : (K+n+1)*p=(K+n)*p+p := by ring
  have e3 : K+n+1-1=K+n := by omega
  rw [e3,e2]
  rw [e1] at htip
  omega

theorem upper_window (A K n p t k : ℕ) (hn : 1≤n) (htip : t=A+(K+2*n)*p) (h1 : t<k+p) (h2 : k≤t)
    (hk : n*p≤k) :
    A+((K+n)-1)*p<k-n*p ∧ k-n*p≤A+(K+n)*p := by
  obtain ⟨m,hm⟩ : ∃ m,K+n=m+1 := ⟨K+n-1,by omega⟩
  have e1 : (K+2*n)*p=m*p+p+n*p := by
    have : K+2*n=m+1+n := by omega
    rw [this]; ring
  have e2 : (K+n)*p=m*p+p := by rw [hm]; ring
  have e3 : K+n-1=m := by omega
  rw [e3,e2]
  rw [e1] at htip
  omega

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

theorem fibre_tip (t : ℕ) (hlo : r+2*n*p≤t) (hhi : t<r+2*n*p+p) :
    pz p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) n=t := by
  unfold pz
  exact (WrapPrefixWindow.original_tip p r n t hlo hhi).symm

/-- A surplus row colour is never a residual balanced colour. -/
theorem surplus_not_residual (z : Fin d) (i : Fin b) :
    (WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(WrapPrefixSchur.surplusRow H z:ZMod p) := by
  have hs : Function.Injective (fun x:Fin b ⊕ Fin d => (H.er x:ℕ)) := by
    intro x y he
    exact H.er.injective (Fin.ext he)
  have hh := WrapFibreCount.residual_injective p (r+2*n*p) H.hp2
    (fun x:Fin b ⊕ Fin d => (H.er x:ℕ)) hs (fun x => lt_trans (H.er x).2 H.he)
  intro he
  have hx : WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i)=r+2*n*p+2*(H.er (Sum.inl i):ℕ) := by
    simp only [WrapPrefixCoreGeometry.xs_eq,WrapFibreCount.balancedRow]
  have hz : WrapPrefixSchur.surplusRow H z=r+2*n*p+2*(H.er (Sum.inr z):ℕ) := by
    unfold WrapPrefixSchur.surplusRow
    exact WrapPrefixGeometry.row_surplus r H.er z
  rw [hx,hz] at he
  exact Sum.inl_ne_inr (hh he)

theorem bit_le (γ : ℕ) : WrapJointProfile.bit p r γ≤1 := by
  unfold WrapJointProfile.bit
  have := Nat.mod_lt (WrapJointProfile.lower p r γ-r) (show 0<2 by norm_num)
  omega


end RowSeparationFinal


section ColumnCoupling
variable {p : ℕ} [Fact p.Prime]


variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)


theorem dot_transpose {K α : Type*} [CommRing K] [Fintype α] (a b : α → K) (M : Matrix α α K) :
    a ⬝ᵥ M *ᵥ b=b ⬝ᵥ Mᵀ *ᵥ a := by
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose,dotProduct_comm]


/-- A surplus column colour is never a residual balanced colour. -/
theorem surplus_col_not_residual (y : Fin d) (i : Fin b) :
    (WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(WrapPrefixSchur.surplusCol H y:ZMod p) := by
  have hs : Function.Injective (fun x:Fin b ⊕ Fin d => (H.ec x:ℕ)) := by
    intro x z he
    exact H.ec.injective (Fin.ext he)
  have hh := WrapFibreCount.residual_injective p (r+2*n*p+1) H.hp2
    (fun x:Fin b ⊕ Fin d => (H.ec x:ℕ)) hs (fun x => lt_trans (H.ec x).2 H.he)
  intro he
  have hx : WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i)=r+2*n*p+2*(H.er (Sum.inl i):ℕ) := by
    simp only [WrapPrefixCoreGeometry.xs_eq,WrapFibreCount.balancedRow]
  have hz : WrapPrefixSchur.surplusCol H y=r+2*n*p+2*(H.ec (Sum.inr y):ℕ)+1 := by
    unfold WrapPrefixSchur.surplusCol
    exact WrapPrefixGeometry.col_surplus r (Fact.out:p.Prime).pos shift H.ec y
  have hr := H.hres i
  rw [hx] at he
  rw [he,hz] at hr
  have : ((r+2*n*p+1+2*(H.ec (Sum.inl i):ℕ):ℕ):ZMod p)=((r+2*n*p+1+2*(H.ec (Sum.inr y):ℕ):ℕ):ZMod p) := by
    rw [show r+2*n*p+1+2*(H.ec (Sum.inl i):ℕ)=r+2*n*p+2*(H.ec (Sum.inl i):ℕ)+1 by ring,
      show r+2*n*p+1+2*(H.ec (Sum.inr y):ℕ)=r+2*n*p+2*(H.ec (Sum.inr y):ℕ)+1 by ring]
    exact hr.symm
  exact Sum.inl_ne_inr (hh this)

end ColumnCoupling

section ColumnSeparation
variable {p : ℕ} [Fact p.Prime]


omit [Fact p.Prime] in
theorem pxr_flip (γ k η n : ℕ) (c : Fin n) : pxr p γ k (1-η) n c=pyc p γ k η n c := rfl

omit [Fact p.Prime] in
theorem pyc_flip (γ k η n : ℕ) (hη : η≤1) (c : Fin n) : pyc p γ k (1-η) n c=pxr p γ k η n c := by
  unfold pyc pxr
  have : 1-(1-η)=η := by omega
  rw [this]

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)


end ColumnSeparation

namespace TwoTermDeformation
section TwoParameterTransport
variable (p : ℕ) [Fact p.Prime]


end TwoParameterTransport
end TwoTermDeformation

namespace TwoTermDeformation
section TwoParameterSource
variable (p : ℕ) [Fact p.Prime]


variable {ι : Type} [Fintype ι] [DecidableEq ι]


section Core
variable {β : Type} [Fintype β] [DecidableEq β]


end Core


section Node
variable {β : Type} [Fintype β] [DecidableEq β]


end Node


section Normalized
variable {β : Type} [Fintype β] [DecidableEq β]


end Normalized

end TwoParameterSource
end TwoTermDeformation

/-! ## R2: outside kills across FRACTIONAL cuts in the one-parameter ring

The integer family is UNDEFORMED: its parameter is set to zero in the
cleared world, where every original integer denominator `t/p` is a nonzero
constant. The fractional parameter `Y` is evaluated at the central pole.
Every nonvanishing below is an explicitly evaluated value of an ORIGINAL
cleared numerator; no generic-nonzero statement is specialized. -/

section FractionalCleared
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)

/-- The integer pole parameter set to zero: the one-parameter world. -/
noncomputable def specInt : (ZMod p)[X][X] →+* (ZMod p)[X] := Polynomial.evalRingHom 0

/-- The fractional parameter as the outer variable `Y` of the one-parameter
residue field `F_p(U)(Y)`. -/
noncomputable def embedY : (ZMod p)[X] →+* WrapPoleResidue.Residue p :=
  (algebraMap (RatFunc (ZMod p))[X] (WrapPoleResidue.Residue p)).comp
    (Polynomial.mapRingHom (RatFunc.C:ZMod p →+* RatFunc (ZMod p)))

noncomputable def embed1 : (ZMod p)[X][X] →+* WrapPoleResidue.Residue p := (embedY p).comp (specInt p)

theorem embedY_injective : Function.Injective (embedY p) :=
  (RatFunc.algebraMap_injective (RatFunc (ZMod p))).comp
    (Polynomial.map_injective _ RatFunc.C_injective)

theorem embedY_C (k : ZMod p) : embedY p (Polynomial.C k)=RatFunc.C (RatFunc.C k) := by
  simp [embedY,RatFunc.algebraMap_C]

theorem embedY_X : embedY p Polynomial.X=(RatFunc.X:WrapPoleResidue.Residue p) := by
  simp [embedY,RatFunc.algebraMap_X]

theorem embed1_const (k : ZMod p) : embed1 p (bconst p k)=RatFunc.C (RatFunc.C k) := by
  simp only [embed1,specInt,bconst,RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C]
  exact embedY_C p k

theorem embed1_nat (k : ℕ) : embed1 p (bconst p (k:ZMod p))=(k:WrapPoleResidue.Residue p) := by
  rw [embed1_const]; simp only [map_natCast]

theorem embed1_frac : embed1 p (bFrac p)=(RatFunc.X:WrapPoleResidue.Residue p) := by
  simp only [embed1,specInt,bFrac,RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C]
  exact embedY_X p

theorem embed1_int : embed1 p (bInt p)=0 := by
  simp only [embed1,specInt,bInt,RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_X,map_zero]

theorem q_zmod_ne (hq0 : 0<q) (hqp : q<p) : (q:ZMod p)≠0 := by
  intro hz
  have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
  omega

/-- Original denominators with the integer family undeformed. -/
theorem specInt_dfac (t : ℕ) : specInt p (dfac p q o t)=
    if p∣t then Polynomial.C ((t/p:ℕ):ZMod p)
    else if p∣q*t-o then Polynomial.C ((((q*t-o)/p:ℕ):ZMod p))+Polynomial.C (q:ZMod p)*Polynomial.X
    else 1 := by
  unfold dfac
  split_ifs <;> simp [specInt,bconst,bInt,bFrac]

theorem quot_ne_zero (M t : ℕ) (hM : M<p*p) (ht : t∈Icc 1 M) (h1 : p∣t) : ((t/p:ℕ):ZMod p)≠0 := by
  have ht1 := mem_Icc.mp ht
  have hp := (Fact.out:p.Prime).pos
  have hlt : t/p<p := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have hpos : 0<t/p := Nat.div_pos (Nat.le_of_dvd (by omega) h1) hp
  simpa using zmod_cast_ne p (t/p) 0 hlt hp (by omega)

/-- With the integer family undeformed no original denominator vanishes
identically: an integer pole keeps its nonzero original quotient. -/
theorem specInt_dfac_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) (t : ℕ) (ht : t∈Icc 1 M) :
    specInt p (dfac p q o t)≠0 := by
  rw [specInt_dfac]
  split_ifs with h1 h2
  · rw [Ne,Polynomial.C_eq_zero]
    exact quot_ne_zero p M t hM ht h1
  · intro hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 1) hz
    simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_one,
      Polynomial.coeff_zero,mul_one,one_ne_zero,if_false,zero_add] at hc
    exact hq hc
  · exact one_ne_zero

theorem embed1_dfac_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) (t : ℕ) (ht : t∈Icc 1 M) :
    embed1 p (dfac p q o t)≠0 := by
  intro hz
  apply specInt_dfac_ne p q o M hM hq t ht
  apply embedY_injective p
  rw [map_zero]
  exact hz

theorem specInt_clearing_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) :
    specInt p (clearing p q o M)≠0 := by
  unfold clearing
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun t ht => specInt_dfac_ne p q o M hM hq t ht)

theorem embed1_clearing_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) :
    embed1 p (clearing p q o M)≠0 := by
  unfold clearing
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun t ht => embed1_dfac_ne p q o M hM hq t ht)

theorem embed1_dfac (t : ℕ) : embed1 p (dfac p q o t)=
    if p∣t then ((t/p:ℕ):WrapPoleResidue.Residue p)
    else if p∣q*t-o then ((((q*t-o)/p:ℕ):WrapPoleResidue.Residue p)+
      (q:WrapPoleResidue.Residue p)*RatFunc.X) else 1 := by
  unfold dfac
  split_ifs <;> simp only [map_add,map_mul,map_one,embed1_nat,embed1_int,embed1_frac,add_zero]

/-- Clearing an ORIGINAL one-parameter increment residue. -/
theorem embed1_clearedDelta (M t : ℕ) (hM : M<p*p) (ht : t∈Icc 1 M) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    embed1 p (clearedDelta p q o M t)=
      embed1 p (clearing p q o M)*WrapDeform.residue p (WrapIncrement.delta p q o t) := by
  have hq := q_zmod_ne p q hq0 hqp
  have hD := embed1_dfac_ne p q o M hM hq t ht
  have hc := congrArg (embed1 p) (cofactor_mul p q o M t ht)
  rw [map_mul] at hc
  rw [WrapPoleResidue.delta p q o t (WrapSimplePole.q_res_ne p q hq0 hqp) hle h2,← hc]
  unfold clearedDelta deltaWeight
  have hdf := embed1_dfac p q o t
  by_cases h1 : p∣t
  · have h2' := not_both p q o t hqp ho0 hoq hle h1
    have hdv : embed1 p (dfac p q o t)=((t/p:ℕ):WrapPoleResidue.Residue p) := by
      rw [hdf,if_pos h1]
    rw [hdv] at hD ⊢
    simp only [if_pos h1,if_neg h2',map_mul,map_one,mul_zero,sub_zero,one_mul]
    field_simp
  · by_cases h3 : p∣q*t-o
    · have hdv : embed1 p (dfac p q o t)=((((q*t-o)/p:ℕ):WrapPoleResidue.Residue p)+
          (q:WrapPoleResidue.Residue p)*RatFunc.X) := by
        rw [hdf,if_neg h1,if_pos h3]
      rw [hdv] at hD ⊢
      simp only [if_neg h1,if_pos h3,map_mul,map_neg,embed1_nat,zero_sub]
      field_simp
    · simp only [if_neg h1,if_neg h3,map_mul,map_zero,zero_mul,mul_zero,sub_zero]

theorem embed1_clearedLoad (M a : ℕ) (haM : a≤M) (hM : M<p*p) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) :
    embed1 p (clearedLoad p q o M a)=
      embed1 p (clearing p q o M)*WrapDeform.residue p (WrapEntryRelation.load p q o a) := by
  unfold clearedLoad WrapEntryRelation.load
  rw [map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨h1,h2,h3⟩ := load_terms p q o M a haM hM hq0 hoq t ht
  exact embed1_clearedDelta p q o M t hM h1 hq0 hqp ho0 hoq h2 h3

theorem dsq_residue1 (t : ℕ) (hq0 : 0<q) (hqp : q<p) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    WrapDeform.residue p (WrapIncrement.dsq p q o t)=
      (if p∣t then (1:WrapPoleResidue.Residue p)/((t/p:ℕ):WrapPoleResidue.Residue p) else 0)^2-
      (q:WrapPoleResidue.Residue p)^2*(if p∣q*t-o then
        (1:WrapPoleResidue.Residue p)/((((q*t-o)/p:ℕ):WrapPoleResidue.Residue p)+
          (q:WrapPoleResidue.Residue p)*RatFunc.X) else 0)^2 := by
  unfold WrapIncrement.dsq
  rw [Polynomial.C_pow,Polynomial.C_pow,map_pow,map_pow,map_sub,map_mul,map_pow,map_pow,map_pow,
    WrapPoleResidue.pure_constant p t h2,WrapPoleResidue.constant_nat,
    WrapSimplePole.argument_nat p q o t hle,
    WrapPoleResidue.normalized_nat p (q*t-o) q (WrapSimplePole.q_res_ne p q hq0 hqp)]

theorem embed1_clearedSquare (M t : ℕ) (hM : M<p*p) (ht : t∈Icc 1 M) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    embed1 p (clearedSquare p q o M t)=
      embed1 p (clearing p q o M)^2*WrapDeform.residue p (WrapIncrement.dsq p q o t) := by
  have hq := q_zmod_ne p q hq0 hqp
  have hD := embed1_dfac_ne p q o M hM hq t ht
  have hc := congrArg (embed1 p) (cofactor_mul p q o M t ht)
  rw [map_mul] at hc
  rw [dsq_residue1 p q o t hq0 hqp hle h2,← hc]
  unfold clearedSquare squareWeight
  have hdf := embed1_dfac p q o t
  by_cases h1 : p∣t
  · have h2' := not_both p q o t hqp ho0 hoq hle h1
    have hdv : embed1 p (dfac p q o t)=((t/p:ℕ):WrapPoleResidue.Residue p) := by
      rw [hdf,if_pos h1]
    rw [hdv] at hD ⊢
    simp only [if_pos h1,if_neg h2',map_mul,map_one,map_pow,one_mul]
    field_simp
    ring
  · by_cases h3 : p∣q*t-o
    · have hdv : embed1 p (dfac p q o t)=((((q*t-o)/p:ℕ):WrapPoleResidue.Residue p)+
          (q:WrapPoleResidue.Residue p)*RatFunc.X) := by
        rw [hdf,if_neg h1,if_pos h3]
      rw [hdv] at hD ⊢
      simp only [if_neg h1,if_pos h3,map_mul,map_neg,map_pow,embed1_const,zero_pow two_ne_zero,
        zero_sub]
      simp only [map_pow,map_natCast]
      field_simp
    · simp only [if_neg h1,if_neg h3,map_mul,map_zero,zero_mul,mul_zero,sub_zero,
        zero_pow two_ne_zero]

theorem residue_constants1 (u : GaussLoc p) (u0 : ZMod p)
    (h : res p u=CatalanCore.Uniform.Content.Hybrid.rfH p u0) :
    WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0) := by
  rw [WrapOwnCore.constants,RingHom.comp_apply,WrapPoleResidue.constant,h,rfH_eq]

/-- Exact cleared residue of an actual ONE-parameter entry at two original
nodes of one colour (divided original displacement). -/
theorem embed1_clearedEntry (M : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (u : GaussLoc p) (u0 : ZMod p)
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (a b : ℕ) (ha : a≤M) (hb : b≤M) (hcol : (a:ZMod p)=(b:ZMod p))
    (hab : ((b/p:ℕ):ZMod p)≠((a/p:ℕ):ZMod p)) :
    embed1 p (clearedEntry p q o M u0 a b)=
      embed1 p (clearing p q o M)*WrapDeform.residue p (WrapDeformedEntry.entry p q o u a b) := by
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  have hu0' : WrapDeform.residue p (WrapEntryRelation.constants p u)=RatFunc.C (RatFunc.C u0) := hu0
  have hd := congrArg (WrapDeform.residue p)
    (WrapEntryRelation.divided_commutator p q o (M+1) u (by nlinarith) a b (by omega) (by omega) hcol)
  simp only [map_mul,map_sub,map_natCast,hu0'] at hd
  have hne : ((b/p:ℕ):WrapPoleResidue.Residue p)-((a/p:ℕ):WrapPoleResidue.Residue p)≠0 := by
    intro hz
    apply hab
    have h := sub_eq_zero.mp hz
    have hinj : Function.Injective (fun k : ZMod p =>
        (RatFunc.C (RatFunc.C k) : WrapPoleResidue.Residue p)) :=
      RatFunc.C_injective.comp RatFunc.C_injective
    apply hinj
    simpa only [map_natCast] using h
  unfold clearedEntry
  rw [map_mul,map_sub,embed1_clearedLoad p q o M b hb hMp hq0 hqp ho0 hoq,
    embed1_clearedLoad p q o M a ha hMp hq0 hqp ho0 hoq,embed1_const]
  simp only [map_div₀,map_sub,map_natCast]
  have hE : WrapDeform.residue p (WrapDeformedEntry.entry p q o u a b)=
      (((b/p:ℕ):WrapPoleResidue.Residue p)-((a/p:ℕ):WrapPoleResidue.Residue p))⁻¹*
        (RatFunc.C (RatFunc.C u0)*(WrapDeform.residue p (WrapEntryRelation.load p q o b)-
          WrapDeform.residue p (WrapEntryRelation.load p q o a))) := by
    rw [← hd,← mul_assoc,rational_inv_mul_cancel _ hne,one_mul]
  rw [rational_div_eq_mul_inv,hE]
  ring

theorem embed1_clearedDiag (M : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (u : GaussLoc p) (u0 : ZMod p)
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (a : ℕ) (ha : a≤M) :
    embed1 p (clearedDiag p q o M u0 a)=
      embed1 p (clearing p q o M)^2*WrapDeform.residue p (WrapDeformedEntry.entry p q o u a a) := by
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  unfold clearedDiag WrapDeformedEntry.entry
  rw [if_pos rfl]
  have hc : WrapDeform.embed p (Polynomial.C u)=WrapOwnCore.constants p u := rfl
  rw [hc]
  simp only [map_neg,map_mul,map_sum,hu0,embed1_const,Finset.mul_sum,mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨h1,h2,h3⟩ := load_terms p q o M a ha hMp hq0 hoq t ht
  rw [embed1_clearedSquare p q o M t hMp h1 hq0 hqp ho0 hoq h2 h3]
  ring

/-- Spectral-outer cleared polynomials with the integer family undeformed,
in the one-parameter residue field (outer variable = original spectral `U`). -/
noncomputable def embed1P : (ZMod p)[X][X][X] →+* WrapPoleResidue.Residue p :=
  Polynomial.eval₂RingHom (embed1 p) (RatFunc.C (RatFunc.X:RatFunc (ZMod p)))

/-- The same embedding through the faithful swapped bivariate embedding. -/
noncomputable def embed1Q : (ZMod p)[X][X][X] →+* WrapPoleResidue.Residue p :=
  (WrapBivariate.swapped (K:=ZMod p)).comp (Polynomial.mapRingHom (specInt p))

theorem swapped_C (f : (ZMod p)[X]) :
    WrapBivariate.swapped (K:=ZMod p) (Polynomial.C f)=embedY p f := by
  have h : (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp Polynomial.C=
      (RatFunc.C:ZMod p →+* RatFunc (ZMod p)) := Subsingleton.elim _ _
  change algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))
      (((Polynomial.Bivariate.swap (R:=ZMod p)) (Polynomial.C f)).map
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p))))=_
  rw [Polynomial.Bivariate.swap_C,Polynomial.map_map,h]
  rfl

theorem embed1P_C (b : (ZMod p)[X][X]) : embed1P p (Polynomial.C b)=embed1 p b := by
  simp only [embed1P,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]

theorem embed1P_X : embed1P p Polynomial.X=RatFunc.C (RatFunc.X:RatFunc (ZMod p)) := by
  simp only [embed1P,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]

theorem embed1Q_C (b : (ZMod p)[X][X]) : embed1Q p (Polynomial.C b)=embed1 p b := by
  simp only [embed1Q,RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_C]
  exact swapped_C p _

theorem embed1Q_X : embed1Q p Polynomial.X=RatFunc.C (RatFunc.X:RatFunc (ZMod p)) := by
  change algebraMap (RatFunc (ZMod p))[X] (RatFunc (RatFunc (ZMod p)))
      (((Polynomial.Bivariate.swap (R:=ZMod p)) ((Polynomial.X:(ZMod p)[X][X][X]).map (specInt p))).map
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p))))=_
  rw [Polynomial.map_X,Polynomial.Bivariate.swap_Y,Polynomial.map_C,RatFunc.algebraMap_C,RatFunc.algebraMap_X]

theorem embed1P_eq : embed1P p=embed1Q p :=
  Polynomial.ringHom_ext (fun b => (embed1P_C p b).trans (embed1Q_C p b).symm)
    ((embed1P_X p).trans (embed1Q_X p).symm)

end FractionalCleared

section FractionalFibreSystem
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)
variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)

/-- The ORIGINAL one-parameter bordered fibre system: common block with the
original spectral diagonal, balanced columns and the direction column. -/
noncomputable def ringSystem1 (s u : GaussLoc p) (load : Bool) :
    Matrix (Fin k ⊕ Fin (n+1)) (Fin k ⊕ Fin (n+1)) (WrapDeform.Extension p) :=
  Matrix.fromBlocks
    (Matrix.of fun i j => WrapDeformedEntry.entry p q o u (cn i) (cn j)+
      if i=j then WrapOwnCore.constants p s else 0)
    (Matrix.of fun i j => if h : (j:ℕ)<n then WrapDeformedEntry.entry p q o u (cn i) (yc ⟨j,h⟩)
      else if load then WrapOwnCore.constants p u*WrapEntryRelation.load p q o (cn i) else 1)
    (Matrix.of fun i j => WrapDeformedEntry.entry p q o u (bordRow xr z i) (cn j))
    (Matrix.of fun i j => if h : (j:ℕ)<n then WrapDeformedEntry.entry p q o u (bordRow xr z i) (yc ⟨j,h⟩)
      else if load then WrapOwnCore.constants p u*WrapEntryRelation.load p q o (bordRow xr z i) else 1)

theorem ringSystem1_reindex (s u : GaussLoc p) (load : Bool) :
    (ringSystem1 p q o cn xr yc z s u load).submatrix (bordEquiv k n) (bordEquiv k n)=
      Matrix.fromBlocks (WrapFibreCore.core p q o s u cn xr yc)
        (Matrix.of fun i (_:Unit) => if load then WrapOwnCore.constants p u*
          WrapEntryRelation.load p q o (Sum.elim cn xr i) else 1)
        (Matrix.of fun (_:Unit) j => WrapDeformedEntry.entry p q o u z (Sum.elim cn yc j))
        (Matrix.of fun (_:Unit) (_:Unit) => if load then WrapOwnCore.constants p u*
          WrapEntryRelation.load p q o z else 1) := by
  classical
  have hlt (c : Fin n) : ((Fin.castAdd 1 c:Fin (n+1)):ℕ)<n := by simp
  have hnl : ¬((Fin.last n:Fin (n+1)):ℕ)<n := by simp
  have hbc (c : Fin n) : bordRow xr z (Fin.castAdd 1 c)=xr c := by
    unfold bordRow; rw [dif_pos (hlt c)]; rfl
  have hbl : bordRow xr z (Fin.last n)=z := by unfold bordRow; rw [dif_neg hnl]
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,ringSystem1,Matrix.fromBlocks_apply₁₁,
      Matrix.of_apply,WrapFibreCore.core,Matrix.add_apply,Sum.elim_inl,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    split_ifs <;> simp
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inl_inr,ringSystem1,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₁₁,Matrix.of_apply,dif_pos (hlt j),
      WrapFibreCore.core,Matrix.add_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,add_zero]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inr,ringSystem1,
      Matrix.fromBlocks_apply₁₂,Matrix.of_apply,dif_neg hnl,Sum.elim_inl]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inl_inr,ringSystem1,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₁₁,Matrix.of_apply,hbc,
      WrapFibreCore.core,Matrix.add_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,add_zero]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,ringSystem1,Matrix.fromBlocks_apply₂₂,
      Matrix.fromBlocks_apply₁₁,Matrix.of_apply,hbc,dif_pos (hlt j),
      WrapFibreCore.core,Matrix.add_apply,Sum.elim_inr,
      Matrix.zero_apply,add_zero]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,bordEquiv_inr,ringSystem1,
      Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₂,Matrix.of_apply,hbc,dif_neg hnl,Sum.elim_inr]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inr,ringSystem1,
      Matrix.fromBlocks_apply₂₁,Matrix.of_apply,hbl,Sum.elim_inl]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,bordEquiv_inr,ringSystem1,
      Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₂₁,Matrix.of_apply,hbl,dif_pos (hlt j),Sum.elim_inr]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inr,ringSystem1,Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply,hbl,dif_neg hnl]

/-- Residue of the ORIGINAL one-parameter bordered fibre determinant in
Schur form. -/
theorem residue_ringSystem1_det (s u : GaussLoc p) (load : Bool)
    (hP : ((WrapFibreCore.core p q o s u cn xr yc).map (WrapDeform.residue p)).det≠0) :
    WrapDeform.residue p (ringSystem1 p q o cn xr yc z s u load).det=
      ((WrapFibreCore.core p q o s u cn xr yc).map (WrapDeform.residue p)).det*
        (WrapDeform.residue p (if load then WrapOwnCore.constants p u*
          WrapEntryRelation.load p q o z else 1)-
          (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u z (Sum.elim cn yc j))) ⬝ᵥ
            ((WrapFibreCore.core p q o s u cn xr yc).map (WrapDeform.residue p))⁻¹ *ᵥ
            (fun i => WrapDeform.residue p (if load then WrapOwnCore.constants p u*
              WrapEntryRelation.load p q o (Sum.elim cn xr i) else 1))) := by
  rw [← Matrix.det_submatrix_equiv_self (bordEquiv k n),ringSystem1_reindex]
  exact map_bordered_det (WrapDeform.residue p) _ _ _ _ hP

end FractionalFibreSystem


section FractionalClearedSystem
variable {p : ℕ} [Fact p.Prime] {q o : ℕ}
variable {k n : ℕ} {cn : Fin k → ℕ} {xr yc : Fin n → ℕ} {z : ℕ}

noncomputable def rowScale1 (Δ : WrapPoleResidue.Residue p) : Fin k ⊕ Fin (n+1) → WrapPoleResidue.Residue p :=
  Sum.elim (fun _ => Δ^2) (fun _ => Δ)
noncomputable def colScale1 (Δ : WrapPoleResidue.Residue p) (load : Bool) :
    Fin k ⊕ Fin (n+1) → WrapPoleResidue.Residue p :=
  Sum.elim (fun _ => 1) (fun j => if (j:ℕ)<n then 1 else if load then 1 else Δ⁻¹)

theorem embed1_clearedSystem {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (s u : GaussLoc p) (u0 : ZMod p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (load : Bool) (i j : Fin k ⊕ Fin (n+1)) :
    embed1P p (clearedSystem p q o cn xr yc z M u0 load i j)=
      rowScale1 (n:=n) (embed1 p (clearing p q o M)) i*
        WrapDeform.residue p (ringSystem1 p q o cn xr yc z s u load i j)*
        colScale1 (n:=n) (embed1 p (clearing p q o M)) load j := by
  have hq := q_zmod_ne p q H.hq0 H.hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H.hq0) H.hM
  have hΔ : embed1 p (clearing p q o M)≠0 := embed1_clearing_ne p q o M hMp hq
  have hC (b : (ZMod p)[X][X]) : embed1P p (Polynomial.C b)=embed1 p b := embed1P_C p b
  have hU : WrapDeform.residue p (WrapOwnCore.constants p s)=embed1P p Polynomial.X := by
    rw [WrapOwnCore.constants,RingHom.comp_apply,WrapPoleResidue.constant,hs,embed1P_X]
  have hLoad (a : ℕ) (ha : a≤M) : embed1 p (clearedLoadRow p q o M u0 a)=
      embed1 p (clearing p q o M)*WrapDeform.residue p
        (WrapOwnCore.constants p u*WrapEntryRelation.load p q o a) := by
    unfold clearedLoadRow
    rw [map_mul,embed1_const,embed1_clearedLoad p q o M a ha hMp H.hq0 H.hqp H.ho0 H.hoq,map_mul,hu0]
    ring
  have hEnt (a b : ℕ) (ha : a≤M) (hb : b≤M) (hcol : (a:ZMod p)=(b:ZMod p))
      (hab : ((b/p:ℕ):ZMod p)≠((a/p:ℕ):ZMod p)) :
      embed1 p (clearedEntry p q o M u0 a b)=
        embed1 p (clearing p q o M)*WrapDeform.residue p (WrapDeformedEntry.entry p q o u a b) :=
    embed1_clearedEntry p q o M H.hM H.hq0 H.hqp H.ho0 H.hoq u u0 hu0 a b ha hb hcol hab
  rcases i with i|i <;> rcases j with j|j
  · simp only [clearedSystem,spectralSystem,ringSystem1,Matrix.fromBlocks_apply₁₁,Matrix.add_apply,
      Matrix.smul_apply,Matrix.map_apply,Matrix.of_apply,clearedA,rowScale1,colScale1,Sum.elim_inl,mul_one]
    by_cases hij : i=j
    · subst hij
      simp only [Matrix.one_apply_eq,smul_eq_mul,mul_one,if_true,map_add,map_mul,map_pow,hC,hU]
      rw [embed1_clearedDiag p q o M H.hM H.hq0 H.hqp H.ho0 H.hoq u u0 hu0 _ (H.hcn i)]
      ring
    · simp only [Matrix.one_apply_ne hij,smul_eq_mul,mul_zero,zero_add,if_neg hij,add_zero,map_mul,hC]
      rw [hEnt _ _ (H.hcn i) (H.hcn j) ((H.ccn i).trans (H.ccn j).symm) (H.qcc i j hij)]
      ring
  · simp only [clearedSystem,spectralSystem,ringSystem1,Matrix.fromBlocks_apply₁₂,
      Matrix.map_apply,Matrix.of_apply,clearedB,rowScale1,colScale1,Sum.elim_inl,Sum.elim_inr]
    by_cases hj : (j:ℕ)<n
    · simp only [dif_pos hj,if_pos hj,mul_one,map_mul,hC]
      rw [hEnt _ _ (H.hcn i) (H.hyc _) ((H.ccn i).trans (H.cyc _).symm) (H.qcb i _)]
      ring
    · simp only [dif_neg hj,if_neg hj]
      cases load
      · simp only [Bool.false_eq_true,↓reduceIte,map_one,mul_one,hC]
        field_simp
      · simp only [↓reduceIte,mul_one,map_mul,hC]
        rw [hLoad _ (H.hcn i)]
        rw [map_mul]; ring
  · simp only [clearedSystem,spectralSystem,ringSystem1,Matrix.fromBlocks_apply₂₁,
      Matrix.map_apply,Matrix.of_apply,clearedE,rowScale1,colScale1,Sum.elim_inl,Sum.elim_inr,mul_one,hC]
    rw [hEnt _ _ (H.bord_le i) (H.hcn j) ((H.bord_colour i).trans (H.ccn j).symm) (H.qbc i j)]
  · simp only [clearedSystem,spectralSystem,ringSystem1,Matrix.fromBlocks_apply₂₂,
      Matrix.map_apply,Matrix.of_apply,clearedD,rowScale1,colScale1,Sum.elim_inr]
    by_cases hj : (j:ℕ)<n
    · simp only [dif_pos hj,if_pos hj,mul_one,hC]
      rw [hEnt _ _ (H.bord_le i) (H.hyc _) ((H.bord_colour i).trans (H.cyc _).symm) (H.qbb i _)]
    · simp only [dif_neg hj,if_neg hj]
      cases load
      · simp only [Bool.false_eq_true,↓reduceIte,map_one,mul_one,hC]
        field_simp
      · simp only [↓reduceIte,mul_one,hC]
        rw [hLoad _ (H.bord_le i)]

/-- The one-parameter cleared determinant is the residue of the ORIGINAL
bordered determinant times explicit powers of the (nonzero) clearing factor. -/
theorem embed1_clearedSystem_det {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (s u : GaussLoc p) (u0 : ZMod p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (load : Bool) :
    embed1P p (clearedSystem p q o cn xr yc z M u0 load).det=
      embed1 p (clearing p q o M)^(2*k+n)*(if load then embed1 p (clearing p q o M) else 1)*
        WrapDeform.residue p (ringSystem1 p q o cn xr yc z s u load).det := by
  have hq := q_zmod_ne p q H.hq0 H.hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H.hq0) H.hM
  have hΔ : embed1 p (clearing p q o M)≠0 := embed1_clearing_ne p q o M hMp hq
  rw [RingHom.map_det (WrapDeform.residue p)]
  have h1 : embed1P p (clearedSystem p q o cn xr yc z M u0 load).det=
      ((embed1P p).mapMatrix (clearedSystem p q o cn xr yc z M u0 load)).det :=
    eval₂_det (embed1 p) _ _
  rw [h1]
  have he : (embed1P p).mapMatrix (clearedSystem p q o cn xr yc z M u0 load)=
      Matrix.of fun i j => rowScale1 (n:=n) (embed1 p (clearing p q o M)) i*
        ((WrapDeform.residue p).mapMatrix (ringSystem1 p q o cn xr yc z s u load)) i j*
        colScale1 (n:=n) (embed1 p (clearing p q o M)) load j := by
    ext i j
    exact embed1_clearedSystem H s u u0 hs hu0 load i j
  rw [he,det_scaled]
  congr 1
  simp only [rowScale1,colScale1,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Finset.prod_const_one,one_mul,Fin.prod_univ_castSucc,
    Fin.coe_castSucc,Fin.is_lt,↓reduceIte,Fin.val_last,lt_irrefl]
  cases load
  · simp only [Bool.false_eq_true,↓reduceIte,mul_one]
    simp only [one_pow,one_mul]
    field_simp
    ring
  · simp only [↓reduceIte,mul_one,one_pow,one_mul]
    ring

/-- The one-parameter cross argument, parametrised by its input: distinct
cleared bordered cross products (integer family undeformed) give distinct
ORIGINAL residue directions. Used by the fractional (central `Y`) test
below and by the integer (top `Y`) test of R3. -/
theorem residue_cross1_of_spec {M n k1 k2 : ℕ}
    {cn1 : Fin k1 → ℕ} {xr1 yc1 : Fin n → ℕ} {z1 : ℕ}
    {cn2 : Fin k2 → ℕ} {xr2 yc2 : Fin n → ℕ} {z2 : ℕ}
    (H1 : FibreHyp p q o cn1 xr1 yc1 z1 M) (H2 : FibreHyp p q o cn2 xr2 yc2 z2 M)
    (s u : GaussLoc p) (u0 : ZMod p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (hbr : specInt p ((clearedD p q o xr1 yc1 z1 M u0 true).det*(clearedD p q o xr2 yc2 z2 M u0 false).det)≠
      specInt p ((clearedD p q o xr2 yc2 z2 M u0 true).det*(clearedD p q o xr1 yc1 z1 M u0 false).det)) :
    WrapDeform.residue p ((ringSystem1 p q o cn1 xr1 yc1 z1 s u true).det*
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u false).det-
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u true).det*(ringSystem1 p q o cn1 xr1 yc1 z1 s u false).det)≠0 := by
  intro hres
  have hq := q_zmod_ne p q H1.hq0 H1.hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H1.hq0) H1.hM
  have hcl := specInt_clearing_ne p q o M hMp hq
  obtain ⟨dAN,cAN⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn1 M u0)
    (clearedB p q o cn1 yc1 M u0 true) (clearedE p q o cn1 xr1 z1 M u0) (clearedD p q o xr1 yc1 z1 M u0 true)
  obtain ⟨dAD,cAD⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn1 M u0)
    (clearedB p q o cn1 yc1 M u0 false) (clearedE p q o cn1 xr1 z1 M u0) (clearedD p q o xr1 yc1 z1 M u0 false)
  obtain ⟨dBN,cBN⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn2 M u0)
    (clearedB p q o cn2 yc2 M u0 true) (clearedE p q o cn2 xr2 z2 M u0) (clearedD p q o xr2 yc2 z2 M u0 true)
  obtain ⟨dBD,cBD⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn2 M u0)
    (clearedB p q o cn2 yc2 M u0 false) (clearedE p q o cn2 xr2 z2 M u0) (clearedD p q o xr2 yc2 z2 M u0 false)
  simp only [Fintype.card_fin] at dAN cAN dAD cAD dBN cBN dBD cBD
  have hdeg (P : ((ZMod p)[X][X])[X]) (a : ℕ) (h : P.natDegree≤a) :
      (P.map (specInt p)).natDegree≤a := Polynomial.natDegree_map_le.trans h
  have hP := cross_ne_of_top k1 k2 _ _ _ _ (hdeg _ _ dAN) (hdeg _ _ dAD) (hdeg _ _ dBN) (hdeg _ _ dBD) (by
    rw [Polynomial.coeff_map,Polynomial.coeff_map,Polynomial.coeff_map,Polynomial.coeff_map,cAN,cAD,cBN,cBD]
    intro h
    apply hbr
    have hc2 : specInt p ((clearing p q o M^2)^k1*(clearing p q o M^2)^k2)≠0 := by
      simp only [map_mul,map_pow]
      exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hcl)) (pow_ne_zero _ (pow_ne_zero _ hcl))
    apply mul_left_cancel₀ hc2
    simp only [map_mul,map_pow] at h ⊢
    linear_combination h)
  apply hP
  apply WrapBivariate.swapped_injective (K:=ZMod p)
  rw [map_mul,map_mul]
  change embed1Q p (clearedSystem p q o cn1 xr1 yc1 z1 M u0 true).det*
      embed1Q p (clearedSystem p q o cn2 xr2 yc2 z2 M u0 false).det=
    embed1Q p (clearedSystem p q o cn2 xr2 yc2 z2 M u0 true).det*
      embed1Q p (clearedSystem p q o cn1 xr1 yc1 z1 M u0 false).det
  rw [← embed1P_eq p]
  rw [embed1_clearedSystem_det H1 s u u0 hs hu0,embed1_clearedSystem_det H2 s u u0 hs hu0,
    embed1_clearedSystem_det H2 s u u0 hs hu0,embed1_clearedSystem_det H1 s u u0 hs hu0]
  simp only [↓reduceIte,Bool.false_eq_true,mul_one]
  have h0 : WrapDeform.residue p (ringSystem1 p q o cn1 xr1 yc1 z1 s u true).det*
      WrapDeform.residue p (ringSystem1 p q o cn2 xr2 yc2 z2 s u false).det=
      WrapDeform.residue p (ringSystem1 p q o cn2 xr2 yc2 z2 s u true).det*
      WrapDeform.residue p (ringSystem1 p q o cn1 xr1 yc1 z1 s u false).det := by
    have h := hres
    simp only [map_sub,map_mul] at h
    exact sub_eq_zero.mp h
  linear_combination (embed1 p (clearing p q o M)^(2*k1+n)*embed1 p (clearing p q o M)*
    embed1 p (clearing p q o M)^(2*k2+n))*h0

/-- Two cleared adjacent one-parameter fibre systems whose central
evaluations (integer family undeformed, fractional parameter at the central
pole) separate have distinct ORIGINAL residue directions. -/
theorem residue_cross1_ne {M n k1 k2 : ℕ}
    {cn1 : Fin k1 → ℕ} {xr1 yc1 : Fin n → ℕ} {z1 : ℕ}
    {cn2 : Fin k2 → ℕ} {xr2 yc2 : Fin n → ℕ} {z2 : ℕ}
    (H1 : FibreHyp p q o cn1 xr1 yc1 z1 M) (H2 : FibreHyp p q o cn2 xr2 yc2 z2 M)
    (s u : GaussLoc p) (u0 : ZMod p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (ev0 : (ZMod p)[X] →+* RatFunc (ZMod p)) (ts : ℕ) (htsM : ts∈Icc 1 M)
    (hz : ∀ t∈Icc 1 M,(ev0.comp (specInt p)) (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,(ev0.comp (specInt p)) (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k)
    (cut1 cut2 : ℕ)
    (hrow1 : ∀ i,ts≤bordRow xr1 z1 i ↔ cut1≤bordRow xr1 z1 i/p) (hcol1 : ∀ c,ts≤yc1 c ↔ cut1≤yc1 c/p)
    (hq1 : ∀ i c,((yc1 c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr1 z1 i/p:ℕ):RatFunc (ZMod p)))
    (hrow2 : ∀ i,ts≤bordRow xr2 z2 i ↔ cut2≤bordRow xr2 z2 i/p) (hcol2 : ∀ c,ts≤yc2 c ↔ cut2≤yc2 c/p)
    (hq2 : ∀ i c,((yc2 c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr2 z2 i/p:ℕ):RatFunc (ZMod p)))
    (hne : (scaledStepLoad (centralWeight p q o (ev0.comp (specInt p)) u0 M ts) cut1
          (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p)).det*
        (scaledStep (centralWeight p q o (ev0.comp (specInt p)) u0 M ts) cut2
          (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p)).det≠
      (scaledStepLoad (centralWeight p q o (ev0.comp (specInt p)) u0 M ts) cut2
          (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p)).det*
        (scaledStep (centralWeight p q o (ev0.comp (specInt p)) u0 M ts) cut1
          (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p)).det) :
    WrapDeform.residue p ((ringSystem1 p q o cn1 xr1 yc1 z1 s u true).det*
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u false).det-
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u true).det*(ringSystem1 p q o cn1 xr1 yc1 z1 s u false).det)≠0 := by
  have hq := q_zmod_ne p q H1.hq0 H1.hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H1.hq0) H1.hM
  have hD (load : Bool) {xr yc : Fin n → ℕ} {zz : ℕ} (cut : ℕ)
      (hr : ∀ i,ts≤bordRow xr zz i ↔ cut≤bordRow xr zz i/p) (hc : ∀ c,ts≤yc c ↔ cut≤yc c/p)
      (hqq : ∀ i c,((yc c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr zz i/p:ℕ):RatFunc (ZMod p))) :
      (ev0.comp (specInt p)) (clearedD p q o xr yc zz M u0 load).det=
        ((if load then scaledStepLoad else scaledStep)
          (centralWeight p q o (ev0.comp (specInt p)) u0 M ts) cut
          (fun i => bordRow xr zz i/p) (fun c => yc c/p)).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det
      (ev_clearedD (q:=q) (o:=o) (ev0.comp (specInt p)) M ts htsM hz hev u0 cut hr hc hqq load)
  have hbr : specInt p ((clearedD p q o xr1 yc1 z1 M u0 true).det*(clearedD p q o xr2 yc2 z2 M u0 false).det)≠
      specInt p ((clearedD p q o xr2 yc2 z2 M u0 true).det*(clearedD p q o xr1 yc1 z1 M u0 false).det) := by
    intro h
    apply hne
    have h' := congrArg ev0 h
    have e1 : ∀ x,ev0 (specInt p x)=(ev0.comp (specInt p)) x := fun _ => rfl
    rw [e1,e1,map_mul,map_mul] at h'
    rw [hD true cut1 hrow1 hcol1 hq1,hD false cut2 hrow2 hcol2 hq2,
      hD true cut2 hrow2 hcol2 hq2,hD false cut1 hrow1 hcol1 hq1] at h'
    simpa only [↓reduceIte,Bool.false_eq_true] using h'
  exact residue_cross1_of_spec H1 H2 s u u0 hs hu0 hbr

end FractionalClearedSystem

section FractionalSeparation
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)

/-- Evaluation of the fractional parameter at a central point (after the
integer family has been left undeformed). -/
noncomputable def evFrac (c : ZMod p) : (ZMod p)[X] →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p) (RatFunc (ZMod p))).comp (Polynomial.evalRingHom c)

/-- At the fractional central point, with the integer family undeformed,
exactly the central original denominator vanishes. -/
theorem evFrac_dfac_eq_zero (M ts : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (htsI : ¬p∣ts) (hts : p∣q*ts-o) (htsM : ts∈Icc 1 M)
    (t : ℕ) (ht : t∈Icc 1 M) :
    ((evFrac p (-((((q*ts-o)/p:ℕ):ZMod p))/(q:ZMod p))).comp (specInt p)) (dfac p q o t)=0 ↔ t=ts := by
  have hq := q_zmod_ne p q hq0 hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  have ht1 := mem_Icc.mp ht
  have hts1 := mem_Icc.mp htsM
  have hinj := (algebraMap (ZMod p) (RatFunc (ZMod p))).injective
  rw [RingHom.comp_apply,specInt_dfac]
  simp only [evFrac,RingHom.comp_apply,Polynomial.coe_evalRingHom]
  constructor
  · intro hz
    have hz' := hinj (hz.trans (map_zero _).symm)
    split_ifs at hz' with h1 h2
    · exfalso
      simp only [Polynomial.eval_C] at hz'
      exact quot_ne_zero p M t hMp ht h1 hz'
    · simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X] at hz'
      have he : ((((q*t-o)/p:ℕ)):ZMod p)=((((q*ts-o)/p:ℕ)):ZMod p) := by
        field_simp at hz'
        linear_combination hz'
      have hle1 : q*t≤q*M := Nat.mul_le_mul_left q ht1.2
      have hle2 : q*ts≤q*M := Nat.mul_le_mul_left q hts1.2
      have hlt : (q*t-o)/p<p := (Nat.div_lt_iff_lt_mul (Fact.out:p.Prime).pos).mpr (by omega)
      have hlts : (q*ts-o)/p<p := (Nat.div_lt_iff_lt_mul (Fact.out:p.Prime).pos).mpr (by omega)
      have hq' := nat_cast_eq_of_lt p _ _ hlt hlts he
      have hx : q*t-o=q*ts-o := by
        calc q*t-o=(q*t-o)/p*p := (Nat.div_mul_cancel h2).symm
          _=(q*ts-o)/p*p := by rw [hq']
          _=q*ts-o := Nat.div_mul_cancel hts
      have h1' : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1.1; omega
      have h2' : o≤q*ts := by have := Nat.le_mul_of_pos_right q hts1.1; omega
      have : q*t=q*ts := by omega
      exact Nat.eq_of_mul_eq_mul_left hq0 this
    · simp at hz'
  · intro he
    subst he
    simp only [if_neg htsI,if_pos hts,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
      Polynomial.eval_X]
    have : ((((q*t-o)/p:ℕ):ZMod p))+(q:ZMod p)*(-((((q*t-o)/p:ℕ):ZMod p))/(q:ZMod p))=0 := by
      field_simp
      ring
    rw [this,map_zero]

/-- Section 8.3 in the ONE-parameter ring at a FRACTIONAL cut: the central
fractional test with the integer family undeformed separates two adjacent
actual fibres. The value is an explicit evaluation of ORIGINAL cleared
numerators. -/
theorem profile_separation_frac (γ1 k1 η1 γ2 k2 η2 n M ts cut1 cut2 : ℕ) (s u : GaussLoc p) (u0 : ZMod p)
    (hγ1 : γ1<p) (hγ2 : γ2<p) (hη1 : η1≤1) (hη2 : η2≤1) (hn : 1≤n)
    (hk1 : k1+2*n<p) (hk2 : k2+2*n<p) (hz1 : pz p γ1 k1 n≤M) (hz2 : pz p γ2 k2 n≤M)
    (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (hu00 : u0≠0) (htsM : ts∈Icc 1 M) (htsI : ¬p∣ts) (hts : p∣q*ts-o)
    (hcase : (cut1=k1+n+1 ∧ cut2=k2+n) ∨ (cut1=k1+n ∧ cut2=k2+n+1))
    (hw1 : γ1+(cut1-1)*p<ts ∧ ts≤γ1+cut1*p) (hw2 : γ2+(cut2-1)*p<ts ∧ ts≤γ2+cut2*p) :
    WrapDeform.residue p
      ((ringSystem1 p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u true).det*
        (ringSystem1 p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u false).det-
      (ringSystem1 p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u true).det*
        (ringSystem1 p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u false).det)≠0 := by
  have H1 := profileHyp p q o γ1 k1 η1 n M hγ1 hη1 hk1 hz1 hM hq0 hqp ho0 hoq
  have H2 := profileHyp p q o γ2 k2 η2 n M hγ2 hη2 hk2 hz2 hM hq0 hqp ho0 hoq
  set ev0 := evFrac p (-((((q*ts-o)/p:ℕ):ZMod p))/(q:ZMod p)) with hev0
  have hz : ∀ t∈Icc 1 M,(ev0.comp (specInt p)) (dfac p q o t)=0 ↔ t=ts :=
    fun t ht => evFrac_dfac_eq_zero p q o M ts hM hq0 hqp ho0 hoq htsI hts htsM t ht
  have hev : ∀ k,(ev0.comp (specInt p)) (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k := by
    intro k
    simp [hev0,evFrac,specInt,bconst]
  have hwt : (ev0.comp (specInt p)) (deltaWeight p q o ts)≠0 := by
    simp only [deltaWeight,if_neg htsI,if_pos hts,map_neg,hev,ne_eq,neg_eq_zero,
      map_eq_zero_iff _ (algebraMap (ZMod p) (RatFunc (ZMod p))).injective]
    exact q_zmod_ne p q hq0 hqp
  have hc1 : 1≤cut1 := by rcases hcase with h|h <;> omega
  have hc2 : 1≤cut2 := by rcases hcase with h|h <;> omega
  have hrow (γ k η cut : ℕ) (hγ : γ<p) (hc : 1≤cut) (hw : γ+(cut-1)*p<ts ∧ ts≤γ+cut*p)
      (i : Fin (n+1)) :
      ts≤bordRow (pxr p γ k η n) (pz p γ k n) i ↔ cut≤bordRow (pxr p γ k η n) (pz p γ k n) i/p := by
    rw [bord_quot p _ _ _ _ hγ,bord_node]
    exact central_cut p γ cut ts _ hc hw.1 hw.2
  have hcol (γ k η cut : ℕ) (hγ : γ<p) (hc : 1≤cut) (hw : γ+(cut-1)*p<ts ∧ ts≤γ+cut*p) (c : Fin n) :
      ts≤pyc p γ k η n c ↔ cut≤pyc p γ k η n c/p := by
    rw [col_quot p _ _ _ _ hγ]
    unfold pyc profileColQ
    exact central_cut p γ cut ts _ hc hw.1 hw.2
  have hq (γ k η : ℕ) (hγ : γ<p) (hη : η≤1) (hk : k+2*n<p) (i : Fin (n+1)) (c : Fin n) :
      ((pyc p γ k η n c/p:ℕ):RatFunc (ZMod p))≠((bordRow (pxr p γ k η n) (pz p γ k n) i/p:ℕ):RatFunc (ZMod p)) := by
    rw [col_quot p _ _ _ _ hγ,bord_quot p _ _ _ _ hγ]
    unfold profileColQ profileRowQ
    have := c.2; have := i.2
    split_ifs <;> exact rat_cast_ne p _ _ (by omega) (by omega) (by omega)
  apply residue_cross1_ne H1 H2 s u u0 hs hu0 ev0 ts htsM hz hev cut1 cut2
    (hrow γ1 k1 η1 cut1 hγ1 hc1 hw1) (hcol γ1 k1 η1 cut1 hγ1 hc1 hw1) (hq γ1 k1 η1 hγ1 hη1 hk1)
    (hrow γ2 k2 η2 cut2 hγ2 hc2 hw2) (hcol γ2 k2 η2 cut2 hγ2 hc2 hw2) (hq γ2 k2 η2 hγ2 hη2 hk2)
  set g := centralWeight p q o (ev0.comp (specInt p)) u0 M ts with hgdef
  have hg : g≠0 := by
    rw [hgdef,centralWeight]
    refine mul_ne_zero (mul_ne_zero ?_ hwt) (ev_cofactor_self p q o (ev0.comp (specInt p)) M ts htsM hz)
    exact (_root_.map_ne_zero _).mpr hu00
  have hr1 : (fun i => bordRow (pxr p γ1 k1 η1 n) (pz p γ1 k1 n) i/p)=profileRowQ k1 η1 n :=
    funext (bord_quot p _ _ _ _ hγ1)
  have hr2 : (fun i => bordRow (pxr p γ2 k2 η2 n) (pz p γ2 k2 n) i/p)=profileRowQ k2 η2 n :=
    funext (bord_quot p _ _ _ _ hγ2)
  have hcc1 : (fun c => pyc p γ1 k1 η1 n c/p)=profileColQ k1 η1 n := funext (col_quot p _ _ _ _ hγ1)
  have hcc2 : (fun c => pyc p γ2 k2 η2 n c/p)=profileColQ k2 η2 n := funext (col_quot p _ _ _ _ hγ2)
  rw [hr1,hr2,hcc1,hcc2]
  have hK (k : ℕ) (hk : k+2*n<p) : ∀ a b : ℕ,a≤k+2*n → b≤k+2*n →
      (a:RatFunc (ZMod p))=(b:RatFunc (ZMod p)) → a=b :=
    fun a b ha hb h => rat_cast_inj p (k+2*n) hk a b ha hb h
  rcases hcase with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · obtain ⟨hE1,hD1⟩ := profile_lower (K:=RatFunc (ZMod p)) k1 η1 n hη1 hn (hK k1 hk1)
    obtain ⟨hE2,hD2⟩ := profile_upper (K:=RatFunc (ZMod p)) k2 η2 n hη2 hn (hK k2 hk2)
    exact scaled_cross_ne g hg n _ _ _ _ _ _ 0 1 zero_ne_one hE1 hE2 hD1 hD2
  · obtain ⟨hE1,hD1⟩ := profile_upper (K:=RatFunc (ZMod p)) k1 η1 n hη1 hn (hK k1 hk1)
    obtain ⟨hE2,hD2⟩ := profile_lower (K:=RatFunc (ZMod p)) k2 η2 n hη2 hn (hK k2 hk2)
    exact scaled_cross_ne g hg n _ _ _ _ _ _ 1 0 one_ne_zero hE1 hE2 hD1 hD2

end FractionalSeparation

section FractionalBinding
variable {p : ℕ} [Fact p.Prime]
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Reduced actual ONE-parameter prefix core. -/
noncomputable def coreBar1 (s u : GaussLoc p) := (H.core s u).map (WrapDeform.residue p)

/-- Original one-parameter displacement kills every cross-colour entry. -/
theorem core_cross_zero1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (i j : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hij : H.colour i≠H.colour j) : WrapDeform.residue p (H.core s u i j)=0 := by
  obtain ⟨E,hQE,-,-,-⟩ := WrapPrefixSource.actual_core_source p q o N s u (fun i:Fin r => (i:ℕ))
    H.xs H.ys (single_bound H) H.common_bound H.row_bound H.col_bound H.same_colour
    (H.core_unit s u hs hu huc)
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have he := congrArg (fun Mx => WrapDeform.residue p (Mx i j)) hQE
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] at he
  refine he.trans ?_
  simp only [WrapPrefixSource.own,Matrix.of_apply]
  split_ifs with h
  · exact absurd h hij
  · exact map_zero _

theorem coreBar1_det (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : (coreBar1 H s u).det≠0 := by
  have h := ((H.core_unit s u hs hu huc).map (WrapDeform.residue p)).ne_zero
  rwa [RingHom.map_det] at h

theorem sigma_cross_zero1 (u : GaussLoc p) (t : ℕ) (ht : t<N) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hi : H.colour i≠(t:ZMod p)) : WrapDeform.residue p (H.sigma u t i)=0 := by
  obtain ⟨ev,hv,-,-⟩ := WrapPrefixSource.actual_border_source p q o N t u (WrapPrefixSchur.colNode H)
    (single_bound H) ht (WrapPrefixSchur.col_bound H)
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have he := congrArg (fun f => WrapDeform.residue p (f i)) hv
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] at he
  have hc : ((WrapPrefixSchur.colNode H i:ℕ):ZMod p)≠(t:ZMod p) := by
    rw [show ((WrapPrefixSchur.colNode H i:ℕ):ZMod p)=H.colour i from colNode_colour H i]
    exact hi
  rw [if_neg hc,map_zero] at he
  exact he

theorem colSigma_cross_zero1 (u : GaussLoc p) (t : ℕ) (ht : t<N) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hi : H.colour i≠(t:ZMod p)) : WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)=0 := by
  obtain ⟨ev,hv,-,-⟩ := WrapPrefixSource.actual_border_source p q o N t u (WrapPrefixSchur.rowNode H)
    (single_bound H) ht (WrapPrefixSchur.row_bound H)
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have he := congrArg (fun f => WrapDeform.residue p (f i)) hv
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] at he
  have hc : ((WrapPrefixSchur.rowNode H i:ℕ):ZMod p)≠(t:ZMod p) := by
    rw [show ((WrapPrefixSchur.rowNode H i:ℕ):ZMod p)=H.colour i from rowNode_colour H i]
    exact hi
  rw [if_neg hc,map_zero] at he
  unfold WrapPrefixSchur.columnSigma
  rw [WrapEntryRelation.entry_symm]
  exact he

/-- Profile nodes of the actual one-parameter fibre of an original node `t`. -/
noncomputable def fibreCore1 (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (s u : GaussLoc p) (t : ℕ) :=
  WrapFibreCore.core p q o s u
    (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
    (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (WrapJointProfile.bit p r (t:ZMod p).val) n)
    (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (WrapJointProfile.bit p r (t:ZMod p).val) n)

theorem fibre_blk1 (s u : GaussLoc p) (t : ℕ)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (UFMoments.blk (coreBar1 H s u) H.colour (t:ZMod p)).submatrix
        (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)=
      (fibreCore1 H s u t).map (WrapDeform.residue p) := by
  rw [UFMoments.blk,Matrix.submatrix_submatrix,coreBar1,Matrix.submatrix_map]
  have hw : (H.core s u).submatrix (fun i => (fibreEquiv H (t:ZMod p) hres i).1)
      (fun j => (fibreEquiv H (t:ZMod p) hres j).1)=
      WrapFibreCore.core p q o s u
        (fun i:Fin (WrapJointProfile.count p r (t:ZMod p).val) => (t:ZMod p).val+(i:ℕ)*p)
        (fun c:Fin n => WrapJointProfile.rowProfile p r (t:ZMod p).val c)
        (fun c:Fin n => WrapJointProfile.colProfile p r (t:ZMod p).val c) :=
    WrapJointProfile.whole_core p r n e b d shift q o H.hp H.hp2 s u H.er H.ec (t:ZMod p) hres
  rw [show ((Subtype.val ∘ ⇑(fibreEquiv H (t:ZMod p) hres)):_ → _)=
    (fun i => (fibreEquiv H (t:ZMod p) hres i).1) from rfl,hw]
  congr 1
  unfold fibreCore1
  congr 1
  · funext c; exact rowProfile_eq (p:=p) _ c
  · funext c; exact colProfile_eq (p:=p) _ c

theorem fibreCore1_det_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    ((fibreCore1 H s u t).map (WrapDeform.residue p)).det≠0 := by
  rw [← fibre_blk1 H s u t hres,Matrix.det_submatrix_equiv_self]
  have hb : ∀ a c,H.colour a≠H.colour c → coreBar1 H s u a c=0 :=
    fun a c h => core_cross_zero1 H s u hs hu huc a c h
  exact (UFMoments.inv_restrict (coreBar1 H s u) H.colour
    (isUnit_iff_ne_zero.mpr (coreBar1_det H s u hs hu huc)) hb (t:ZMod p)).1.ne_zero

/-- The actual reduced one-parameter response of node `t` is its ORIGINAL
profile response. -/
theorem fibre_moment1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p))
    (f : ℕ → WrapDeform.Extension p) :
    (fun i => WrapDeform.residue p (H.sigma u t i)) ⬝ᵥ (coreBar1 H s u)⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i)))=
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
            (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
              (WrapJointProfile.bit p r (t:ZMod p).val) n) j))) ⬝ᵥ
        ((fibreCore1 H s u t).map (WrapDeform.residue p))⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (f (Sum.elim
          (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
          (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
            (WrapJointProfile.bit p r (t:ZMod p).val) n) i))) := by
  classical
  have hb : ∀ a c,H.colour a≠H.colour c → coreBar1 H s u a c=0 :=
    fun a c h => core_cross_zero1 H s u hs hu huc a c h
  have hsz : ∀ a,H.colour a≠(t:ZMod p) → WrapDeform.residue p (H.sigma u t a)=0 :=
    fun a h => sigma_cross_zero1 H u t ht a h
  rw [fibre_response (coreBar1 H s u) H.colour (coreBar1_det H s u hs hu huc) hb (t:ZMod p) _ _ hsz]
  rw [← WrapTransport.response_reindex (UFMoments.blk (coreBar1 H s u) H.colour (t:ZMod p))
    (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)]
  have hl : (fun i:{a // H.colour a=(t:ZMod p)} => WrapDeform.residue p (H.sigma u t i.1)) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
            (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
              (WrapJointProfile.bit p r (t:ZMod p).val) n) j)) := by
    funext j
    simp only [Function.comp_apply,WrapPrefixWindow.Setup.sigma]
    rw [fibre_col H (t:ZMod p) hres j]
    rcases j with j|j
    · rfl
    · simp only [Sum.elim_inr]
      rw [colProfile_eq]
  have hr : (fun i:{a // H.colour a=(t:ZMod p)} =>
      WrapDeform.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i.1))) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun i => WrapDeform.residue p (f (Sum.elim
          (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
          (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
            (WrapJointProfile.bit p r (t:ZMod p).val) n) i)) := by
    funext i
    simp only [Function.comp_apply]
    rw [fibre_row H (t:ZMod p) hres i]
    rcases i with i|i
    · rfl
    · simp only [Sum.elim_inr]
      rw [rowProfile_eq]
  rw [fibre_blk1 H s u t hres,hl,hr]

omit [Fact p.Prime] in
theorem core1_transpose {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fact p.Prime] (s u : GaussLoc p) (c : ι → ℕ) (xs ys : κ → ℕ) :
    (WrapFibreCore.core p q o s u c xs ys)ᵀ=WrapFibreCore.core p q o s u c ys xs := by
  ext i j
  simp only [Matrix.transpose_apply,WrapFibreCore.core,Matrix.add_apply,Matrix.of_apply]
  rw [WrapEntryRelation.entry_symm]
  congr 1
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks_apply₁₁,Matrix.one_apply,eq_comm]

/-- The transposed actual one-parameter fibre is the fibre with the
complementary bit. -/
theorem fibreCore1_transpose (s u : GaussLoc p) (t : ℕ) :
    (fibreCore1 H s u t)ᵀ=WrapFibreCore.core p q o s u
      (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
      (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)
      (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) := by
  unfold fibreCore1
  rw [core1_transpose,_root_.funext (pxr_flip (p:=p) _ _ _ n),
    _root_.funext (pyc_flip (p:=p) _ _ _ n (bit_le _))]

/-- The actual reduced one-parameter COLUMN response of node `t` is the
ORIGINAL profile response of its fibre with the complementary bit. -/
theorem col_fibre_moment1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p))
    (f : ℕ → WrapDeform.Extension p) :
    (fun i => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)) ⬝ᵥ (coreBar1 H s u)ᵀ⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)))=
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((WrapFibreCore.core p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (WrapDeform.residue p))⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (f (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i))) := by
  classical
  have hbT : ∀ a c,H.colour a≠H.colour c → (coreBar1 H s u)ᵀ a c=0 :=
    fun a c h => core_cross_zero1 H s u hs hu huc c a (Ne.symm h)
  have hdetT : (coreBar1 H s u)ᵀ.det≠0 := by
    rw [Matrix.det_transpose]; exact coreBar1_det H s u hs hu huc
  have hsz : ∀ a,H.colour a≠(t:ZMod p) → WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t a)=0 :=
    fun a h => colSigma_cross_zero1 H u t ht a h
  rw [fibre_response (coreBar1 H s u)ᵀ H.colour hdetT hbT (t:ZMod p) _ _ hsz]
  rw [← WrapTransport.response_reindex (UFMoments.blk (coreBar1 H s u)ᵀ H.colour (t:ZMod p))
    (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)]
  have hblk : (UFMoments.blk (coreBar1 H s u)ᵀ H.colour (t:ZMod p)).submatrix
      (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)=
      (WrapFibreCore.core p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (WrapDeform.residue p) := by
    have h1 : UFMoments.blk (coreBar1 H s u)ᵀ H.colour (t:ZMod p)=
        (UFMoments.blk (coreBar1 H s u) H.colour (t:ZMod p))ᵀ := rfl
    rw [h1,← Matrix.transpose_submatrix,fibre_blk1 H s u t hres,← Matrix.transpose_map,fibreCore1_transpose]
  have hl : (fun i:{a // H.colour a=(t:ZMod p)} => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i.1)) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j)) := by
    funext j
    simp only [Function.comp_apply,WrapPrefixSchur.columnSigma,WrapPrefixSchur.rowNode]
    rw [fibre_row H (t:ZMod p) hres j,WrapEntryRelation.entry_symm]
    rcases j with j|j
    · rfl
    · simp only [Sum.elim_inr]
      rw [rowProfile_eq,pyc_flip _ _ _ _ (bit_le _)]
  have hr : (fun i:{a // H.colour a=(t:ZMod p)} =>
      WrapDeform.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i.1))) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun i => WrapDeform.residue p (f (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i)) := by
    funext i
    simp only [Function.comp_apply]
    rw [fibre_col H (t:ZMod p) hres i]
    rcases i with i|i
    · rfl
    · simp only [Sum.elim_inr]
      rw [colProfile_eq,pxr_flip]
  rw [hblk,hl,hr]

theorem colFibre1_det_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    ((WrapFibreCore.core p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (WrapDeform.residue p)).det≠0 := by
  rw [← fibreCore1_transpose,Matrix.transpose_map,Matrix.det_transpose]
  exact fibreCore1_det_ne H s u hs hu huc t hres

theorem residue_rowMoment1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    WrapDeform.residue p (WrapPrefixSchur.rowMoment H s u t)=
      WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)-
        (fun i => WrapDeform.residue p (H.sigma u t i)) ⬝ᵥ (coreBar1 H s u)⁻¹ *ᵥ
          (fun i => WrapDeform.residue p (H.rowLoad u i)) := by
  rw [WrapPrefixSchur.rowMoment,map_sub,residue_response _ _ (H.core_unit s u hs hu huc)]
  rfl

theorem residue_rowRef1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    WrapDeform.residue p (WrapPrefixSchur.rowReference H s u t)=
      1-(fun i => WrapDeform.residue p (H.sigma u t i)) ⬝ᵥ (coreBar1 H s u)⁻¹ *ᵥ 1 := by
  rw [WrapPrefixSchur.rowReference,map_sub,map_one,residue_response _ _ (H.core_unit s u hs hu huc)]
  simp only [Pi.one_apply,map_one]
  rfl

theorem residue_colMoment1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    WrapDeform.residue p (WrapPrefixSchur.colMoment H s u t)=
      WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)-
        (fun i => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)) ⬝ᵥ (coreBar1 H s u)ᵀ⁻¹ *ᵥ
          (fun i => WrapDeform.residue p (H.colLoad u i)) := by
  rw [WrapPrefixSchur.colMoment,map_sub,residue_response _ _ (H.core_unit s u hs hu huc),
    dot_transpose,Matrix.transpose_nonsing_inv]
  rfl

theorem residue_colRef1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    WrapDeform.residue p (WrapPrefixSchur.colReference H s u t)=
      1-(fun i => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)) ⬝ᵥ (coreBar1 H s u)ᵀ⁻¹ *ᵥ 1 := by
  rw [WrapPrefixSchur.colReference,map_sub,map_one,residue_response _ _ (H.core_unit s u hs hu huc),
    dot_transpose,Matrix.transpose_nonsing_inv]
  simp only [Pi.one_apply,map_one]
  rfl

/-- Profile border and load of node `t` (one-parameter residues). -/
noncomputable def fibreSigma1 (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (u : GaussLoc p) (t : ℕ) :
    Fin (WrapJointProfile.count p r (t:ZMod p).val) ⊕ Fin n → WrapPoleResidue.Residue p :=
  fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
    (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
      (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
        (WrapJointProfile.bit p r (t:ZMod p).val) n) j))

noncomputable def fibreLoad1 (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (u : GaussLoc p) (t : ℕ) :
    Fin (WrapJointProfile.count p r (t:ZMod p).val) ⊕ Fin n → WrapPoleResidue.Residue p :=
  fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
    (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
      (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
        (WrapJointProfile.bit p r (t:ZMod p).val) n) i))

theorem fibre_load1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => WrapDeform.residue p (H.sigma u t i)) ⬝ᵥ (coreBar1 H s u)⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (H.rowLoad u i))=
      fibreSigma1 H u t ⬝ᵥ ((fibreCore1 H s u t).map (WrapDeform.residue p))⁻¹ *ᵥ fibreLoad1 H u t :=
  fibre_moment1 H s u hs hu huc t ht hres
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a)

theorem fibre_one1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => WrapDeform.residue p (H.sigma u t i)) ⬝ᵥ (coreBar1 H s u)⁻¹ *ᵥ 1=
      fibreSigma1 H u t ⬝ᵥ ((fibreCore1 H s u t).map (WrapDeform.residue p))⁻¹ *ᵥ 1 := by
  have h := fibre_moment1 H s u hs hu huc t ht hres (fun _ => (1:WrapDeform.Extension p))
  simp only [map_one] at h
  exact h

theorem col_fibre_load1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)) ⬝ᵥ (coreBar1 H s u)ᵀ⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (H.colLoad u i))=
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((WrapFibreCore.core p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (WrapDeform.residue p))⁻¹ *ᵥ
        (fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i))) :=
  col_fibre_moment1 H s u hs hu huc t ht hres
    (fun a => WrapOwnCore.constants p u*WrapEntryRelation.load p q o a)

theorem col_fibre_one1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => WrapDeform.residue p (WrapPrefixSchur.columnSigma H u t i)) ⬝ᵥ (coreBar1 H s u)ᵀ⁻¹ *ᵥ 1=
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((WrapFibreCore.core p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (WrapDeform.residue p))⁻¹ *ᵥ 1 := by
  have h := col_fibre_moment1 H s u hs hu huc t ht hres (fun _ => (1:WrapDeform.Extension p))
  simp only [map_one] at h
  exact h

omit [Fact p.Prime] in
theorem profile_core_eq1 [Fact p.Prime] (s u : GaussLoc p) (γ : ℕ) :
    WrapPrefixType.core p q o r (WrapJointProfile.count p r γ) n γ s u=
      WrapFibreCore.core p q o s u (pcn p γ (WrapJointProfile.count p r γ))
        (pxr p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n)
        (pyc p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n) := by
  unfold WrapPrefixType.core
  congr 1
  · funext c; exact rowProfile_eq (p:=p) _ c
  · funext c; exact colProfile_eq (p:=p) _ c

theorem profile_rows_eq1 (γ : ℕ) :
    WrapPrefixType.rows p r (WrapJointProfile.count p r γ) n γ=
      Sum.elim (pcn p γ (WrapJointProfile.count p r γ))
        (pxr p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n) := by
  unfold WrapPrefixType.rows
  congr 1
  funext c; exact rowProfile_eq (p:=p) _ c

theorem profile_cols_eq1 (γ : ℕ) :
    WrapPrefixType.cols p r (WrapJointProfile.count p r γ) n γ=
      Sum.elim (pcn p γ (WrapJointProfile.count p r γ))
        (pyc p γ (WrapJointProfile.count p r γ) (WrapJointProfile.bit p r γ) n) := by
  unfold WrapPrefixType.cols
  congr 1
  funext c; exact colProfile_eq (p:=p) _ c

/-- The actual original one-parameter anchor, in fibre form, together with
its nonzero reduced reference. -/
theorem residue_anchor1 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    WrapDeform.residue p (H.anchor s u)=
      (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o H.t0)-
        fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ fibreLoad1 H u H.t0)*
      (1-fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ 1)⁻¹ ∧
    1-fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ 1≠0 := by
  have hm0 : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have hres0 := fun i => H.hfree H.t0 hm0 i
  have hQ : IsUnit (fibreCore1 H s u H.t0).det :=
    WrapBalancedTest.unit_ne p _ (by rw [RingHom.map_det]; exact fibreCore1_det_ne H s u hs hu huc H.t0 hres0)
  obtain ⟨G1,-,-,hB⟩ := H.arithmetic_source H.t0 hm0 s u hs hu huc
  have hcore : WrapPrefixType.core p q o r (WrapJointProfile.count p r (H.t0:ZMod p).val) n
      (H.t0:ZMod p).val s u=fibreCore1 H s u H.t0 :=
    profile_core_eq1 (q:=q) (o:=o) (r:=r) (n:=n) s u (H.t0:ZMod p).val
  have hrows := profile_rows_eq1 (p:=p) (r:=r) (n:=n) (H.t0:ZMod p).val
  have hcols := profile_cols_eq1 (p:=p) (r:=r) (n:=n) (H.t0:ZMod p).val
  change WrapDeform.residue p (WrapPrefixWindow.reference p q o r
    (WrapJointProfile.count p r (H.t0:ZMod p).val) n (H.t0:ZMod p).val H.t0 s u)≠0 at hB
  have hBu := WrapBalancedTest.unit_ne p _ hB
  have href : WrapDeform.residue p (WrapPrefixWindow.reference p q o r
      (WrapJointProfile.count p r (H.t0:ZMod p).val) n (H.t0:ZMod p).val H.t0 s u)=
      1-fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ 1 := by
    rw [WrapPrefixWindow.reference,hcols,hcore,map_sub,map_one,residue_response _ _ hQ]
    simp only [Pi.one_apply,map_one]
    rfl
  have ha : H.anchor s u=WrapPrefixWindow.anchorDirection p q o r
      (WrapJointProfile.count p r (H.t0:ZMod p).val) n (H.t0:ZMod p).val H.t0 s u := rfl
  refine ⟨?_,href ▸ hB⟩
  rw [ha,WrapPrefixWindow.anchorDirection,map_mul,WrapPoleResidue.inverse _ _ hBu,href,
    hrows,hcols,hcore,map_sub,residue_response _ _ hQ]
  rfl

end FractionalBinding

section FractionalKills
variable {p : ℕ} [Fact p.Prime]
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

set_option maxHeartbeats 2000000 in
/-- Binding of a separated pair of fibre directions to the actual
one-parameter coupling at an outside node `v` against the original anchor:
the common tail of the fractional (R2) and the integer (R3) kills. -/
theorem node_coupling1_of_cross (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (v η : ℕ)
    (hvlo : r+2*n*p≤v) (hvhi : v<r+2*n*p+p) (hvN : v<N)
    (hPv : ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p)).det≠0)
    (hps : WrapDeform.residue p
      ((ringSystem1 p q o (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) v s u true).det*
        (ringSystem1 p q o (pcn p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val)) (pxr p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val) n) (pyc p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val) n) H.t0 s u false).det-
      (ringSystem1 p q o (pcn p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val)) (pxr p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val) n) (pyc p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val) n) H.t0 s u true).det*
        (ringSystem1 p q o (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) v s u false).det)≠0) :
    (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o v)-
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ
      (fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))-
    WrapDeform.residue p (H.anchor s u)*
    (1-(fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ 1)≠0 := by
  classical
  have hres0 : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(H.t0:ZMod p) :=
    fun i => H.hfree H.t0 (mem_Icc.mpr ⟨le_rfl,H.hle⟩) i
  have hP0 := fibreCore1_det_ne H s u hs hu huc H.t0 hres0
  have hRvT := residue_ringSystem1_det p q o _ _ _ v s u true hPv
  have hRvF := residue_ringSystem1_det p q o _ _ _ v s u false hPv
  have hR0T := residue_ringSystem1_det p q o _ _ _ H.t0 s u true hP0
  have hR0F := residue_ringSystem1_det p q o _ _ _ H.t0 s u false hP0
  simp only [↓reduceIte,Bool.false_eq_true,map_one] at hRvT hRvF hR0T hR0F
  obtain ⟨hanc,hr0⟩ := residue_anchor1 H s u hs hu huc
  rw [hanc]
  intro hc
  apply hps
  rw [map_sub,map_mul,map_mul]
  have key := coupling_cross ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p)).det
    ((fibreCore1 H s u H.t0).map (WrapDeform.residue p)).det
    (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o v)-
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ
      (fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))
    (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o H.t0)-
      fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ fibreLoad1 H u H.t0)
    (1-(fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ 1)
    (1-fibreSigma1 H u H.t0 ⬝ᵥ ((fibreCore1 H s u H.t0).map (WrapDeform.residue p))⁻¹ *ᵥ 1) hr0
  rw [hc,zero_mul,zero_mul,zero_mul] at key
  rw [hRvT,hRvF,hR0T,hR0F]
  exact key.symm

set_option maxHeartbeats 2000000 in
/-- Section 8.3 in the ONE-parameter ring at an actual outside node `v`
with fibre bit `η`, separated from the anchor by an original FRACTIONAL
pole `k`: the actual reduced coupling against the original anchor is
nonzero. The integer family is undeformed; only the fractional parameter
is evaluated (at the central pole), on ORIGINAL cleared numerators. -/
theorem node_coupling1_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (v k η : ℕ) (hη : η≤1)
    (hkI : ¬p∣k) (hkF : p∣q*k-o)
    (hsep : (v<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤v))
    (hvlo : r+2*n*p≤v) (hvhi : v<r+2*n*p+p) (hvN : v<N)
    (hPv : ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p)).det≠0) :
    (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o v)-
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ
      (fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))-
    WrapDeform.residue p (H.anchor s u)*
    (1-(fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ 1)≠0 := by
  classical
  obtain ⟨u0,hu0'⟩ := huc
  have huc : WrapConstant.Has p u := ⟨u0,hu0'⟩
  have hu0 := residue_constants1 p u u0 hu0'
  have hu00 : u0≠0 := by
    intro h; apply hu; rw [hu0',h,map_zero]
  have ht0N : H.t0<N := lt_of_le_of_lt H.hle H.htvN
  have ht0lo := H.hlo
  have ht0hi : H.t0<r+2*n*p+p := lt_of_le_of_lt H.hle H.hhi
  have ho0 : 0<o := by
    rcases Nat.eq_zero_or_pos o with h|h
    · exact absurd (by rw [h]; simp) H.ho
    · exact h
  have htv := (fibre_tip (p:=p) (r:=r) (n:=n) v hvlo hvhi).symm
  have ht0 := (fibre_tip (p:=p) (r:=r) (n:=n) H.t0 ht0lo ht0hi).symm
  unfold pz at htv ht0
  have hNp : N<p*p := single_bound H
  have hkv : WrapJointProfile.count p r (v:ZMod p).val+2*n<p := by
    by_contra hc
    have : p*p≤(WrapJointProfile.count p r (v:ZMod p).val+2*n)*p := Nat.mul_le_mul_right p (by omega)
    omega
  have hk0 : WrapJointProfile.count p r (H.t0:ZMod p).val+2*n<p := by
    by_contra hc
    have : p*p≤(WrapJointProfile.count p r (H.t0:ZMod p).val+2*n)*p := Nat.mul_le_mul_right p (by omega)
    omega
  have hnp : n*p≤k := by
    have : n*p≤2*n*p := by nlinarith
    rcases hsep with h|h <;> omega
  have hts1 : 1≤k-n*p := by
    have : n*p+n*p=2*n*p := by ring
    rcases hsep with h|h <;> omega
  have htsN : k-n*p≤N := by rcases hsep with h|h <;> omega
  have hle : o≤q*(k-n*p) := by
    have := Nat.le_mul_of_pos_right q hts1
    have := H.hoq
    omega
  have hqk : q*(k-n*p)-o=(q*k-o)-q*n*p := by
    rw [Nat.mul_sub]
    have : q*(n*p)=q*n*p := by ring
    rw [this]
    have : q*n*p≤q*k := by rw [mul_assoc]; exact Nat.mul_le_mul_left q hnp
    omega
  have hF' : p∣q*(k-n*p)-o := by
    rw [hqk]
    exact Nat.dvd_sub hkF (Dvd.intro_left (q*n) (by ring))
  have hI' : ¬p∣k-n*p := by
    intro hI
    apply hkI
    have := Nat.dvd_add hI (Dvd.intro_left n rfl : p∣n*p)
    rwa [Nat.sub_add_cancel hnp] at this
  have hpzv : pz p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) n=v := by
    unfold pz; exact htv.symm
  have hpz0 : pz p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) n=H.t0 := by
    unfold pz; exact ht0.symm
  have hz1 : pz p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) n≤N := by
    rw [hpzv]; exact hvN.le
  have hz2 : pz p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) n≤N := by
    rw [hpz0]; exact ht0N.le
  obtain ⟨cut1,cut2,hcase,hw1,hw2⟩ : ∃ cut1 cut2,
      ((cut1=WrapJointProfile.count p r (v:ZMod p).val+n+1 ∧ cut2=WrapJointProfile.count p r (H.t0:ZMod p).val+n) ∨
        (cut1=WrapJointProfile.count p r (v:ZMod p).val+n ∧ cut2=WrapJointProfile.count p r (H.t0:ZMod p).val+n+1)) ∧
      ((v:ZMod p).val+(cut1-1)*p<k-n*p ∧ k-n*p≤(v:ZMod p).val+cut1*p) ∧
      ((H.t0:ZMod p).val+(cut2-1)*p<k-n*p ∧ k-n*p≤(H.t0:ZMod p).val+cut2*p) := by
    rcases hsep with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact ⟨_,_,Or.inl ⟨rfl,rfl⟩,lower_window _ _ n p v k htv h1 (by omega),
        upper_window _ _ n p H.t0 k H.hn ht0 (by omega) h2 hnp⟩
    · exact ⟨_,_,Or.inr ⟨rfl,rfl⟩,upper_window _ _ n p v k H.hn htv (by omega) h2 hnp,
        lower_window _ _ n p H.t0 k ht0 h1 (by omega)⟩
  have hps := profile_separation_frac p q o (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)
    η (H.t0:ZMod p).val
    (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val)
    n N (k-n*p) cut1 cut2 s u u0 (ZMod.val_lt _) (ZMod.val_lt _) hη (bit_le _) H.hn hkv hk0
    hz1 hz2 H.hN H.hq0 H.hqp ho0 H.hoq hs hu0 hu00 (mem_Icc.mpr ⟨hts1,htsN⟩) hI' hF' hcase hw1 hw2
  rw [hpzv,hpz0] at hps
  exact node_coupling1_of_cross H s u hs hu huc v η hvlo hvhi hvN hPv hps

/-- R2, ACTUAL one-parameter kill: an outside surplus ROW separated from the
anchor by an original FRACTIONAL pole has nonzero actual coupling. -/
theorem rowCoupling_frac_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z : Fin d) (k : ℕ)
    (hkI : ¬p∣k) (hkF : p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusRow H z<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusRow H z))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusRow H z)
    (hvhi : WrapPrefixSchur.surplusRow H z<r+2*n*p+p) :
    WrapPrefixSchur.rowCoupling H s u z≠0 := by
  have hvN : WrapPrefixSchur.surplusRow H z<N := WrapPrefixSchur.surplus_row_bound H z
  have hresv := surplus_not_residual H z
  unfold WrapPrefixSchur.rowCoupling
  rw [map_sub,map_mul,residue_rowMoment1 H s u hs hu huc,residue_rowRef1 H s u hs hu huc,
    fibre_load1 H s u hs hu huc _ hvN hresv,fibre_one1 H s u hs hu huc _ hvN hresv]
  exact node_coupling1_ne H s u hs hu huc _ k _ (bit_le _) hkI hkF hsep hvlo hvhi hvN
    (fibreCore1_det_ne H s u hs hu huc _ hresv)

/-- R2, ACTUAL one-parameter kill: an outside surplus COLUMN separated from
the anchor by an original FRACTIONAL pole has nonzero actual coupling (its
column fibre is the actual fibre with the complementary bit). -/
theorem colCoupling_frac_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (y : Fin d) (k : ℕ)
    (hkI : ¬p∣k) (hkF : p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusCol H y<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusCol H y))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusCol H y)
    (hvhi : WrapPrefixSchur.surplusCol H y<r+2*n*p+p) :
    WrapPrefixSchur.colCoupling H s u y≠0 := by
  have hvN : WrapPrefixSchur.surplusCol H y<N := WrapPrefixSchur.surplus_col_bound H y
  have hresv := surplus_col_not_residual H y
  unfold WrapPrefixSchur.colCoupling
  rw [map_sub,map_mul,residue_colMoment1 H s u hs hu huc,residue_colRef1 H s u hs hu huc,
    col_fibre_load1 H s u hs hu huc _ hvN hresv,col_fibre_one1 H s u hs hu huc _ hvN hresv]
  exact node_coupling1_ne H s u hs hu huc _ k _ (by omega) hkI hkF hsep hvlo hvhi hvN
    (colFibre1_det_ne H s u hs hu huc _ hresv)


end FractionalKills

-- R2_END_MARKER

/-! ## R3 / Harmonic Lemma (HARMONIC-LEMMA.md), generic field part

Finite differences of the shifted harmonic load `ℓ_A(s) = Σ_{h<s} 1/(A+h)`
(L4), the binomial Leibniz rule (L5), and the Cauchy uniqueness step of
Theorem B: a degree-`<n` denominator whose product with `ℓ_A` has vanishing
differences of orders `n+1..2n` is zero. -/

section HarmonicLemma
open fwdDiff
variable {F : Type*} [Field F]

/-- Explicit `m`-th forward difference at `y`. -/
noncomputable def fd (g : ℕ → F) (m y : ℕ) : F :=
  ∑ s∈range (m+1),(-1:F)^(m-s)*(m.choose s:F)*g (y+s)

theorem fd_eq (g : ℕ → F) (m y : ℕ) : fd g m y=(Δ_[1])^[m] g y := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold fd
  apply Finset.sum_congr rfl
  intro s _
  rw [zsmul_eq_mul,smul_eq_mul,mul_one]
  push_cast
  ring

theorem fd_succ (g : ℕ → F) (m y : ℕ) : fd g (m+1) y=fd g m (y+1)-fd g m y := by
  rw [fd_eq,fd_eq,fd_eq,Function.iterate_succ_apply']
  rfl

theorem fd_zero (g : ℕ → F) (y : ℕ) : fd g 0 y=g y := by
  simp [fd]

theorem fd_sum {ι : Type*} (t : Finset ι) (a : ι → F) (g : ι → ℕ → F) (m y : ℕ) :
    fd (fun s => ∑ i∈t,a i*g i s) m y=∑ i∈t,a i*fd (g i) m y := by
  unfold fd
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The shifted harmonic load. -/
noncomputable def hload (A : F) (s : ℕ) : F := ∑ h∈range s,1/(A+(h:F))

/-- Rising product `(a)_j`. -/
noncomputable def rise (a : F) (j : ℕ) : F := ∏ i∈range j,(a+(i:F))

theorem rise_succ (a : F) (j : ℕ) : rise a (j+1)=rise a j*(a+j) := by
  simp only [rise,Finset.prod_range_succ]

theorem rise_succ' (a : F) (j : ℕ) : rise a (j+1)=a*rise (a+1) j := by
  simp only [rise]
  rw [Finset.prod_range_succ',mul_comm]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring

theorem rise_add (a : F) (j l : ℕ) : rise a (j+l)=rise a j*rise (a+j) l := by
  simp only [rise]
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring

theorem rise_ne (a : F) (j : ℕ) (h : ∀ i<j,a+(i:F)≠0) : rise a j≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun i hi => h i (Finset.mem_range.mp hi))

/-- L4: `Δ^{j+1} ℓ_A(k) = (-1)^j j! / (A+k)_{j+1}`. -/
theorem hload_fd (A : F) (j k : ℕ) (hA : ∀ i≤j,A+((k+i:ℕ):F)≠0) :
    fd (hload A) (j+1) k=(-1)^j*(j.factorial:F)/rise (A+k) (j+1) := by
  induction j generalizing k with
  | zero =>
    rw [fd_succ,fd_zero,fd_zero]
    have h0 := hA 0 le_rfl
    simp only [Nat.add_zero] at h0
    simp only [hload,Finset.sum_range_succ,rise,Finset.prod_range_succ,Finset.prod_range_zero,
      pow_zero,Nat.factorial_zero,Nat.cast_one,Nat.cast_zero,add_zero,one_mul]
    ring
  | succ j ih =>
    rw [fd_succ,ih (k+1) (fun i hi => by
        have := hA (i+1) (by omega)
        rwa [show k+1+i=k+(i+1) by omega]),
      ih k (fun i hi => hA i (by omega))]
    have hne (i : ℕ) (hi : i≤j+1) : A+(k:F)+(i:F)≠0 := by
      have := hA i hi; push_cast at this; rwa [← add_assoc] at this
    have hR : rise (A+(k:F)) (j+2)≠0 :=
      rise_ne _ _ (fun i hi => hne i (by omega))
    have hR0 : rise (A+(k:F)) (j+1)≠0 :=
      rise_ne _ _ (fun i hi => hne i (by omega))
    have hR1 : rise (A+((k+1:ℕ):F)) (j+1)≠0 := by
      apply rise_ne
      intro i hi
      have := hne (i+1) (by omega)
      push_cast at this ⊢
      rw [show A+((k:F)+1)+(i:F)=A+(k:F)+((i:F)+1) by ring]
      exact this
    have h1 : rise (A+(k:F)) (j+2)=(A+(k:F))*rise (A+((k+1:ℕ):F)) (j+1) := by
      rw [rise_succ']
      push_cast
      ring_nf
    have h2 : rise (A+(k:F)) (j+2)=rise (A+(k:F)) (j+1)*(A+(k:F)+((j+1:ℕ):F)) := by
      rw [rise_succ]
    rw [div_sub_div _ _ hR1 hR0,div_eq_div_iff (mul_ne_zero hR1 hR0) hR,Nat.factorial_succ]
    push_cast at h1 h2 ⊢
    linear_combination ((-1:F)^j*(j.factorial:F)*rise (A+(k:F)) (j+1))*h1-
      ((-1:F)^j*(j.factorial:F)*rise (A+((k:F)+1)) (j+1))*h2

/-- L5 (binomial form): `Δ^m[C(·,k) f](0) = C(m,k) Δ^{m-k} f(k)`. -/
theorem fd_choose_mul (f : ℕ → F) (m k : ℕ) (hk : k≤m) :
    fd (fun s => (s.choose k:F)*f s) m 0=(m.choose k:F)*fd f (m-k) k := by
  unfold fd
  have hsplit : m+1=k+(m-k+1) := by omega
  rw [hsplit,Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun s hs => by
    simp only [zero_add,Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hs),Nat.cast_zero,zero_mul,
      mul_zero]),zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  have hc : m.choose (k+r)*(k+r).choose k=m.choose k*(m-k).choose r := by
    rw [Nat.choose_mul (by omega)]
    congr 2
    omega
  have hc' : (m.choose (k+r):F)*((k+r).choose k:F)=(m.choose k:F)*((m-k).choose r:F) := by
    have := congrArg (fun x:ℕ => (x:F)) hc
    push_cast at this
    exact this
  have he : m-(k+r)=m-k-r := by omega
  rw [he,zero_add]
  linear_combination ((-1:F)^(m-k-r)*f (k+r))*hc'

theorem cast_ne_of_le (n a b : ℕ) (hk : ∀ k,1≤k → k≤2*n → (k:F)≠0) (ha : a≤2*n) (hb : b≤2*n)
    (hab : a≠b) : (a:F)≠(b:F) := by
  intro h
  rcases Nat.lt_or_gt_of_ne hab with h'|h'
  · apply hk (b-a) (by omega) (by omega)
    rw [Nat.cast_sub h'.le,h,sub_self]
  · apply hk (a-b) (by omega) (by omega)
    rw [Nat.cast_sub h'.le,h,sub_self]

theorem fact_ne (n m : ℕ) (hk : ∀ k,1≤k → k≤2*n → (k:F)≠0) (hm : m≤2*n) :
    (m.factorial:F)≠0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ,Nat.cast_mul]
    exact mul_ne_zero (hk (m+1) (by omega) hm) (ih (by omega))

/-- The single difference term of Theorem B in normalised Cauchy form. -/
theorem harmonic_term (A : F) (n m k : ℕ) (hkm : k<m) (hm : m≤2*n)
    (hk : ∀ k,1≤k → k≤2*n → (k:F)≠0) (hA : ∀ h<2*n,A+(h:F)≠0) :
    (m.choose k:F)*fd (hload A) (m-k) k=
      ((-1:F)^(m-1)*(m.factorial:F)/rise A m)*
        (((-1:F)^k*rise A k/(k.factorial:F))/((m:F)-(k:F))) := by
  obtain ⟨j,rfl⟩ : ∃ j,m=k+j+1 := ⟨m-k-1,by omega⟩
  rw [show k+j+1-k=j+1 by omega,hload_fd A j k (fun i hi => by
    have := hA (k+i) (by omega); push_cast at this ⊢; exact this)]
  have hfac : (((k+j+1).choose k:ℕ):F)*(k.factorial:F)*((j+1).factorial:F)=((k+j+1).factorial:F) := by
    have := Nat.choose_mul_factorial_mul_factorial (show k≤k+j+1 by omega)
    rw [show k+j+1-k=j+1 by omega] at this
    have h' := congrArg (fun x:ℕ => (x:F)) this
    push_cast at h'
    exact h'
  have hfac2 : ((j+1).factorial:F)=((j:F)+1)*(j.factorial:F) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hrise : rise A (k+j+1)=rise A k*rise (A+(k:F)) (j+1) := by
    rw [show k+j+1=k+(j+1) by omega,rise_add]
  have hRk : rise A k≠0 := rise_ne _ _ (fun i hi => hA i (by omega))
  have hRj : rise (A+(k:F)) (j+1)≠0 := rise_ne _ _ (fun i hi => by
    have := hA (k+i) (by omega); push_cast at this; rwa [add_assoc])
  have hkf : (k.factorial:F)≠0 := fact_ne n k hk (by omega)
  have hj1 : (j:F)+1≠0 := by
    have := hk (j+1) (by omega) (by omega); push_cast at this; exact this
  have hd : ((k+j+1:ℕ):F)-(k:F)=(j:F)+1 := by push_cast; ring
  have hsgn : (-1:F)^(k+j+1-1)=(-1:F)^j*(-1:F)^k := by
    rw [show k+j+1-1=j+k by omega,pow_add]
  rw [hd,hsgn,hrise]
  have hσ : (-1:F)^k*(-1:F)^k=1 := by rw [← pow_add,← two_mul,pow_mul]; norm_num
  have hm : ((k+j+1).factorial:F)=((k+j+1).choose k:F)*(k.factorial:F)*(((j:F)+1)*(j.factorial:F)) := by
    rw [← hfac2]; exact hfac.symm
  rw [hm]
  have key : ((k+j+1).choose k:F)*((-1:F)^j*(j.factorial:F)/rise (A+(k:F)) (j+1))*((-1:F)^k*(-1:F)^k)=
      ((-1:F)^j*(-1:F)^k*(((k+j+1).choose k:F)*(k.factorial:F)*(((j:F)+1)*(j.factorial:F)))/
        (rise A k*rise (A+(k:F)) (j+1)))*(((-1:F)^k*rise A k/(k.factorial:F))/((j:F)+1)) := by
    field_simp
  rw [hσ,mul_one] at key
  exact key

/-- Cauchy uniqueness (Theorem B, homogeneous part): a binomial-basis
denominator of degree `< n` whose product with `ℓ_A` has vanishing
differences of orders `n+1, …, 2n` is zero. -/
theorem harmonic_uniq (A : F) (n : ℕ) (hk : ∀ k,1≤k → k≤2*n → (k:F)≠0)
    (hA : ∀ h<2*n,A+(h:F)≠0) (d : ℕ → F)
    (hz : ∀ m,n+1≤m → m≤2*n → fd (fun s => ∑ k∈range n,d k*((s.choose k:F)*hload A s)) m 0=0) :
    ∀ k<n,d k=0 := by
  classical
  let e : Fin n → F := fun k => d k*((-1:F)^(k:ℕ)*rise A k/((k:ℕ).factorial:F))
  have hcm (m : ℕ) (h1 : n+1≤m) (h2 : m≤2*n) : (-1:F)^(m-1)*(m.factorial:F)/rise A m≠0 := by
    have hR : rise A m≠0 := rise_ne _ _ (fun i hi => hA i (by omega))
    have hmf : (m.factorial:F)≠0 := fact_ne n m hk h2
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hmf) hR
  have hsys : (WrapCauchy.matrix (fun i:Fin n => ((n+1+(i:ℕ):ℕ):F)) (fun k:Fin n => ((k:ℕ):F))) *ᵥ e=0 := by
    funext i
    have h := hz (n+1+(i:ℕ)) (by omega) (by have := i.2; omega)
    rw [fd_sum] at h
    have h' : ∑ k∈range n,d k*(((n+1+(i:ℕ)).choose k:F)*fd (hload A) (n+1+(i:ℕ)-k) k)=0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro k hk'
      rw [fd_choose_mul (hload A) _ _ (by have := Finset.mem_range.mp hk'; omega)]
    have h'' : ((-1:F)^(n+1+(i:ℕ)-1)*((n+1+(i:ℕ)).factorial:F)/rise A (n+1+(i:ℕ)))*
        ∑ k∈range n,d k*(((-1:F)^k*rise A k/(k.factorial:F))/(((n+1+(i:ℕ):ℕ):F)-(k:F)))=0 := by
      rw [← h',Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk'
      have hk2 := Finset.mem_range.mp hk'
      rw [harmonic_term A n (n+1+(i:ℕ)) k (by omega) (by have := i.2; omega) hk hA]
      ring
    have hs := (mul_eq_zero.mp h'').resolve_left (hcm _ (by omega) (by have := i.2; omega))
    simp only [Matrix.mulVec,dotProduct,WrapCauchy.matrix,Matrix.of_apply,Pi.zero_apply]
    rw [← hs,← Fin.sum_univ_eq_sum_range (fun k => d k*(((-1:F)^k*rise A k/(k.factorial:F))/
      (((n+1+(i:ℕ):ℕ):F)-(k:F))))]
    apply Finset.sum_congr rfl
    intro k _
    simp only [e]
    ring
  have hdet := WrapCauchy.det_ne (fun i:Fin n => ((n+1+(i:ℕ):ℕ):F)) (fun k:Fin n => ((k:ℕ):F))
    (fun a b h => Fin.ext (by
      by_contra hne
      exact cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega)
        (by intro h'; apply hne; omega) h))
    (fun a b h => Fin.ext (by
      by_contra hne
      exact cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega) hne h))
    (fun a b h => cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega)
      (by have := b.2; omega) h)
  have he0 : e=0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hsys
  intro k hkn
  have hek := congrFun he0 ⟨k,hkn⟩
  simp only [e,Pi.zero_apply] at hek
  have hRk : rise A k≠0 := rise_ne _ _ (fun i hi => hA i (by omega))
  have hkf : (k.factorial:F)≠0 := fact_ne n k hk (by omega)
  exact (mul_eq_zero.mp hek).resolve_right
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hRk) hkf)

end HarmonicLemma

/-! ## R3 / Harmonic Lemma: Theorem A (arbitrary split) and the harmonic
bordered system.  The bordered matrix `[Q | col]` on row nodes `xs` and
column nodes `ys` (an ARBITRARY split of `κ..κ+2n`) with harmonic load
`L(κ+s) = c + ℓ_A(s)` is nonsingular, and its direction is
`c + ℓ_A(n) + γ_n` with `γ_n` depending only on `n`. -/

section HarmonicBordered
open fwdDiff
variable {F : Type*} [Field F]

theorem fd_congr (g1 g2 : ℕ → F) (m y : ℕ) (h : ∀ s≤m,g1 (y+s)=g2 (y+s)) : fd g1 m y=fd g2 m y := by
  unfold fd
  apply Finset.sum_congr rfl
  intro s hs
  rw [h s (by have := Finset.mem_range.mp hs; omega)]

theorem fd_lin (a : F) (f g : ℕ → F) (m y : ℕ) :
    fd (fun s => a*f s+g s) m y=a*fd f m y+fd g m y := by
  unfold fd
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem fd_poly (P : F[X]) (κ m y : ℕ) :
    fd (fun s => P.eval ((κ+s:ℕ):F)) m y=(Δ_[1]^[m] P.eval) ((κ+y:ℕ):F) := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold fd
  apply Finset.sum_congr rfl
  intro s _
  rw [zsmul_eq_mul,nsmul_eq_mul,mul_one]
  push_cast
  ring_nf

theorem fd_poly_hi (P : F[X]) (κ m y : ℕ) (h : P.natDegree<m) :
    fd (fun s => P.eval ((κ+s:ℕ):F)) m y=0 := by
  rw [fd_poly,Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h]
  rfl

theorem fd_poly_top (P : F[X]) (κ n y : ℕ) (h : P.natDegree≤n) :
    fd (fun s => P.eval ((κ+s:ℕ):F)) n y=P.coeff n*(n.factorial:F) := by
  rcases lt_or_eq_of_le h with h'|h'
  · rw [fd_poly_hi P κ n y h',Polynomial.coeff_eq_zero_of_natDegree_lt h',zero_mul]
  · rw [fd_poly,← h',P.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply,Pi.natCast_apply,smul_eq_mul]
    rfl

/-- Newton's forward formula for a function whose high differences at `0` vanish. -/
theorem newton_fd (g : ℕ → F) (n : ℕ) (hz : ∀ k,n<k → fd g k 0=0) (s : ℕ) :
    g s=∑ k∈range (n+1),(s.choose k:F)*fd g k 0 := by
  have h := shift_eq_sum_fwdDiff_iter (1:ℕ) g s 0
  simp only [zero_add,smul_eq_mul,mul_one,nsmul_eq_mul] at h
  rw [h]
  simp only [← fd_eq]
  have e1 : ∑ k∈range (s+1),(s.choose k:F)*fd g k 0=∑ k∈range (s+n+1),(s.choose k:F)*fd g k 0 := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have e2 : ∑ k∈range (n+1),(s.choose k:F)*fd g k 0=∑ k∈range (s+n+1),(s.choose k:F)*fd g k 0 := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [hz k (by omega)]
    simp
  rw [e1,e2]

variable (F) in
/-- `W(t) = ∏_j (t - y_j)`. -/
noncomputable def wpoly {n : ℕ} (ys : Fin n → ℕ) : F[X] := ∏ j,(X-C (ys j:F))

variable (F) in
/-- `W(t)/(t - y_j)`. -/
noncomputable def ppoly {n : ℕ} (ys : Fin n → ℕ) (j : Fin n) : F[X] :=
  ∏ j'∈univ.erase j,(X-C (ys j':F))

theorem wpoly_eq {n : ℕ} (ys : Fin n → ℕ) (j : Fin n) :
    wpoly F ys=(X-C (ys j:F))*ppoly F ys j :=
  (Finset.mul_prod_erase univ (fun j' => (X-C (ys j':F))) (mem_univ j)).symm

theorem wpoly_monic {n : ℕ} (ys : Fin n → ℕ) : (wpoly F ys).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)

theorem wpoly_natDegree {n : ℕ} (ys : Fin n → ℕ) : (wpoly F ys).natDegree=n := by
  unfold wpoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

theorem ppoly_natDegree {n : ℕ} (ys : Fin n → ℕ) (j : Fin n) : (ppoly F ys j).natDegree=n-1 := by
  unfold ppoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C,Finset.sum_const,Finset.card_erase_of_mem (mem_univ j),
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

theorem ppoly_coeff {n : ℕ} (ys : Fin n → ℕ) (j : Fin n) : (ppoly F ys j).coeff n=0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ppoly_natDegree]; have := j.2; omega)

theorem wpoly_coeff {n : ℕ} (ys : Fin n → ℕ) : (wpoly F ys).coeff n=1 := by
  have h := (wpoly_monic (F:=F) ys).leadingCoeff
  rwa [Polynomial.leadingCoeff,wpoly_natDegree] at h

theorem ppoly_eval_other {n : ℕ} (ys : Fin n → ℕ) (j j' : Fin n) (h : j'≠j) :
    (ppoly F ys j').eval (ys j:F)=0 := by
  unfold ppoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i:=j) (Finset.mem_erase.mpr ⟨fun e => h e.symm,mem_univ _⟩)
  simp

theorem ppoly_eval_self {n : ℕ} (ys : Fin n → ℕ) (hy : ∀ a b,a≠b → (ys a:F)≠(ys b:F)) (j : Fin n) :
    (ppoly F ys j).eval (ys j:F)≠0 := by
  unfold ppoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j' hj'
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  exact sub_ne_zero.mpr (hy j j' (Finset.mem_erase.mp hj').1.symm)

theorem wpoly_eval_ne {n : ℕ} (ys : Fin n → ℕ) (x : F) (hx : ∀ j,x≠(ys j:F)) :
    (wpoly F ys).eval x≠0 := by
  unfold wpoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  exact sub_ne_zero.mpr (hx j)

/-- The bordered matrix `[Q | col]`, `Q_{ij} = (L(y_j)-L(x_i))/(y_j-x_i)`, rows
`xs`, columns `ys` (any split; the zone row is just one of the rows). -/
noncomputable def bmat {n : ℕ} (xs : Fin (n+1) → ℕ) (ys : Fin n → ℕ) (L : ℕ → F) (col : Fin (n+1) → F) :
    Matrix (Fin (n+1)) (Fin (n+1)) F :=
  Matrix.of fun i j => if h : (j:ℕ)<n then (L (ys ⟨j,h⟩)-L (xs i))/((ys ⟨j,h⟩:F)-(xs i:F)) else col i

theorem bmat_mulVec {n : ℕ} (xs : Fin (n+1) → ℕ) (ys : Fin n → ℕ) (L : ℕ → F) (col : Fin (n+1) → F)
    (w : Fin (n+1) → F) (i : Fin (n+1)) :
    (bmat xs ys L col *ᵥ w) i=∑ j:Fin n,(L (ys j)-L (xs i))/((ys j:F)-(xs i:F))*w (Fin.castSucc j)+
      col i*w (Fin.last n) := by
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,bmat,Matrix.of_apply,Fin.coe_castSucc,
    Fin.is_lt,dif_pos,Fin.val_last,lt_irrefl,dif_neg,not_false_eq_true]

/-- Theorem A: denominator `D = λW - Σ_j w_j W/(t-y_j)`. -/
noncomputable def dpoly {n : ℕ} (ys : Fin n → ℕ) (w : Fin (n+1) → F) (lam : F) : F[X] :=
  C lam*wpoly F ys-∑ j,C (w (Fin.castSucc j))*ppoly F ys j

/-- Theorem A: numerator `N = δW - Σ_j w_j L(y_j) W/(t-y_j)`. -/
noncomputable def npoly {n : ℕ} (ys : Fin n → ℕ) (L : ℕ → F) (w : Fin (n+1) → F) : F[X] :=
  C (w (Fin.last n))*wpoly F ys-∑ j,C (w (Fin.castSucc j)*L (ys j))*ppoly F ys j

theorem dpoly_natDegree {n : ℕ} (ys : Fin n → ℕ) (w : Fin (n+1) → F) (lam : F) :
    (dpoly ys w lam).natDegree≤n := by
  unfold dpoly
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (wpoly_natDegree ys).le
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [ppoly_natDegree]; omega)

theorem npoly_natDegree {n : ℕ} (ys : Fin n → ℕ) (L : ℕ → F) (w : Fin (n+1) → F) :
    (npoly ys L w).natDegree≤n := by
  unfold npoly
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (wpoly_natDegree ys).le
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [ppoly_natDegree]; omega)

theorem dpoly_coeff {n : ℕ} (ys : Fin n → ℕ) (w : Fin (n+1) → F) (lam : F) :
    (dpoly ys w lam).coeff n=lam := by
  unfold dpoly
  simp only [Polynomial.coeff_sub,Polynomial.coeff_C_mul,wpoly_coeff,Polynomial.finsetSum_coeff,ppoly_coeff,
    mul_zero,Finset.sum_const_zero,sub_zero,mul_one]

theorem npoly_coeff {n : ℕ} (ys : Fin n → ℕ) (L : ℕ → F) (w : Fin (n+1) → F) :
    (npoly ys L w).coeff n=w (Fin.last n) := by
  unfold npoly
  simp only [Polynomial.coeff_sub,Polynomial.coeff_C_mul,wpoly_coeff,Polynomial.finsetSum_coeff,ppoly_coeff,
    mul_zero,Finset.sum_const_zero,sub_zero,mul_one]

theorem dpoly_eval_y {n : ℕ} (ys : Fin n → ℕ) (w : Fin (n+1) → F) (lam : F) (j : Fin n) :
    (dpoly ys w lam).eval (ys j:F)=-(w (Fin.castSucc j)*(ppoly F ys j).eval (ys j:F)) := by
  unfold dpoly
  rw [Polynomial.eval_sub,Polynomial.eval_mul,wpoly_eq ys j,Polynomial.eval_mul,Polynomial.eval_finset_sum,
    Finset.sum_eq_single j (fun j' _ h => by rw [Polynomial.eval_mul,ppoly_eval_other ys j j' h,mul_zero])
      (fun h => absurd (mem_univ j) h)]
  simp

theorem npoly_eval_y {n : ℕ} (ys : Fin n → ℕ) (L : ℕ → F) (w : Fin (n+1) → F) (j : Fin n) :
    (npoly ys L w).eval (ys j:F)=-(w (Fin.castSucc j)*L (ys j)*(ppoly F ys j).eval (ys j:F)) := by
  unfold npoly
  rw [Polynomial.eval_sub,Polynomial.eval_mul,wpoly_eq ys j,Polynomial.eval_mul,Polynomial.eval_finset_sum,
    Finset.sum_eq_single j (fun j' _ h => by rw [Polynomial.eval_mul,ppoly_eval_other ys j j' h,mul_zero])
      (fun h => absurd (mem_univ j) h)]
  simp

/-- Theorem A, row equations: a row of `[Q | 1] w = λ L` is the
interpolation condition `N(x) = L(x) D(x)` at that row node. -/
theorem interp_x {n : ℕ} (ys : Fin n → ℕ) (L : ℕ → F) (w : Fin (n+1) → F) (lam : F) (x : ℕ)
    (hx : ∀ j,(x:F)≠(ys j:F))
    (hrow : ∑ j:Fin n,(L (ys j)-L x)/((ys j:F)-(x:F))*w (Fin.castSucc j)+w (Fin.last n)=lam*L x) :
    (npoly ys L w).eval (x:F)=L x*(dpoly ys w lam).eval (x:F) := by
  have key : ∀ j,(L (ys j)-L x)/((ys j:F)-(x:F))*w (Fin.castSucc j)*(wpoly F ys).eval (x:F)=
      -((L (ys j)-L x)*w (Fin.castSucc j)*(ppoly F ys j).eval (x:F)) := by
    intro j
    have hne : (ys j:F)-(x:F)≠0 := sub_ne_zero.mpr (hx j).symm
    rw [wpoly_eq ys j,Polynomial.eval_mul]
    simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    field_simp
    ring
  have hs : (∑ j:Fin n,(L (ys j)-L x)/((ys j:F)-(x:F))*w (Fin.castSucc j))*(wpoly F ys).eval (x:F)=
      -∑ j:Fin n,(L (ys j)-L x)*w (Fin.castSucc j)*(ppoly F ys j).eval (x:F) := by
    rw [Finset.sum_mul,← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => key j)
  have hs2 : ∑ j:Fin n,(L (ys j)-L x)*w (Fin.castSucc j)*(ppoly F ys j).eval (x:F)=
      ∑ j:Fin n,w (Fin.castSucc j)*L (ys j)*(ppoly F ys j).eval (x:F)-
        L x*∑ j:Fin n,w (Fin.castSucc j)*(ppoly F ys j).eval (x:F) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [npoly,dpoly,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finset_sum]
  linear_combination (wpoly F ys).eval (x:F)*hrow-hs+hs2

theorem cast_ne_off (N a b : ℕ) (hk : ∀ k,1≤k → k≤N → (k:F)≠0) (κ : ℕ) (ha : κ≤a ∧ a≤κ+N)
    (hb : κ≤b ∧ b≤κ+N) (hab : a≠b) : (a:F)≠(b:F) := by
  intro h
  rcases Nat.lt_or_gt_of_ne hab with h'|h'
  · apply hk (b-a) (by omega) (by omega)
    rw [Nat.cast_sub h'.le,h,sub_self]
  · apply hk (a-b) (by omega) (by omega)
    rw [Nat.cast_sub h'.le,h,sub_self]

/-- The Cauchy matrix `[1/(m-k)]`, `m = n+1..2n`, `k = 0..n-1`. -/
noncomputable def hcauchy (F : Type*) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) F :=
  WrapCauchy.matrix (fun i:Fin n => ((n+1+(i:ℕ):ℕ):F)) (fun k:Fin n => ((k:ℕ):F))

/-- Its solution against `-1/(m-n)`: independent of the load parameter. -/
noncomputable def heps (F : Type*) [Field F] (n : ℕ) : Fin n → F :=
  (hcauchy F n)⁻¹ *ᵥ (fun i => -1/(((n+1+(i:ℕ):ℕ):F)-(n:F)))

/-- The constant `γ_n` of the harmonic direction `c + ℓ_A(n) + γ_n`. -/
noncomputable def hgam (F : Type*) [Field F] (n : ℕ) : F :=
  -∑ k:Fin n,heps F n k/((n:F)-((k:ℕ):F))

theorem hcauchy_det_ne (n : ℕ) (hk : ∀ k,1≤k → k≤2*n → (k:F)≠0) : (hcauchy F n).det≠0 :=
  WrapCauchy.det_ne (fun i:Fin n => ((n+1+(i:ℕ):ℕ):F)) (fun k:Fin n => ((k:ℕ):F))
    (fun a b h => Fin.ext (by
      by_contra hne
      exact cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega)
        (by intro h'; apply hne; omega) h))
    (fun a b h => Fin.ext (by
      by_contra hne
      exact cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega) hne h))
    (fun a b h => cast_ne_of_le n _ _ hk (by have := a.2; omega) (by have := b.2; omega)
      (by have := b.2; omega) h)

/-- Hypotheses of the harmonic bordered system on an ARBITRARY split of the
nodes `κ..κ+2n` into `n+1` rows and `n` columns. -/
structure HSplit (n κ : ℕ) (A c : F) (L : ℕ → F) (xs : Fin (n+1) → ℕ) (ys : Fin n → ℕ) : Prop where
  hn : 1≤n
  hk : ∀ k,1≤k → k≤2*n → (k:F)≠0
  hA : ∀ h<2*n,A+(h:F)≠0
  hL : ∀ s≤2*n,L (κ+s)=c+hload A s
  hxr : ∀ i,κ≤xs i ∧ xs i≤κ+2*n
  hyr : ∀ j,κ≤ys j ∧ ys j≤κ+2*n
  hxy : ∀ i j,xs i≠ys j
  hyy : Function.Injective ys
  hcov : ∀ s≤2*n,(∃ i,xs i=κ+s) ∨ (∃ j,ys j=κ+s)

variable {n κ : ℕ} {A c : F} {L : ℕ → F} {xs : Fin (n+1) → ℕ} {ys : Fin n → ℕ}

theorem HSplit.cxy (H : HSplit n κ A c L xs ys) (i : Fin (n+1)) (j : Fin n) : (xs i:F)≠(ys j:F) :=
  cast_ne_off (2*n) _ _ H.hk κ (H.hxr i) (H.hyr j) (H.hxy i j)

theorem HSplit.cyy (H : HSplit n κ A c L xs ys) (a b : Fin n) (h : a≠b) : (ys a:F)≠(ys b:F) :=
  cast_ne_off (2*n) _ _ H.hk κ (H.hyr a) (H.hyr b) (fun e => h (H.hyy e))

/-- Theorem A on the whole node set: `N = L D` at every node. -/
theorem HSplit.interp (H : HSplit n κ A c L xs ys) (w : Fin (n+1) → F) (lam : F)
    (hw : bmat xs ys L 1 *ᵥ w=fun i => lam*L (xs i)) (s : ℕ) (hs : s≤2*n) :
    (npoly ys L w).eval ((κ+s:ℕ):F)=L (κ+s)*(dpoly ys w lam).eval ((κ+s:ℕ):F) := by
  rcases H.hcov s hs with ⟨i,hi⟩|⟨j,hj⟩
  · rw [← hi]
    apply interp_x ys L w lam (xs i) (fun j => H.cxy i j)
    have h := congrFun hw i
    rw [bmat_mulVec] at h
    simpa only [Pi.one_apply,one_mul] using h
  · rw [← hj,npoly_eval_y,dpoly_eval_y]
    ring

/-- The difference identities shared by the homogeneous and the
inhomogeneous case (orders `n+1..2n`, and order `n`). -/
theorem HSplit.core (H : HSplit n κ A c L xs ys) (w : Fin (n+1) → F) (lam : F)
    (hw : bmat xs ys L 1 *ᵥ w=fun i => lam*L (xs i)) :
    (∀ m,n<m → m≤2*n → ∑ k∈range (n+1),fd (fun s => (dpoly ys w lam).eval ((κ+s:ℕ):F)) k 0*
        ((m.choose k:F)*fd (hload A) (m-k) k)=0) ∧
    (w (Fin.last n)*(n.factorial:F)=c*(lam*(n.factorial:F))+∑ k∈range (n+1),
        fd (fun s => (dpoly ys w lam).eval ((κ+s:ℕ):F)) k 0*((n.choose k:F)*fd (hload A) (n-k) k)) := by
  set g := fun s => (dpoly ys w lam).eval ((κ+s:ℕ):F) with hg
  have hzD : ∀ k,n<k → fd g k 0=0 := fun k hk =>
    fd_poly_hi _ κ k 0 (lt_of_le_of_lt (dpoly_natDegree ys w lam) hk)
  have hN (m : ℕ) (hnm : n≤m) (hm : m≤2*n) : fd (fun s => (npoly ys L w).eval ((κ+s:ℕ):F)) m 0=
      c*fd g m 0+∑ k∈range (n+1),fd g k 0*((m.choose k:F)*fd (hload A) (m-k) k) := by
    rw [fd_congr _ (fun s => c*g s+∑ k∈range (n+1),fd g k 0*((s.choose k:F)*hload A s)) m 0 (by
      intro s hs
      simp only [zero_add]
      rw [H.interp w lam hw s (by omega),H.hL s (by omega)]
      change (c+hload A s)*g s=c*g s+∑ k∈range (n+1),fd g k 0*((s.choose k:F)*hload A s)
      rw [add_mul]
      congr 1
      rw [newton_fd g n hzD s,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring),fd_lin,fd_sum (range (n+1)) (fun k => fd g k 0) (fun k s => (s.choose k:F)*hload A s)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [fd_choose_mul _ _ _ (by have := Finset.mem_range.mp hk; omega)]
  refine ⟨fun m h1 h2 => ?_,?_⟩
  · have h := hN m h1.le h2
    rw [fd_poly_hi _ κ m 0 (lt_of_le_of_lt (npoly_natDegree ys L w) h1),hzD m h1,mul_zero,zero_add] at h
    exact h.symm
  · have h := hN n le_rfl (by have := H.hn; omega)
    rw [fd_poly_top _ κ n 0 (npoly_natDegree ys L w),npoly_coeff] at h
    have hd : fd g n 0=lam*(n.factorial:F) := by
      rw [hg,fd_poly_top _ κ n 0 (dpoly_natDegree ys w lam),dpoly_coeff]
    rw [hd] at h
    exact h

/-- Nonsingularity of the harmonic bordered system, for every split. -/
theorem HSplit.det_ne (H : HSplit n κ A c L xs ys) : (bmat xs ys L 1).det≠0 := by
  intro h0
  obtain ⟨w,hw0,hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hw0
  have hw' : bmat xs ys L 1 *ᵥ w=fun i => (0:F)*L (xs i) := by
    rw [hw]; funext i; simp
  obtain ⟨h1,-⟩ := H.core w 0 hw'
  set g := fun s => (dpoly ys w 0).eval ((κ+s:ℕ):F) with hg
  have hzD : ∀ k,n<k → fd g k 0=0 := fun k hk =>
    fd_poly_hi _ κ k 0 (lt_of_le_of_lt (dpoly_natDegree ys w 0) hk)
  have hdn : fd g n 0=0 := by
    rw [hg,fd_poly_top _ κ n 0 (dpoly_natDegree ys w 0),dpoly_coeff,zero_mul]
  have hlow : ∀ k<n,fd g k 0=0 := harmonic_uniq A n H.hk H.hA (fun k => fd g k 0) (by
    intro m h1' h2'
    rw [fd_sum (range n) (fun k => fd g k 0) (fun k s => (s.choose k:F)*hload A s)]
    have := h1 m (by omega) h2'
    rw [Finset.sum_range_succ,hdn,zero_mul,add_zero] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fd_choose_mul _ _ _ (by have := Finset.mem_range.mp hk; omega)])
  have hg0 : ∀ s,g s=0 := by
    intro s
    rw [newton_fd g n hzD s]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases Nat.lt_or_ge k n with h|h
    · rw [hlow k h,mul_zero]
    · rw [show k=n by omega,hdn,mul_zero]
  have hD (a : ℕ) (ha : κ≤a) : (dpoly ys w 0).eval (a:F)=0 := by
    have := hg0 (a-κ)
    simp only [hg] at this
    rwa [Nat.add_sub_cancel' ha] at this
  have hwj : ∀ j,w (Fin.castSucc j)=0 := by
    intro j
    have h := hD (ys j) (H.hyr j).1
    rw [dpoly_eval_y] at h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_right (ppoly_eval_self ys H.cyy j)
  have hwl : w (Fin.last n)=0 := by
    have hi := H.interp w 0 hw' (xs 0-κ) (by have := H.hxr 0; omega)
    rw [Nat.add_sub_cancel' (H.hxr 0).1,hD (xs 0) (H.hxr 0).1,mul_zero] at hi
    simp only [npoly,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_finset_sum,hwj,zero_mul,Finset.sum_const_zero,sub_zero] at hi
    exact (mul_eq_zero.mp hi).resolve_right (wpoly_eval_ne ys _ (fun j => H.cxy 0 j))
  funext i
  rw [Pi.zero_apply]
  induction i using Fin.lastCases with
  | last => exact hwl
  | cast j => exact hwj j

theorem neg_one_pow_pair (n : ℕ) (hn : 1≤n) : (-1:F)^(n-1)*(-1:F)^n=-1 := by
  obtain ⟨j,rfl⟩ : ∃ j,n=j+1 := ⟨n-1,by omega⟩
  rw [show j+1-1=j by omega,pow_succ,← mul_assoc,← pow_add,← two_mul,pow_mul]
  norm_num

/-- The direction of the harmonic bordered system (Cramer form):
`det[Q | L] = (c + ℓ_A(n) + γ_n) det[Q | 1]`, for every split. -/
theorem HSplit.dir (H : HSplit n κ A c L xs ys) :
    (bmat xs ys L (fun i => L (xs i))).det=(c+hload A n+hgam F n)*(bmat xs ys L 1).det := by
  have hd := H.det_ne
  set B := bmat xs ys L 1 with hB
  set w := B⁻¹ *ᵥ (fun i => L (xs i)) with hwdef
  have hw : B *ᵥ w=fun i => 1*L (xs i) := by
    rw [hwdef,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
    funext i; simp
  have hupd : bmat xs ys L (fun i => L (xs i))=B.updateCol (Fin.last n) (fun i => L (xs i)) := by
    ext i j
    simp only [hB,bmat,Matrix.updateCol_apply,Matrix.of_apply]
    by_cases hj : j=Fin.last n
    · subst hj; simp
    · have hj' : (j:ℕ)<n := by
        have := j.2
        have : (j:ℕ)≠n := fun e => hj (Fin.ext (by simpa using e))
        omega
      simp [hj,hj']
  have hcr : (B.updateCol (Fin.last n) (fun i => L (xs i))).det=B.det*w (Fin.last n) := by
    rw [← Matrix.cramer_apply,Matrix.cramer_eq_adjugate_mulVec,hwdef,Matrix.inv_def,
      Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,Ring.inverse_eq_inv']
    field_simp
  rw [hupd,hcr,mul_comm]
  congr 1
  obtain ⟨h1,h2⟩ := H.core w 1 hw
  set g := fun s => (dpoly ys w 1).eval ((κ+s:ℕ):F) with hg
  have hdn : fd g n 0=(n.factorial:F) := by
    rw [hg,fd_poly_top _ κ n 0 (dpoly_natDegree ys w 1),dpoly_coeff,one_mul]
  set E : ℕ → F := fun k => (-1:F)^k*rise A k/(k.factorial:F) with hE
  set ρ : F := (n.factorial:F)*E n with hρ
  have hnf : (n.factorial:F)≠0 := fact_ne n n H.hk (by omega)
  have hRn : rise A n≠0 := rise_ne _ _ (fun i hi => H.hA i (by omega))
  have hρ0 : ρ≠0 := by
    rw [hρ,hE]
    exact mul_ne_zero hnf (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hRn) hnf)
  -- the high-order equations as a Cauchy system
  have hA1 (m : ℕ) (hm1 : n<m) (hm2 : m≤2*n) :
      ∑ k∈range (n+1),fd g k 0*(E k/((m:F)-(k:F)))=0 := by
    have h := h1 m hm1 hm2
    have hCm : (-1:F)^(m-1)*(m.factorial:F)/rise A m≠0 :=
      div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (fact_ne n m H.hk hm2))
        (rise_ne _ _ (fun i hi => H.hA i (by omega)))
    have h' : ((-1:F)^(m-1)*(m.factorial:F)/rise A m)*
        ∑ k∈range (n+1),fd g k 0*(E k/((m:F)-(k:F)))=0 := by
      rw [← h,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [harmonic_term A n m k (by have := Finset.mem_range.mp hk; omega) hm2 H.hk H.hA]
      simp only [hE]
      ring
    exact (mul_eq_zero.mp h').resolve_left hCm
  set x : Fin n → F := fun k => fd g k 0*E k/ρ with hx
  have hcx : hcauchy F n *ᵥ x=fun i:Fin n => -1/(((n+1+(i:ℕ):ℕ):F)-(n:F)) := by
    funext i
    have h := hA1 (n+1+(i:ℕ)) (by omega) (by have := i.2; omega)
    rw [Finset.sum_range_succ,hdn] at h
    have hmn : (((n+1+(i:ℕ):ℕ):F)-(n:F))≠0 := by
      have := H.hk ((i:ℕ)+1) (by omega) (by have := i.2; omega)
      push_cast at this ⊢
      rwa [show (n:F)+1+(i:F)-(n:F)=(i:F)+1 by ring]
    simp only [hcauchy,WrapCauchy.matrix,Matrix.mulVec,dotProduct,Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => 1/(((n+1+(i:ℕ):ℕ):F)-(k:F))*(fd g k 0*E k/ρ))]
    have hs : ∑ k∈range n,1/(((n+1+(i:ℕ):ℕ):F)-(k:F))*(fd g k 0*E k/ρ)=
        (1/ρ)*∑ k∈range n,fd g k 0*(E k/(((n+1+(i:ℕ):ℕ):F)-(k:F))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs]
    have h3 : ∑ k∈range n,fd g k 0*(E k/(((n+1+(i:ℕ):ℕ):F)-(k:F)))=
        -(ρ/(((n+1+(i:ℕ):ℕ):F)-(n:F))) := by
      rw [hρ]; linear_combination h
    rw [h3]
    field_simp
  have hxe : x=heps F n := by
    have hdc := hcauchy_det_ne (F:=F) n H.hk
    rw [heps,← hcx,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdc),
      Matrix.one_mulVec]
  -- the order-n equation gives the direction
  rw [Finset.sum_range_succ,hdn,Nat.choose_self,Nat.sub_self,fd_zero] at h2
  have hlow : ∑ k∈range n,fd g k 0*((n.choose k:F)*fd (hload A) (n-k) k)=
      ((-1:F)^(n-1)*(n.factorial:F)/rise A n)*ρ*∑ k:Fin n,heps F n k/((n:F)-((k:ℕ):F)) := by
    rw [← hxe,hx]
    beta_reduce
    rw [Fin.sum_univ_eq_sum_range (fun k => fd g k 0*E k/ρ/((n:F)-(k:F))),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [harmonic_term A n n k (Finset.mem_range.mp hk) (by omega) H.hk H.hA]
    simp only [hE]
    field_simp
  have hcr : ((-1:F)^(n-1)*(n.factorial:F)/rise A n)*ρ=-(n.factorial:F) := by
    rw [hρ]
    simp only [hE]
    rw [show (-1:F)^(n-1)*(n.factorial:F)/rise A n*((n.factorial:F)*((-1:F)^n*rise A n/(n.factorial:F)))=
      ((-1:F)^(n-1)*(-1:F)^n)*(n.factorial:F) by field_simp; try ring,neg_one_pow_pair n H.hn]
    ring
  rw [hlow,hcr] at h2
  rw [hgam]
  apply mul_right_cancel₀ hnf
  push_cast at h2
  linear_combination h2

end HarmonicBordered

/-! ## R3: the top fractional coefficient (`Y = ∞`) of the cleared world

With the integer family undeformed (`specInt`), every cleared entry is a
polynomial in the fractional parameter `Y` of degree at most the number
`F` of original fractional poles; its `Y^F` coefficient keeps only the
integer poles, i.e. the harmonic load. -/

section TopCoefficient
variable {R : Type*} [CommRing R]

theorem prod_top {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R[X]) (e : ι → ℕ)
    (h : ∀ i∈s,(f i).natDegree≤e i) :
    (∏ i∈s,f i).natDegree≤∑ i∈s,e i ∧ (∏ i∈s,f i).coeff (∑ i∈s,e i)=∏ i∈s,(f i).coeff (e i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1,h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (add_le_add ha' h1),
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' h1,h2]⟩

/-- Column-degree top coefficient of a polynomial determinant. -/
theorem det_top {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X]) (d : ι → ℕ)
    (h : ∀ i j,(M i j).natDegree≤d j) :
    M.det.natDegree≤∑ j,d j ∧ M.det.coeff (∑ j,d j)=(Matrix.of fun i j => (M i j).coeff (d j)).det := by
  have hσ : ∀ σ : Equiv.Perm ι,(∏ i,M (σ i) i).natDegree≤∑ j,d j ∧
      (∏ i,M (σ i) i).coeff (∑ j,d j)=∏ i,(M (σ i) i).coeff (d i) :=
    fun σ => prod_top univ (fun i => M (σ i) i) d (fun i _ => h _ _)
  rw [Matrix.det_apply',Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    rw [← Polynomial.C_eq_intCast]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hσ σ).1
  · rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Polynomial.C_eq_intCast,Polynomial.coeff_C_mul,(hσ σ).2]
    simp only [Matrix.of_apply]

end TopCoefficient

/-- Harmonic numbers `H_m = Σ_{h<m} 1/(h+1)`. -/
noncomputable def harmSum (F : Type*) [Field F] (m : ℕ) : F := ∑ h∈range m,1/((h:F)+1)

theorem harmSum_add {F : Type*} [Field F] (κ s : ℕ) :
    harmSum F (κ+s)=harmSum F κ+hload ((κ:F)+1) s := by
  unfold harmSum hload
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  push_cast
  ring_nf

theorem harmSum_succ {F : Type*} [Field F] (m : ℕ) : harmSum F (m+1)=harmSum F m+1/((m:F)+1) := by
  unfold harmSum
  rw [Finset.sum_range_succ]

/-- The integer poles up to `a` contribute `H_{a/p}`. -/
theorem int_pole_sum {F : Type*} [Field F] (p a : ℕ) :
    ∑ t∈Icc 1 a,(if p∣t then ((t/p:ℕ):F)⁻¹ else 0)=harmSum F (a/p) := by
  induction a with
  | zero => simp [harmSum]
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega),ih,Nat.succ_div]
    by_cases h : p∣a+1
    · rw [if_pos h,if_pos h,harmSum_succ]
      push_cast
      ring
    · rw [if_neg h,if_neg h,add_zero,add_zero]

section ClearedTop
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)

/-- Top fractional degree and leading coefficient of one original
denominator with the integer family undeformed. -/
def topDeg (t : ℕ) : ℕ := if p∣t then 0 else if p∣q*t-o then 1 else 0
noncomputable def topLead (t : ℕ) : ZMod p :=
  if p∣t then ((t/p:ℕ):ZMod p) else if p∣q*t-o then (q:ZMod p) else 1

/-- The number of original fractional poles in `[1, M]`. -/
def fracCount (M : ℕ) : ℕ := ∑ t∈Icc 1 M,topDeg p q o t
/-- The top coefficient of the cleared clearing factor. -/
noncomputable def topClear (M : ℕ) : ZMod p := ∏ t∈Icc 1 M,topLead p q o t

theorem specInt_bconst (k : ZMod p) : specInt p (bconst p k)=Polynomial.C k := by
  simp [specInt,bconst]

theorem specInt_dfac_top (t : ℕ) :
    (specInt p (dfac p q o t)).natDegree≤topDeg p q o t ∧
      (specInt p (dfac p q o t)).coeff (topDeg p q o t)=topLead p q o t := by
  rw [specInt_dfac]
  unfold topDeg topLead
  split_ifs with h1 h2
  · simp
  · refine ⟨?_,?_⟩
    · rw [add_comm]; exact Polynomial.natDegree_linear_le
    · simp [Polynomial.coeff_C,Polynomial.coeff_X_one]
  · simp

theorem topLead_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) (t : ℕ) (ht : t∈Icc 1 M) :
    topLead p q o t≠0 := by
  unfold topLead
  split_ifs with h1 h2
  · exact quot_ne_zero p M t hM ht h1
  · exact hq
  · exact one_ne_zero

theorem topClear_ne (M : ℕ) (hM : M<p*p) (hq : (q:ZMod p)≠0) : topClear p q o M≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun t ht => topLead_ne p q o M hM hq t ht)

theorem cofactor_top (M t : ℕ) (ht : t∈Icc 1 M) :
    (specInt p (cofactor p q o M t)).natDegree≤fracCount p q o M-topDeg p q o t ∧
      (specInt p (cofactor p q o M t)).coeff (fracCount p q o M-topDeg p q o t)=
        ∏ t'∈(Icc 1 M).erase t,topLead p q o t' := by
  have hs : ∑ t'∈(Icc 1 M).erase t,topDeg p q o t'=fracCount p q o M-topDeg p q o t := by
    have := Finset.add_sum_erase (Icc 1 M) (topDeg p q o) ht
    unfold fracCount; omega
  unfold cofactor
  rw [map_prod,← hs]
  exact prod_top _ _ _ (fun t' _ => (specInt_dfac_top p q o t').1)
    |>.imp id (fun h => h.trans (Finset.prod_congr rfl (fun t' _ => (specInt_dfac_top p q o t').2)))

theorem clearedDelta_top (M t : ℕ) (hM : M<p*p) (ht : t∈Icc 1 M) :
    (specInt p (clearedDelta p q o M t)).natDegree≤fracCount p q o M ∧
      (specInt p (clearedDelta p q o M t)).coeff (fracCount p q o M)=
        if p∣t then topClear p q o M*((t/p:ℕ):ZMod p)⁻¹ else 0 := by
  obtain ⟨hd,hc⟩ := cofactor_top p q o M t ht
  have hF : topDeg p q o t≤fracCount p q o M :=
    Finset.single_le_sum (f:=topDeg p q o) (fun _ _ => Nat.zero_le _) ht
  unfold clearedDelta deltaWeight
  by_cases h1 : p∣t
  · have h0 : topDeg p q o t=0 := by unfold topDeg; rw [if_pos h1]
    rw [h0,Nat.sub_zero] at hd hc
    simp only [if_pos h1,map_mul,map_one,one_mul]
    refine ⟨hd,?_⟩
    rw [hc]
    have hq := quot_ne_zero p M t hM ht h1
    have hm := Finset.mul_prod_erase (Icc 1 M) (topLead p q o) ht
    have hl : topLead p q o t=((t/p:ℕ):ZMod p) := by unfold topLead; rw [if_pos h1]
    rw [hl] at hm
    unfold topClear
    rw [← hm]
    field_simp
  · by_cases h2 : p∣q*t-o
    · have h0 : topDeg p q o t=1 := by unfold topDeg; rw [if_neg h1,if_pos h2]
      rw [h0] at hd hF
      simp only [if_neg h1,if_pos h2,map_mul,map_neg,specInt_bconst]
      refine ⟨Polynomial.natDegree_mul_le.trans (by
        rw [Polynomial.natDegree_neg,Polynomial.natDegree_C,zero_add]; exact hd.trans (Nat.sub_le _ _)),?_⟩
      rw [neg_mul,Polynomial.coeff_neg,Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega))]
      simp
    · simp only [if_neg h1,if_neg h2,map_mul,map_zero,zero_mul,Polynomial.natDegree_zero,
        Polynomial.coeff_zero,Nat.zero_le,and_self]

theorem clearedLoad_top (M a : ℕ) (haM : a≤M) (hM : M<p*p) :
    (specInt p (clearedLoad p q o M a)).natDegree≤fracCount p q o M ∧
      (specInt p (clearedLoad p q o M a)).coeff (fracCount p q o M)=
        topClear p q o M*harmSum (ZMod p) (a/p) := by
  have hin : ∀ t∈Icc 1 a,t∈Icc 1 M := fun t ht => by
    have := mem_Icc.mp ht; exact mem_Icc.mpr ⟨this.1,this.2.trans haM⟩
  unfold clearedLoad
  rw [map_sum]
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ (fun t ht => (clearedDelta_top p q o M t hM (hin t ht)).1),?_⟩
  rw [Polynomial.finsetSum_coeff,← int_pole_sum p a,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(clearedDelta_top p q o M t hM (hin t ht)).2]
  split_ifs <;> simp

theorem clearedEntry_top (M : ℕ) (hM : M<p*p) (u0 : ZMod p) (a b : ℕ) (ha : a≤M) (hb : b≤M) :
    (specInt p (clearedEntry p q o M u0 a b)).natDegree≤fracCount p q o M ∧
      (specInt p (clearedEntry p q o M u0 a b)).coeff (fracCount p q o M)=
        u0/(((b/p:ℕ):ZMod p)-((a/p:ℕ):ZMod p))*
          (topClear p q o M*harmSum (ZMod p) (b/p)-topClear p q o M*harmSum (ZMod p) (a/p)) := by
  obtain ⟨hb1,hb2⟩ := clearedLoad_top p q o M b hb hM
  obtain ⟨ha1,ha2⟩ := clearedLoad_top p q o M a ha hM
  unfold clearedEntry
  rw [map_mul,map_sub,specInt_bconst]
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hb1 ha1)),?_⟩
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_sub,hb2,ha2]

theorem clearedLoadRow_top (M : ℕ) (hM : M<p*p) (u0 : ZMod p) (a : ℕ) (ha : a≤M) :
    (specInt p (clearedLoadRow p q o M u0 a)).natDegree≤fracCount p q o M ∧
      (specInt p (clearedLoadRow p q o M u0 a)).coeff (fracCount p q o M)=
        u0*(topClear p q o M*harmSum (ZMod p) (a/p)) := by
  obtain ⟨ha1,ha2⟩ := clearedLoad_top p q o M a ha hM
  unfold clearedLoadRow
  rw [map_mul,specInt_bconst]
  exact ⟨(Polynomial.natDegree_C_mul_le _ _).trans ha1,by rw [Polynomial.coeff_C_mul,ha2]⟩

variable {p q o}
variable {k n : ℕ} {cn : Fin k → ℕ} {xr yc : Fin n → ℕ} {z : ℕ}

/-- The top fractional coefficient of the cleared bordered block is the
harmonic bordered determinant on the fibre quotients, times powers of the
nonzero scalar `u0 · topClear`. -/
theorem clearedD_top {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (u0 : ZMod p) (load : Bool) :
    (specInt p (clearedD p q o xr yc z M u0 load).det).natDegree≤
        n*fracCount p q o M+(if load then fracCount p q o M else 0) ∧
      (specInt p (clearedD p q o xr yc z M u0 load).det).coeff
          (n*fracCount p q o M+(if load then fracCount p q o M else 0))=
        (u0*topClear p q o M)^n*(if load then u0*topClear p q o M else 1)*
          (bmat (fun i => bordRow xr z i/p) (fun c => yc c/p) (harmSum (ZMod p))
            (if load then (fun i => harmSum (ZMod p) (bordRow xr z i/p)) else 1)).det := by
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H.hq0) H.hM
  set Fd := fracCount p q o M
  set d : Fin (n+1) → ℕ := fun j => if (j:ℕ)<n then Fd else if load then Fd else 0 with hd
  have hsum : ∑ j,d j=n*Fd+(if load then Fd else 0) := by
    rw [Fin.sum_univ_castSucc]
    simp [hd]
  have hdeg : ∀ i j,((clearedD p q o xr yc z M u0 load).map (specInt p) i j).natDegree≤d j := by
    intro i j
    simp only [Matrix.map_apply,clearedD,Matrix.of_apply,hd]
    by_cases hj : (j:ℕ)<n
    · rw [dif_pos hj,if_pos hj]
      exact (clearedEntry_top p q o M hMp u0 _ _ (H.bord_le i) (H.hyc _)).1
    · rw [dif_neg hj,if_neg hj]
      cases load
      · simp
      · simp only [↓reduceIte]
        exact (clearedLoadRow_top p q o M hMp u0 _ (H.bord_le i)).1
  obtain ⟨h1,h2⟩ := det_top _ d hdeg
  have he : ((clearedD p q o xr yc z M u0 load).map (specInt p)).det=
      specInt p (clearedD p q o xr yc z M u0 load).det := (RingHom.map_det _ _).symm
  rw [he,hsum] at h1 h2
  refine ⟨h1,?_⟩
  rw [h2]
  set v : Fin (n+1) → ZMod p := fun j => if (j:ℕ)<n then u0*topClear p q o M else
    if load then u0*topClear p q o M else 1 with hv
  have hm : (Matrix.of fun i j => ((clearedD p q o xr yc z M u0 load).map (specInt p) i j).coeff (d j))=
      Matrix.of fun i j => v j*
        (bmat (fun i => bordRow xr z i/p) (fun c => yc c/p) (harmSum (ZMod p))
          (if load then (fun i => harmSum (ZMod p) (bordRow xr z i/p)) else 1)) i j := by
    ext i j
    simp only [Matrix.map_apply,clearedD,Matrix.of_apply,hd,hv,bmat]
    by_cases hj : (j:ℕ)<n
    · rw [dif_pos hj,if_pos hj,dif_pos hj,if_pos hj,
        (clearedEntry_top p q o M hMp u0 _ _ (H.bord_le i) (H.hyc _)).2]
      ring
    · rw [dif_neg hj,if_neg hj,dif_neg hj,if_neg hj]
      cases load
      · simp
      · simp only [↓reduceIte]
        rw [(clearedLoadRow_top p q o M hMp u0 _ (H.bord_le i)).2]
        ring
  rw [hm,Matrix.det_mul_row,Fin.prod_univ_castSucc]
  simp only [hv,Fin.coe_castSucc,Fin.is_lt,↓reduceIte,Fin.val_last,lt_irrefl,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

end ClearedTop

/-! ## R3: separation across INTEGER cuts (top fractional coefficient) -/

section IntegerCross
variable {p : ℕ} [Fact p.Prime] {q o : ℕ}

/-- Integer cut: the top fractional coefficients of the two cleared fibre
systems are the harmonic bordered systems on the fibre quotients; their
directions `H_{κ+n} + γ_n` differ, so the ORIGINAL residue directions do. -/
theorem residue_cross_top_ne {M n k1 k2 : ℕ}
    {cn1 : Fin k1 → ℕ} {xr1 yc1 : Fin n → ℕ} {z1 : ℕ}
    {cn2 : Fin k2 → ℕ} {xr2 yc2 : Fin n → ℕ} {z2 : ℕ}
    (H1 : FibreHyp p q o cn1 xr1 yc1 z1 M) (H2 : FibreHyp p q o cn2 xr2 yc2 z2 M)
    (s u : GaussLoc p) (u0 : ZMod p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0)) (hu00 : u0≠0)
    (κ1 κ2 : ℕ)
    (hS1 : HSplit n κ1 ((κ1:ZMod p)+1) (harmSum (ZMod p) κ1) (harmSum (ZMod p))
      (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p))
    (hS2 : HSplit n κ2 ((κ2:ZMod p)+1) (harmSum (ZMod p) κ2) (harmSum (ZMod p))
      (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p))
    (hδ : harmSum (ZMod p) (κ1+n)≠harmSum (ZMod p) (κ2+n)) :
    WrapDeform.residue p ((ringSystem1 p q o cn1 xr1 yc1 z1 s u true).det*
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u false).det-
      (ringSystem1 p q o cn2 xr2 yc2 z2 s u true).det*(ringSystem1 p q o cn1 xr1 yc1 z1 s u false).det)≠0 := by
  apply residue_cross1_of_spec H1 H2 s u u0 hs hu0
  have hq := q_zmod_ne p q H1.hq0 H1.hqp
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M H1.hq0) H1.hM
  have hsc : u0*topClear p q o M≠0 := mul_ne_zero hu00 (topClear_ne p q o M hMp hq)
  obtain ⟨d1t,c1t⟩ := clearedD_top H1 u0 true
  obtain ⟨d1f,c1f⟩ := clearedD_top H1 u0 false
  obtain ⟨d2t,c2t⟩ := clearedD_top H2 u0 true
  obtain ⟨d2f,c2f⟩ := clearedD_top H2 u0 false
  simp only [↓reduceIte,Bool.false_eq_true,add_zero,mul_one] at d1t c1t d1f c1f d2t c2t d2f c2f
  have e1 := hS1.dir
  have e2 := hS2.dir
  have n1 := hS1.det_ne
  have n2 := hS2.det_ne
  beta_reduce at e1 e2 n1 n2
  rw [← harmSum_add] at e1 e2
  intro h
  rw [map_mul,map_mul] at h
  have hc := congrArg (fun P : (ZMod p)[X] => P.coeff
    ((n*fracCount p q o M+fracCount p q o M)+n*fracCount p q o M)) h
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le d1t d2f,Polynomial.coeff_mul_add_eq_of_natDegree_le d2t d1f,
    c1t,c1f,c2t,c2f,e1,e2] at hc
  apply hδ
  have key : ((u0*topClear p q o M)^n*(u0*topClear p q o M)*(u0*topClear p q o M)^n)*
      (((harmSum (ZMod p) (κ1+n)+hgam (ZMod p) n)-(harmSum (ZMod p) (κ2+n)+hgam (ZMod p) n))*
        ((bmat (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p) (harmSum (ZMod p)) 1).det*
          (bmat (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p) (harmSum (ZMod p)) 1).det))=0 := by
    linear_combination hc
  have hpow : (u0*topClear p q o M)^n*(u0*topClear p q o M)*(u0*topClear p q o M)^n≠0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hsc) hsc) (pow_ne_zero _ hsc)
  have h3 := (mul_eq_zero.mp key).resolve_left hpow
  have h4 := (mul_eq_zero.mp h3).resolve_right (mul_ne_zero n1 n2)
  linear_combination h4

end IntegerCross

section IntegerSeparation
variable (p : ℕ) [Fact p.Prime] (q o : ℕ)

theorem zmod_nat_ne (a : ℕ) (h1 : 1≤a) (h2 : a<p) : (a:ZMod p)≠0 := by
  simpa using zmod_cast_ne p a 0 h2 (Fact.out:p.Prime).pos (by omega)

/-- An actual fibre profile is a split of `κ..κ+2n` for the harmonic system. -/
theorem profile_split (κ η n : ℕ) (hη : η≤1) (hn : 1≤n) (hp : κ+2*n<p) :
    HSplit n κ ((κ:ZMod p)+1) (harmSum (ZMod p) κ) (harmSum (ZMod p))
      (profileRowQ κ η n) (profileColQ κ η n) where
  hn := hn
  hk := fun k h1 h2 => zmod_nat_ne p k h1 (by omega)
  hA := fun h hh => by
    have := zmod_nat_ne p (κ+1+h) (by omega) (by omega)
    push_cast at this
    exact this
  hL := fun s _ => harmSum_add κ s
  hxr := fun i => by unfold profileRowQ; have := i.2; split_ifs <;> omega
  hyr := fun j => by unfold profileColQ; have := j.2; omega
  hxy := fun i j => by unfold profileRowQ profileColQ; have := i.2; have := j.2; split_ifs <;> omega
  hyy := fun a b h => by unfold profileColQ at h; exact Fin.ext (by omega)
  hcov := fun s hs => by
    by_cases h2 : s=2*n
    · left
      refine ⟨Fin.last n,?_⟩
      unfold profileRowQ
      simp only [Fin.val_last,lt_irrefl,↓reduceIte]
      omega
    · rcases Nat.even_or_odd' s with ⟨t,ht|ht⟩ <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hη with rfl|rfl
      · left; refine ⟨⟨t,by omega⟩,?_⟩; unfold profileRowQ; simp only; rw [if_pos (by omega)]; omega
      · right; refine ⟨⟨t,by omega⟩,?_⟩; unfold profileColQ; simp only; omega
      · right; refine ⟨⟨t,by omega⟩,?_⟩; unfold profileColQ; simp only; omega
      · left; refine ⟨⟨t,by omega⟩,?_⟩; unfold profileRowQ; simp only; rw [if_pos (by omega)]; omega

/-- Section 8.3 in the ONE-parameter ring at an INTEGER cut: two actual
fibres with adjacent counts `κ`, `κ+1` (any bits) have distinct ORIGINAL
residue directions. The test is the top fractional coefficient (`Y = ∞`)
of ORIGINAL cleared numerators; the conditions are the fibres' own
quotient bounds `κ_i + 2n < p`. -/
theorem profile_separation_int (γ1 k1 η1 γ2 k2 η2 n M : ℕ) (s u : GaussLoc p) (u0 : ZMod p)
    (hγ1 : γ1<p) (hγ2 : γ2<p) (hη1 : η1≤1) (hη2 : η2≤1) (hn : 1≤n)
    (hk1 : k1+2*n<p) (hk2 : k2+2*n<p) (hz1 : pz p γ1 k1 n≤M) (hz2 : pz p γ2 k2 n≤M)
    (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : WrapDeform.residue p (WrapOwnCore.constants p u)=RatFunc.C (RatFunc.C u0))
    (hu00 : u0≠0) (hadj : k2=k1+1 ∨ k1=k2+1) :
    WrapDeform.residue p
      ((ringSystem1 p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u true).det*
        (ringSystem1 p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u false).det-
      (ringSystem1 p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u true).det*
        (ringSystem1 p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u false).det)≠0 := by
  have H1 := profileHyp p q o γ1 k1 η1 n M hγ1 hη1 hk1 hz1 hM hq0 hqp ho0 hoq
  have H2 := profileHyp p q o γ2 k2 η2 n M hγ2 hη2 hk2 hz2 hM hq0 hqp ho0 hoq
  have hr1 : (fun i => bordRow (pxr p γ1 k1 η1 n) (pz p γ1 k1 n) i/p)=profileRowQ k1 η1 n :=
    funext (bord_quot p _ _ _ _ hγ1)
  have hr2 : (fun i => bordRow (pxr p γ2 k2 η2 n) (pz p γ2 k2 n) i/p)=profileRowQ k2 η2 n :=
    funext (bord_quot p _ _ _ _ hγ2)
  have hcc1 : (fun c => pyc p γ1 k1 η1 n c/p)=profileColQ k1 η1 n := funext (col_quot p _ _ _ _ hγ1)
  have hcc2 : (fun c => pyc p γ2 k2 η2 n c/p)=profileColQ k2 η2 n := funext (col_quot p _ _ _ _ hγ2)
  apply residue_cross_top_ne H1 H2 s u u0 hs hu0 hu00 k1 k2
  · rw [hr1,hcc1]; exact profile_split p k1 η1 n hη1 hn hk1
  · rw [hr2,hcc2]; exact profile_split p k2 η2 n hη2 hn hk2
  · have hstep (κ : ℕ) (hκ : κ+n+1<p) : harmSum (ZMod p) (κ+n)≠harmSum (ZMod p) (κ+1+n) := by
      rw [show κ+1+n=(κ+n)+1 by omega,harmSum_succ]
      intro h
      have h0 : 1/((κ:ZMod p)+(n:ZMod p)+1)=0 := by push_cast at h; linear_combination -h
      have := zmod_nat_ne p (κ+n+1) (by omega) hκ
      push_cast at this
      exact one_div_ne_zero this h0
    rcases hadj with rfl|rfl
    · exact hstep k1 (by omega)
    · exact fun h => hstep k2 (by omega) h.symm

end IntegerSeparation

section IntegerKills
variable {p : ℕ} [Fact p.Prime]
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Two fibre tips separated by an integer pole within one period have
adjacent quotients. -/
theorem int_adjacent (A1 K1 A2 K2 p j : ℕ) (hA1 : A1<p) (hA2 : A2<p) (h1 : A1+K1*p<j*p)
    (h2 : j*p≤A2+K2*p) (h3 : A2+K2*p<A1+K1*p+p) : K2=K1+1 := by
  have a : K1<j := by
    by_contra hc
    have := Nat.mul_le_mul_right p (not_lt.mp hc)
    omega
  have b : j≤K2 := by
    by_contra hc
    have := Nat.mul_le_mul_right p (show K2+1≤j by omega)
    have e : (K2+1)*p=K2*p+p := by ring
    omega
  have c : K2≤K1+1 := by
    by_contra hc
    have := Nat.mul_le_mul_right p (show K1+2≤K2 by omega)
    have e : (K1+2)*p=K1*p+p+p := by ring
    omega
  omega

set_option maxHeartbeats 2000000 in
/-- Section 8.3 in the ONE-parameter ring at an actual outside node `v`
with fibre bit `η`, separated from the anchor by an original INTEGER pole
`k`: the actual reduced coupling against the original anchor is nonzero.
The two fibres have adjacent counts; each satisfies its own quotient bound,
so the upper one gives `p > κ+2n+1`. -/
theorem node_coupling_int_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (v k η : ℕ) (hη : η≤1)
    (hkI : p∣k)
    (hsep : (v<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤v))
    (hvlo : r+2*n*p≤v) (hvhi : v<r+2*n*p+p) (hvN : v<N)
    (hPv : ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p)).det≠0) :
    (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o v)-
      (fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ
      (fun i => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))-
    WrapDeform.residue p (H.anchor s u)*
    (1-(fun j => WrapDeform.residue p (WrapDeformedEntry.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((WrapFibreCore.core p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (WrapDeform.residue p))⁻¹ *ᵥ 1)≠0 := by
  classical
  obtain ⟨u0,hu0'⟩ := huc
  have huc : WrapConstant.Has p u := ⟨u0,hu0'⟩
  have hu0 := residue_constants1 p u u0 hu0'
  have hu00 : u0≠0 := by
    intro h; apply hu; rw [hu0',h,map_zero]
  have ht0N : H.t0<N := lt_of_le_of_lt H.hle H.htvN
  have ht0lo := H.hlo
  have ht0hi : H.t0<r+2*n*p+p := lt_of_le_of_lt H.hle H.hhi
  have ho0 : 0<o := by
    rcases Nat.eq_zero_or_pos o with h|h
    · exact absurd (by rw [h]; simp) H.ho
    · exact h
  have htv := (fibre_tip (p:=p) (r:=r) (n:=n) v hvlo hvhi).symm
  have ht0 := (fibre_tip (p:=p) (r:=r) (n:=n) H.t0 ht0lo ht0hi).symm
  unfold pz at htv ht0
  have hNp : N<p*p := single_bound H
  have hkv : WrapJointProfile.count p r (v:ZMod p).val+2*n<p := by
    by_contra hc
    have : p*p≤(WrapJointProfile.count p r (v:ZMod p).val+2*n)*p := Nat.mul_le_mul_right p (by omega)
    omega
  have hk0 : WrapJointProfile.count p r (H.t0:ZMod p).val+2*n<p := by
    by_contra hc
    have : p*p≤(WrapJointProfile.count p r (H.t0:ZMod p).val+2*n)*p := Nat.mul_le_mul_right p (by omega)
    omega
  have hpzv : pz p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) n=v := by
    unfold pz; exact htv.symm
  have hpz0 : pz p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) n=H.t0 := by
    unfold pz; exact ht0.symm
  have hz1 : pz p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) n≤N := by
    rw [hpzv]; exact hvN.le
  have hz2 : pz p (H.t0:ZMod p).val (WrapJointProfile.count p r (H.t0:ZMod p).val) n≤N := by
    rw [hpz0]; exact ht0N.le
  have hadj : WrapJointProfile.count p r (H.t0:ZMod p).val=WrapJointProfile.count p r (v:ZMod p).val+1 ∨
      WrapJointProfile.count p r (v:ZMod p).val=WrapJointProfile.count p r (H.t0:ZMod p).val+1 := by
    obtain ⟨j,rfl⟩ := hkI
    rcases hsep with ⟨h1,h2⟩|⟨h1,h2⟩
    · left
      have := int_adjacent _ _ _ _ p j (ZMod.val_lt (v:ZMod p)) (ZMod.val_lt (H.t0:ZMod p))
        (by rw [← htv,mul_comm j p]; exact h1) (by rw [← ht0,mul_comm j p]; exact h2)
        (by rw [← htv,← ht0]; omega)
      omega
    · right
      have := int_adjacent _ _ _ _ p j (ZMod.val_lt (H.t0:ZMod p)) (ZMod.val_lt (v:ZMod p))
        (by rw [← ht0,mul_comm j p]; exact h1) (by rw [← htv,mul_comm j p]; exact h2)
        (by rw [← htv,← ht0]; omega)
      omega
  have hps := profile_separation_int p q o (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)
    η (H.t0:ZMod p).val
    (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val)
    n N s u u0 (ZMod.val_lt _) (ZMod.val_lt _) hη (bit_le _) H.hn hkv hk0
    hz1 hz2 H.hN H.hq0 H.hqp ho0 H.hoq hs hu0 hu00 hadj
  rw [hpzv,hpz0] at hps
  exact node_coupling1_of_cross H s u hs hu huc v η hvlo hvhi hvN hPv hps

/-- R3, ACTUAL one-parameter kill: an outside surplus ROW separated from the
anchor by an original INTEGER pole has nonzero actual coupling. -/
theorem rowCoupling_int_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z : Fin d) (k : ℕ) (hkI : p∣k)
    (hsep : (WrapPrefixSchur.surplusRow H z<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusRow H z))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusRow H z)
    (hvhi : WrapPrefixSchur.surplusRow H z<r+2*n*p+p) :
    WrapPrefixSchur.rowCoupling H s u z≠0 := by
  have hvN : WrapPrefixSchur.surplusRow H z<N := WrapPrefixSchur.surplus_row_bound H z
  have hresv := surplus_not_residual H z
  unfold WrapPrefixSchur.rowCoupling
  rw [map_sub,map_mul,residue_rowMoment1 H s u hs hu huc,residue_rowRef1 H s u hs hu huc,
    fibre_load1 H s u hs hu huc _ hvN hresv,fibre_one1 H s u hs hu huc _ hvN hresv]
  exact node_coupling_int_ne H s u hs hu huc _ k _ (bit_le _) hkI hsep hvlo hvhi hvN
    (fibreCore1_det_ne H s u hs hu huc _ hresv)

/-- R3, ACTUAL one-parameter kill: an outside surplus COLUMN separated from
the anchor by an original INTEGER pole has nonzero actual coupling. -/
theorem colCoupling_int_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (y : Fin d) (k : ℕ) (hkI : p∣k)
    (hsep : (WrapPrefixSchur.surplusCol H y<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusCol H y))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusCol H y)
    (hvhi : WrapPrefixSchur.surplusCol H y<r+2*n*p+p) :
    WrapPrefixSchur.colCoupling H s u y≠0 := by
  have hvN : WrapPrefixSchur.surplusCol H y<N := WrapPrefixSchur.surplus_col_bound H y
  have hresv := surplus_col_not_residual H y
  unfold WrapPrefixSchur.colCoupling
  rw [map_sub,map_mul,residue_colMoment1 H s u hs hu huc,residue_colRef1 H s u hs hu huc,
    col_fibre_load1 H s u hs hu huc _ hvN hresv,col_fibre_one1 H s u hs hu huc _ hvN hresv]
  exact node_coupling_int_ne H s u hs hu huc _ k _ (by omega) hkI hsep hvlo hvhi hvN
    (colFibre1_det_ne H s u hs hu huc _ hresv)


end IntegerKills

section PoleKills
variable {p : ℕ} [Fact p.Prime]
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- R2 ∪ R3 row kill: an outside surplus ROW separated from the anchor by
any original pole (integer or fractional) has nonzero actual coupling. -/
theorem rowCoupling_pole_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z : Fin d) (k : ℕ) (hk : p∣k ∨ p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusRow H z<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusRow H z))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusRow H z)
    (hvhi : WrapPrefixSchur.surplusRow H z<r+2*n*p+p) :
    WrapPrefixSchur.rowCoupling H s u z≠0 := by
  by_cases hkI : p∣k
  · exact rowCoupling_int_ne H s u hs hu huc z k hkI hsep hvlo hvhi
  · exact rowCoupling_frac_ne H s u hs hu huc z k hkI (hk.resolve_left hkI) hsep hvlo hvhi

/-- R2 ∪ R3 column kill. -/
theorem colCoupling_pole_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (y : Fin d) (k : ℕ) (hk : p∣k ∨ p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusCol H y<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusCol H y))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusCol H y)
    (hvhi : WrapPrefixSchur.surplusCol H y<r+2*n*p+p) :
    WrapPrefixSchur.colCoupling H s u y≠0 := by
  by_cases hkI : p∣k
  · exact colCoupling_int_ne H s u hs hu huc y k hkI hsep hvlo hvhi
  · exact colCoupling_frac_ne H s u hs hu huc y k hkI (hk.resolve_left hkI) hsep hvlo hvhi

end PoleKills

theorem ovl_translate (r R a b c : ℕ) : ovl (r+c) (R+c) (a+c) (b+c)=ovl r R a b := by
  unfold ovl
  omega

/-- The three-translate border overlap is invariant under a common
translation of the border and the credited window (virtual to actual
coordinates), once the window starts at least one period in. -/
theorem beta3_translate (m a p w0 w1 c : ℕ) (hw0 : p≤w0) (hw : w0≤w1) :
    beta3 m (a+c) p (w0+c) (w1+c)=beta3 m a p w0 w1 := by
  unfold beta3
  rw [show a+c+2*m=(a+2*m)+c by ring,show w0+c+p=(w0+p)+c by ring,show w1+c+p=(w1+p)+c by ring,
    show w0+c-p=(w0-p)+c by omega,show w1+c-p=(w1-p)+c by omega,ovl_translate,ovl_translate,ovl_translate]


-- R3_MARKER


#print axioms spectral_top_domain
#print axioms stepBordered_zero
#print axioms stepBordered_one
#print axioms scaled_cross_ne
#print axioms coupling_cross
#print axioms embed1_clearedEntry
#print axioms embed1_clearedSystem_det
#print axioms residue_cross1_ne
#print axioms profile_separation_frac
#print axioms node_coupling1_ne
#print axioms rowCoupling_frac_ne
#print axioms colCoupling_frac_ne
#print axioms hload_fd
#print axioms fd_choose_mul
#print axioms harmonic_uniq
#print axioms residue_cross1_of_spec
#print axioms residue_cross1_ne
#print axioms node_coupling1_of_cross
#print axioms node_coupling1_ne
#print axioms HSplit.det_ne
#print axioms HSplit.dir
#print axioms clearedD_top
#print axioms residue_cross_top_ne
#print axioms profile_separation_int
#print axioms node_coupling_int_ne
#print axioms rowCoupling_int_ne
#print axioms colCoupling_int_ne
#print axioms rowCoupling_pole_ne
#print axioms colCoupling_pole_ne
#print axioms beta3_translate

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed

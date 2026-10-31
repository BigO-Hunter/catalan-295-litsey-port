module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixFamily
public import CatalanCore.Uniform.Content.UFSimple.WrapExpr
public import CatalanCore.Uniform.Content.UFSimple.WrapBivariate

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

/-- At an own-source zero, adding the actual last balanced pair
preserves the independently loaded fibre moment. -/
theorem append_moment (q o r k n gamma : ℕ) (s u : GaussLoc p)
    (direction : WrapDeform.Extension p)
    (hQ : IsUnit (WrapPrefixType.core p q o r k n gamma s u).det)
    (hM : IsUnit (WrapPrefixType.core p q o r k (n+1) gamma s u).det)
    (hz : WrapPrefixWindow.rowOwn p q o r k n gamma
      (WrapJointProfile.rowProfile p r gamma n) s u direction=0) :
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
  have hsource : sx ⬝ᵥ Q⁻¹ *ᵥ uR=zx := by
    exact (sub_eq_zero.mp hz).symm
  have hb := append_core (p:=p) q o r k n gamma s u
  have hunit : IsUnit ((WrapPrefixType.core p q o r k (n+1) gamma s u).submatrix
      (appendEquiv k n) (appendEquiv k n)).det := by
    rw [Matrix.det_submatrix_equiv_self]
    exact hM
  rw [hb] at hunit
  have hm := WrapAlgebra.mixedBorder_response_mixed Q hQ uR uC sx sy
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
  exact congrArg (WrapDeform.residue p) (he.symm.trans hm)

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

/-- The virtual own reference has the original nonzero residue. -/
theorem translated_reference (q o t delta : ℕ) (u : GaussLoc p)
    (rows cols : α → ℕ) (P : Matrix α α (WrapDeform.Extension p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (hw : ∀ h∈Icc 1 delta,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (hQ : IsUnit (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P).det) :
    WrapDeform.residue p (1-
      (fun i => WrapDeformedEntry.entry p q o u (t+delta) (cols i+delta)) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P)⁻¹ *ᵥ 1)=
    WrapDeform.residue p (1-
      (fun i => WrapDeformedEntry.entry p q o u t (cols i)) ⬝ᵥ
      (Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P)⁻¹ *ᵥ 1) := by
  let Q0 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i) (cols j))+P
  let Q1 := Matrix.of (fun i j => WrapDeformedEntry.entry p q o u (rows i+delta) (cols j+delta))+P
  have hm : Q1.map (WrapDeform.residue p)=Q0.map (WrapDeform.residue p) :=
    translated_matrix_map q o t delta u rows cols P hr hc hw
  exact WrapPrefixType.reference_map_congr (WrapDeform.residue p) Q1 Q0
    (unit_of_same_reduction Q0 Q1 hQ hm) hQ _ _ hm
    (fun i => WrapPrefixType.entry_residue_shift p q o t _ t delta u rfl (hc i) hw)

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

/-- Lower-count row profile in the cut ordering. -/
theorem lower_cut_rows (r k n gamma : ℕ)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=0) :
    WrapPrefixType.rows p r k (n+1) gamma=Sum.elim
      (fun i:Fin k => gamma+(i:ℕ)*p) (fun i:Fin (n+1) => gamma+(k+2*(i:ℕ))*p) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.rows,Sum.elim_inr,WrapJointProfile.rowProfile,WrapJointProfile.lower,hk,hb]
    ring

/-- Lower-count column profile in the independent cut ordering. -/
theorem lower_cut_cols (r k n gamma : ℕ)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=0) :
    WrapPrefixType.cols p r k (n+1) gamma=Sum.elim
      (fun i:Fin k => gamma+(i:ℕ)*p) (fun i:Fin (n+1) => gamma+(k+2*(i:ℕ)+1)*p) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.cols,Sum.elim_inr,WrapJointProfile.colProfile,WrapJointProfile.lower,hk,hb]
    ring

/-- Upper-count reference rows after the common-count cut. -/
theorem upper_cut_rows (r k n gamma : ℕ)
    (hk : WrapJointProfile.count p r gamma=k+1) (hb : WrapJointProfile.bit p r gamma=1) :
    WrapPrefixType.rows p r (k+1) n gamma=Sum.elim
      (fun i:Fin (k+1) => gamma+(i:ℕ)*p) (fun i:Fin n => gamma+(k+2+2*(i:ℕ))*p) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.rows,Sum.elim_inr,WrapJointProfile.rowProfile,WrapJointProfile.lower,hk,hb]
    ring

/-- Upper-count reference columns after the common-count cut. -/
theorem upper_cut_cols (r k n gamma : ℕ)
    (hk : WrapJointProfile.count p r gamma=k+1) (hb : WrapJointProfile.bit p r gamma=1) :
    WrapPrefixType.cols p r (k+1) n gamma=Sum.elim
      (fun i:Fin (k+1) => gamma+(i:ℕ)*p) (fun i:Fin n => gamma+(k+1+2*(i:ℕ))*p) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [WrapPrefixType.cols,Sum.elim_inr,WrapJointProfile.colProfile,WrapJointProfile.lower,hk,hb]
    ring

/-- The lower cut matrix is the original canonical mixed profile. -/
theorem lower_cut_core (q o r k n gamma : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=0) :
    WrapPrefixType.core p q o r k (n+1) gamma s u=lowerCutCore (p:=p) q o gamma k n s u := by
  ext i j
  simp only [WrapPrefixType.core,lowerCutCore,WrapFibreCore.core,Matrix.add_apply,Matrix.of_apply]
  congr 1
  change WrapDeformedEntry.entry p q o u (WrapPrefixType.rows p r k (n+1) gamma i)
      (WrapPrefixType.cols p r k (n+1) gamma j)=_
  rw [lower_cut_rows (p:=p) r k n gamma hk hb,lower_cut_cols (p:=p) r k n gamma hk hb]

/-- The upper cut matrix preserves the original common spectral nodes. -/
theorem upper_cut_core (q o r k n gamma : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k+1) (hb : WrapJointProfile.bit p r gamma=1) :
    WrapPrefixType.core p q o r (k+1) n gamma s u=upperCutCore (p:=p) q o gamma k n s u := by
  ext i j
  simp only [WrapPrefixType.core,upperCutCore,WrapFibreCore.core,Matrix.add_apply,Matrix.of_apply]
  congr 1
  change WrapDeformedEntry.entry p q o u (WrapPrefixType.rows p r (k+1) n gamma i)
      (WrapPrefixType.cols p r (k+1) n gamma j)=_
  rw [upper_cut_rows (p:=p) r k n gamma hk hb,upper_cut_cols (p:=p) r k n gamma hk hb]

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

/-- The two virtual common-count cases have exactly the four actual
profile shapes used by the mixed-border and column-replacement steps. -/
theorem profile_count_cases (old target n full targetFull bit : ℕ)
    (hbit : bit≤1) (hanchor : full=old+n) (htarget : targetFull=target+n+bit)
    (hcell : targetFull=full ∨ targetFull=full+1) :
    (bit=0 ∧ target=old) ∨ (bit=1 ∧ target+1=old) ∨
      (bit=0 ∧ target=old+1) ∨ (bit=1 ∧ target=old) := by
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

theorem profile_entry (q o k n gamma bit : ℕ) (s u : GaussLoc p) (i j : Fin k ⊕ Fin n) :
    profileCore (p:=p) q o k n gamma bit s u i j=
      WrapDeformedEntry.entry p q o u (profileRows p k n gamma bit i) (profileCols p k n gamma bit j)+
        WrapPrefixType.spectral p k n s i j := rfl

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

theorem profile_col_prefix (q o r k n gamma bit : ℕ) (s u : GaussLoc p)
    (hk : WrapJointProfile.count p r gamma=k) (hb : WrapJointProfile.bit p r gamma=bit)
    (direction : WrapDeform.Extension p) :
    profileColOwn (p:=p) q o k n gamma bit s u direction=
      WrapPrefixWindow.colOwn p q o r k n gamma (gamma+(k+2*n)*p) s u direction := by
  unfold profileColOwn WrapPrefixWindow.colOwn
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

/-- A distinct zone appended to the row nodes supplies the square
Cauchy factor in the central-threshold test. -/
theorem cauchy_zone_nodes_injective (x : Fin n → K) (t : K)
    (hx : Function.Injective x) (ht : ∀ i,x i≠t) :
    Function.Injective (Fin.lastCases t x : Fin (n+1) → K) := by
  intro i j he
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i0,rfl⟩|rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j0,rfl⟩|rfl
  · exact congrArg Fin.castSucc (hx (by simpa using he))
  · exact False.elim (ht i0 (by simpa using he))
  · exact False.elim (ht j0 (by simpa using he.symm))
  · rfl

/-- Cleared own-source test matrix with n+1 central poles. Its two
factors are the square Cauchy block and the normalized rectangular one. -/
noncomputable def centralPotentialArrow (x y : Fin n → K) (z : Fin (n+1) → K) (t : K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  -(WrapCauchy.matrix (Fin.lastCases t x) z)*((cauchyWithOnes y z)ᵀ)

theorem centralPotentialArrow_det_ne (x y : Fin n → K) (z : Fin (n+1) → K) (t : K)
    (hx : Function.Injective x) (hy : Function.Injective y) (hz : Function.Injective z)
    (hxt : ∀ i,x i≠t) (hxz : ∀ i j,x i≠z j) (hyz : ∀ i j,y i≠z j) (htz : ∀ j,t≠z j) :
    (centralPotentialArrow x y z t).det≠0 := by
  have hA := WrapCauchy.det_ne (Fin.lastCases t x) z (cauchy_zone_nodes_injective x t hx hxt) hz (by
    intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · simpa only [Fin.lastCases_last] using htz j
    · simpa only [Fin.lastCases_castSucc] using hxz a j)
  have hB := cauchyWithOnes_det_ne y z hy hz hyz
  unfold centralPotentialArrow
  rw [Matrix.det_mul,Matrix.det_neg,Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hA) hB

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

/-- At a central threshold, independent low/high row and column
partitions give exactly the two square Cauchy blocks from the handoff. -/
theorem step_block_eq {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut) :
    (Matrix.of fun i j => stepEntry (K:=K) cut (Sum.elim xL xH i) (Sum.elim yH yL j))=
      Matrix.fromBlocks
        (-(WrapCauchy.matrix (fun i => (xL i:K)) (fun j => (yH j:K)))) 0 0
        (WrapCauchy.matrix (fun i => (xH i:K)) (fun j => (yL j:K))) := by
  classical
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · simp only [Matrix.of_apply,Sum.elim_inl,Matrix.fromBlocks_apply₁₁,Matrix.neg_apply,
      WrapCauchy.matrix,stepEntry,stepValue,if_pos (hxL i),if_neg (not_lt_of_ge (hyH j)),
      sub_zero]
    exact one_div_reverse _ _
  · simp only [Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply,stepEntry,stepValue,if_pos (hxL i),if_pos (hyL j),sub_self,zero_div]
  · simp only [Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply,stepEntry,stepValue,if_neg (not_lt_of_ge (hxH i)),
      if_neg (not_lt_of_ge (hyH j)),sub_self,zero_div]
  · simp only [Matrix.of_apply,Sum.elim_inr,Matrix.fromBlocks_apply₂₂,WrapCauchy.matrix,
      stepEntry,stepValue,if_neg (not_lt_of_ge (hxH i)),if_pos (hyL j),zero_sub,neg_div]
    rw [one_div_reverse,neg_neg]

/-- The original central-threshold step core is nonsingular whenever
its actual quotient coordinates supply distinct Cauchy nodes. -/
theorem step_block_det_ne {l h : ℕ} (cut : ℕ)
    (xL yH : Fin l → ℕ) (xH yL : Fin h → ℕ)
    (hxL : ∀ i,xL i<cut) (hyH : ∀ i,cut≤yH i)
    (hxH : ∀ i,cut≤xH i) (hyL : ∀ i,yL i<cut)
    (hxiL : Function.Injective (fun i => (xL i:K)))
    (hyiH : Function.Injective (fun i => (yH i:K)))
    (hxiH : Function.Injective (fun i => (xH i:K)))
    (hyiL : Function.Injective (fun i => (yL i:K)))
    (hxy0 : ∀ i j,(xL i:K)≠(yH j:K)) (hxy1 : ∀ i j,(xH i:K)≠(yL j:K)) :
    (Matrix.of fun i j => stepEntry (K:=K) cut (Sum.elim xL xH i) (Sum.elim yH yL j)).det≠0 := by
  rw [step_block_eq cut xL yH xH yL hxL hyH hxH hyL,
    Matrix.det_fromBlocks_zero₂₁,Matrix.det_neg]
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (WrapCauchy.det_ne _ _ hxiL hyiH hxy0))
    (WrapCauchy.det_ne _ _ hxiH hyiL hxy1)

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

/-- Move the ORIGINAL spectral coordinate past the two pole coordinates
inside cleared polynomials. Both swaps are the existing polynomial swaps. -/
noncomputable def spectralLast : K[X][X][X] →+* K[X][X][X] :=
  (Polynomial.Bivariate.swap (R:=K[X])).toRingHom.comp
    (Polynomial.mapRingHom (Polynomial.Bivariate.swap (R:=K)).toRingHom)

theorem spectralLast_injective : Function.Injective (spectralLast (K:=K)) :=
  (Polynomial.Bivariate.swap (R:=K[X])).injective.comp
    (Polynomial.map_injective _ (Polynomial.Bivariate.swap (R:=K)).injective)

/-- The ORIGINAL cleared three-variable expression embeds faithfully in
the actual nested residue field, without evaluating a generic pivot. -/
noncomputable def embedThree : K[X][X][X] →+* RatFunc (RatFunc (RatFunc K)) :=
  (algebraMap (RatFunc (RatFunc K))[X] (RatFunc (RatFunc (RatFunc K)))).comp
    (Polynomial.mapRingHom (WrapBivariate.embed (K:=K)))

theorem embedThree_injective : Function.Injective (embedThree (K:=K)) :=
  (IsFractionRing.injective (RatFunc (RatFunc K))[X] (RatFunc (RatFunc (RatFunc K)))).comp
    (Polynomial.map_injective _ WrapBivariate.embed_injective)

/-- A nonzero spectral-leading polynomial proves nonvanishing of the
ORIGINAL field expression after returning to its original variable order. -/
theorem embedThree_ne_of_spectralLast (F : K[X][X][X])
    (hF : spectralLast F≠0) : embedThree F≠0 := by
  intro hz
  have hzero : F=0 := embedThree_injective (by simpa only [map_zero] using hz)
  exact hF (by rw [hzero,map_zero])

theorem spectralLast_original_spectral :
    spectralLast (K:=K) (Polynomial.C (Polynomial.C (Polynomial.X:K[X])))=
      (Polynomial.X:K[X][X][X]) := by
  simp [spectralLast,Polynomial.Bivariate.swap_C,Polynomial.Bivariate.swap_X,Polynomial.Bivariate.swap_Y]

theorem spectralLast_integer_pole :
    spectralLast (K:=K) (Polynomial.X:K[X][X][X])=
      Polynomial.C (Polynomial.X:K[X][X]) := by
  simp [spectralLast,Polynomial.Bivariate.swap_X,Polynomial.Bivariate.swap_Y]

theorem spectralLast_fractional_pole :
    spectralLast (K:=K) (Polynomial.C (Polynomial.X:K[X][X]))=
      Polynomial.C (Polynomial.C (Polynomial.X:K[X])) := by
  simp [spectralLast,Polynomial.Bivariate.swap_C,Polynomial.Bivariate.swap_X,Polynomial.Bivariate.swap_Y]

end SpectralOrder

noncomputable def twoHarmonicLoad {K : Type*} [Field K]
    (integer fractional : K) (epsilon : Bool) (j : ℕ) : K :=
  (∑ h∈range j,(1:K)/(1+integer+(h:K)))-
    ∑ h∈range (j+if epsilon then 1 else 0),(1:K)/(fractional+(h:K))

theorem twoHarmonicLoad_zero_integer {K : Type*} [Field K]
    (fractional : K) (epsilon : Bool) (j : ℕ) :
    twoHarmonicLoad (0:K) fractional epsilon j=WrapHarmonic.load fractional epsilon j := by
  simp only [twoHarmonicLoad,WrapHarmonic.load,add_zero]

theorem rational_div_eq_mul_inv {S : Type*} [CommRing S] [IsDomain S]
    (a b : RatFunc S) : a/b=a*b⁻¹ := div_eq_mul_inv a b

theorem rational_one_div {S : Type*} [CommRing S] [IsDomain S]
    (a : RatFunc S) : (1:RatFunc S)/a=a⁻¹ := one_div a

theorem rational_div_one {S : Type*} [CommRing S] [IsDomain S]
    (a : RatFunc S) : a/(1:RatFunc S)=a := div_one a

section TwoParameterDescent
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable (phi : R →+* K)

local instance firstParameterDomain : IsDomain (WrapParameter.Extension phi) :=
  WrapPrefixSchur.parameter_domain phi

/-- Faithful original polynomial representation with two independent
pole parameters. The original spectral variable stays in R. -/
noncomputable def bivariateParameterEmbed : R[X][X] →+*
    WrapParameter.Extension (WrapParameter.residue phi) :=
  (algebraMap (WrapParameter.Extension phi)[X]
    (WrapParameter.Extension (WrapParameter.residue phi))).comp
      (Polynomial.mapRingHom (algebraMap R[X] (WrapParameter.Extension phi)))

noncomputable def secondParameterUniformizer (pi : R) :=
  WrapParameter.uniformizer (WrapParameter.residue phi) (WrapParameter.uniformizer phi pi)

/-- An original specialization-unit polynomial is a generic unit.
This does not assert that a generic pivot survives specialization. -/
theorem original_denominator_unit (D : R[X]) (hD : IsUnit (D.eval 0)) :
    IsUnit (algebraMap R[X] (WrapParameter.Extension phi) D) := by
  apply WrapParameter.unit_of_poly_ne phi
  intro hz
  have hm : D.map phi=0 := by
    apply IsFractionRing.injective K[X] (RatFunc K)
    change algebraMap K[X] (RatFunc K) (D.map phi)=0 at hz
    simpa only [map_zero] using hz
  have hc := congrArg (fun f:K[X] => f.coeff 0) hm
  simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hc
  have hu : IsUnit (D.coeff 0) := by simpa only [←Polynomial.coeff_zero_eq_eval_zero] using hD
  exact (hu.map phi).ne_zero hc

/-- The ORIGINAL D(0,0) unit already makes its generic two-parameter
image a unit; no elimination denominator is involved. -/
theorem bivariate_original_denominator_unit (D : R[X][X])
    (hD : IsUnit ((D.eval 0).eval 0)) : IsUnit (bivariateParameterEmbed phi D) := by
  apply original_denominator_unit (WrapParameter.residue phi)
  change IsUnit ((D.map (algebraMap R[X] (WrapParameter.Extension phi))).eval 0)
  rw [Polynomial.eval_zero_map]
  exact original_denominator_unit phi (D.eval 0) hD

/-- The elementary denominator in Section 8.1, after removing the
ORIGINAL simple-pole uniformizer power. -/
noncomputable def originalShiftDenominator (pi d q : R) (epsilon : ℕ) : R[X] :=
  Polynomial.C d+Polynomial.C (q*pi^(1-epsilon))*Polynomial.X

theorem originalShiftDenominator_factor (pi d q : R) (epsilon : ℕ)
    (he : epsilon≤1) :
    Polynomial.C (pi^epsilon)*originalShiftDenominator pi d q epsilon=
      Polynomial.C (pi^epsilon*d)+Polynomial.C (q*pi)*Polynomial.X := by
  have hs : epsilon+(1-epsilon)=1 := by omega
  have hp : pi^epsilon*pi^(1-epsilon)=pi := by rw [←pow_add,hs,pow_one]
  have hq : pi^epsilon*(q*pi^(1-epsilon))=q*pi := by
    calc
      _=q*(pi^epsilon*pi^(1-epsilon)) := by ring
      _=_ := by rw [hp]
  simp only [originalShiftDenominator,mul_add,←mul_assoc,←map_mul,hq]

theorem originalShiftDenominator_at_zero (pi d q : R) (epsilon : ℕ)
    (hd : IsUnit d) : IsUnit ((originalShiftDenominator pi d q epsilon).eval 0) := by
  simpa only [originalShiftDenominator,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_mul,Polynomial.eval_X,mul_zero,add_zero] using hd

/-- The displayed entry exponents are genuine nonnegative exponents;
Nat subtraction has not silently truncated a negative power. -/
theorem original_entry_exponents (epsilon v : ℕ) (he : epsilon≤1) (hv : v≤1) :
    epsilon+v+(2-epsilon-v)=2 ∧ 2*epsilon+(2-2*epsilon)=2 := by omega

/-- The original normalized reciprocal in a generic pole family,
using its original simple-pole exponent and original unit quotient. -/
noncomputable def originalScaledPoleInverse (pi d q : R) (epsilon : ℕ) :
    WrapParameter.Extension phi :=
  algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C (pi^(1-epsilon)))*
    Ring.inverse (algebraMap R[X] (WrapParameter.Extension phi)
      (originalShiftDenominator pi d q epsilon))

theorem originalScaledPoleInverse_specializes (pi d q : R) (epsilon : ℕ)
    (hd : IsUnit d) :
    WrapSpecialization.Rel phi (originalScaledPoleInverse phi pi d q epsilon)
      (pi^(1-epsilon)*Ring.inverse d) := by
  have hD0 := originalShiftDenominator_at_zero pi d q epsilon hd
  have hD := original_denominator_unit phi _ hD0
  have hI := WrapSpecialization.Rel.inverse_polynomial
    (phi:=phi) (originalShiftDenominator pi d q epsilon) hD0
    (Ring.inverse (algebraMap R[X] (WrapParameter.Extension phi)
      (originalShiftDenominator pi d q epsilon))) (Ring.mul_inverse_cancel _ hD)
  have hC := WrapSpecialization.Rel.constant (phi:=phi) (pi^(1-epsilon))
  simpa only [originalScaledPoleInverse,originalShiftDenominator,
    Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,
    mul_zero,add_zero] using WrapSpecialization.Rel.mul hC hI

theorem map_ring_inverse_of_unit {S : Type*} [CommRing S] (f : S →+* R)
    (a : S) (ha : IsUnit a) : f (Ring.inverse a)=Ring.inverse (f a) := by
  apply mul_left_cancel₀ (ha.map f).ne_zero
  rw [←map_mul,Ring.mul_inverse_cancel _ ha,map_one,Ring.mul_inverse_cancel _ (ha.map f)]

/-- The original coefficient lift commutes with a cleared elementary
specialization because the ORIGINAL quotient is already a unit. -/
theorem originalScaledPoleInverse_map_specializes {S : Type*} [CommRing S]
    (f : S →+* R) (pi d q : S) (epsilon : ℕ) (hd : IsUnit d) :
    WrapSpecialization.Rel phi
      (originalScaledPoleInverse phi (f pi) (f d) (f q) epsilon)
      (f (pi^(1-epsilon)*Ring.inverse d)) := by
  simpa only [map_mul,map_pow,map_ring_inverse_of_unit f d hd] using
    originalScaledPoleInverse_specializes phi (f pi) (f d) (f q) epsilon (hd.map f)

/-- Multiplication by the ORIGINAL deformed denominator gives the
uniformizer, before any residue or pivot operation. -/
theorem originalScaledPoleInverse_identity (pi d q : R) (epsilon : ℕ)
    (he : epsilon≤1) (hd : IsUnit d) :
    algebraMap R[X] (WrapParameter.Extension phi)
      (Polynomial.C (pi^epsilon*d)+Polynomial.C (q*pi)*Polynomial.X)*
        originalScaledPoleInverse phi pi d q epsilon=WrapParameter.uniformizer phi pi := by
  have hD := original_denominator_unit phi _ (originalShiftDenominator_at_zero pi d q epsilon hd)
  have hs : epsilon+(1-epsilon)=1 := by omega
  have hp : pi^epsilon*pi^(1-epsilon)=pi := by rw [←pow_add,hs,pow_one]
  rw [←originalShiftDenominator_factor pi d q epsilon he,map_mul]
  unfold originalScaledPoleInverse
  calc
    _=(algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C (pi^epsilon))*
        algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C (pi^(1-epsilon))))*
      (algebraMap R[X] (WrapParameter.Extension phi) (originalShiftDenominator pi d q epsilon)*
        Ring.inverse (algebraMap R[X] (WrapParameter.Extension phi)
          (originalShiftDenominator pi d q epsilon))) := by ring
    _=_ := by rw [Ring.mul_inverse_cancel _ hD,mul_one,←map_mul,←map_mul,hp]; rfl

/-- Descend the ORIGINAL bivariate numerator coefficient by coefficient,
using the existing one-parameter descent twice. -/
theorem bivariate_parameter_descend (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a)
    (hpi : Prime pi) (F : R[X][X]) (k : ℕ)
    (h : secondParameterUniformizer phi pi^k∣bivariateParameterEmbed phi F) :
    Polynomial.C (Polynomial.C pi)^k∣F := by
  obtain ⟨x,hx⟩ := h
  have hd := WrapParameter.descend (WrapParameter.residue phi)
    (WrapParameter.uniformizer phi pi) (WrapParameter.residue_zero_iff phi pi hker)
    (WrapParameterLift.uniformizer_prime phi pi hker hpi)
    (F.map (algebraMap R[X] (WrapParameter.Extension phi))) k x hx
  rw [←map_pow,Polynomial.C_dvd_iff_dvd_coeff] at hd ⊢
  intro i
  obtain ⟨y,hy⟩ := hd i
  simp only [Polynomial.coeff_map] at hy
  exact WrapParameter.descend phi pi hker hpi (F.coeff i) k y hy

/-- Original N/D descent at both zero parameters. Only the ORIGINAL
D(0,0) is canceled; no elimination pivot is specialized. -/
theorem bivariate_original_specialize (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a)
    (hpi : Prime pi) (D N : R[X][X]) (k : ℕ)
    (h : secondParameterUniformizer phi pi^k∣bivariateParameterEmbed phi (D*N))
    (hD : IsUnit ((D.eval 0).eval 0)) : pi^k∣(N.eval 0).eval 0 := by
  have hd := bivariate_parameter_descend phi pi hker hpi (D*N) k h
  let ev : R[X][X] →+* R :=
    (Polynomial.evalRingHom (0:R)).comp (Polynomial.evalRingHom (0:R[X]))
  have he := WrapAlgebra.specialize_cleared ev
    (Polynomial.C (Polynomial.C pi)^k) D N hd hD
  simpa only [ev,RingHom.coe_comp,Function.comp_apply,Polynomial.coe_evalRingHom,
    Polynomial.eval_pow,Polynomial.eval_C] using he

/-- Finite original entry sums retain their original-unit clearing
representations over either coefficient ring. -/
theorem parameter_sum_specializes {α : Type*} (S : Finset α)
    (f : α → WrapParameter.Extension phi) (f0 : α → R)
    (h : ∀ i∈S,WrapSpecialization.Rel phi (f i) (f0 i)) :
    WrapSpecialization.Rel phi (∑ i∈S,f i) (∑ i∈S,f0 i) := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty =>
    intro h
    simp only [Finset.sum_empty]
    exact WrapSpecialization.Rel.zero
  | @insert i S hi ih =>
    intro h
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact WrapSpecialization.Rel.add (h i (mem_insert_self i S))
      (ih (fun j hj => h j (mem_insert_of_mem hj)))

/-- A unit in the original specialization proves a generic unit,
using its original clearing representation rather than evaluating a pivot. -/
theorem parameter_unit_of_specialization (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a)
    (hpi : Prime pi) (x : WrapParameter.Extension phi) (x0 : R)
    (hx : WrapSpecialization.Rel phi x x0) (hu : IsUnit x0) : IsUnit x := by
  have he : WrapEvaluation.Rel phi 0 x x0 := hx
  exact WrapUnits.of_residue_ne phi x
    (WrapEvaluation.Rel.residue_ne pi hker hpi he (hu.map phi).ne_zero)

theorem parameter_matrix_unit {α : Type*} [Fintype α] [DecidableEq α]
    (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (Q : Matrix α α (WrapParameter.Extension phi)) (Q0 : Matrix α α R)
    (hQ : ∀ i j,WrapSpecialization.Rel phi (Q i j) (Q0 i j))
    (hu : IsUnit Q0.det) : IsUnit Q.det :=
  parameter_unit_of_specialization phi pi hker hpi _ _
    (WrapSpecialization.determinant phi Q Q0 hQ) hu

theorem sum_vecMul_eq {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → R) (Q : Matrix α α R) : (∑ j,(v ᵥ* Q) j)=v ⬝ᵥ (Q *ᵥ 1) := by
  simp only [Matrix.vecMul,Matrix.mulVec,dotProduct,Pi.one_apply,mul_one,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Cleared reference arrows inherit ORIGINAL entry specialization;
no inverse matrix occurs in this relation. -/
theorem parameter_arrow_specializes {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α (WrapParameter.Extension phi)) (Q0 : Matrix α α R)
    (sigma : α → WrapParameter.Extension phi) (sigma0 : α → R)
    (hQ : ∀ i j,WrapSpecialization.Rel phi (Q i j) (Q0 i j))
    (hs : ∀ i,WrapSpecialization.Rel phi (sigma i) (sigma0 i))
    (i j : α ⊕ Unit) :
    WrapSpecialization.Rel phi (WrapArrowCore.arrow Q sigma i j)
      (WrapArrowCore.arrow Q0 sigma0 i j) := by
  rcases i with i|⟨⟩ <;> rcases j with j|⟨⟩
  · exact hQ i j
  · exact WrapSpecialization.Rel.one
  · exact hs j
  · exact WrapSpecialization.Rel.one

/-- Both generic pivot and reference are supplied by their original
nonzero tests. Central tests need not preserve either individual pivot. -/
theorem parameter_reference_unit {α : Type*} [Fintype α] [DecidableEq α]
    (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (Q : Matrix α α (WrapParameter.Extension phi)) (Q0 : Matrix α α R)
    (sigma : α → WrapParameter.Extension phi) (sigma0 : α → R)
    (hQ : ∀ i j,WrapSpecialization.Rel phi (Q i j) (Q0 i j))
    (hs : ∀ i,WrapSpecialization.Rel phi (sigma i) (sigma0 i))
    (hu : IsUnit Q0.det) (hB : IsUnit (1-sigma0 ⬝ᵥ (Q0⁻¹ *ᵥ 1))) :
    IsUnit Q.det ∧ IsUnit (1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1)) := by
  have hnew := parameter_matrix_unit phi pi hker hpi Q Q0 hQ hu
  have hA0 : IsUnit (WrapArrowCore.arrow Q0 sigma0).det := by
    rw [WrapArrowCore.det_arrow Q0 hu sigma0]
    exact hu.mul hB
  have hA := parameter_matrix_unit phi pi hker hpi
    (WrapArrowCore.arrow Q sigma) (WrapArrowCore.arrow Q0 sigma0)
    (parameter_arrow_specializes phi Q Q0 sigma sigma0 hQ hs) hA0
  rw [WrapArrowCore.det_arrow Q hnew sigma] at hA
  exact ⟨hnew,isUnit_of_mul_isUnit_right hA⟩

theorem parameter_constant_residue (a : R) :
    WrapParameter.residue phi (algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C a))=
      RatFunc.C (phi a) := by
  rw [WrapParameter.residue_map]
  change algebraMap K[X] (RatFunc K) ((Polynomial.C a).map phi)=_
  rw [Polynomial.map_C,RatFunc.algebraMap_C]

theorem parameter_inverse_residue (x : WrapParameter.Extension phi) (hx : IsUnit x) :
    WrapParameter.residue phi (Ring.inverse x)=(WrapParameter.residue phi x)⁻¹ := by
  have hh := congrArg (WrapParameter.residue phi) (Ring.mul_inverse_cancel x hx)
  rw [map_mul,map_one] at hh
  exact eq_inv_of_mul_eq_one_right hh

/-- An original nonpole contributes zero after normalized reduction,
even with the independent new pole parameter. -/
theorem originalScaledPoleInverse_zero_residue (pi d q : R) (hp : phi pi=0) :
    WrapParameter.residue phi (originalScaledPoleInverse phi pi d q 0)=0 := by
  unfold originalScaledPoleInverse
  rw [map_mul,parameter_constant_residue]
  simp only [Nat.sub_zero,pow_one,hp,map_zero,zero_mul]

/-- A simple original pole retains its actual quotient plus the new
parameter, in the second residue field. -/
theorem originalScaledPoleInverse_one_residue (pi d q : R) (hd : IsUnit d) :
    WrapParameter.residue phi (originalScaledPoleInverse phi pi d q 1)=
      (1:RatFunc K)/(RatFunc.C (phi d)+RatFunc.C (phi q)*(RatFunc.X:RatFunc K)) := by
  have hD := original_denominator_unit phi _ (originalShiftDenominator_at_zero pi d q 1 hd)
  have he : WrapParameter.residue phi
      (algebraMap R[X] (WrapParameter.Extension phi) (originalShiftDenominator pi d q 1))=
        RatFunc.C (phi d)+RatFunc.C (phi q)*(RatFunc.X:RatFunc K) := by
    rw [WrapParameter.residue_map]
    change algebraMap K[X] (RatFunc K) ((originalShiftDenominator pi d q 1).map phi)=_
    simp only [originalShiftDenominator,Nat.sub_self,pow_zero,mul_one,
      Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
      map_add,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  unfold originalScaledPoleInverse
  rw [map_mul,parameter_constant_residue,parameter_inverse_residue phi _ hD,he]
  simp only [Nat.sub_self,pow_zero,map_one,one_mul,one_div]

/-- The standard inverse perturbation identity gives the required
SECOND uniformizer power at an original nonpole. -/
theorem normalized_inverse_difference (pi A B Ainv Dinv : R)
    (hA : A*Ainv=1) (hD : (A+pi*B)*Dinv=1) : pi^2∣pi*Dinv-pi*Ainv := by
  refine ⟨-B*Dinv*Ainv,?_⟩
  linear_combination pi*Ainv*hD-pi*Dinv*hA

/-- Regular normalized reciprocals retain the original first-order
source under an independent pole deformation. -/
theorem originalScaledPoleInverse_nonpole_congr (pi d q : R) (hd : IsUnit d) :
    (WrapParameter.uniformizer phi pi)^2∣originalScaledPoleInverse phi pi d q 0-
      algebraMap R[X] (WrapParameter.Extension phi) (Polynomial.C (pi*Ring.inverse d)) := by
  let C : R →+* WrapParameter.Extension phi :=
    (algebraMap R[X] (WrapParameter.Extension phi)).comp Polynomial.C
  let Y := algebraMap R[X] (WrapParameter.Extension phi) Polynomial.X
  let D := algebraMap R[X] (WrapParameter.Extension phi) (originalShiftDenominator pi d q 0)
  have hA : C d*C (Ring.inverse d)=1 := by rw [←map_mul,Ring.mul_inverse_cancel _ hd,map_one]
  have hDu := original_denominator_unit phi _ (originalShiftDenominator_at_zero pi d q 0 hd)
  have he : D=C d+C pi*(C q*Y) := by
    dsimp only [D,C,Y,originalShiftDenominator,RingHom.comp_apply]
    simp only [Nat.sub_zero,pow_one,map_add,map_mul]
    ring
  have hD : (C d+C pi*(C q*Y))*Ring.inverse D=1 := by
    rw [←he]
    exact Ring.mul_inverse_cancel _ hDu
  have hh := normalized_inverse_difference (C pi) (C d) (C q*Y)
    (C (Ring.inverse d)) (Ring.inverse D) hA hD
  simpa only [originalScaledPoleInverse,Nat.sub_zero,pow_one,map_mul,C,D,
    WrapParameter.uniformizer,RingHom.comp_apply] using hh

/-- The normalized bordered direction annihilates its own row response.
This uses only the proved inverse identity for its reference scalar. -/
theorem reference_direction_zero {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α R) (sigma y : α → R) (Lt bInv : R)
    (hB : (1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1))*bInv=1) :
    let d := (Lt-sigma ⬝ᵥ (Q⁻¹ *ᵥ y))*bInv
    (Lt-d)-sigma ⬝ᵥ (Q⁻¹ *ᵥ fun i => y i-d)=0 := by
  dsimp only
  let d := (Lt-sigma ⬝ᵥ (Q⁻¹ *ᵥ y))*bInv
  have hd : d*(1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1))=Lt-sigma ⬝ᵥ (Q⁻¹ *ᵥ y) := by
    dsimp only [d]
    calc
      _=(Lt-sigma ⬝ᵥ (Q⁻¹ *ᵥ y))*((1-sigma ⬝ᵥ (Q⁻¹ *ᵥ 1))*bInv) := by ring
      _=_ := by rw [hB,mul_one]
  change (Lt-d)-sigma ⬝ᵥ (Q⁻¹ *ᵥ fun i => y i-d)=0
  have he : (fun i => y i-d)=y-d • (1:α → R) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [he,Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,dotProduct_smul]
  simp only [smul_eq_mul]
  linear_combination -hd

end TwoParameterDescent

namespace TwoTermDeformation
variable (p : ℕ) [Fact p.Prime]

noncomputable def coefficientDomain :=
  WrapPrefixSchur.parameter_domain (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)
attribute [local instance] coefficientDomain

abbrev Ring := WrapParameter.Extension (WrapDeform.residue p)

noncomputable def ringDomain :=
  WrapPrefixSchur.parameter_domain (R:=WrapDeform.Extension p)
    (K:=WrapPoleResidue.Residue p) (WrapDeform.residue p)
attribute [local instance] ringDomain

noncomputable def coefficient : WrapDeform.Extension p →+* Ring p :=
  (algebraMap (WrapDeform.Extension p)[X] (Ring p)).comp
    (Polynomial.C:WrapDeform.Extension p →+* (WrapDeform.Extension p)[X])

noncomputable def integerPoleSpecialization :=
  @originalScaledPoleInverse_map_specializes (WrapDeform.Extension p)
    (WrapPoleResidue.Residue p) _ _ _ (WrapDeform.residue p)
    (GaussLoc p) _ (WrapOwnCore.constants p)

open Classical in
/-- Deform the integer-pole family independently of the existing
fractional-pole parameter; its original quotient determines the branch. -/
noncomputable def integerNormalized (a : GaussLoc p) : Ring p :=
  if ha : res p a=0 then
    originalScaledPoleInverse (WrapDeform.residue p)
      (WrapOwnCore.constants p (UFMoments.piL p))
      (WrapOwnCore.constants p (WrapPole.quotient p a ha)) (WrapOwnCore.constants p 1) 1
  else
    originalScaledPoleInverse (WrapDeform.residue p)
      (WrapOwnCore.constants p (UFMoments.piL p))
      (WrapOwnCore.constants p a) (WrapOwnCore.constants p 1) 0

/-- At zero integer deformation, recover the actual old generic
fractional-parameter coefficient, using original elementary units only. -/
theorem integer_specializes (a : GaussLoc p)
    (hpole : ∀ ha : res p a=0,IsUnit (WrapPole.quotient p a ha))
    (hnonpole : res p a≠0 → IsUnit a) :
    WrapSpecialization.Rel (WrapDeform.residue p) (integerNormalized p a)
      (WrapOwnCore.constants p (WrapPole.originalNormalized p a)) := by
  classical
  by_cases ha : res p a=0
  · rw [integerNormalized,dif_pos ha,WrapPole.originalNormalized,dif_pos ha]
    simpa only [Nat.sub_self,pow_zero,one_mul] using
      integerPoleSpecialization p
        (UFMoments.piL p) (WrapPole.quotient p a ha) 1 1 (hpole ha)
  · rw [integerNormalized,dif_neg ha,WrapPole.originalNormalized,dif_neg ha]
    simpa only [Nat.sub_zero,pow_one] using
      integerPoleSpecialization p
        (UFMoments.piL p) a 1 0 (hnonpole ha)

noncomputable def delta (q o t : ℕ) : Ring p :=
  integerNormalized p (t:GaussLoc p)-
    coefficient p (WrapOwnCore.constants p (q:GaussLoc p))*
      coefficient p (WrapPole.normalizedInverse p (WrapIncrement.argument p q o t) (q:GaussLoc p))

noncomputable def dsq (q o t : ℕ) : Ring p :=
  integerNormalized p (t:GaussLoc p)^2-
    coefficient p (WrapOwnCore.constants p ((q:GaussLoc p)^2))*
      coefficient p (WrapPole.normalizedInverse p (WrapIncrement.argument p q o t) (q:GaussLoc p))^2

theorem delta_specializes (q o t : ℕ) (ht : ¬p^2∣t) :
    WrapSpecialization.Rel (WrapDeform.residue p) (delta p q o t) (WrapIncrement.delta p q o t) := by
  unfold delta WrapIncrement.delta
  simp only [sub_eq_add_neg]
  apply WrapSpecialization.Rel.add
  · exact integer_specializes p (t:GaussLoc p)
      (fun ha => WrapSimplePole.quotient_unit p t ht ha) (fun h => isUnit_of_res_ne _ h)
  · apply WrapSpecialization.Rel.neg
    exact WrapSpecialization.Rel.mul (WrapSpecialization.Rel.constant _)
      (WrapSpecialization.Rel.constant _)

theorem dsq_specializes (q o t : ℕ) (ht : ¬p^2∣t) :
    WrapSpecialization.Rel (WrapDeform.residue p) (dsq p q o t) (WrapIncrement.dsq p q o t) := by
  have hp := integer_specializes p (t:GaussLoc p)
    (fun ha => WrapSimplePole.quotient_unit p t ht ha) (fun h => isUnit_of_res_ne _ h)
  have he : WrapIncrement.dsq p q o t=
      (WrapOwnCore.constants p (WrapPole.originalNormalized p (t:GaussLoc p)))^2-
      WrapOwnCore.constants p ((q:GaussLoc p)^2)*
        (WrapPole.normalizedInverse p (WrapIncrement.argument p q o t) (q:GaussLoc p))^2 := by
    unfold WrapIncrement.dsq WrapOwnCore.constants
    simp only [RingHom.comp_apply,map_pow]
  rw [he]
  unfold dsq
  simp only [sub_eq_add_neg,pow_two]
  apply WrapSpecialization.Rel.add
  · exact WrapSpecialization.Rel.mul hp hp
  · apply WrapSpecialization.Rel.neg
    exact WrapSpecialization.Rel.mul (WrapSpecialization.Rel.constant _)
      (WrapSpecialization.Rel.mul (WrapSpecialization.Rel.constant _) (WrapSpecialization.Rel.constant _))

/-- Actual two-parameter original-node matrix entry. The node-difference
reciprocal stays ORIGINAL; both pole families are independently deformed. -/
noncomputable def entry (q o : ℕ) (u : GaussLoc p) (a b : ℕ) : Ring p :=
  if a=b then -(coefficient p (WrapOwnCore.constants p u)*∑ t∈Icc 1 a,dsq p q o t)
  else coefficient p (WrapOwnCore.constants p u)*
    coefficient p (WrapOwnCore.constants p
      (WrapPole.originalNormalized p ((max a b-min a b:ℕ):GaussLoc p)))*
      ∑ t∈Ioc (min a b) (max a b),delta p q o t

theorem entry_specializes (q o N : ℕ) (hN : N<p*p)
    (u : GaussLoc p) (a b : ℕ) (ha : a<N) (hb : b<N) :
    WrapSpecialization.Rel (WrapDeform.residue p) (entry p q o u a b)
      (WrapDeformedEntry.entry p q o u a b) := by
  classical
  by_cases hab : a=b
  · rw [entry,WrapDeformedEntry.entry,if_pos hab,if_pos hab]
    apply WrapSpecialization.Rel.neg
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.constant _
    · apply parameter_sum_specializes
      intro t ht
      have ht1 := (Finset.mem_Icc.mp ht).1
      have htN := lt_of_le_of_lt (Finset.mem_Icc.mp ht).2 ha
      exact dsq_specializes p q o t (Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN))
  · rw [entry,WrapDeformedEntry.entry,if_neg hab,if_neg hab]
    apply WrapSpecialization.Rel.mul
    · exact WrapSpecialization.Rel.mul (WrapSpecialization.Rel.constant _) (WrapSpecialization.Rel.constant _)
    · apply parameter_sum_specializes
      intro t ht
      have ht1 : 1≤t := by have := (Finset.mem_Ioc.mp ht).1; omega
      have htN := lt_of_le_of_lt (Finset.mem_Ioc.mp ht).2 (max_lt ha hb)
      exact delta_specializes p q o t (Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN))

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def matrix (Fr : Frame) (q o : ℕ) (c : ι → ℕ) (xs ys : κ → ℕ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) (Ring p) :=
  Matrix.of (fun i j => entry p q o (WrapOriginalEntry.normInv p Fr)
    (UFMember.rowNode c xs i) (UFMember.colNode c ys j))+
    (WrapDeformedFamily.spectral p).map ((coefficient p).comp (WrapDeformedFamily.coefficient p))

theorem matrix_specializes (Fr : Frame) (q o N : ℕ) (hN : N<p*p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (i j : ι ⊕ κ) :
    WrapSpecialization.Rel (WrapDeform.residue p) (matrix p Fr q o c xs ys i j)
      (WrapDeformedFamily.matrix p Fr q o c xs ys i j) := by
  unfold matrix WrapDeformedFamily.matrix
  simp only [Matrix.add_apply,Matrix.map_apply,RingHom.comp_apply,Matrix.of_apply]
  exact WrapSpecialization.Rel.add
    (entry_specializes p q o N hN _ _ _ (UFMember.rowNode_lt hc hx i) (UFMember.colNode_lt hc hy j))
    (WrapSpecialization.Rel.constant _)

noncomputable def determinant_relation {τ : Type*} [Fintype τ] [DecidableEq τ] :=
  WrapSpecialization.determinant (R:=WrapDeform.Extension p) (K:=WrapPoleResidue.Residue p)
    (ι:=τ) (WrapDeform.residue p)
noncomputable def descend_relation :=
  @WrapSpecialization.Rel.descend (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p)
noncomputable def coefficientPrime :=
  WrapPrefixSchur.parameter_prime p
noncomputable def uniformizer :=
  WrapParameter.uniformizer (WrapDeform.residue p) (WrapDeform.uniformizer p)

/-- Descend the actual two-parameter ORIGINAL family determinant to its
existing one-parameter representation, before the original scalar bridge. -/
theorem one_parameter_content (Fr : Frame) (q o N : ℕ) (hN : N<p*p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (k : ℕ) (hcontent : uniformizer p^k∣(matrix p Fr q o c xs ys).det) :
    WrapDeform.uniformizer p^k∣(WrapDeformedFamily.matrix p Fr q o c xs ys).det := by
  obtain ⟨v,hv⟩ := hcontent
  exact descend_relation p (WrapDeform.uniformizer p) (WrapDeform.residue_zero_iff p)
    (coefficientPrime p)
    (determinant_relation p _ _ (matrix_specializes p Fr q o N hN c xs ys hc hx hy)) k v hv

/-- Every original common deletion uses its own ORIGINAL determinant.
Only elementary original denominators are specialized in either stage. -/
theorem original_gle {Fr : Frame} {q o N : ℕ} (T : Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (k : ℕ) (hcontent : uniformizer p^k∣(matrix p Fr q o c xs ys).det) :
    GLE p (2*Fintype.card (ι ⊕ κ)-k)
      (CatalanCore.Rect.FullN Fr c xs ys (Polynomial.X:ℚ[X])).det := by
  exact WrapDeformedFamily.original_gle p T D hqp hN hsq c xs ys hc hx hy k
    (one_parameter_content p Fr q o N hN c xs ys hc hx hy k hcontent)

/-- Actual mixed prefix core with the ORIGINAL common spectral
coordinates; absorbed balanced pairs carry no extra spectral diagonal. -/
noncomputable def mixedCore (q o : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : κ → ℕ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) (Ring p) :=
  Matrix.of (fun i j => entry p q o u (Sum.elim c xs i) (Sum.elim c ys j))+
    (Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix ι ι (WrapDeform.Extension p)))
      0 0 (0:Matrix κ κ (WrapDeform.Extension p))).map (coefficient p)

theorem mixedCore_specializes (q o N : ℕ) (hN : N<p*p) (s u : GaussLoc p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (i j : ι ⊕ κ) :
    WrapSpecialization.Rel (WrapDeform.residue p) (mixedCore p q o s u c xs ys i j)
      (WrapFibreCore.core p q o s u c xs ys i j) := by
  unfold mixedCore WrapFibreCore.core
  simp only [Matrix.add_apply,Matrix.map_apply,Matrix.of_apply]
  exact WrapSpecialization.Rel.add
    (entry_specializes p q o N hN u _ _ (UFMember.rowNode_lt hc hx i) (UFMember.colNode_lt hc hy j))
    (WrapSpecialization.Rel.constant _)

noncomputable def matrix_unit_transfer {α : Type*} [Fintype α] [DecidableEq α] :=
  @parameter_matrix_unit (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p) α _ _

/-- The already built actual one-parameter pivot supplies a nonzero
original test, so the independent integer deformation preserves generic
invertibility. It need not preserve a later central test's pivots. -/
theorem mixedCore_unit (q o N : ℕ) (hN : N<p*p) (s u : GaussLoc p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hQ : IsUnit (WrapFibreCore.core p q o s u c xs ys).det) :
    IsUnit (mixedCore p q o s u c xs ys).det :=
  matrix_unit_transfer p (WrapDeform.uniformizer p) (WrapDeform.residue_zero_iff p)
    (coefficientPrime p) _ _ (mixedCore_specializes p q o N hN s u c xs ys hc hx hy) hQ

noncomputable def own {α : Type*} (col : α → ZMod p) (Q : Matrix α α (Ring p)) : Matrix α α (Ring p) :=
  Matrix.of fun i j => if col i=col j then Q i j else 0

theorem own_specializes {α : Type*} (col : α → ZMod p)
    (Q : Matrix α α (Ring p)) (Q0 : Matrix α α (WrapDeform.Extension p))
    (hQ : ∀ i j,WrapSpecialization.Rel (WrapDeform.residue p) (Q i j) (Q0 i j)) (i j : α) :
    WrapSpecialization.Rel (WrapDeform.residue p) (own p col Q i j)
      (WrapPrefixSource.own p col Q0 i j) := by
  classical
  by_cases h : col i=col j
  · simpa only [own,WrapPrefixSource.own,Matrix.of_apply,if_pos h] using hQ i j
  · simp only [own,WrapPrefixSource.own,Matrix.of_apply,if_neg h]
    exact WrapSpecialization.Rel.zero

noncomputable def constants : GaussLoc p →+* Ring p :=
  (coefficient p).comp (WrapOwnCore.constants p)
noncomputable def load (q o t : ℕ) : Ring p := ∑ k∈Icc 1 t,delta p q o k

theorem load_specializes (q o N : ℕ) (hN : N<p*p) (t : ℕ) (ht : t<N) :
    WrapSpecialization.Rel (WrapDeform.residue p) (load p q o t) (WrapEntryRelation.load p q o t) := by
  apply parameter_sum_specializes
  intro k hk
  exact delta_specializes p q o k
    (Smith.not_sq_dvd_of_lt (mem_Icc.mp hk).1 (lt_trans (lt_of_le_of_lt (mem_Icc.mp hk).2 ht) hN))

theorem uniformizer_cast : (p:Ring p)=uniformizer p := by
  unfold uniformizer WrapParameter.uniformizer
  rw [←WrapEntryRelation.uniformizer_cast p]
  simp only [map_natCast]

theorem difference_factor (w : ℕ) (hw : ¬p^2∣w) :
    (w:Ring p)*constants p (WrapPole.originalNormalized p (w:GaussLoc p))=uniformizer p := by
  have hh := congrArg (coefficient p) (WrapEntryRelation.factor p w hw)
  simpa only [map_mul,map_natCast,constants,WrapEntryRelation.constants,WrapOwnCore.constants,
    coefficient,uniformizer,WrapParameter.uniformizer,RingHom.comp_apply] using hh

theorem prefix_sub (q o a b : ℕ) (hab : a≤b) :
    load p q o b-load p q o a=∑ k∈Ioc a b,delta p q o k := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold load
  rw [he,he,← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem entry_symm (q o : ℕ) (u : GaussLoc p) (a b : ℕ) :
    entry p q o u a b=entry p q o u b a := by
  classical
  by_cases hab : a=b
  · subst b; rfl
  · simp only [entry,hab,Ne.symm hab,↓reduceIte,min_comm a b,max_comm a b]

theorem commutator_of_lt (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (hab : a<b) (hb : b<N) :
    ((b:Ring p)-(a:Ring p))*entry p q o u a b=
      uniformizer p*(constants p u*(load p q o b-load p q o a)) := by
  have hw2 : ¬p^2∣b-a := Smith.not_sq_dvd_of_lt (by omega) (by omega)
  rw [entry,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le,
    ←prefix_sub p q o a b hab.le]
  rw [←Nat.cast_sub hab.le]
  change ((b-a:ℕ):Ring p)*(constants p u*
    constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*
      (load p q o b-load p q o a))=_
  calc
    _=(((b-a:ℕ):Ring p)*constants p
        (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p)))*
      (constants p u*(load p q o b-load p q o a)) := by ring
    _=_ := by rw [difference_factor p (b-a) hw2]

/-- Exact displacement at original row/column nodes in the independent
two-parameter deformation, before reduction or inverse elimination. -/
theorem commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    ((b:Ring p)-(a:Ring p))*entry p q o u a b=
      uniformizer p*(constants p u*(load p q o b-load p q o a)) := by
  rcases lt_trichotomy a b with hab|hab|hba
  · exact commutator_of_lt p q o N u hN a b hab hb
  · subst b; simp
  · have hh := commutator_of_lt p q o N u hN b a hba ha
    rw [entry_symm p q o u b a] at hh
    calc
      _=-(((a:Ring p)-(b:Ring p))*entry p q o u a b) := by ring
      _=-(uniformizer p*(constants p u*(load p q o a-load p q o b))) := congrArg Neg.neg hh
      _=_ := by ring

noncomputable def parameterPrime :=
  WrapParameterLift.uniformizer_prime (R:=WrapDeform.Extension p) (K:=WrapPoleResidue.Residue p)
    (WrapDeform.residue p) (WrapDeform.uniformizer p)
    (WrapDeform.residue_zero_iff p) (coefficientPrime p)

/-- Cancel the original uniformizer on an actual own-colour entry.
Both quotient coordinates are original independent row/column coordinates. -/
theorem divided_commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) (hcol : (a:ZMod p)=(b:ZMod p)) :
    (((b/p:ℕ):Ring p)-((a/p:ℕ):Ring p))*entry p q o u a b=
      constants p u*(load p q o b-load p q o a) := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp hcol
  have hpa := Nat.mod_add_div a p
  have hpb := Nat.mod_add_div b p
  have hn : b+p*(a/p)=a+p*(b/p) := by omega
  have hh := congrArg (fun n:ℕ => (n:Ring p)) hn
  push_cast at hh
  have hc : (b:Ring p)-(a:Ring p)=
      uniformizer p*(((b/p:ℕ):Ring p)-((a/p:ℕ):Ring p)) := by
    rw [←uniformizer_cast p]
    calc
      _=((b:Ring p)+(p:Ring p)*((a/p:ℕ):Ring p))-(a:Ring p)-
          (p:Ring p)*((a/p:ℕ):Ring p) := by ring
      _=((a:Ring p)+(p:Ring p)*((b/p:ℕ):Ring p))-(a:Ring p)-
          (p:Ring p)*((a/p:ℕ):Ring p) := by rw [hh]
      _=_ := by ring
  apply mul_left_cancel₀ (parameterPrime p).ne_zero
  have hr := commutator p q o N u hN a b ha hb
  rw [hc] at hr
  simp only [mul_assoc] at hr
  exact hr

/-- The original common spectral diagonal contributes zero to the
actual mixed displacement. Absorbed pairs retain their actual coordinates. -/
theorem mixedCore_commutator (q o N : ℕ) (hN : N<p*p) (s u : GaussLoc p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (i j : ι ⊕ κ) :
    (((Sum.elim c ys j : ℕ):Ring p)-((Sum.elim c xs i : ℕ):Ring p))*mixedCore p q o s u c xs ys i j=
      uniformizer p*(constants p u*(load p q o (Sum.elim c ys j)-load p q o (Sum.elim c xs i))) := by
  let S : Matrix (ι ⊕ κ) (ι ⊕ κ) (WrapDeform.Extension p) :=
    Matrix.fromBlocks (WrapOwnCore.constants p s • (1:Matrix ι ι (WrapDeform.Extension p))) 0 0 0
  have hz : (((Sum.elim c ys j : ℕ):Ring p)-((Sum.elim c xs i : ℕ):Ring p))*coefficient p (S i j)=0 := by
    rcases i with i|i <;> rcases j with j|j
    · by_cases hij : i=j
      · subst j; simp only [Sum.elim_inl,sub_self,zero_mul]
      · simp only [S,Matrix.fromBlocks_apply₁₁,Matrix.smul_apply,smul_eq_mul,
          Matrix.one_apply,if_neg hij,mul_zero,map_zero]
    · simp only [S,Matrix.fromBlocks_apply₁₂,Matrix.zero_apply,map_zero,mul_zero]
    · simp only [S,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,map_zero,mul_zero]
    · simp only [S,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,map_zero,mul_zero]
  change (((Sum.elim c ys j : ℕ):Ring p)-((Sum.elim c xs i : ℕ):Ring p))*
    (entry p q o u (Sum.elim c xs i) (Sum.elim c ys j)+coefficient p (S i j))=_
  rw [mul_add,hz,add_zero]
  exact commutator p q o N u hN _ _ (UFMember.rowNode_lt hc hx i) (UFMember.colNode_lt hc hy j)

abbrev Residue := RatFunc (WrapPoleResidue.Residue p)
noncomputable def residue := WrapParameter.residue (WrapDeform.residue p)
noncomputable def poleOneResidue :=
  @originalScaledPoleInverse_one_residue (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p)
noncomputable def poleZeroResidue :=
  @originalScaledPoleInverse_zero_residue (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p)
noncomputable def constantResidue :=
  @parameter_constant_residue (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p)

theorem coefficient_residue (a : WrapDeform.Extension p) :
    residue p (coefficient p a)=RatFunc.C (WrapDeform.residue p a) := by
  simpa only [residue,coefficient,RingHom.comp_apply] using constantResidue p a

theorem first_constant_residue (a : GaussLoc p) :
    WrapDeform.residue p (WrapOwnCore.constants p a)=RatFunc.C (res p a) := by
  simpa only [WrapOwnCore.constants,RingHom.comp_apply] using WrapPoleResidue.constant p a

/-- The independently deformed integer family has exactly its ORIGINAL
quotient-plus-parameter pole residue; original nonpoles vanish. -/
theorem integer_residue (t : ℕ) (h2 : ¬p^2∣t) :
    residue p (integerNormalized p (t:GaussLoc p))=
      if p∣t then (1:Residue p)/(((t/p:ℕ):Residue p)+RatFunc.X) else 0 := by
  classical
  by_cases hd : p∣t
  · have ha := (WrapSimplePole.res_nat_zero p t).mpr hd
    rw [integerNormalized,dif_pos ha,if_pos hd]
    have hu := (WrapSimplePole.quotient_unit p t h2 ha).map (WrapOwnCore.constants p)
    have hh := poleOneResidue p (WrapOwnCore.constants p (UFMoments.piL p))
      (WrapOwnCore.constants p (WrapPole.quotient p (t:GaussLoc p) ha))
      (WrapOwnCore.constants p 1) hu
    rw [WrapPoleResidue.quotient_nat p t ha] at hh ⊢
    have hn (k : ℕ) : WrapDeform.residue p (WrapOwnCore.constants p (k:GaussLoc p))=
        (k:WrapPoleResidue.Residue p) := by
      simpa only [WrapOwnCore.constants,RingHom.comp_apply] using WrapPoleResidue.constant_nat p k
    simpa only [residue,hn,map_one,map_natCast,one_mul] using hh
  · have ha : res p (t:GaussLoc p)≠0 := fun h => hd ((WrapSimplePole.res_nat_zero p t).mp h)
    rw [integerNormalized,dif_neg ha,if_neg hd]
    have hp : WrapDeform.residue p (WrapOwnCore.constants p (UFMoments.piL p))=0 := by
      rw [first_constant_residue,res_piL,map_zero]
    exact poleZeroResidue p (WrapOwnCore.constants p (UFMoments.piL p))
      (WrapOwnCore.constants p (t:GaussLoc p)) (WrapOwnCore.constants p 1) hp

/-- Exact actual two-term residue with independent integer and fractional
pole parameters. All masks are the ORIGINAL arithmetic pole masks. -/
theorem delta_residue (q o t : ℕ) (hq0 : 0<q) (hqp : q<p)
    (hle : o≤q*t) (h2 : ¬p^2∣t) :
    residue p (delta p q o t)=
      (if p∣t then (1:Residue p)/(((t/p:ℕ):Residue p)+RatFunc.X) else 0)-
      (q:Residue p)*(if p∣q*t-o then
        (1:Residue p)/((((q*t-o)/p:ℕ):Residue p)+(q:Residue p)*
          RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) else 0) := by
  rw [delta,map_sub,map_mul,integer_residue p t h2,coefficient_residue,coefficient_residue,
    first_constant_residue,WrapSimplePole.res_nat]
  simp only [map_natCast]
  rw [WrapSimplePole.argument_nat p q o t hle,
    WrapPoleResidue.normalized_nat p (q*t-o) q (WrapSimplePole.q_res_ne p q hq0 hqp)]
  by_cases hi : p∣t <;> by_cases hf : p∣q*t-o <;>
    simp only [hi,hf,↓reduceIte,map_zero,map_div₀,map_add,map_mul,map_one,map_natCast]

/-- Exact harmonic identification of the ACTUAL independently deformed
cumulative load, retaining all absorbed periods and both pole parameters. -/
theorem load_residue (q o root j0 gamma j N : ℕ)
    (hq0 : 0<q) (hqp : q<p) (hoq : o<q) (hk0 : 0<root) (hk : root≤p)
    (hg : gamma<p) (hroot : q*root=j0*p+o) (hN : N<p*p) (hnode : gamma+j*p<N) :
    residue p (load p q o (gamma+j*p))=
      twoHarmonicLoad (RatFunc.X:Residue p)
        ((j0:Residue p)/(q:Residue p)+RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p))
        (decide (root≤gamma)) j := by
  have hp := (Fact.out : p.Prime).pos
  have hqb := WrapSimplePole.q_res_ne p q hq0 hqp
  have hqf : (q:ZMod p)≠0 := by
    intro hz
    apply hqb
    exact (WrapSimplePole.res_nat_zero p q).mpr ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hq1 := WrapActualLoad.q_ne p q hqb
  have hq2 : (q:Residue p)≠0 := by
    intro hz
    apply hq1
    apply (RatFunc.C:WrapPoleResidue.Residue p →+* Residue p).injective
    simpa only [map_natCast,map_zero] using hz
  have he : residue p (load p q o (gamma+j*p))=
      WrapPoleLoad.fractional p 1 0 p (RatFunc.X:Residue p) (gamma+j*p)-
      WrapPoleLoad.fractional p q o root
        (RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) (gamma+j*p) := by
    unfold load
    rw [map_sum]
    unfold WrapPoleLoad.fractional
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht1 := (mem_Icc.mp ht).1
    have htN := lt_of_le_of_lt (mem_Icc.mp ht).2 hnode
    have h2 : ¬p^2∣t := Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN)
    have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
    rw [delta_residue p q o t hq0 hqp hle h2]
    have hiff := WrapPoleLoad.fractional_pole_iff p q o root j0 t hoq ht1 hroot hqf
    simp only [Nat.mod_self,Nat.one_mul,Nat.sub_zero,Nat.cast_one,one_mul]
    simp only [←Nat.dvd_iff_mod_eq_zero,←hiff]
    by_cases hi : p∣t <;> by_cases hf : p∣q*t-o <;>
      simp only [hi,hf,↓reduceIte,mul_zero,rational_one_div,rational_div_eq_mul_inv,one_div,div_eq_mul_inv,one_mul]
  rw [he,WrapPoleLoad.fractional_eq p 1 0 p 1 gamma j (RatFunc.X:Residue p)
      hp hp le_rfl hg (by omega) (by simpa only [Nat.cast_one] using (one_ne_zero : (1:Residue p)≠0)),
    WrapPoleLoad.fractional_eq p q o root j0 gamma j
      (RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) hp hk0 hk hg hroot hq2]
  simp only [twoHarmonicLoad,WrapPoleCount.count,if_neg (not_le.mpr hg),Nat.add_zero,
    Nat.cast_one,div_one]
  simp [rational_div_one]

section ActualPrefix
variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def prefixCore (s u : GaussLoc p) :=
  mixedCore p q o s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
noncomputable def prefixOwn (s u : GaussLoc p) :=
  own p H.colour (prefixCore p H s u)

theorem prefixCore_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : IsUnit (prefixCore p H s u).det := by
  have hN : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  exact mixedCore_unit p q o N hN s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
    H.common_bound H.row_bound H.col_bound (H.core_unit s u hs hu huc)

theorem prefixOwn_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : IsUnit (prefixOwn p H s u).det := by
  have hN : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  exact matrix_unit_transfer p (WrapDeform.uniformizer p) (WrapDeform.residue_zero_iff p)
    (coefficientPrime p) _ _
    (own_specializes p H.colour _ _
      (mixedCore_specializes p q o N hN s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
        H.common_bound H.row_bound H.col_bound)) (H.own_unit s u hs hu huc)

noncomputable def reference_unit_transfer {α : Type*} [Fintype α] [DecidableEq α] :=
  @parameter_reference_unit (WrapDeform.Extension p) (WrapPoleResidue.Residue p)
    _ _ _ (WrapDeform.residue p) α _ _

noncomputable def prefixSigma (u : GaussLoc p) (t : ℕ)
    (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  if H.colour i=(t:ZMod p) then
    entry p q o u t (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i) else 0

noncomputable def prefixReference (s u : GaussLoc p) (t : ℕ) :=
  1-prefixSigma p H u t ⬝ᵥ ((prefixOwn p H s u)⁻¹ *ᵥ 1)

theorem prefixSigma_specializes (u : GaussLoc p) (t : ℕ) (ht : t<N)
    (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    WrapSpecialization.Rel (WrapDeform.residue p) (prefixSigma p H u t i) (H.ownSigma u t i) := by
  have hN : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  by_cases h : H.colour i=(t:ZMod p)
  · simpa only [prefixSigma,WrapPrefixWindow.Setup.ownSigma,WrapPrefixWindow.Setup.sigma,UFMember.colNode,if_pos h] using
      entry_specializes p q o N hN u t _ ht (UFMember.colNode_lt H.common_bound H.col_bound i)
  · simp only [prefixSigma,WrapPrefixWindow.Setup.ownSigma,if_neg h]
    exact WrapSpecialization.Rel.zero

theorem prefixReference_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : IsUnit (prefixReference p H s u H.t0) := by
  have ht : H.t0∈Icc H.t0 H.tv := mem_Icc.mpr ⟨le_rfl,H.hle⟩
  have htN := lt_of_le_of_lt H.hle H.htvN
  have hN : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  obtain ⟨G,hG,hres,hB⟩ := H.own_source H.t0 ht s u hs hu huc
  have hBunit := WrapBalancedTest.unit_ne p (H.ownReference s u H.t0) hB
  have he : H.ownReference s u H.t0=
      1-H.ownSigma u H.t0 ⬝ᵥ ((H.own s u)⁻¹ *ᵥ 1) := by
    unfold WrapPrefixWindow.Setup.ownReference
    rw [sum_vecMul_eq]
  have hB0 : IsUnit (1-H.ownSigma u H.t0 ⬝ᵥ ((H.own s u)⁻¹ *ᵥ 1)) := by
    rw [←he]
    exact hBunit
  exact (reference_unit_transfer p (WrapDeform.uniformizer p) (WrapDeform.residue_zero_iff p)
    (coefficientPrime p) (prefixOwn p H s u) (H.own s u) (prefixSigma p H u H.t0) (H.ownSigma u H.t0)
    (own_specializes p H.colour _ _
      (mixedCore_specializes p q o N hN s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
        H.common_bound H.row_bound H.col_bound))
    (prefixSigma_specializes p H u H.t0 htN) (H.own_unit s u hs hu huc) hB0).2

noncomputable def prefixRowLoad (u : GaussLoc p)
    (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  constants p u*load p q o (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i)
noncomputable def prefixColLoad (u : GaussLoc p)
    (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  constants p u*load p q o (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)

noncomputable def prefixAnchor (s u : GaussLoc p) :=
  (constants p u*load p q o H.t0-
    prefixSigma p H u H.t0 ⬝ᵥ ((prefixOwn p H s u)⁻¹ *ᵥ prefixRowLoad p H u))*
      Ring.inverse (prefixReference p H s u H.t0)

noncomputable def own_direction_zero {α : Type*} [Fintype α] [DecidableEq α] :=
  @reference_direction_zero (Ring p) _ _ α _ _

theorem prefixAnchor_zero (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    (constants p u*load p q o H.t0-prefixAnchor p H s u)-
      prefixSigma p H u H.t0 ⬝ᵥ ((prefixOwn p H s u)⁻¹ *ᵥ
        fun i => prefixRowLoad p H u i-prefixAnchor p H s u)=0 := by
  have hB := Ring.mul_inverse_cancel (prefixReference p H s u H.t0)
    (prefixReference_unit p H s u hs hu huc)
  exact own_direction_zero p (prefixOwn p H s u) (prefixSigma p H u H.t0)
    (prefixRowLoad p H u) (constants p u*load p q o H.t0)
    (Ring.inverse (prefixReference p H s u H.t0)) hB

end ActualPrefix

end TwoTermDeformation

section CentralPole

theorem affine_central_factor {R : Type*} [CommRing R] (a b point : R)
    (ha : a+b*point=0) :
    Polynomial.C b*((Polynomial.X:R[X])+Polynomial.C (-point))=
      Polynomial.C a+Polynomial.C b*Polynomial.X := by
  have he : b*(-point)=a := by linear_combination -ha
  rw [mul_add,←map_mul,he,add_comm]



noncomputable def centralFactor (point : GaussLoc p) : WrapDeform.Extension p :=
  WrapDeform.embed p (((Polynomial.X:(GaussLoc p)[X])+Polynomial.C (-point)):(GaussLoc p)[X])

/-- A polynomial test needs no generic denominator or pivot unit. -/
theorem polynomial_at (point : GaussLoc p) (f : (GaussLoc p)[X]) :
    WrapPoleTest.At p point (WrapDeform.embed p f) (f.eval point) := by
  unfold WrapPoleTest.At WrapEvaluation.Rel
  refine ⟨f,1,by simp,?_,by simp⟩
  simp only [map_one,one_mul]
  rfl

/-- Clear the single central pole before evaluating. The vanished
linear factor cancels the original affine pole denominator exactly. -/
theorem central_affine_at (a b point : GaussLoc p) (hb : res p b≠0)
    (ha : a+b*point=0) :
    WrapPoleTest.At p point (centralFactor (p:=p) point*Ring.inverse (WrapPole.affine p a b))
      (Ring.inverse b) := by
  have hbU : IsUnit b := isUnit_of_res_ne b hb
  have hf := affine_central_factor a b point ha
  have he : WrapDeform.embed p (Polynomial.C b)*centralFactor (p:=p) point=WrapPole.affine p a b := by
    unfold centralFactor WrapPole.affine
    rw [←map_mul,hf]
  unfold WrapPoleTest.At WrapEvaluation.Rel
  refine ⟨1,Polynomial.C b,by simpa only [Polynomial.eval_C] using hbU,?_,?_⟩
  · rw [map_one]
    change WrapDeform.embed p (Polynomial.C b)*(centralFactor (p:=p) point*
      Ring.inverse (WrapPole.affine p a b))=1
    rw [←mul_assoc,he]
    exact Ring.mul_inverse_cancel _ (WrapPole.affine_unit p a b hb)
  · simp only [Polynomial.eval_one,Polynomial.eval_C]
    exact (Ring.mul_inverse_cancel b hbU).symm

/-- Every other affine pole is regular at the central test, so clearing
the central factor sends it to zero. -/
theorem other_affine_at (a b point : GaussLoc p) (hb : res p b≠0)
    (ha : IsUnit (a+b*point)) :
    WrapPoleTest.At p point (centralFactor (p:=p) point*Ring.inverse (WrapPole.affine p a b)) 0 := by
  unfold WrapPoleTest.At WrapEvaluation.Rel
  refine ⟨(Polynomial.X:(GaussLoc p)[X])+Polynomial.C (-point),Polynomial.C a+Polynomial.C b*Polynomial.X,
    by simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X] using ha,?_,?_⟩
  · change WrapPole.affine p a b*(centralFactor (p:=p) point*Ring.inverse (WrapPole.affine p a b))=
      centralFactor (p:=p) point
    calc
      _=centralFactor (p:=p) point*(WrapPole.affine p a b*Ring.inverse (WrapPole.affine p a b)) := by ring
      _=_ := by rw [Ring.mul_inverse_cancel _ (WrapPole.affine_unit p a b hb),mul_one]
  · simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,add_neg_cancel,mul_zero]

/-- A normalized original nonpole contributes zero to the cleared
central-pole test, directly in its original representation. -/
theorem central_nonpole_at (a b point : GaussLoc p) (ha : res p a≠0) :
    WrapPoleTest.At p point (centralFactor (p:=p) point*WrapPole.normalizedInverse p a b) 0 := by
  classical
  unfold WrapPole.normalizedInverse
  rw [dif_neg ha]
  unfold WrapPoleTest.At WrapEvaluation.Rel
  refine ⟨Polynomial.C (UFMoments.piL p)*((Polynomial.X:(GaussLoc p)[X])+Polynomial.C (-point)),
    Polynomial.C a+Polynomial.C (UFMoments.piL p)*Polynomial.C b*Polynomial.X,
    by simpa only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X] using
      WrapPoleTest.nonpole_unit p a b point ha,?_,?_⟩
  · change WrapPole.denominator p a b*(centralFactor (p:=p) point*
        (WrapDeform.uniformizer p*Ring.inverse (WrapPole.denominator p a b)))=
      WrapDeform.embed p (Polynomial.C (UFMoments.piL p)*((Polynomial.X:(GaussLoc p)[X])+Polynomial.C (-point)))
    rw [map_mul]
    change _=WrapDeform.uniformizer p*centralFactor (p:=p) point
    calc
      _=WrapDeform.uniformizer p*centralFactor (p:=p) point*
        (WrapPole.denominator p a b*Ring.inverse (WrapPole.denominator p a b)) := by ring
      _=_ := by rw [Ring.mul_inverse_cancel _ (WrapPole.denominator_unit p a b ha),mul_one]
  · simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
      add_neg_cancel,mul_zero]

theorem central_point_algebra {R : Type*} [CommRing R]
    (a b x h h0 : R) (hi : b*x=1) :
    (a+b*h)+b*(-a*x-h0)=b*(h-h0) := by
  linear_combination -a*hi

/-- Central-threshold pole location in the original coefficient ring. -/
noncomputable def centralPoint (q j0 h0 : ℕ) : GaussLoc p :=
  -(j0:GaussLoc p)*Ring.inverse (q:GaussLoc p)-(h0:GaussLoc p)

theorem central_point_identity (q j0 h h0 : ℕ) (hq : res p (q:GaussLoc p)≠0) :
    ((j0+q*h:ℕ):GaussLoc p)+(q:GaussLoc p)*centralPoint (p:=p) q j0 h0=
      (q:GaussLoc p)*((h:GaussLoc p)-(h0:GaussLoc p)) := by
  have hi := Ring.mul_inverse_cancel (q:GaussLoc p) (isUnit_of_res_ne (q:GaussLoc p) hq)
  unfold centralPoint
  push_cast
  exact central_point_algebra (j0:GaussLoc p) (q:GaussLoc p) _ _ _ hi

theorem central_other_unit (q j0 h h0 : ℕ) (hq : res p (q:GaussLoc p)≠0)
    (hh : h<p) (hh0 : h0<p) (hne : h≠h0) :
    IsUnit (((j0+q*h:ℕ):GaussLoc p)+(q:GaussLoc p)*centralPoint (p:=p) q j0 h0) := by
  rw [central_point_identity q j0 h h0 hq]
  apply (isUnit_of_res_ne (q:GaussLoc p) hq).mul
  apply isUnit_of_res_ne ((h:GaussLoc p)-(h0:GaussLoc p))
  intro hz
  apply (sub_ne_zero.mpr (WrapHarmonicPivot.cast_ne p h h0 hh hh0 hne))
  apply (RatFunc.C:ZMod p →+* RatFunc (ZMod p)).injective
  simpa only [map_sub,map_natCast,map_zero] using hz

/-- The cleared family has exactly one surviving pole term. -/
theorem central_family_at (q j0 h h0 : ℕ) (hq : res p (q:GaussLoc p)≠0)
    (hh : h<p) (hh0 : h0<p) :
    WrapPoleTest.At p (centralPoint (p:=p) q j0 h0)
      (centralFactor (p:=p) (centralPoint (p:=p) q j0 h0)*
        Ring.inverse (WrapPole.affine p ((j0+q*h:ℕ):GaussLoc p) (q:GaussLoc p)))
      (if h=h0 then Ring.inverse (q:GaussLoc p) else 0) := by
  by_cases he : h=h0
  · subst h
    rw [if_pos rfl]
    exact central_affine_at _ _ _ hq (by rw [central_point_identity q j0 h0 h0 hq,sub_self,mul_zero])
  · rw [if_neg he]
    exact other_affine_at _ _ _ hq (central_other_unit q j0 h h0 hq hh hh0 he)

/-- Existing cleared specialization is closed under the finite sums
appearing in original pole prefixes. -/
theorem central_sum_at {α : Type*} (point : GaussLoc p) (S : Finset α)
    (f : α → WrapDeform.Extension p) (v : α → GaussLoc p)
    (hv : ∀ a∈S,WrapPoleTest.At p point (centralFactor (p:=p) point*f a) (v a)) :
    WrapPoleTest.At p point (centralFactor (p:=p) point*∑ a∈S,f a) (∑ a∈S,v a) := by
  classical
  revert hv
  induction S using Finset.induction_on with
  | empty =>
    intro hv
    simp only [Finset.sum_empty,mul_zero]
    exact WrapEvaluation.Rel.zero
  | @insert a S ha ih =>
    intro hv
    have hA := hv a (mem_insert_self a S)
    have hS := ih (fun b hb => hv b (mem_insert_of_mem hb))
    rw [Finset.sum_insert ha,Finset.sum_insert ha,mul_add]
    exact WrapEvaluation.Rel.add hA hS

/-- Scalar multiplication preserves the already-cleared test. -/
theorem central_scalar_at (point c : GaussLoc p) (f : WrapDeform.Extension p) (v : GaussLoc p)
    (hf : WrapPoleTest.At p point (centralFactor (p:=p) point*f) v) :
    WrapPoleTest.At p point
      (centralFactor (p:=p) point*(WrapDeform.embed p (Polynomial.C c)*f)) (c*v) := by
  have hc : WrapPoleTest.At p point (WrapDeform.embed p (Polynomial.C c)) c := by
    simpa only [Polynomial.eval_C] using polynomial_at point (Polynomial.C c)
  have he : centralFactor (p:=p) point*(WrapDeform.embed p (Polynomial.C c)*f)=
      WrapDeform.embed p (Polynomial.C c)*(centralFactor (p:=p) point*f) := by ring
  rw [he]
  exact WrapEvaluation.Rel.mul hc hf


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

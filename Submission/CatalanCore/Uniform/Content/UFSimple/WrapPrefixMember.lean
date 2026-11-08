module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPrefixSchur
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapMixedDeletion
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapRestrict
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapDamage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixMember

section Restriction
variable {R K ι τ : Type*} [CommRing R] [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
  {p : ℕ} [Fact p.Prime]

/-- The independently loaded source moment of a colour. -/
noncomputable def moment (phi : R →+* K) (col : ι → ZMod p) (Q : Matrix ι ι R)
    (LR LC : ι → R) (gamma : ZMod p) :=
  ∑ i∈univ.filter (fun i => col i=gamma),phi ((Q⁻¹ *ᵥ LR) i)*phi (LC i)

/-- Restriction preserves every untouched actual mixed colour fibre. -/
theorem moment_restrict (phi : R →+* K) (col : ι → ZMod p) (f : τ → ι) (gamma : ZMod p)
    (E : {i:τ // col (f i)=gamma} ≃ {i:ι // col i=gamma}) (hE : ∀ i,f i.1=(E i).1)
    (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (hb : ∀ i j,col i≠col j → Q i j=0)
    (hf : IsUnit (Q.submatrix f f).det) (LR LC : ι → R) :
    moment phi (col ∘ f) (Q.submatrix f f) (LR ∘ f) (LC ∘ f) gamma=moment phi col Q LR LC gamma := by
  have hbf : ∀ i j,col (f i)≠col (f j) → (Q.submatrix f f) i j=0 := fun i j h => hb (f i) (f j) h
  have hm : blk (Q.submatrix f f) (col ∘ f) gamma=(blk Q col gamma).submatrix E E := by
    apply Matrix.ext
    intro i j
    change Q (f i.1) (f j.1)=Q (E i).1 (E j).1
    rw [hE i,hE j]
  have hR : (fun i:{i:τ // col (f i)=gamma} => LR (f i.1))=(fun i => LR i.1) ∘ E := by
    funext i
    exact congrArg LR (hE i)
  have hC : (fun i:{i:τ // col (f i)=gamma} => LC (f i.1))=(fun i => LC i.1) ∘ E := by
    funext i
    exact congrArg LC (hE i)
  unfold moment
  rw [WrapType.mixed_fiber_moment_response (Q.submatrix f f) (col ∘ f) hf hbf gamma (LR ∘ f) (LC ∘ f) phi,
    WrapType.mixed_fiber_moment_response Q col hQ hb gamma LR LC phi,hm]
  change phi ((fun i => LC (f i.1)) ⬝ᵥ ((blk Q col gamma).submatrix E E)⁻¹ *ᵥ (fun i => LR (f i.1)))=_
  rw [hR,hC]
  exact congrArg phi (WrapTransport.response_reindex (blk Q col gamma) E E
    (fun i => LR i.1) (fun i => LC i.1))

/-- Untouched own linear responses preserve both the source numerator
and its reference, with independent row and column loads. -/
theorem own_response_restrict (col : ι → ZMod p) (f : τ → ι) (gamma : ZMod p)
    (E : {i:τ // col (f i)=gamma} ≃ {i:ι // col i=gamma}) (hE : ∀ i,f i.1=(E i).1)
    (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (hb : ∀ i j,col i≠col j → Q i j=0)
    (hf : IsUnit (Q.submatrix f f).det) (sigma LR : ι → R)
    (hsigma : ∀ i,col i≠gamma → sigma i=0) :
    (sigma ∘ f) ⬝ᵥ (Q.submatrix f f)⁻¹ *ᵥ (LR ∘ f)=sigma ⬝ᵥ Q⁻¹ *ᵥ LR := by
  have hbf : ∀ i j,col (f i)≠col (f j) → (Q.submatrix f f) i j=0 := fun i j h => hb (f i) (f j) h
  have hsf : ∀ i,col (f i)≠gamma → sigma (f i)=0 := fun i h => hsigma (f i) h
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec,
    own_fiber_form (Q.submatrix f f) (col ∘ f) hf hbf gamma (sigma ∘ f) (LR ∘ f) hsf,
    own_fiber_form Q col hQ hb gamma sigma LR hsigma]
  have hm : blk (Q.submatrix f f) (col ∘ f) gamma=(blk Q col gamma).submatrix E E := by
    apply Matrix.ext
    intro i j
    change Q (f i.1) (f j.1)=Q (E i).1 (E j).1
    rw [hE i,hE j]
  rw [hm]
  have he := WrapTransport.response_reindex (blk Q col gamma) E E
    (fun i => LR i.1) (fun i => sigma i.1)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at he
  have hs : (fun i:{i:τ // col (f i)=gamma} => (sigma ∘ f) i.1)=(fun i => sigma i.1) ∘ E := by
    funext i
    exact congrArg sigma (hE i)
  have hL : (fun i:{i:τ // col (f i)=gamma} => (LR ∘ f) i.1)=(fun i => LR i.1) ∘ E := by
    funext i
    exact congrArg LR (hE i)
  change ((fun i => (sigma ∘ f) i.1) ᵥ* ((blk Q col gamma).submatrix E E)⁻¹) ⬝ᵥ
    (fun i => (LR ∘ f) i.1)=((fun i => sigma i.1) ᵥ* (blk Q col gamma)⁻¹) ⬝ᵥ (fun i => LR i.1)
  rw [hs,hL]
  exact he

end Restriction


section Single
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]


end Single


/-- Rewrite the unshifted row moment as the independently shifted own
load response before taking residues. -/
theorem shifted_row_identity {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (Q : Matrix α α R) (sigma L : α → R) (Lt direction : R) :
    (Lt-sigma ⬝ᵥ Q⁻¹ *ᵥ L)-direction*(1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1)=
      (Lt-direction)-sigma ⬝ᵥ Q⁻¹ *ᵥ (fun i => L i-direction) := by
  have hL : (fun i => L i-direction)=L-direction • (1:α → R) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hL,Matrix.mulVec_sub,dotProduct_sub,Matrix.mulVec_smul,dotProduct_smul,smul_eq_mul]
  ring

theorem shifted_col_identity {R α : Type*} [CommRing R] [Fintype α] [DecidableEq α]
    (Q : Matrix α α R) (sigma L : α → R) (Lt direction : R) :
    (Lt-L ⬝ᵥ Q⁻¹ *ᵥ sigma)-direction*(1-(1:α → R) ⬝ᵥ Q⁻¹ *ᵥ sigma)=
      (Lt-direction)-(fun i => L i-direction) ⬝ᵥ Q⁻¹ *ᵥ sigma := by
  have hL : (fun i => L i-direction)=L-direction • (1:α → R) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hL,sub_dotProduct,smul_dotProduct,smul_eq_mul]
  ring

section ColumnRestriction
variable {R ι τ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
  {p : ℕ} [Fact p.Prime]

theorem own_column_response_restrict (col : ι → ZMod p) (f : τ → ι) (gamma : ZMod p)
    (E : {i:τ // col (f i)=gamma} ≃ {i:ι // col i=gamma}) (hE : ∀ i,f i.1=(E i).1)
    (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (hb : ∀ i j,col i≠col j → Q i j=0)
    (hf : IsUnit (Q.submatrix f f).det) (sigma L : ι → R)
    (hsigma : ∀ i,col i≠gamma → sigma i=0) :
    (L ∘ f) ⬝ᵥ (Q.submatrix f f)⁻¹ *ᵥ (sigma ∘ f)=L ⬝ᵥ Q⁻¹ *ᵥ sigma := by
  have hQT : IsUnit Qᵀ.det := by rw [Matrix.det_transpose]; exact hQ
  have hfT : IsUnit ((Qᵀ).submatrix f f).det := by
    change IsUnit (Q.submatrix f f)ᵀ.det
    rw [Matrix.det_transpose]
    exact hf
  have hbT : ∀ i j,col i≠col j → Qᵀ i j=0 := fun i j h => hb j i (Ne.symm h)
  rw [WrapTransport.response_transpose,WrapTransport.response_transpose Q sigma L]
  exact own_response_restrict col f gamma E hE Qᵀ hQT hbT hfT sigma L hsigma

end ColumnRestriction

section Quotients
variable {R : Type*} [CommRing R]

theorem coordinate_quotient (p a b : ℕ) (hmod : a%p=b%p) :
    (b:R)-(a:R)=(p:R)*((b/p:R)-(a/p:R)) := by
  have ha := Nat.mod_add_div a p
  have hb := Nat.mod_add_div b p
  have hn : b+p*(a/p)=a+p*(b/p) := by omega
  have he := congrArg (fun n:ℕ => (n:R)) hn
  push_cast at he
  linear_combination he

end Quotients


section SingleReindex
variable {K α τ : Type*} [Field K] [Fintype α] [DecidableEq α] [Fintype τ] [DecidableEq τ]

/-- Apply the existing mixed single-deletion identity through the exact
original fibre equivalence, rather than an assumed deletion certificate. -/
theorem single_restriction_moment (Q : Matrix α α K) (hQ : IsUnit Q.det)
    (f : τ → α) (E : (τ ⊕ Unit) ≃ α) (hE : ∀ i,E (Sum.inl i)=f i)
    (hf : IsUnit (Q.submatrix f f).det) (tR tC LR LC sigma : α → K) (Lt direction : K)
    (hdisp : ∀ i j,(tC j-tR i)*Q i j=LC j-LR i)
    (hsigma : ∀ i,tC i*sigma i=LC i-Lt)
    (hfull : sigma ⬝ᵥ Q⁻¹ *ᵥ (fun i => LR i-direction)=Lt-direction)
    (hminor : (sigma ∘ f) ⬝ᵥ (Q.submatrix f f)⁻¹ *ᵥ (fun i => LR (f i)-direction)=Lt-direction)
    (hB : 1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1≠0) :
    (fun i => LC i-direction) ⬝ᵥ Q⁻¹ *ᵥ (fun i => LR i-direction)=
      (fun i => LC (f i)-direction) ⬝ᵥ (Q.submatrix f f)⁻¹ *ᵥ (fun i => LR (f i)-direction) := by
  let QE := Q.submatrix E E
  have hQE : IsUnit QE.det := by rw [Matrix.det_submatrix_equiv_self E]; exact hQ
  have hmat : QE.toBlocks₁₁=Q.submatrix f f := by
    apply Matrix.ext
    intro i j
    change Q (E (Sum.inl i)) (E (Sum.inl j))=Q (f i) (f j)
    rw [hE i,hE j]
  have hfullE : (sigma ∘ E) ⬝ᵥ QE⁻¹ *ᵥ (fun i => LR (E i)-direction)=Lt-direction :=
    (WrapTransport.response_reindex Q E E (fun i => LR i-direction) sigma).trans hfull
  have href : (∑ j,(QEᵀ⁻¹ *ᵥ (sigma ∘ E)) j)=sigma ⬝ᵥ Q⁻¹ *ᵥ 1 := by
    calc
      _=(1:τ ⊕ Unit → K) ⬝ᵥ QEᵀ⁻¹ *ᵥ (sigma ∘ E) := by simp only [dotProduct,Pi.one_apply,one_mul]
      _=(sigma ∘ E) ⬝ᵥ QE⁻¹ *ᵥ (1:τ ⊕ Unit → K) :=
        (WrapTransport.response_transpose QE 1 (sigma ∘ E)).symm
      _=sigma ⬝ᵥ Q⁻¹ *ᵥ 1 := WrapTransport.response_reindex Q E E 1 sigma
  have hminorE : (fun i => (sigma ∘ E) (Sum.inl i)) ⬝ᵥ QE.toBlocks₁₁⁻¹ *ᵥ
      (fun i => (LR ∘ E) (Sum.inl i)-direction)=Lt-direction := by
    simpa only [hmat,Function.comp_def,hE] using hminor
  have hm := WrapMixedDeletion.single_deletion_moment QE hQE (by rw [hmat]; exact hf)
    (tR ∘ E) (tC ∘ E) (LR ∘ E) (LC ∘ E) (sigma ∘ E) Lt direction
    (fun i j => hdisp (E i) (E j)) (fun i => hsigma (E i)) hfullE hminorE (by rw [href]; exact hB)
  have hfullM := WrapTransport.response_reindex Q E E (fun i => LR i-direction) (fun i => LC i-direction)
  have he := hfullM.symm.trans hm
  simpa only [hmat,Function.comp_def,hE] using he

end SingleReindex

section LocalMap
variable {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]
  {p : ℕ} [Fact p.Prime]

theorem mapped_response (phi : R →+* K) (Q : Matrix α α R) (hQ : IsUnit Q.det) (LR LC : α → R) :
    (phi ∘ LC) ⬝ᵥ (Q.map phi)⁻¹ *ᵥ (phi ∘ LR)=phi (LC ⬝ᵥ Q⁻¹ *ᵥ LR) := by
  rw [map_inv_of_unit phi Q hQ]
  simp only [dotProduct,Matrix.mulVec,Matrix.map_apply,Function.comp_apply,map_sum,map_mul]

theorem mapped_block_unit (phi : R →+* K) (Q : Matrix α α R) (hQ : IsUnit Q.det) :
    IsUnit (Q.map phi).det := by
  change IsUnit ((phi.mapMatrix Q).det)
  rw [← RingHom.map_det]
  exact hQ.map phi

theorem local_moment_map (phi : R →+* K) (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ i j,col i≠col j → D i j=0) (gamma : ZMod p) (LR LC : α → R) :
    (fun i:{i // col i=gamma} => phi (LC i.1)) ⬝ᵥ ((blk D col gamma).map phi)⁻¹ *ᵥ
      (fun i => phi (LR i.1))=moment phi col D LR LC gamma := by
  rw [moment,WrapType.mixed_fiber_moment_response D col hD hb gamma LR LC phi]
  exact mapped_response phi (blk D col gamma) (inv_restrict D col hD hb gamma).1 _ _

theorem local_own_response_map (phi : R →+* K) (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ i j,col i≠col j → D i j=0) (gamma : ZMod p) (sigma L : α → R)
    (hsigma : ∀ i,col i≠gamma → sigma i=0) :
    (fun i:{i // col i=gamma} => phi (sigma i.1)) ⬝ᵥ ((blk D col gamma).map phi)⁻¹ *ᵥ
      (fun i => phi (L i.1))=phi (sigma ⬝ᵥ D⁻¹ *ᵥ L) := by
  rw [Matrix.dotProduct_mulVec sigma D⁻¹ L,own_fiber_form D col hD hb gamma sigma L hsigma]
  have he := mapped_response phi (blk D col gamma) (inv_restrict D col hD hb gamma).1
    (fun i => L i.1) (fun i => sigma i.1)
  rw [Matrix.dotProduct_mulVec (fun i => sigma i.1) (blk D col gamma)⁻¹ (fun i => L i.1)] at he
  exact he

end LocalMap

section Reduction
variable (p : ℕ) [Fact p.Prime]
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- The actual first-order global couplings reduce to their literal
own-colour responses on both axes, for any retained common family. -/
theorem coupling_reduction (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (WrapFibreCore.core p q o s u c xs ys).det)
    (t : ℕ) (ht : t<N) (direction : WrapDeform.Extension p) :
    let Q := WrapFibreCore.core p q o s u c xs ys
    let col := WrapFibreIndex.colour p c xs
    let D := WrapPrefixSource.own p col Q
    let sr := fun i => WrapDeformedEntry.entry p q o u t (Sum.elim c ys i)
    let sc := fun i => WrapDeformedEntry.entry p q o u (Sum.elim c xs i) t
    let sor := fun i => if col i=(t:ZMod p) then sr i else 0
    let soc := fun i => if col i=(t:ZMod p) then sc i else 0
    let LR := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c xs i)-direction
    let LC := fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim c ys i)-direction
    WrapDeform.residue p (sr ⬝ᵥ Q⁻¹ *ᵥ LR)=WrapDeform.residue p (sor ⬝ᵥ D⁻¹ *ᵥ LR) ∧
      WrapDeform.residue p (LC ⬝ᵥ Q⁻¹ *ᵥ sc)=WrapDeform.residue p (LC ⬝ᵥ D⁻¹ *ᵥ soc) := by
  classical
  intro Q col D sr sc sor soc LR LC
  obtain ⟨E,hQE,hD,_,_⟩ := WrapPrefixSource.actual_core_source p q o N s u c xs ys hN hc hx hy hcol hQ
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hm : Q.map (WrapDeform.residue p)=D.map (WrapDeform.residue p) := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M => WrapDeform.residue p (M i j)) hQE
    simpa only [Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      map_add,map_mul,hp,zero_mul,add_zero] using he
  have hrowcol (i:ι ⊕ β) : ((Sum.elim c xs i:ℕ):ZMod p)=col i := by cases i <;> rfl
  have hcolcol (i:ι ⊕ β) : ((Sum.elim c ys i:ℕ):ZMod p)=col i := by
    cases i with
    | inl i => rfl
    | inr i => exact (hcol i).symm
  have hboundR (i:ι ⊕ β) : Sum.elim c xs i<N := by cases i with | inl i => exact hc i | inr i => exact hx i
  have hboundC (i:ι ⊕ β) : Sum.elim c ys i<N := by cases i with | inl i => exact hc i | inr i => exact hy i
  obtain ⟨vr,hvr,_,_⟩ := WrapPrefixSource.actual_border_source p q o N t u (Sum.elim c ys) hN ht hboundC
  obtain ⟨vc,hvc,_,_⟩ := WrapPrefixSource.actual_border_source p q o N t u (Sum.elim c xs) hN ht hboundR
  have hsr : ∀ i,WrapDeform.residue p (sr i)=WrapDeform.residue p (sor i) := by
    intro i
    have he := congrArg (fun v => WrapDeform.residue p (v i)) hvr
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hp,zero_mul,add_zero,hcolcol] using he
  have hsc : ∀ i,WrapDeform.residue p (sc i)=WrapDeform.residue p (soc i) := by
    intro i
    have he := congrArg (fun v => WrapDeform.residue p (v i)) hvc
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hp,zero_mul,add_zero,hrowcol,
      sc,soc,WrapEntryRelation.entry_symm p q o u t (Sum.elim c xs i)] using he
  exact ⟨WrapPrefixType.response_map_congr (WrapDeform.residue p) Q D hQ hD LR sr LR sor hm (fun _ => rfl) hsr,
    WrapPrefixType.response_map_congr (WrapDeform.residue p) Q D hQ hD sc LC soc LC hm hsc (fun _ => rfl)⟩

end Reduction

section Actual
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def common (K : Finset (Fin r)) (i : WrapKeep.Keep K) : ℕ := (i.1:ℕ)

noncomputable def core (K : Finset (Fin r)) (s u : GaussLoc p) :=
  WrapFibreCore.core p q o s u (common K) H.xs H.ys

/-- Every original common deletion has the actual mixed prefix unit;
no full-family determinant divisibility is inherited. -/
theorem core_unit (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit (core H K s u).det :=
  WrapPrefixCoreGeometry.core_unit p (n:=n) (e:=e) (b:=b) (d:=d) q o H.root H.j0 r shift N s u hs hu huc
    H.hq0 H.hqp H.hq2 H.hoq H.hroot0 H.hrootp H.hroot H.hN H.hn H.hp H.he H.er H.ec H.hres H.hsize
    (common K) (fun i => i.1.2)

/-- Restriction preserves the original spectral common diagonal and
both original balanced node families exactly. -/
theorem core_restrict (K : Finset (Fin r)) (s u : GaussLoc p) :
    core H K s u=(H.core s u).submatrix (Sum.map Subtype.val id) (Sum.map Subtype.val id) := by
  classical
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [core,common,WrapPrefixWindow.Setup.core,WrapFibreCore.core,
      Matrix.submatrix_apply,Sum.map_inl,Sum.map_inr,id_eq,Matrix.add_apply,Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Sum.elim_inl,Sum.elim_inr,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Matrix.zero_apply,
      Subtype.val_inj]


noncomputable def colour (K : Finset (Fin r)) := WrapFibreIndex.colour p (common K) H.xs
noncomputable def own (K : Finset (Fin r)) (s u : GaussLoc p) :=
  WrapPrefixSource.own p (colour H K) (core H K s u)
noncomputable def embed (K : Finset (Fin r)) :
    (WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) → (Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) := Sum.map Subtype.val id
noncomputable def rowLoad (K : Finset (Fin r)) (u : GaussLoc p) := H.rowLoad u ∘ embed K
noncomputable def colLoad (K : Finset (Fin r)) (u : GaussLoc p) := H.colLoad u ∘ embed K
noncomputable def ownSigma (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) := H.ownSigma u t ∘ embed K
noncomputable def ownReference (K : Finset (Fin r)) (s u : GaussLoc p) (t : ℕ) :=
  1-ownSigma H K u t ⬝ᵥ (own H K s u)⁻¹ *ᵥ 1
noncomputable def sourceMoment (K : Finset (Fin r)) (s u : GaussLoc p) (gamma : ZMod p) :=
  moment (WrapDeform.residue p) (colour H K) (own H K s u)
    (fun i => rowLoad H K u i-H.anchor s u) (fun i => colLoad H K u i-H.anchor s u) gamma
noncomputable def weight (K : Finset (Fin r)) (s u : GaussLoc p) (gamma : ZMod p) :=
  RatFunc.C (RatFunc.C (wT p q o gamma))*WrapDeform.residue p (WrapOwnCore.constants p u)-
    sourceMoment H K s u gamma-H.sourceConstant s u

theorem colour_embed (K : Finset (Fin r)) (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    colour H K i=H.colour (embed K i) := by cases i <;> rfl

theorem own_restrict (K : Finset (Fin r)) (s u : GaussLoc p) :
    own H K s u=(H.own s u).submatrix (embed K) (embed K) := by
  rw [own,core_restrict H]
  apply Matrix.ext
  intro i j
  simp only [WrapPrefixSource.own,Matrix.of_apply,Matrix.submatrix_apply,colour_embed,
    WrapPrefixWindow.Setup.own,embed]

theorem own_unit (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    IsUnit (own H K s u).det := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  obtain ⟨E,hE,hD,_,_⟩ := WrapPrefixSource.actual_core_source p q o N s u (common K) H.xs H.ys
    hsingle (fun i => H.common_bound i.1) H.row_bound H.col_bound H.same_colour (core_unit H K s u hs hu huc)
  exact hD

/-- Every untouched actual mixed fibre is preserved, including all
balanced-cycle coordinates and the original common spectral entries. -/
noncomputable def fibreEquiv (K : Finset (Fin r)) (gamma : ZMod p)
    (hg : gamma∉K.image (fun i:Fin r => (i:ZMod p))) :
    {i:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour (embed K i)=gamma} ≃
      {i:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour i=gamma} where
  toFun i := ⟨embed K i.1,i.2⟩
  invFun i := match i with
    | ⟨Sum.inl j,hj⟩ => ⟨Sum.inl ⟨j,by
        intro hk
        exact hg (mem_image.mpr ⟨j,hk,hj⟩)⟩,hj⟩
    | ⟨Sum.inr j,hj⟩ => ⟨Sum.inr j,hj⟩
  left_inv i := by rcases i with ⟨i,hi⟩; cases i <;> rfl
  right_inv i := by rcases i with ⟨i,hi⟩; cases i <;> rfl

/-- Untouched independently loaded prefix source moments are unchanged. -/
theorem moment_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (gamma : ZMod p) (hg : gamma∉K.image (fun i:Fin r => (i:ZMod p))) :
    sourceMoment H K s u gamma=H.moment s u gamma := by
  have hb : ∀ i j,H.colour i≠H.colour j → H.own s u i j=0 := by
    intro i j hij
    simp only [WrapPrefixWindow.Setup.own,WrapPrefixSource.own,Matrix.of_apply,hij,↓reduceIte]
  have hk := own_unit H K s u hs hu huc
  rw [own_restrict H] at hk
  have he := moment_restrict (WrapDeform.residue p) H.colour (embed K) gamma
    (fibreEquiv H K gamma hg) (fun _ => rfl) (H.own s u) (H.own_unit s u hs hu huc) hb hk
    (fun i => H.rowLoad u i-H.anchor s u) (fun i => H.colLoad u i-H.anchor s u)
  have hcol : colour H K=H.colour ∘ embed K := funext (colour_embed H K)
  simpa only [sourceMoment,own_restrict,hcol,rowLoad,colLoad,Function.comp_def,
    moment,WrapPrefixWindow.Setup.moment] using he

theorem weight_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (gamma : ZMod p) (hg : gamma∉K.image (fun i:Fin r => (i:ZMod p))) :
    weight H K s u gamma=H.weight s u gamma := by
  unfold weight WrapPrefixWindow.Setup.weight
  rw [moment_unchanged H K s u hs hu huc gamma hg]


noncomputable def actual_response_restrict {α τ : Type*} [Fintype α] [DecidableEq α] [Fintype τ] [DecidableEq τ] :=
  own_response_restrict (R:=WrapDeform.Extension p) (ι:=α) (τ:=τ) (p:=p)

theorem fibreEquiv_val (K : Finset (Fin r)) (gamma : ZMod p)
    (hg : gamma∉K.image (fun i:Fin r => (i:ZMod p)))
    (i : {i:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour (embed K i)=gamma}) :
    embed K i.1=(fibreEquiv H K gamma hg i).1 := rfl

/-- Untouched own source responses persist integrally after common deletion. -/
theorem own_response_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (L : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p) :
    ownSigma H K u t ⬝ᵥ (own H K s u)⁻¹ *ᵥ (L ∘ embed K)=
      H.ownSigma u t ⬝ᵥ (H.own s u)⁻¹ *ᵥ L := by
  have hb : ∀ i j,H.colour i≠H.colour j → H.own s u i j=0 := by
    intro i j hij
    simp only [WrapPrefixWindow.Setup.own,WrapPrefixSource.own,Matrix.of_apply,hij,↓reduceIte]
  have hk := own_unit H K s u hs hu huc
  rw [own_restrict H] at hk
  let E := fibreEquiv H K (t:ZMod p) ht
  have hcol : colour H K=H.colour ∘ embed K := funext (colour_embed H K)
  have he := actual_response_restrict (p:=p) H.colour (embed K) (t:ZMod p) E
    (fibreEquiv_val H K (t:ZMod p) ht)
    (H.own s u) (H.own_unit s u hs hu huc) hb hk (H.ownSigma u t) L
    (by intro i hi; simp only [WrapPrefixWindow.Setup.ownSigma,hi,↓reduceIte])
  rw [own_restrict H]
  exact he

theorem reference_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    ownReference H K s u t=H.ownReference s u t := by
  have he := own_response_unchanged H K s u hs hu huc t ht 1
  have ho : H.ownReference s u t=1-H.ownSigma u t ⬝ᵥ (H.own s u)⁻¹ *ᵥ 1 := by
    have hh := Matrix.dotProduct_mulVec (H.ownSigma u t) (H.own s u)⁻¹
      (1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p)
    simp only [dotProduct,Pi.one_apply,mul_one] at hh
    exact congrArg (fun a:WrapDeform.Extension p => 1-a) hh.symm
  rw [ho,ownReference]
  exact congrArg (fun a:WrapDeform.Extension p => 1-a) he

/-- The original arithmetic own source survives at every untouched
selected colour, even if the old representative colour was deleted. -/
theorem own_source (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    ∃ G1:WrapDeform.Extension p,
      (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u)-
        ownSigma H K u t ⬝ᵥ (own H K s u)⁻¹ *ᵥ (fun i => rowLoad H K u i-H.anchor s u)=
          WrapDeform.uniformizer p*G1 ∧
      WrapDeform.residue p G1=
        (WrapDeform.residue p (WrapOwnCore.constants p u)*
          RatFunc.C (RatFunc.C (cauchyH (wT p q o) (t:ZMod p)-cauchyH (wT p q o) (H.t0:ZMod p))))*
            WrapDeform.residue p (ownReference H K s u t) ∧
      WrapDeform.residue p (ownReference H K s u t)≠0 := by
  obtain ⟨G1,hm,hr,hne⟩ := H.own_source t ht s u hs hu huc
  have he := own_response_unchanged H K s u hs hu huc t hg
    (fun i => H.rowLoad u i-H.anchor s u)
  rw [← Matrix.dotProduct_mulVec] at hm
  refine ⟨G1,?_,?_,?_⟩
  · rw [show (fun i => rowLoad H K u i-H.anchor s u)=
        (fun i => H.rowLoad u i-H.anchor s u) ∘ embed K from rfl,he]
    exact hm
  · rw [reference_unchanged H K s u hs hu huc t hg]
    exact hr
  · rw [reference_unchanged H K s u hs hu huc t hg]
    exact hne

theorem selected_weight_zero (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    weight H K s u (t:ZMod p)=0 := by
  rw [weight_unchanged H K s u hs hu huc _ hg]
  exact H.weight_zero t ht s u hs hu huc


noncomputable def sigma (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) := H.sigma u t ∘ embed K

theorem rowLoad_eq (K : Finset (Fin r)) (u : GaussLoc p) :
    rowLoad H K u=(fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim (common K) H.xs i)) := by
  funext i
  cases i <;> rfl

theorem colLoad_eq (K : Finset (Fin r)) (u : GaussLoc p) :
    colLoad H K u=(fun i => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (Sum.elim (common K) H.ys i)) := by
  funext i
  cases i <;> rfl

theorem sigma_eq (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) :
    sigma H K u t=(fun i => WrapDeformedEntry.entry p q o u t (Sum.elim (common K) H.ys i)) := by
  funext i
  cases i <;> rfl

theorem ownSigma_eq (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) :
    ownSigma H K u t=(fun i => if colour H K i=(t:ZMod p) then sigma H K u t i else 0) := by
  funext i
  simp only [ownSigma,sigma,Function.comp_apply,WrapPrefixWindow.Setup.ownSigma,colour_embed]

/-- The actual common-deletion member has the original normalized
window source at each untouched selected colour. -/
theorem normalized_source (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    ∃ F:WrapDeform.Extension p,
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ rowLoad H K u=
        H.anchor s u*(1-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ 1)+
          WrapDeform.uniformizer p*((1-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ 1)*F) ∧
      WrapDeform.residue p F=
        WrapDeform.residue p (WrapOwnCore.constants p u)*
          RatFunc.C (RatFunc.C (cauchyH (wT p q o) (t:ZMod p)-cauchyH (wT p q o) (H.t0:ZMod p)))-
        ∑ gamma:ZMod p,if gamma=(t:ZMod p) then 0 else
          sourceMoment H K s u gamma/(RatFunc.C (RatFunc.C gamma)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  obtain ⟨G1,hm,hr,hne⟩ := own_source H K s u hs hu huc t ht hg
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have htN : t<N := lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN
  have hsigma := ownSigma_eq H K u t
  rw [sigma_eq H K u t] at hsigma
  have href : ownReference H K s u t=
      1-∑ j,((fun i => if colour H K i=(t:ZMod p) then
        WrapDeformedEntry.entry p q o u t (Sum.elim (common K) H.ys i) else 0) ᵥ* (own H K s u)⁻¹) j := by
    rw [ownReference,hsigma,Matrix.dotProduct_mulVec]
    simp only [dotProduct,Pi.one_apply,mul_one]
  rw [rowLoad_eq H K u,hsigma,Matrix.dotProduct_mulVec] at hm
  rw [href] at hr hne
  have he := WrapPrefixType.actual_normalized_source p q o N t s u (common K) H.xs H.ys
    hsingle htN (fun i => H.common_bound i.1) H.row_bound H.col_bound H.same_colour
    (core_unit H K s u hs hu huc) (H.anchor s u) G1 _ hm hr hne
  simpa only [sigma_eq,rowLoad_eq,colLoad_eq,sourceMoment,moment,core,own,colour] using he

theorem cauchy_source (K : Finset (Fin r)) (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    ∃ F : WrapDeform.Extension p,
      WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ rowLoad H K u=
        H.anchor s u*(1-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ 1)+
          WrapDeform.uniformizer p*((1-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ 1)*F) ∧
      WrapDeform.residue p F=H.sourceOffset s u+
        ∑ gamma : ZMod p,weight H K s u gamma/
          (RatFunc.C (RatFunc.C gamma)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  classical
  obtain ⟨F,hm,hr⟩ := normalized_source H K s u hs hu huc t ht hg
  refine ⟨F,hm,?_⟩
  let phi : ZMod p →+* RatFunc (RatFunc (ZMod p)) :=
    (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp RatFunc.C
  have hsum : ∑ gamma : ZMod p,(phi gamma-phi (t:ZMod p))⁻¹=0 := by
    have he := congrArg phi (sum_inv_sub (p:=p) (by have := H.hp2; omega) (t:ZMod p))
    simpa only [map_sum,map_inv₀,map_sub,map_zero] using he
  have hW (z : ZMod p) : phi (cauchyH (wT p q o) z)=
      ∑ gamma : ZMod p,phi (wT p q o gamma)/(phi gamma-phi z) := by
    unfold cauchyH
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro gamma _
    rw [map_mul,map_inv₀,map_sub,div_eq_mul_inv]
  have hM : (∑ gamma : ZMod p,if gamma=(t:ZMod p) then 0 else
      sourceMoment H K s u gamma/(phi gamma-phi (t:ZMod p)))=
      ∑ gamma : ZMod p,sourceMoment H K s u gamma/(phi gamma-phi (t:ZMod p)) := by
    apply Finset.sum_congr rfl
    intro gamma _
    by_cases he : gamma=(t:ZMod p)
    · simp only [he,↓reduceIte,sub_self,div_zero]
    · rw [if_neg he]
  have hV : (∑ gamma : ZMod p,weight H K s u gamma/(phi gamma-phi (t:ZMod p)))=
      WrapDeform.residue p (WrapOwnCore.constants p u)*
        (∑ gamma : ZMod p,phi (wT p q o gamma)/(phi gamma-phi (t:ZMod p)))-
      ∑ gamma : ZMod p,sourceMoment H K s u gamma/(phi gamma-phi (t:ZMod p)) := by
    change (∑ gamma : ZMod p,(phi (wT p q o gamma)*WrapDeform.residue p (WrapOwnCore.constants p u)-
      sourceMoment H K s u gamma-H.sourceConstant s u)/(phi gamma-phi (t:ZMod p)))=_
    simp only [div_eq_mul_inv,sub_mul,Finset.sum_sub_distrib]
    rw [← Finset.mul_sum,hsum,mul_zero,sub_zero]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro gamma _
    ring
  rw [hr]
  change WrapDeform.residue p (WrapOwnCore.constants p u)*
    phi (cauchyH (wT p q o) (t:ZMod p)-cauchyH (wT p q o) (H.t0:ZMod p))-
      (∑ gamma : ZMod p,if gamma=(t:ZMod p) then 0 else sourceMoment H K s u gamma/(phi gamma-phi (t:ZMod p)))=
    -WrapDeform.residue p (WrapOwnCore.constants p u)*phi (cauchyH (wT p q o) (H.t0:ZMod p))+
      ∑ gamma : ZMod p,weight H K s u gamma/(phi gamma-phi (t:ZMod p))
  rw [map_sub,hM,hV,← hW (t:ZMod p)]
  ring


/-- Expose the unique deleted original common node in one colour fibre.
Every balanced coordinate remains on the retained side. -/
noncomputable def singleFibreEquiv (K : Finset (Fin r)) (gamma : ZMod p)
    (a : Fin r) (ha : a∈K) (hgamma : (a:ZMod p)=gamma)
    (honly : ∀ i∈K,(i:ZMod p)=gamma → i=a) :
    ({i:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour (embed K i)=gamma} ⊕ Unit) ≃
      {i:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour i=gamma} := by
  let F : ({i:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour (embed K i)=gamma} ⊕ Unit) →
      {i:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour i=gamma} :=
    Sum.elim (fun i => ⟨embed K i.1,i.2⟩) (fun _ => ⟨Sum.inl a,hgamma⟩)
  apply Equiv.ofBijective F
  constructor
  · intro i j hij
    rcases i with i|i <;> rcases j with j|j
    · apply congrArg Sum.inl
      apply Subtype.ext
      have he := congrArg Subtype.val hij
      change embed K i.1=embed K j.1 at he
      exact (Sum.map_injective.mpr ⟨Subtype.val_injective,Function.injective_id⟩) he
    · exfalso
      have he := congrArg Subtype.val hij
      rcases i with ⟨i,hi⟩
      cases i with
      | inl i => exact i.2 (by have hv : i.1=a := Sum.inl.inj he; rw [hv]; exact ha)
      | inr i =>
        change Sum.inr i=Sum.inl a at he
        exact Sum.inr_ne_inl he
    · exfalso
      have he := congrArg Subtype.val hij.symm
      rcases j with ⟨j,hj⟩
      cases j with
      | inl j => exact j.2 (by have hv : j.1=a := Sum.inl.inj he; rw [hv]; exact ha)
      | inr j =>
        change Sum.inr j=Sum.inl a at he
        exact Sum.inr_ne_inl he
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  · intro i
    rcases i with ⟨i,hi⟩
    cases i with
    | inl i =>
      by_cases he : i=a
      · subst i
        exact ⟨Sum.inr (),rfl⟩
      · have hk : i∉K := fun hk => he (honly i hk hi)
        exact ⟨Sum.inl ⟨Sum.inl ⟨i,hk⟩,hi⟩,rfl⟩
    | inr i => exact ⟨Sum.inl ⟨Sum.inr i,hi⟩,rfl⟩

end Actual

namespace Schur

open WrapPrefixSchur
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)
variable (K : Finset (Fin r))
include H

attribute [local instance] WrapPrefixSchur.extensionDomain

noncomputable def rowNode (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) : ℕ := Sum.elim (common K) H.xs i

noncomputable def colNode (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) : ℕ := Sum.elim (common K) H.ys i

noncomputable def surplusRow (z : Fin d) : ℕ :=
  r+2*(WrapPrefixGeometry.rowBorderEquiv (n:=n) (p:=p) H.er (Sum.inr z):ℕ)

noncomputable def surplusCol (y : Fin d) : ℕ :=
  r+2*(WrapPrefixGeometry.colBorderEquiv (n:=n) (Fact.out:p.Prime).pos shift H.ec (Sum.inr y):ℕ)+1

noncomputable def bBlock (u : GaussLoc p) : Matrix (WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) (Fin d) (WrapDeform.Extension p) :=
  Matrix.of fun i y => WrapDeformedEntry.entry p q o u (rowNode H K i) (surplusCol H y)

noncomputable def cBlock (u : GaussLoc p) : Matrix (Fin d) (WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) (WrapDeform.Extension p) :=
  Matrix.of fun z i => WrapDeformedEntry.entry p q o u (surplusRow H z) (colNode H K i)

noncomputable def dBlock (u : GaussLoc p) : Matrix (Fin d) (Fin d) (WrapDeform.Extension p) :=
  Matrix.of fun z y => WrapDeformedEntry.entry p q o u (surplusRow H z) (surplusCol H y)

noncomputable def full (s u : GaussLoc p) := Matrix.fromBlocks (core H K s u) (bBlock H K u) (cBlock H K u) (dBlock H u)

noncomputable def schur (s u : GaussLoc p) := dBlock H u-cBlock H K u*(core H K s u)⁻¹*bBlock H K u

noncomputable def columnSigma (u : GaussLoc p) (t : ℕ) (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  WrapDeformedEntry.entry p q o u (rowNode H K i) t

noncomputable def rowReference (s u : GaussLoc p) (t : ℕ) := 1-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ 1

noncomputable def colReference (s u : GaussLoc p) (t : ℕ) := 1-(1:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p) ⬝ᵥ
  (core H K s u)⁻¹ *ᵥ columnSigma H K u t

noncomputable def rowMoment (s u : GaussLoc p) (t : ℕ) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ rowLoad H K u

noncomputable def colMoment (s u : GaussLoc p) (t : ℕ) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-colLoad H K u ⬝ᵥ (core H K s u)⁻¹ *ᵥ columnSigma H K u t

theorem row_bound (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) : rowNode H K i<N := by
  cases i with
  | inl i => exact H.common_bound i.1
  | inr i => exact H.row_bound i

theorem col_bound (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) : colNode H K i<N := by
  cases i with
  | inl i => exact H.common_bound i.1
  | inr i => exact H.col_bound i

theorem surplus_row_bound (z : Fin d) : surplusRow H z<N := by
  have hi := (WrapPrefixGeometry.rowBorderEquiv (n:=n) (p:=p) H.er (Sum.inr z)).2
  have := H.hsize
  unfold surplusRow
  omega

theorem surplus_col_bound (y : Fin d) : surplusCol H y<N := by
  have hi := (WrapPrefixGeometry.colBorderEquiv (n:=n) (Fact.out:p.Prime).pos shift H.ec (Sum.inr y)).2
  have := H.hsize
  unfold surplusCol
  omega

/-- Exact original-coordinate row/column reference identity for the
entire actual mixed prefix core. -/
theorem shared_moments (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N) :
    rowReference H K s u t*colMoment H K s u t=rowMoment H K s u t*colReference H K s u t := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  apply scaled_cross_direction (WrapDeform.uniformizer p) (parameter_prime p).ne_zero
    (core H K s u) (core_unit H K s u hs hu huc)
    (fun i => (rowNode H K i:WrapDeform.Extension p)) (fun i => (colNode H K i:WrapDeform.Extension p))
    (rowLoad H K u) (colLoad H K u) (sigma H K u t) (columnSigma H K u t)
    (t:WrapDeform.Extension p) (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)
  · simpa only [core,rowNode,colNode,rowLoad_eq,colLoad_eq] using
      WrapPrefixSource.core_displacement p q o N s u (common K) H.xs H.ys
        hsingle (fun i => H.common_bound i.1) H.row_bound H.col_bound
  · intro i
    have he := WrapEntryRelation.commutator p q o N u hsingle t (colNode H K i) ht (col_bound H K i)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,sigma_eq,
      rowLoad_eq,colLoad_eq,columnSigma,rowNode,colNode] using he
  · intro i
    have he := WrapEntryRelation.commutator p q o N u hsingle (rowNode H K i) t (row_bound H K i) ht
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,sigma_eq,
      rowLoad_eq,colLoad_eq,columnSigma,rowNode,colNode] using he


/-- Reduction of the actual core and border preserves the already proved
own reference; all off-colour entries vanish by original displacement. -/
theorem row_reference_residue (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N) :
    WrapDeform.residue p (rowReference H K s u t)=WrapDeform.residue p (ownReference H K s u t) := by
  classical
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  obtain ⟨E,hQE,hD,hE0,hE⟩ := WrapPrefixSource.actual_core_source p q o N s u
    (common K) H.xs H.ys hsingle (fun i => H.common_bound i.1) H.row_bound H.col_bound
    H.same_colour (core_unit H K s u hs hu huc)
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hm : (core H K s u).map (WrapDeform.residue p)=(own H K s u).map (WrapDeform.residue p) := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M => WrapDeform.residue p (M i j)) hQE
    simpa only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero,
      Matrix.map_apply,core,own,colour] using he
  obtain ⟨v,hv,hv0,hvr⟩ := WrapPrefixSource.actual_border_source p q o N t u (colNode H K)
    hsingle ht (col_bound H K)
  have hcol (i : WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b)) : (colNode H K i:ZMod p)=colour H K i := by
    cases i with
    | inl i => rfl
    | inr i => exact (H.same_colour i).symm
  have hb : ∀ i,WrapDeform.residue p (sigma H K u t i)=WrapDeform.residue p (ownSigma H K u t i) := by
    intro i
    have he := congrArg (fun f => WrapDeform.residue p (f i)) hv
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] at he
    rw [hcol i] at he
    simpa only [ownSigma_eq,sigma_eq,colNode] using he
  have he := WrapPrefixType.reference_map_congr (WrapDeform.residue p) (core H K s u) (own H K s u)
    (core_unit H K s u hs hu huc) (own_unit H K s u hs hu huc) (sigma H K u t) (ownSigma H K u t) hm hb
  exact he

/-- The selected original row reference is an integral unit. -/
theorem row_reference_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    IsUnit (rowReference H K s u t) := by
  obtain ⟨G,hG,hr,hne⟩ := own_source H K s u hs hu huc t ht hg
  apply WrapBalancedTest.unit_ne p
  change WrapDeform.residue p (rowReference H K s u t)≠0
  rw [row_reference_residue H K s u hs hu huc t (lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN)]
  exact hne

/-- Both actual axes use the same normalized Cauchy source, with no
extra column-source hypothesis. -/
theorem two_sided_source (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t∈Icc H.t0 H.tv)
    (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    ∃ F : WrapDeform.Extension p,
      rowMoment H K s u t=H.anchor s u*rowReference H K s u t+
        WrapDeform.uniformizer p*(rowReference H K s u t*F) ∧
      colMoment H K s u t=H.anchor s u*colReference H K s u t+
        WrapDeform.uniformizer p*(colReference H K s u t*F) ∧
      WrapDeform.residue p F=H.sourceOffset s u+
        ∑ gamma : ZMod p,weight H K s u gamma/
          (RatFunc.C (RatFunc.C gamma)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  obtain ⟨F,hF,hr⟩ := cauchy_source H K t ht hg s u hs hu huc
  refine ⟨F,hF,?_,hr⟩
  exact column_source_of_row _ _ _ _ _ _ _ (row_reference_unit H K s u hs hu huc t ht hg)
    (shared_moments H K s u hs hu huc t (lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN)) hF


/-- The mixed displacement of the actual residual Schur block. -/
theorem actual_displacement (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z y : Fin d) :
    ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))*schur H K s u z y=
      WrapDeform.uniformizer p*(rowReference H K s u (surplusRow H z)*colMoment H K s u (surplusCol H y)-
        rowMoment H K s u (surplusRow H z)*colReference H K s u (surplusCol H y)) := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  simp only [rowReference,colReference,rowMoment,colMoment,sigma_eq]
  apply normalized_displacement (WrapDeform.uniformizer p) (core H K s u) (core_unit H K s u hs hu huc)
    (bBlock H K u) (cBlock H K u) (dBlock H u)
    (fun i => (rowNode H K i:WrapDeform.Extension p)) (fun i => (colNode H K i:WrapDeform.Extension p))
    (rowLoad H K u) (colLoad H K u)
    (fun z => (surplusRow H z:WrapDeform.Extension p)) (fun y => (surplusCol H y:WrapDeform.Extension p))
    (fun z => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (surplusRow H z))
    (fun y => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (surplusCol H y))
  · simpa only [core,rowNode,colNode,rowLoad_eq,colLoad_eq] using
      WrapPrefixSource.core_displacement p q o N s u (common K) H.xs H.ys
        hsingle (fun i => H.common_bound i.1) H.row_bound H.col_bound
  · intro i y
    have he := WrapEntryRelation.commutator p q o N u hsingle (rowNode H K i) (surplusCol H y)
      (row_bound H K i) (surplus_col_bound H y)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,bBlock,Matrix.of_apply,
      rowLoad_eq,rowNode] using he
  · intro z i
    have he := WrapEntryRelation.commutator p q o N u hsingle (surplusRow H z) (colNode H K i)
      (surplus_row_bound H z) (col_bound H K i)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,cBlock,Matrix.of_apply,
      colLoad_eq,colNode] using he
  · intro z y
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,dBlock,Matrix.of_apply] using
      WrapEntryRelation.commutator p q o N u hsingle (surplusRow H z) (surplusCol H y)
        (surplus_row_bound H z) (surplus_col_bound H y)

/-- Residually distinct ORIGINAL coordinates have an integral unit difference. -/
theorem difference_unit (a b : ℕ) (hab : (a:ZMod p)≠(b:ZMod p)) :
    IsUnit ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p)) := by
  apply WrapBalancedTest.unit_ne p
  change WrapDeform.residue p ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))≠0
  rw [map_sub,map_natCast,map_natCast]
  have hinj := ((RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp
    (RatFunc.C:ZMod p →+* RatFunc (ZMod p))).injective
  intro hz
  apply hab
  apply hinj
  simpa only [RingHom.comp_apply,map_natCast] using sub_eq_zero.mp hz |>.symm

/-- Every actual residual Schur entry contains the first integral order. -/
theorem exists_divided_schur (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p)) :
    ∃ W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p),schur H K s u=WrapDeform.uniformizer p • W := by
  classical
  have he : ∀ z y,∃ w:WrapDeform.Extension p,schur H K s u z y=WrapDeform.uniformizer p*w := by
    intro z y
    have hd := difference_unit H (surplusRow H z) (surplusCol H y) (hdist z y)
    have hn : WrapDeform.residue p ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))≠0 :=
      (hd.map (WrapDeform.residue p)).ne_zero
    obtain ⟨w,hw⟩ := schur_entry_divisible (WrapDeform.residue p) (WrapDeform.uniformizer p) _ _ _
      (WrapDeform.residue_zero_iff p) hn (actual_displacement H K s u hs hu huc z y)
    exact ⟨w,hw⟩
  choose W hW using he
  exact ⟨Matrix.of W,Matrix.ext (fun z y => hW z y)⟩


noncomputable def retained (s u : GaussLoc p) : Finset (ZMod p) := by
  classical
  exact univ.filter (fun gamma => weight H K s u gamma≠0)

noncomputable def residueNode (p : ℕ) [Fact p.Prime] : ZMod p →+* RatFunc (RatFunc (ZMod p)) :=
  (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp RatFunc.C

theorem retained_source (s u : GaussLoc p) (t : ℕ) :
    (∑ gamma : ZMod p,weight H K s u gamma/(residueNode p gamma-residueNode p (t:ZMod p)))=
      ∑ gamma∈retained H K s u,weight H K s u gamma/(residueNode p gamma-residueNode p (t:ZMod p)) := by
  classical
  unfold retained
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro gamma _
  by_cases h : weight H K s u gamma=0
  · simp only [h,ne_eq,not_true_eq_false,↓reduceIte,zero_div]
  · simp only [h,ne_eq,not_false_eq_true,↓reduceIte]

/-- The actual joint entries have the second integral order and the
same finite Cauchy factors as the retained original source. -/
theorem joint_entries (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H K s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hz : surplusRow H z∈Icc H.t0 H.tv) (hy : surplusCol H y∈Icc H.t0 H.tv)
    (hzq : (surplusRow H z:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (hyq : (surplusCol H y:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    ∃ J:WrapDeform.Extension p,W z y=WrapDeform.uniformizer p*J ∧
      WrapDeform.residue p J=∑ gamma∈retained H K s u,
        (WrapDeform.residue p (rowReference H K s u (surplusRow H z))/
          (residueNode p gamma-residueNode p (surplusRow H z:ZMod p)))*
        (weight H K s u gamma*WrapDeform.residue p (colReference H K s u (surplusCol H y))/
          (residueNode p gamma-residueNode p (surplusCol H y:ZMod p))) := by
  classical
  obtain ⟨F,hFR,hFC,hF⟩ := two_sided_source H K s u hs hu huc (surplusRow H z) hz hzq
  obtain ⟨G,hGR,hGC,hG⟩ := two_sided_source H K s u hs hu huc (surplusCol H y) hy hyq
  have hd := difference_unit H (surplusRow H z) (surplusCol H y) (hdist z y)
  have he := actual_displacement H K s u hs hu huc z y
  rw [hW] at he
  change ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))*
    (WrapDeform.uniformizer p*W z y)=_ at he
  have hxRet : ∀ gamma∈retained H K s u,residueNode p gamma-residueNode p (surplusRow H z:ZMod p)≠0 := by
    intro gamma hg heq
    have hgamma := (residueNode p).injective (sub_eq_zero.mp heq)
    have hw := (mem_filter.mp hg).2
    rw [hgamma,selected_weight_zero H K s u hs hu huc _ hz hzq] at hw
    exact hw rfl
  have hyRet : ∀ gamma∈retained H K s u,residueNode p gamma-residueNode p (surplusCol H y:ZMod p)≠0 := by
    intro gamma hg heq
    have hgamma := (residueNode p).injective (sub_eq_zero.mp heq)
    have hw := (mem_filter.mp hg).2
    rw [hgamma,selected_weight_zero H K s u hs hu huc _ hy hyq] at hw
    exact hw rfl
  have hdelta : WrapDeform.residue p ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))=
      residueNode p (surplusCol H y:ZMod p)-residueNode p (surplusRow H z:ZMod p) := by
    simp only [map_sub,map_natCast]
  have hxy : residueNode p (surplusCol H y:ZMod p)-residueNode p (surplusRow H z:ZMod p)≠0 := by
    intro heq
    exact (hdist z y) ((residueNode p).injective (sub_eq_zero.mp heq)).symm
  exact joint_cauchy (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H K s u (surplusRow H z)) (colReference H K s u (surplusCol H y))
    (rowMoment H K s u (surplusRow H z)) (colMoment H K s u (surplusCol H y)) (H.anchor s u) F G
    (parameter_prime p).ne_zero hd he hFR hGC (retained H K s u) (residueNode p) (weight H K s u)
    (H.sourceOffset s u) _ _ hdelta hxy hxRet hyRet
    (hF.trans (congrArg (fun a => H.sourceOffset s u+a) (retained_source H K s u _)))
    (hG.trans (congrArg (fun a => H.sourceOffset s u+a) (retained_source H K s u _)))


noncomputable def rowCoupling (s u : GaussLoc p) (z : Fin d) :=
  WrapDeform.residue p (rowMoment H K s u (surplusRow H z)-H.anchor s u*rowReference H K s u (surplusRow H z))

noncomputable def colCoupling (s u : GaussLoc p) (y : Fin d) :=
  WrapDeform.residue p (colMoment H K s u (surplusCol H y)-H.anchor s u*colReference H K s u (surplusCol H y))

noncomputable def cauchyRow (s u : GaussLoc p) (z : Fin d) (gamma : ZMod p) :=
  WrapDeform.residue p (rowReference H K s u (surplusRow H z))/
    (residueNode p gamma-residueNode p (surplusRow H z:ZMod p))

noncomputable def cauchyCol (s u : GaussLoc p) (gamma : ZMod p) (y : Fin d) :=
  weight H K s u gamma*WrapDeform.residue p (colReference H K s u (surplusCol H y))/
    (residueNode p gamma-residueNode p (surplusCol H y:ZMod p))

/-- An actual outside column supplies the exact retained-column kill. -/
theorem actual_column_kill (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H K s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hz : surplusRow H z∈Icc H.t0 H.tv)
    (hzq : (surplusRow H z:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    WrapDeform.residue p (W z y)=colCoupling H K s u y*cauchyRow H K s u z (surplusCol H y:ZMod p) := by
  obtain ⟨F,hFR,hFC,hF⟩ := two_sided_source H K s u hs hu huc (surplusRow H z) hz hzq
  have he := actual_displacement H K s u hs hu huc z y
  rw [hW] at he
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hd := (difference_unit H _ _ (hdist z y)).map (WrapDeform.residue p)
  have hk := column_kill_identity (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H K s u (surplusRow H z)) (colReference H K s u (surplusCol H y))
    (rowMoment H K s u (surplusRow H z)) (colMoment H K s u (surplusCol H y)) (H.anchor s u) F
    (parameter_prime p).ne_zero hp hd.ne_zero he hFR
  simpa only [colCoupling,cauchyRow,map_sub,map_natCast] using hk

/-- An actual outside row supplies the opposite kill for each retained
nonzero source colour. -/
theorem actual_row_kill (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H K s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hy : surplusCol H y∈Icc H.t0 H.tv)
    (hw : weight H K s u (surplusRow H z:ZMod p)≠0)
    (hyq : (surplusCol H y:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    WrapDeform.residue p (W z y)=
      (rowCoupling H K s u z/weight H K s u (surplusRow H z:ZMod p))*
        cauchyCol H K s u (surplusRow H z:ZMod p) y := by
  obtain ⟨G,hGR,hGC,hG⟩ := two_sided_source H K s u hs hu huc (surplusCol H y) hy hyq
  have he := actual_displacement H K s u hs hu huc z y
  rw [hW] at he
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hd := (difference_unit H _ _ (hdist z y)).map (WrapDeform.residue p)
  have hk := row_kill_identity (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H K s u (surplusRow H z)) (colReference H K s u (surplusCol H y))
    (rowMoment H K s u (surplusRow H z)) (colMoment H K s u (surplusCol H y)) (H.anchor s u) G
    (parameter_prime p).ne_zero hp hd.ne_zero he hGC _ hw
  simpa only [rowCoupling,cauchyCol,map_sub,map_natCast,neg_sub] using hk

noncomputable def activeColumns (s u : GaussLoc p) : Finset (Fin d) := by
  classical
  exact univ.filter (fun y => colCoupling H K s u y≠0)
noncomputable def activeRows (s u : GaussLoc p) : Finset (Fin d) := by
  classical
  exact univ.filter (fun z => rowCoupling H K s u z≠0 ∧ weight H K s u (surplusRow H z:ZMod p)≠0)
noncomputable def killedColumns (s u : GaussLoc p) :=
  (activeColumns H K s u).image (fun y => (surplusCol H y:ZMod p))
noncomputable def killedRows (s u : GaussLoc p) :=
  (activeRows H K s u).image (fun z => (surplusRow H z:ZMod p))

/-- Full original-prefix integral content, with the retained source and
all nonzero actual outside couplings supplied by the original matrix. -/
theorem actual_content (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (Jr Jc : Finset (Fin d)) (hJr : ∀ z∈Jr,surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,surplusCol H y∈Icc H.t0 H.tv)
    (hJrq : ∀ z∈Jr,(surplusRow H z:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (hJcq : ∀ y∈Jc,(surplusCol H y:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    WrapDeform.uniformizer p^(d+WrapCount.gain (Jr.card+Jc.card-d)
      (retained H K s u\(killedColumns H K s u∪killedRows H K s u)).card)∣(full H K s u).det := by
  classical
  obtain ⟨W,hW⟩ := exists_divided_schur H K s u hs hu huc hdist
  have hJoint : ∀ z∈Jr,∀ y∈Jc,∃ J:WrapDeform.Extension p,W z y=WrapDeform.uniformizer p*J ∧
      WrapDeform.residue p J=∑ gamma∈retained H K s u,cauchyRow H K s u z gamma*cauchyCol H K s u gamma y := by
    intro z hz y hy
    exact joint_entries H K s u hs hu huc hdist W hW z y (hJr z hz) (hJc y hy) (hJrq z hz) (hJcq y hy)
  choose! Hc hJ hCauchy using hJoint
  have hKR : ∀ gamma∈killedColumns H K s u,∃ y:Fin d,∃ l:RatFunc (RatFunc (ZMod p)),l≠0 ∧
      ∀ z∈Jr,WrapDeform.residue p (W z y)=l*cauchyRow H K s u z gamma := by
    intro gamma hg
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hg
    exact ⟨y,colCoupling H K s u y,(mem_filter.mp hy).2,
      fun z hz => actual_column_kill H K s u hs hu huc hdist W hW z y (hJr z hz) (hJrq z hz)⟩
  have hKC : ∀ gamma∈killedRows H K s u,∃ z:Fin d,∃ l:RatFunc (RatFunc (ZMod p)),l≠0 ∧
      ∀ y∈Jc,WrapDeform.residue p (W z y)=l*cauchyCol H K s u gamma y := by
    intro gamma hg
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hg
    have hz' := (mem_filter.mp hz).2
    exact ⟨z,rowCoupling H K s u z/weight H K s u (surplusRow H z:ZMod p),div_ne_zero hz'.1 hz'.2,
      fun y hy => actual_row_kill H K s u hs hu huc hdist W hW z y (hJc y hy) hz'.2 (hJcq y hy)⟩
  simpa only [Fintype.card_fin,full] using jblock_kill_content (WrapDeform.residue p)
    (WrapDeform.uniformizer p) (parameter_prime p) (WrapDeform.residue_zero_iff p) (parameter_lift p)
    (core H K s u) (bBlock H K u) (cBlock H K u) (dBlock H u) W (core_unit H K s u hs hu huc)
    hW Jr Jc (Matrix.of Hc) hJ (retained H K s u) (cauchyRow H K s u) (cauchyCol H K s u)
    hCauchy (killedColumns H K s u) (killedRows H K s u) hKR hKC


/-- Exact independent reindexing of the ORIGINAL full matrix. Absorbed
cycles remain balanced nodes, and only original common nodes carry X. -/
theorem full_reindex (s u : GaussLoc p) :
    full H K s u=(WrapFibreCore.core p q o s u (common K)
      (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)).submatrix
        (WrapPrefixGeometry.rowFullEquiv (WrapKeep.Keep K) H.er)
        (WrapPrefixGeometry.colFullEquiv (WrapKeep.Keep K) (Fact.out:p.Prime).pos shift H.ec) := by
  classical
  apply Matrix.ext
  intro i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp only [full,core,WrapFibreCore.core,bBlock,cBlock,dBlock,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.submatrix_apply,Matrix.add_apply,Matrix.of_apply,Matrix.zero_apply,add_zero,
      WrapPrefixGeometry.rowFullEquiv,WrapPrefixGeometry.colFullEquiv,Equiv.trans_apply,
      Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,Equiv.sumAssoc_apply_inr,Equiv.sumCongr_apply,Equiv.refl_apply,Equiv.sumCongr,Equiv.coe_fn_mk,Sum.map_inl,Sum.map_inr,
      Sum.elim_inl,Sum.elim_inr,common,rowNode,colNode,surplusRow,surplusCol,
      WrapPrefixWindow.Setup.xs,WrapPrefixWindow.Setup.ys,WrapPrefixCoreGeometry.xs,WrapPrefixCoreGeometry.ys]

/-- The original deformed-family interface is exactly the concrete
mixed prefix matrix at the original spectral parameter. -/
theorem full_original {Fr : Frame} :
    full H K (algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X) (WrapOriginalEntry.normInv p Fr)=
      (WrapDeformedFamily.matrix p Fr q o (common K)
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)).submatrix
          (WrapPrefixGeometry.rowFullEquiv (WrapKeep.Keep K) H.er)
          (WrapPrefixGeometry.colFullEquiv (WrapKeep.Keep K) (Fact.out:p.Prime).pos shift H.ec) := by
  rw [full_reindex H K]
  congr 1
  apply Matrix.ext
  intro i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp only [WrapFibreCore.core,WrapDeformedFamily.matrix,WrapDeformedFamily.spectral,
      Matrix.add_apply,Matrix.map_apply,Matrix.of_apply,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,map_zero,add_zero,
      WrapOwnCore.constants,WrapDeformedFamily.coefficient,WrapDeformedFamily.originalMap,
      RingHom.comp_apply,Sum.elim_inl,Sum.elim_inr,CatalanCore.Uniform.Content.UFMember.rowNode,CatalanCore.Uniform.Content.UFMember.colNode]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  split <;> simp only [mul_one,mul_zero,map_mul,map_one,map_zero,Polynomial.C_mul,Polynomial.C_1,Polynomial.C_0]

/-- The actual member determinant descends to its ORIGINAL polynomial;
no inverse pivot is specialized. -/
theorem original_gle {Fr : Frame} (T : CatalanCore.Uniform.Content.Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (Jr Jc : Finset (Fin d)) (hJr : ∀ z∈Jr,surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,surplusCol H y∈Icc H.t0 H.tv)
    (hJrq : ∀ z∈Jr,(surplusRow H z:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (hJcq : ∀ y∈Jc,(surplusCol H y:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    let s := algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X
    let u := WrapOriginalEntry.normInv p Fr
    GLE p (2*(r-K.card+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d)
      (retained H K s u\(killedColumns H K s u∪killedRows H K s u)).card))
      (CatalanCore.Rect.FullN Fr (common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) (Polynomial.X:ℚ[X])).det := by
  intro s u
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hc : ∀ i:WrapKeep.Keep K,common K i<N := fun i => H.common_bound i.1
  have hx : ∀ i:Fin (n*p+e),r+2*(i:ℕ)<N := by intro i; have := i.2; have := H.hsize; omega
  have hy : ∀ i:Fin (n*p+e),r+2*(i:ℕ)+1<N := by intro i; have := i.2; have := H.hsize; omega
  have hh := actual_content H K s u (WrapFrameResidue.spectral p) (WrapFrameResidue.normInv_ne p D)
    (WrapFrameResidue.normInv_constant p D) hdist Jr Jc hJr hJc hJrq hJcq
  rw [full_original H K] at hh
  have hg := WrapPrefixSchur.original_gle_of_mixed_content p T D H.hqp hsingle hsq
    (common K) (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1) hc hx hy
    (WrapPrefixGeometry.rowFullEquiv (WrapKeep.Keep K) H.er)
    (WrapPrefixGeometry.colFullEquiv (WrapKeep.Keep K) (Fact.out:p.Prime).pos shift H.ec) _ hh
  have hk : Fintype.card (WrapKeep.Keep K)=r-K.card := by
    simp only [WrapKeep.Keep,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]
  simpa only [Fintype.card_sum,Fintype.card_fin,hk,Nat.add_assoc] using hg

end Schur


section QuietCouplings
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def fullOwnColumnSigma (u : GaussLoc p) (t : ℕ)
    (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  if H.colour i=(t:ZMod p) then
    WrapDeformedEntry.entry p q o u (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i) t else 0
noncomputable def ownColumnSigma (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) :=
  fullOwnColumnSigma H u t ∘ embed K

theorem ownColumnSigma_eq (K : Finset (Fin r)) (u : GaussLoc p) (t : ℕ) :
    ownColumnSigma H K u t=(fun i => if colour H K i=(t:ZMod p) then
      Schur.columnSigma H K u t i else 0) := by
  funext i
  cases i <;> rfl

theorem own_column_response_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)))
    (L : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p) :
    (L ∘ embed K) ⬝ᵥ (own H K s u)⁻¹ *ᵥ ownColumnSigma H K u t=
      L ⬝ᵥ (H.own s u)⁻¹ *ᵥ fullOwnColumnSigma H u t := by
  have hb : ∀ i j,H.colour i≠H.colour j → H.own s u i j=0 := by
    intro i j hij
    simp only [WrapPrefixWindow.Setup.own,WrapPrefixSource.own,Matrix.of_apply,hij,↓reduceIte]
  have hk := own_unit H K s u hs hu huc
  rw [own_restrict H] at hk
  rw [own_restrict H]
  exact own_column_response_restrict H.colour (embed K) (t:ZMod p)
    (fibreEquiv H K (t:ZMod p) ht) (fibreEquiv_val H K (t:ZMod p) ht)
    (H.own s u) (H.own_unit s u hs hu huc) hb hk (fullOwnColumnSigma H u t) L
    (by intro i hi; simp only [fullOwnColumnSigma,hi,↓reduceIte])

/-- Both actual outside couplings persist at every untouched colour.
Their values are compared after reduction, without specializing any pivot. -/
theorem couplings_unchanged (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t<N) (hg : (t:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p))) :
    WrapDeform.residue p (Schur.rowMoment H K s u t-H.anchor s u*Schur.rowReference H K s u t)=
      WrapDeform.residue p (WrapPrefixSchur.rowMoment H s u t-H.anchor s u*WrapPrefixSchur.rowReference H s u t) ∧
    WrapDeform.residue p (Schur.colMoment H K s u t-H.anchor s u*Schur.colReference H K s u t)=
      WrapDeform.residue p (WrapPrefixSchur.colMoment H s u t-H.anchor s u*WrapPrefixSchur.colReference H s u t) := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hM := coupling_reduction p q o N s u (common K) H.xs H.ys hsingle
    (fun i => H.common_bound i.1) H.row_bound H.col_bound H.same_colour (core_unit H K s u hs hu huc) t ht (H.anchor s u)
  have hF := coupling_reduction p q o N s u (fun i:Fin r => (i:ℕ)) H.xs H.ys hsingle
    H.common_bound H.row_bound H.col_bound H.same_colour (H.core_unit s u hs hu huc) t ht (H.anchor s u)
  have hMR : WrapDeform.residue p (sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ (fun i => rowLoad H K u i-H.anchor s u))=
      WrapDeform.residue p (ownSigma H K u t ⬝ᵥ (own H K s u)⁻¹ *ᵥ (fun i => rowLoad H K u i-H.anchor s u)) := by
    simpa only [sigma_eq,ownSigma_eq,rowLoad_eq,core,own,colour] using hM.1
  have hMC : WrapDeform.residue p ((fun i => colLoad H K u i-H.anchor s u) ⬝ᵥ (core H K s u)⁻¹ *ᵥ Schur.columnSigma H K u t)=
      WrapDeform.residue p ((fun i => colLoad H K u i-H.anchor s u) ⬝ᵥ (own H K s u)⁻¹ *ᵥ ownColumnSigma H K u t) := by
    have hsc : Schur.columnSigma H K u t=(fun i => WrapDeformedEntry.entry p q o u (Sum.elim (common K) H.xs i) t) := by
      funext i
      rfl
    simpa only [ownColumnSigma_eq,colLoad_eq,hsc,core,own,colour] using hM.2
  have hFR : WrapDeform.residue p (H.sigma u t ⬝ᵥ (H.core s u)⁻¹ *ᵥ (fun i => H.rowLoad u i-H.anchor s u))=
      WrapDeform.residue p (H.ownSigma u t ⬝ᵥ (H.own s u)⁻¹ *ᵥ (fun i => H.rowLoad u i-H.anchor s u)) := by
    exact hF.1
  have hFC : WrapDeform.residue p ((fun i => H.colLoad u i-H.anchor s u) ⬝ᵥ (H.core s u)⁻¹ *ᵥ WrapPrefixSchur.columnSigma H u t)=
      WrapDeform.residue p ((fun i => H.colLoad u i-H.anchor s u) ⬝ᵥ (H.own s u)⁻¹ *ᵥ fullOwnColumnSigma H u t) := by
    exact hF.2
  have hr := congrArg (WrapDeform.residue p) (own_response_unchanged H K s u hs hu huc t hg
    (fun i => H.rowLoad u i-H.anchor s u))
  have hc := congrArg (WrapDeform.residue p) (own_column_response_unchanged H K s u hs hu huc t hg
    (fun i => H.colLoad u i-H.anchor s u))
  constructor
  · dsimp only [Schur.rowMoment,Schur.rowReference,WrapPrefixSchur.rowMoment,WrapPrefixSchur.rowReference]
    rw [shifted_row_identity,shifted_row_identity,map_sub,map_sub]
    simpa only [map_sub] using congrArg (fun a => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u)-a)
      (hMR.trans (hr.trans hFR.symm))
  · dsimp only [Schur.colMoment,Schur.colReference,WrapPrefixSchur.colMoment,WrapPrefixSchur.colReference]
    rw [shifted_col_identity,shifted_col_identity,map_sub,map_sub]
    simpa only [map_sub] using congrArg (fun a => WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.anchor s u)-a)
      (hMC.trans (hc.trans hFC.symm))

end QuietCouplings


section Retained
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def fullRetained (s u : GaussLoc p) :=
  WrapPrefixSchur.retained H s u\(WrapPrefixSchur.killedColumns H s u∪WrapPrefixSchur.killedRows H s u)
noncomputable def retained (K : Finset (Fin r)) (s u : GaussLoc p) :=
  Schur.retained H K s u\(Schur.killedColumns H K s u∪Schur.killedRows H K s u)

/-- An untouched colour cannot enlarge the member's retained source.
Both original outside coupling kills survive the literal restriction. -/
theorem retained_quiet (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (gamma : ZMod p) (hg : gamma∉K.image (fun i:Fin r => (i:ZMod p)))
    (hm : gamma∈retained H K s u) : gamma∈fullRetained H s u := by
  classical
  obtain ⟨hmw,hmkill⟩ := mem_sdiff.mp hm
  have hwm : weight H K s u gamma≠0 := (mem_filter.mp hmw).2
  have hwf : H.weight s u gamma≠0 := by rw [← weight_unchanged H K s u hs hu huc gamma hg]; exact hwm
  apply mem_sdiff.mpr
  refine ⟨mem_filter.mpr ⟨mem_univ _,hwf⟩,?_⟩
  intro hk
  rcases mem_union.mp hk with hc|hr
  · obtain ⟨y,hy,hyg⟩ := mem_image.mp hc
    have hyg' : (Schur.surplusCol H y:ZMod p)=gamma := hyg
    have hq : (Schur.surplusCol H y:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)) := by simpa only [hyg'] using hg
    have he := (couplings_unchanged H K s u hs hu huc (Schur.surplusCol H y) (Schur.surplus_col_bound H y) hq).2
    have hval : Schur.colCoupling H K s u y=WrapPrefixSchur.colCoupling H s u y := he
    have hne : Schur.colCoupling H K s u y≠0 := by rw [hval]; exact (mem_filter.mp hy).2
    apply hmkill
    apply mem_union_left
    exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,hne⟩,hyg⟩
  · obtain ⟨z,hz,hzg⟩ := mem_image.mp hr
    have hzg' : (Schur.surplusRow H z:ZMod p)=gamma := hzg
    have hq : (Schur.surplusRow H z:ZMod p)∉K.image (fun i:Fin r => (i:ZMod p)) := by simpa only [hzg'] using hg
    have he := (couplings_unchanged H K s u hs hu huc (Schur.surplusRow H z) (Schur.surplus_row_bound H z) hq).1
    have hval : Schur.rowCoupling H K s u z=WrapPrefixSchur.rowCoupling H s u z := he
    have hne : Schur.rowCoupling H K s u z≠0 := by rw [hval]; exact (mem_filter.mp hz).2.1
    apply hmkill
    apply mem_union_right
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,hne,by simpa only [hzg'] using hwm⟩,hzg⟩

end Retained


section FullFibre
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)
attribute [local instance] WrapPrefixSchur.extensionDomain

abbrev FullFibre (gamma : ZMod p) :=
  {i:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour i=gamma}
noncomputable def fibreMatrix (s u : GaussLoc p) (gamma : ZMod p) :=
  (blk (H.own s u) H.colour gamma).map (WrapDeform.residue p)
noncomputable def fibreRow (u : GaussLoc p) (gamma : ZMod p) (i:FullFibre H gamma) :=
  WrapDeform.residue p (H.rowLoad u i.1)
noncomputable def fibreCol (u : GaussLoc p) (gamma : ZMod p) (i:FullFibre H gamma) :=
  WrapDeform.residue p (H.colLoad u i.1)
noncomputable def fibreSigma (u : GaussLoc p) (t : ℕ) (i:FullFibre H (t:ZMod p)) :=
  WrapDeform.residue p (H.sigma u t i.1)
noncomputable def fibreRowCoord (t : ℕ) (i:FullFibre H (t:ZMod p)) : RatFunc (RatFunc (ZMod p)) :=
  ((WrapPrefixSchur.rowNode H i.1/p:ℕ):RatFunc (RatFunc (ZMod p)))-((t/p:ℕ):RatFunc (RatFunc (ZMod p)))
noncomputable def fibreColCoord (t : ℕ) (i:FullFibre H (t:ZMod p)) : RatFunc (RatFunc (ZMod p)) :=
  ((WrapPrefixSchur.colNode H i.1/p:ℕ):RatFunc (RatFunc (ZMod p)))-((t/p:ℕ):RatFunc (RatFunc (ZMod p)))

theorem full_own_block (s u : GaussLoc p) :
    ∀ i j,H.colour i≠H.colour j → H.own s u i j=0 := by
  intro i j hij
  simp only [WrapPrefixWindow.Setup.own,WrapPrefixSource.own,Matrix.of_apply,hij,↓reduceIte]

theorem fibre_matrix_unit (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (gamma : ZMod p) : IsUnit (fibreMatrix H s u gamma).det :=
  mapped_block_unit (WrapDeform.residue p) _
    (inv_restrict (H.own s u) H.colour (H.own_unit s u hs hu huc) (full_own_block H s u) gamma).1

/-- Original quotient coordinates give the exact own-block displacement,
including the unchanged original spectral diagonal. -/
theorem fibre_displacement (s u : GaussLoc p) (t : ℕ)
    (i j : FullFibre H (t:ZMod p)) :
    (fibreColCoord H t j-fibreRowCoord H t i)*fibreMatrix H s u (t:ZMod p) i j=
      fibreCol H u (t:ZMod p) j-fibreRow H u (t:ZMod p) i := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hcolour : (WrapPrefixSchur.rowNode H i.1:ZMod p)=(WrapPrefixSchur.colNode H j.1:ZMod p) := by
    have hi : (WrapPrefixSchur.rowNode H i.1:ZMod p)=H.colour i.1 := by cases i.1 <;> rfl
    have hj : (WrapPrefixSchur.colNode H j.1:ZMod p)=H.colour j.1 := by
      cases j.1 with
      | inl j => rfl
      | inr j => exact (H.same_colour j).symm
    exact hi.trans (i.2.trans (j.2.symm.trans hj.symm))
  have hcoord := coordinate_quotient (R:=WrapDeform.Extension p) p (WrapPrefixSchur.rowNode H i.1)
    (WrapPrefixSchur.colNode H j.1) ((ZMod.natCast_eq_natCast_iff' _ _ p).mp hcolour)
  rw [WrapEntryRelation.uniformizer_cast p] at hcoord
  have he := WrapPrefixSource.core_displacement p q o N s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
    hsingle H.common_bound H.row_bound H.col_bound i.1 j.1
  change ((WrapPrefixSchur.colNode H j.1:WrapDeform.Extension p)-(WrapPrefixSchur.rowNode H i.1:WrapDeform.Extension p))*
    H.core s u i.1 j.1=WrapDeform.uniformizer p*(H.colLoad u j.1-H.rowLoad u i.1) at he
  rw [hcoord] at he
  have hdiv : (((WrapPrefixSchur.colNode H j.1/p:ℕ):WrapDeform.Extension p)-
      ((WrapPrefixSchur.rowNode H i.1/p:ℕ):WrapDeform.Extension p))*H.core s u i.1 j.1=
      H.colLoad u j.1-H.rowLoad u i.1 := by
    have hpi : WrapDeform.uniformizer p≠0 := (WrapPrefixSchur.parameter_prime p).ne_zero
    apply mul_left_cancel₀ hpi
    simpa only [mul_assoc] using he
  have hm : H.own s u i.1 j.1=H.core s u i.1 j.1 := by
    simp only [WrapPrefixWindow.Setup.own,WrapPrefixSource.own,Matrix.of_apply,
      i.2.trans j.2.symm,↓reduceIte]
  have hf := congrArg (WrapDeform.residue p) hdiv
  simp only [map_mul,map_sub,map_natCast] at hf
  change (_-_) * WrapDeform.residue p (H.own s u i.1 j.1)=_
  rw [hm]
  dsimp only [fibreRowCoord,fibreColCoord,fibreRow,fibreCol]
  linear_combination hf

theorem fibre_sigma_displacement (u : GaussLoc p) (t : ℕ) (ht : t<N)
    (i : FullFibre H (t:ZMod p)) :
    fibreColCoord H t i*fibreSigma H u t i=
      fibreCol H u (t:ZMod p) i-WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t) := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hcol : (t:ZMod p)=(WrapPrefixSchur.colNode H i.1:ZMod p) := by
    have hc : (WrapPrefixSchur.colNode H i.1:ZMod p)=H.colour i.1 := by
      cases i.1 with
      | inl i => rfl
      | inr i => exact (H.same_colour i).symm
    exact i.2.symm.trans hc.symm
  have he := congrArg (WrapDeform.residue p) (WrapEntryRelation.divided_commutator p q o N u hsingle
    t (WrapPrefixSchur.colNode H i.1) ht (WrapPrefixSchur.col_bound H i.1) hcol)
  simp only [map_mul,map_sub,map_natCast] at he
  simpa only [fibreColCoord,fibreSigma,fibreCol,WrapPrefixWindow.Setup.sigma,
    WrapPrefixWindow.Setup.colLoad,WrapPrefixSchur.colNode,mul_sub,map_mul,map_sub,
    WrapOwnCore.constants,WrapEntryRelation.constants] using he

theorem full_fibre_source (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    fibreSigma H u t ⬝ᵥ (fibreMatrix H s u (t:ZMod p))⁻¹ *ᵥ
      (fun i => fibreRow H u (t:ZMod p) i-WrapDeform.residue p (H.anchor s u))=
        WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)-WrapDeform.residue p (H.anchor s u) ∧
    1-fibreSigma H u t ⬝ᵥ (fibreMatrix H s u (t:ZMod p))⁻¹ *ᵥ 1≠0 := by
  classical
  obtain ⟨G,hm,hr,hne⟩ := H.own_source t ht s u hs hu huc
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hsupport : ∀ i,H.colour i≠(t:ZMod p) → H.ownSigma u t i=0 := by
    intro i hi
    simp only [WrapPrefixWindow.Setup.ownSigma,hi,↓reduceIte]
  have hsig : (fun i:FullFibre H (t:ZMod p) => WrapDeform.residue p (H.ownSigma u t i.1))=fibreSigma H u t := by
    funext i
    simp only [WrapPrefixWindow.Setup.ownSigma,i.2,↓reduceIte,fibreSigma]
  have hresp := local_own_response_map (WrapDeform.residue p) (H.own s u) H.colour (H.own_unit s u hs hu huc)
    (full_own_block H s u) (t:ZMod p) (H.ownSigma u t) (fun i => H.rowLoad u i-H.anchor s u) hsupport
  have hresp1 := local_own_response_map (WrapDeform.residue p) (H.own s u) H.colour (H.own_unit s u hs hu huc)
    (full_own_block H s u) (t:ZMod p) (H.ownSigma u t) (1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p) hsupport
  simp only [hsig,map_sub] at hresp
  simp only [hsig,Pi.one_apply,map_one] at hresp1
  rw [← Matrix.dotProduct_mulVec] at hm
  have hf := congrArg (WrapDeform.residue p) hm
  simp only [map_sub,map_mul,hp,zero_mul] at hf
  refine ⟨hresp.trans (by simpa only [map_mul] using (sub_eq_zero.mp hf).symm),?_⟩
  have hRef : H.ownReference s u t=1-H.ownSigma u t ⬝ᵥ (H.own s u)⁻¹ *ᵥ 1 := by
    rw [Matrix.dotProduct_mulVec]
    simp only [WrapPrefixWindow.Setup.ownReference,dotProduct,Pi.one_apply,mul_one]
  rw [hRef,map_sub,map_one,← hresp1] at hne
  exact hne

theorem full_fibre_moment (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (gamma : ZMod p) :
    (fun i => fibreCol H u gamma i-WrapDeform.residue p (H.anchor s u)) ⬝ᵥ (fibreMatrix H s u gamma)⁻¹ *ᵥ
      (fun i => fibreRow H u gamma i-WrapDeform.residue p (H.anchor s u))=H.moment s u gamma := by
  simpa only [fibreRow,fibreCol,fibreMatrix,map_sub,moment,WrapPrefixWindow.Setup.moment] using
    local_moment_map (WrapDeform.residue p) (H.own s u) H.colour (H.own_unit s u hs hu huc)
      (full_own_block H s u) gamma (fun i => H.rowLoad u i-H.anchor s u) (fun i => H.colLoad u i-H.anchor s u)

end FullFibre


section SingleRow
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

abbrev KeptFibre (K : Finset (Fin r)) (gamma : ZMod p) :=
  {i:WrapKeep.Keep K ⊕ ((Fin n × Fin p) ⊕ Fin b) // H.colour (embed K i)=gamma}
noncomputable def keptFibreMap (K : Finset (Fin r)) (gamma : ZMod p) (i:KeptFibre H K gamma) : FullFibre H gamma :=
  ⟨embed K i.1,i.2⟩

/-- A single original common deletion at a selected colour creates no
retained weight when its actual remaining row coupling vanishes. -/
theorem single_row_weight (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) (a:Fin r) (ha:a∈K) (hgamma:(a:ZMod p)=(t:ZMod p))
    (honly : ∀ i∈K,(i:ZMod p)=(t:ZMod p) → i=a)
    (hrow : WrapDeform.residue p (Schur.rowMoment H K s u t-H.anchor s u*Schur.rowReference H K s u t)=0) :
    weight H K s u (t:ZMod p)=0 := by
  classical
  let gamma : ZMod p := (t:ZMod p)
  let colK := fun i => H.colour (embed K i)
  let f := keptFibreMap H K gamma
  let E := singleFibreEquiv H K gamma a ha hgamma honly
  let D := own H K s u
  have hbK : ∀ i j,colK i≠colK j → D i j=0 := by
    intro i j hij
    change H.colour (embed K i)≠H.colour (embed K j) at hij
    simp only [D,own,WrapPrefixSource.own,Matrix.of_apply,colour_embed,hij,↓reduceIte]
  have hDU := own_unit H K s u hs hu huc
  have hmat : (fibreMatrix H s u gamma).submatrix f f=(blk D colK gamma).map (WrapDeform.residue p) := by
    apply Matrix.ext
    intro i j
    change WrapDeform.residue p (H.own s u (embed K i.1) (embed K j.1))=WrapDeform.residue p (own H K s u i.1 j.1)
    rw [own_restrict H]
    rfl
  have hf : IsUnit ((fibreMatrix H s u gamma).submatrix f f).det := by
    rw [hmat]
    exact mapped_block_unit (WrapDeform.residue p) _ (inv_restrict D colK hDU hbK gamma).1
  have htN : t<N := lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hred := (coupling_reduction p q o N s u (common K) H.xs H.ys hsingle
    (fun i => H.common_bound i.1) H.row_bound H.col_bound H.same_colour
    (core_unit H K s u hs hu huc) t htN (H.anchor s u)).1
  have hMR : WrapDeform.residue p (sigma H K u t ⬝ᵥ (core H K s u)⁻¹ *ᵥ (fun i => rowLoad H K u i-H.anchor s u))=
      WrapDeform.residue p (ownSigma H K u t ⬝ᵥ D⁻¹ *ᵥ (fun i => rowLoad H K u i-H.anchor s u)) := by
    simpa only [D,sigma_eq,ownSigma_eq,rowLoad_eq,core,own,colour] using hred
  dsimp only [Schur.rowMoment,Schur.rowReference] at hrow
  rw [shifted_row_identity,map_sub,hMR] at hrow
  simp only [map_sub] at hrow
  have hOwn := (sub_eq_zero.mp hrow).symm
  have hsupport : ∀ i,colK i≠gamma → ownSigma H K u t i=0 := by
    intro i hi
    exact if_neg hi
  have hSig : (fun i:KeptFibre H K gamma => WrapDeform.residue p (ownSigma H K u t i.1))=
      fibreSigma H u t ∘ f := by
    funext i
    change WrapDeform.residue p (if H.colour (embed K i.1)=gamma then H.sigma u t (embed K i.1) else 0)=_
    rw [if_pos i.2]
    rfl
  have hLR : (fun i:KeptFibre H K gamma => WrapDeform.residue p (rowLoad H K u i.1-H.anchor s u))=
      (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) := by
    funext i
    rw [map_sub]
    rfl
  have hLC : (fun i:KeptFibre H K gamma => WrapDeform.residue p (colLoad H K u i.1-H.anchor s u))=
      (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) := by
    funext i
    rw [map_sub]
    rfl
  have hLocal := local_own_response_map (WrapDeform.residue p) D colK hDU hbK gamma
    (ownSigma H K u t) (fun i => rowLoad H K u i-H.anchor s u) hsupport
  rw [hSig,hLR,← hmat] at hLocal
  have hMinor := hLocal.trans hOwn
  have hData := full_fibre_source H s u hs hu huc t ht
  have hm := single_restriction_moment (fibreMatrix H s u gamma) (fibre_matrix_unit H s u hs hu huc gamma)
    f E (fun _ => rfl) hf (fibreRowCoord H t) (fibreColCoord H t) (fibreRow H u gamma) (fibreCol H u gamma)
    (fibreSigma H u t) (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t))
    (WrapDeform.residue p (H.anchor s u)) (fibre_displacement H s u t) (fibre_sigma_displacement H u t htN)
    hData.1 hMinor hData.2
  have hMemberMoment := local_moment_map (WrapDeform.residue p) D colK hDU hbK gamma
    (fun i => rowLoad H K u i-H.anchor s u) (fun i => colLoad H K u i-H.anchor s u)
  rw [hLR,hLC,← hmat] at hMemberMoment
  have hcol : colour H K=colK := funext (colour_embed H K)
  have hMem : (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) ⬝ᵥ
      ((fibreMatrix H s u gamma).submatrix f f)⁻¹ *ᵥ
      (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u))=sourceMoment H K s u gamma := by
    simpa only [sourceMoment,hcol,D] using hMemberMoment
  have hEqual : H.moment s u gamma=sourceMoment H K s u gamma :=
    (full_fibre_moment H s u hs hu huc gamma).symm.trans (hm.trans hMem)
  have hw : weight H K s u gamma=H.weight s u gamma := by
    unfold weight WrapPrefixWindow.Setup.weight
    rw [← hEqual]
  rw [hw]
  exact H.weight_zero t ht s u hs hu huc

end SingleRow


section ColumnFibre
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def fibreColumnSigma (u : GaussLoc p) (t : ℕ) (i:FullFibre H (t:ZMod p)) :=
  WrapDeform.residue p (WrapDeformedEntry.entry p q o u (WrapPrefixSchur.rowNode H i.1) t)

theorem fibre_column_sigma_displacement (u : GaussLoc p) (t : ℕ) (ht : t<N)
    (i : FullFibre H (t:ZMod p)) :
    fibreRowCoord H t i*fibreColumnSigma H u t i=
      fibreRow H u (t:ZMod p) i-WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t) := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hcol : (t:ZMod p)=(WrapPrefixSchur.rowNode H i.1:ZMod p) := by
    have hc : (WrapPrefixSchur.rowNode H i.1:ZMod p)=H.colour i.1 := by cases i.1 <;> rfl
    exact i.2.symm.trans hc.symm
  have he := congrArg (WrapDeform.residue p) (WrapEntryRelation.divided_commutator p q o N u hsingle
    t (WrapPrefixSchur.rowNode H i.1) ht (WrapPrefixSchur.row_bound H i.1) hcol)
  simp only [map_mul,map_sub,map_natCast] at he
  rw [WrapEntryRelation.entry_symm p q o u t (WrapPrefixSchur.rowNode H i.1)] at he
  simpa only [fibreRowCoord,fibreColumnSigma,fibreRow,WrapPrefixWindow.Setup.rowLoad,
    WrapPrefixSchur.rowNode,mul_sub,map_mul,map_sub,WrapOwnCore.constants,WrapEntryRelation.constants] using he

theorem fibre_column_reference_ne (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    1-(1:FullFibre H (t:ZMod p) → RatFunc (RatFunc (ZMod p))) ⬝ᵥ
      (fibreMatrix H s u (t:ZMod p))⁻¹ *ᵥ fibreColumnSigma H u t≠0 := by
  classical
  let gamma : ZMod p := (t:ZMod p)
  let kc := WrapJointProfile.count p r gamma.val
  let Q := blk (H.own s u) H.colour gamma
  let sig : FullFibre H gamma → WrapDeform.Extension p :=
    fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixSchur.rowNode H i.1)
  have hQ := (inv_restrict (H.own s u) H.colour (H.own_unit s u hs hu huc) (full_own_block H s u) gamma).1
  have hblk : Q=(H.core s u).toSquareBlock H.colour gamma := by
    apply Matrix.ext
    intro i j
    exact if_pos (i.2.trans j.2.symm)
  obtain ⟨direction,hR,hC,hBR,hBC⟩ := WrapPrefixType.anchor p (H.profile_hyp t ht) (H.count_eq t ht)
    s u hs hu huc (H.profile_common_bound t ht) (by rw [← H.tip t ht]; exact lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN)
  change IsUnit (WrapPrefixWindow.columnReference p q o r H.commonCount n gamma.val
    (gamma.val+(H.commonCount+2*n)*p) s u) at hBC
  have htip := congrArg (fun v:ℕ => WrapPrefixWindow.columnReference p q o r H.commonCount n gamma.val v s u) (H.tip t ht)
  have hBCt : IsUnit (WrapPrefixWindow.columnReference p q o r H.commonCount n gamma.val t s u) := htip.symm ▸ hBC
  have hcount := congrArg (fun k:ℕ => WrapPrefixWindow.columnReference p q o r k n gamma.val t s u) (H.count_eq t ht)
  have hBCk : IsUnit (WrapPrefixWindow.columnReference p q o r kc n gamma.val t s u) := hcount.symm ▸ hBCt
  have hprofile := WrapPrefixWindow.profile_response p r n e b d shift q o H.hp H.hp2 s u H.er H.ec gamma
    (H.hfree t ht) (fun a => WrapDeformedEntry.entry p q o u t a) (fun _ => (1:WrapDeform.Extension p))
  have hRef : 1-(1:FullFibre H gamma → WrapDeform.Extension p) ⬝ᵥ Q⁻¹ *ᵥ sig=
      WrapPrefixWindow.columnReference p q o r kc n gamma.val t s u := by
    rw [hblk]
    have hT := WrapTransport.response_transpose (WrapPrefixType.core p q o r kc n gamma.val s u)
      (fun i => WrapDeformedEntry.entry p q o u t (WrapPrefixType.rows p r kc n gamma.val i))
      (fun _ => (1:WrapDeform.Extension p))
    exact congrArg (fun v:WrapDeform.Extension p => 1-v) (hprofile.trans hT)

  have hRefU : IsUnit (1-(1:FullFibre H gamma → WrapDeform.Extension p) ⬝ᵥ Q⁻¹ *ᵥ sig) := hRef.symm ▸ hBCk
  have hmap := mapped_response (WrapDeform.residue p) Q hQ sig (1:FullFibre H gamma → WrapDeform.Extension p)
  have hsig : (WrapDeform.residue p ∘ sig)=fibreColumnSigma H u t := by
    funext i
    change WrapDeform.residue p (WrapDeformedEntry.entry p q o u t (WrapPrefixSchur.rowNode H i.1))=_
    rw [WrapEntryRelation.entry_symm p q o u t (WrapPrefixSchur.rowNode H i.1)]
    rfl
  rw [hsig] at hmap
  simp only [Function.comp_def,Pi.one_apply,map_one] at hmap
  have hv : 1-(1:FullFibre H gamma → RatFunc (RatFunc (ZMod p))) ⬝ᵥ (fibreMatrix H s u gamma)⁻¹ *ᵥ fibreColumnSigma H u t=
      WrapDeform.residue p (1-(1:FullFibre H gamma → WrapDeform.Extension p) ⬝ᵥ Q⁻¹ *ᵥ sig) := by
    rw [map_sub,map_one,← hmap]
    rfl
  rw [hv]
  exact (hRefU.map (WrapDeform.residue p)).ne_zero

end ColumnFibre


section ColumnLocalMap
variable {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]
  {p : ℕ} [Fact p.Prime]

theorem local_own_column_response_map (phi : R →+* K) (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ i j,col i≠col j → D i j=0) (gamma : ZMod p) (sigma L : α → R)
    (hsigma : ∀ i,col i≠gamma → sigma i=0) :
    (fun i:{i // col i=gamma} => phi (L i.1)) ⬝ᵥ ((blk D col gamma).map phi)⁻¹ *ᵥ
      (fun i => phi (sigma i.1))=phi (L ⬝ᵥ D⁻¹ *ᵥ sigma) := by
  have hDT : IsUnit Dᵀ.det := by rw [Matrix.det_transpose]; exact hD
  have hbT : ∀ i j,col i≠col j → Dᵀ i j=0 := fun i j h => hb j i (Ne.symm h)
  have he := local_own_response_map phi Dᵀ col hDT hbT gamma sigma L hsigma
  have hT : (blk Dᵀ col gamma).map phi=((blk D col gamma).map phi)ᵀ := rfl
  rw [hT,← WrapTransport.response_transpose ((blk D col gamma).map phi)
    (fun i => phi (sigma i.1)) (fun i => phi (L i.1)),← WrapTransport.response_transpose D sigma L] at he
  exact he

end ColumnLocalMap

section FullColumnSource
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

theorem full_column_fibre_source (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    fibreColumnSigma H u t ⬝ᵥ (fibreMatrix H s u (t:ZMod p))ᵀ⁻¹ *ᵥ
      (fun i => fibreCol H u (t:ZMod p) i-WrapDeform.residue p (H.anchor s u))=
        WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)-WrapDeform.residue p (H.anchor s u) ∧
    1-fibreColumnSigma H u t ⬝ᵥ (fibreMatrix H s u (t:ZMod p))ᵀ⁻¹ *ᵥ 1≠0 := by
  let Q := fibreMatrix H s u (t:ZMod p)
  let LR := fibreRow H u (t:ZMod p)
  let LC := fibreCol H u (t:ZMod p)
  let sr := fibreSigma H u t
  let sc := fibreColumnSigma H u t
  let Lt := WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)
  let direction := WrapDeform.residue p (H.anchor s u)
  have htN : t<N := lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN
  have hsource := full_fibre_source H s u hs hu huc t ht
  have hcross := WrapMixedReference.cross_direction Q (fibre_matrix_unit H s u hs hu huc _)
    (fibreRowCoord H t) (fibreColCoord H t) LR LC sr sc 0 Lt
    (fibre_displacement H s u t)
    (by intro i; simpa only [sub_zero] using fibre_sigma_displacement H u t htN i)
    (by intro i; have he := fibre_column_sigma_displacement H u t htN i; linear_combination -he)
  have hR : Lt-sr ⬝ᵥ Q⁻¹ *ᵥ LR=direction*(1-sr ⬝ᵥ Q⁻¹ *ᵥ 1) := by
    have he := shifted_row_identity Q sr LR Lt direction
    rw [hsource.1,sub_self] at he
    exact sub_eq_zero.mp he
  have hC : Lt-LC ⬝ᵥ Q⁻¹ *ᵥ sc=direction*(1-(1:FullFibre H (t:ZMod p) → RatFunc (RatFunc (ZMod p))) ⬝ᵥ Q⁻¹ *ᵥ sc) := by
    have he := WrapPrefixSchur.column_source_of_row 0 _ _ _ _ direction 0
      (isUnit_iff_ne_zero.mpr hsource.2) hcross (by simpa only [mul_zero,zero_mul,add_zero] using hR)
    simpa only [mul_zero,zero_mul,add_zero] using he
  have hCS : (fun i => LC i-direction) ⬝ᵥ Q⁻¹ *ᵥ sc=Lt-direction := by
    have he := shifted_col_identity Q sc LC Lt direction
    rw [hC,sub_self] at he
    exact (sub_eq_zero.mp he.symm).symm
  constructor
  · exact (WrapTransport.response_transpose Q sc (fun i => LC i-direction)).symm.trans hCS
  · rw [← WrapTransport.response_transpose Q sc 1]
    exact fibre_column_reference_ne H s u hs hu huc t ht

end FullColumnSource

section SingleColumn
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

theorem single_column_weight (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (t : ℕ) (ht : t∈Icc H.t0 H.tv) (a:Fin r) (ha:a∈K) (hgamma:(a:ZMod p)=(t:ZMod p))
    (honly : ∀ i∈K,(i:ZMod p)=(t:ZMod p) → i=a)
    (hcolumn : WrapDeform.residue p (Schur.colMoment H K s u t-H.anchor s u*Schur.colReference H K s u t)=0) :
    weight H K s u (t:ZMod p)=0 := by
  classical
  let gamma : ZMod p := (t:ZMod p)
  let colK := fun i => H.colour (embed K i)
  let f := keptFibreMap H K gamma
  let E := singleFibreEquiv H K gamma a ha hgamma honly
  let D := own H K s u
  have hbK : ∀ i j,colK i≠colK j → D i j=0 := by
    intro i j hij
    change H.colour (embed K i)≠H.colour (embed K j) at hij
    simp only [D,own,WrapPrefixSource.own,Matrix.of_apply,colour_embed,hij,↓reduceIte]
  have hDU := own_unit H K s u hs hu huc
  have hmat : (fibreMatrix H s u gamma).submatrix f f=(blk D colK gamma).map (WrapDeform.residue p) := by
    apply Matrix.ext
    intro i j
    change WrapDeform.residue p (H.own s u (embed K i.1) (embed K j.1))=WrapDeform.residue p (own H K s u i.1 j.1)
    rw [own_restrict H]
    rfl
  have hf : IsUnit ((fibreMatrix H s u gamma).submatrix f f).det := by
    rw [hmat]
    exact mapped_block_unit (WrapDeform.residue p) _ (inv_restrict D colK hDU hbK gamma).1
  have htN : t<N := lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  have hred := (coupling_reduction p q o N s u (common K) H.xs H.ys hsingle
    (fun i => H.common_bound i.1) H.row_bound H.col_bound H.same_colour
    (core_unit H K s u hs hu huc) t htN (H.anchor s u)).2
  have hMC : WrapDeform.residue p ((fun i => colLoad H K u i-H.anchor s u) ⬝ᵥ (core H K s u)⁻¹ *ᵥ Schur.columnSigma H K u t)=
      WrapDeform.residue p ((fun i => colLoad H K u i-H.anchor s u) ⬝ᵥ D⁻¹ *ᵥ ownColumnSigma H K u t) := by
    have hsc : Schur.columnSigma H K u t=(fun i => WrapDeformedEntry.entry p q o u (Sum.elim (common K) H.xs i) t) := by funext i; rfl
    simpa only [D,ownColumnSigma_eq,colLoad_eq,hsc,core,own,colour] using hred
  dsimp only [Schur.colMoment,Schur.colReference] at hcolumn
  rw [shifted_col_identity,map_sub,hMC] at hcolumn
  simp only [map_sub] at hcolumn
  have hOwn := (sub_eq_zero.mp hcolumn).symm
  have hsupport : ∀ i,colK i≠gamma → ownColumnSigma H K u t i=0 := by
    intro i hi
    exact if_neg hi
  have hSig : (fun i:KeptFibre H K gamma => WrapDeform.residue p (ownColumnSigma H K u t i.1))=
      fibreColumnSigma H u t ∘ f := by
    funext i
    change WrapDeform.residue p (if H.colour (embed K i.1)=gamma then WrapDeformedEntry.entry p q o u (WrapPrefixSchur.rowNode H (embed K i.1)) t else 0)=_
    rw [if_pos i.2]
    rfl
  have hLR : (fun i:KeptFibre H K gamma => WrapDeform.residue p (rowLoad H K u i.1-H.anchor s u))=
      (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) := by
    funext i
    rw [map_sub]
    rfl
  have hLC : (fun i:KeptFibre H K gamma => WrapDeform.residue p (colLoad H K u i.1-H.anchor s u))=
      (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) := by
    funext i
    rw [map_sub]
    rfl
  have hLocal := local_own_column_response_map (WrapDeform.residue p) D colK hDU hbK gamma
    (ownColumnSigma H K u t) (fun i => colLoad H K u i-H.anchor s u) hsupport
  rw [hSig,hLC,← hmat] at hLocal
  have hMinor := hLocal.trans hOwn
  have hMinorT := (WrapTransport.response_transpose ((fibreMatrix H s u gamma).submatrix f f)
    (fibreColumnSigma H u t ∘ f) (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u))).symm.trans hMinor
  have hData := full_column_fibre_source H s u hs hu huc t ht
  have hQT : IsUnit (fibreMatrix H s u gamma)ᵀ.det := by rw [Matrix.det_transpose]; exact fibre_matrix_unit H s u hs hu huc gamma
  have hfT : IsUnit (((fibreMatrix H s u gamma)ᵀ).submatrix f f).det := by
    change IsUnit ((fibreMatrix H s u gamma).submatrix f f)ᵀ.det
    rw [Matrix.det_transpose]
    exact hf
  have hdisT : ∀ i j,(fibreRowCoord H t j-fibreColCoord H t i)*(fibreMatrix H s u gamma)ᵀ i j=
      fibreRow H u gamma j-fibreCol H u gamma i := by
    intro i j
    have he := fibre_displacement H s u t j i
    change _*(fibreMatrix H s u gamma) j i=_
    linear_combination -he
  have hm := single_restriction_moment (fibreMatrix H s u gamma)ᵀ hQT
    f E (fun _ => rfl) hfT (fibreColCoord H t) (fibreRowCoord H t) (fibreCol H u gamma) (fibreRow H u gamma)
    (fibreColumnSigma H u t) (WrapDeform.residue p (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t))
    (WrapDeform.residue p (H.anchor s u)) hdisT (fibre_column_sigma_displacement H u t htN)
    hData.1 hMinorT hData.2
  have hMemberMoment := local_moment_map (WrapDeform.residue p) D colK hDU hbK gamma
    (fun i => rowLoad H K u i-H.anchor s u) (fun i => colLoad H K u i-H.anchor s u)
  rw [hLR,hLC,← hmat] at hMemberMoment
  have hcol : colour H K=colK := funext (colour_embed H K)
  have hMem : (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) ⬝ᵥ
      ((fibreMatrix H s u gamma).submatrix f f)⁻¹ *ᵥ
      (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u))=sourceMoment H K s u gamma := by
    simpa only [sourceMoment,hcol,D] using hMemberMoment
  have hBoth : (fun i => fibreCol H u gamma i-WrapDeform.residue p (H.anchor s u)) ⬝ᵥ
      (fibreMatrix H s u gamma)⁻¹ *ᵥ (fun i => fibreRow H u gamma i-WrapDeform.residue p (H.anchor s u))=
      (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) ⬝ᵥ
      ((fibreMatrix H s u gamma).submatrix f f)⁻¹ *ᵥ (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u)) :=
    (WrapTransport.response_transpose (fibreMatrix H s u gamma)
      (fun i => fibreRow H u gamma i-WrapDeform.residue p (H.anchor s u))
      (fun i => fibreCol H u gamma i-WrapDeform.residue p (H.anchor s u))).trans
        (hm.trans (WrapTransport.response_transpose ((fibreMatrix H s u gamma).submatrix f f)
          (fun i => fibreRow H u gamma (f i)-WrapDeform.residue p (H.anchor s u))
          (fun i => fibreCol H u gamma (f i)-WrapDeform.residue p (H.anchor s u))).symm)
  have hEqual : H.moment s u gamma=sourceMoment H K s u gamma :=
    (full_fibre_moment H s u hs hu huc gamma).symm.trans (hBoth.trans hMem)
  have hw : weight H K s u gamma=H.weight s u gamma := by
    unfold weight WrapPrefixWindow.Setup.weight
    rw [← hEqual]
  rw [hw]
  exact H.weight_zero t ht s u hs hu huc

end SingleColumn


section SingleSupport
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

noncomputable def selectedPoints (Jr Jc : Finset (Fin d)) :=
  Jr.image (fun z => (Schur.surplusRow H z:ZMod p))∪Jc.image (fun y => (Schur.surplusCol H y:ZMod p))

/-- A singly edited selected colour either retains a nonzero actual
coupling kill or has zero new source weight. It never enters retained support. -/
theorem single_retained_excluded (K : Finset (Fin r)) (s u : GaussLoc p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p))) (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (Jr Jc : Finset (Fin d)) (hJr : ∀ z∈Jr,Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,Schur.surplusCol H y∈Icc H.t0 H.tv)
    (gamma : ZMod p) (hg : gamma∈WrapDamage.single K (fun i:Fin r => (i:ZMod p)) (selectedPoints H Jr Jc)) :
    gamma∉retained H K s u := by
  classical
  intro hret
  have hwr : weight H K s u gamma≠0 := (mem_filter.mp (mem_sdiff.mp hret).1).2
  have hnk := (mem_sdiff.mp hret).2
  have hsel := (mem_filter.mp hg).2.1
  have hmult := (mem_filter.mp hg).2.2
  obtain ⟨a,hA⟩ := Finset.card_eq_one.mp hmult
  have ha : a∈K ∧ (a:ZMod p)=gamma := mem_filter.mp (by rw [hA]; exact mem_singleton_self a)
  have honly : ∀ i∈K,(i:ZMod p)=gamma → i=a := by
    intro i hi hc
    have hm : i∈K.filter (fun j:Fin r => (j:ZMod p)=gamma) := mem_filter.mpr ⟨hi,hc⟩
    rw [hA] at hm
    exact mem_singleton.mp hm
  rcases mem_union.mp hsel with hr|hc
  · obtain ⟨z,hz,hzg⟩ := mem_image.mp hr
    have hcoupling : Schur.rowCoupling H K s u z=0 := by
      by_contra hn
      apply hnk
      apply mem_union_right
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,hn,by rw [hzg]; exact hwr⟩,hzg⟩
    have hw := single_row_weight H K s u hs hu huc (Schur.surplusRow H z) (hJr z hz)
      a ha.1 (ha.2.trans hzg.symm) (fun i hi hcol => honly i hi (hcol.trans hzg)) hcoupling
    exact hwr (by simpa only [hzg] using hw)
  · obtain ⟨y,hy,hyg⟩ := mem_image.mp hc
    have hcoupling : Schur.colCoupling H K s u y=0 := by
      by_contra hn
      apply hnk
      apply mem_union_left
      exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,hn⟩,hyg⟩
    have hw := single_column_weight H K s u hs hu huc (Schur.surplusCol H y) (hJc y hy)
      a ha.1 (ha.2.trans hyg.symm) (fun i hi hcol => honly i hi (hcol.trans hyg)) hcoupling
    exact hwr (by simpa only [hyg] using hw)


end SingleSupport

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixMember

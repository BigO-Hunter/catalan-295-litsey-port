module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixWindow
public import CatalanCore.Uniform.Content.UFSimple.WrapIntegral
public import CatalanCore.Uniform.Content.UFSimple.WrapDeformedFamily
public import CatalanCore.Uniform.Content.UFSimple.WrapFrameResidue
public import CatalanCore.Uniform.Content.UFMember.JKill
public import CatalanCore.Uniform.Content.UFMember.Wit

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixSchur

section Algebra
variable {R K ι κ P : Type*} [CommRing R] [IsDomain R] [Field K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Reuse the existing mixed cleared-reference identity with the ORIGINAL
uniformizer-scaled loads. No column-reference unit is needed. -/
theorem scaled_cross_direction (pi : R) (hpi : pi≠0)
    (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (x y LR LC sigmaR sigmaC : ι → R) (t Lt : R)
    (hdisp : ∀ i j,(y j-x i)*Q i j=pi*(LC j-LR i))
    (hrow : ∀ i,(y i-t)*sigmaR i=pi*(LC i-Lt))
    (hcol : ∀ i,(t-x i)*sigmaC i=pi*(Lt-LR i)) :
    (1-sigmaR ⬝ᵥ Q⁻¹ *ᵥ 1)*(Lt-LC ⬝ᵥ Q⁻¹ *ᵥ sigmaC)=
      (Lt-sigmaR ⬝ᵥ Q⁻¹ *ᵥ LR)*(1-(1:ι → R) ⬝ᵥ Q⁻¹ *ᵥ sigmaC) := by
  have he := WrapMixedReference.cross_direction Q hQ x y (pi • LR) (pi • LC) sigmaR sigmaC t (pi*Lt)
    (by intro i j; simpa only [Pi.smul_apply,smul_eq_mul,← mul_sub] using hdisp i j)
    (by intro i; simpa only [Pi.smul_apply,smul_eq_mul,← mul_sub] using hrow i)
    (by intro i; simpa only [Pi.smul_apply,smul_eq_mul,← mul_sub] using hcol i)
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul] at he
  apply mul_left_cancel₀ hpi
  linear_combination he

/-- A selected row source supplies the SAME column source by the cleared
identity; only its already-proved row reference unit is cancelled. -/
theorem column_source_of_row (pi aR aC bR bC direction F : R)
    (hR : IsUnit aR) (hc : aR*bC=bR*aC)
    (hr : bR=direction*aR+pi*(aR*F)) : bC=direction*aC+pi*(aC*F) := by
  apply mul_left_cancel₀ hR.ne_zero
  calc
    aR*bC=bR*aC := hc
    _=(direction*aR+pi*(aR*F))*aC := by rw [hr]
    _=aR*(direction*aC+pi*(aC*F)) := by ring

/-- Consume the EXISTING generic joint-block/wedge-kill Smith theorem,
then the EXISTING integral block determinant theorem. -/
theorem jblock_kill_content (phi : R →+* K) (pi : R) (hpi : Prime pi)
    (hker : ∀ x,phi x=0 ↔ pi∣x)
    (hlift : ∀ z : K,∃ r d : R,phi d≠0 ∧ phi r=phi d*z)
    (Q : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R) (D W : Matrix κ κ R)
    (hQ : IsUnit Q.det) (hSch : D-C*Q⁻¹*B=pi • W)
    (Jr Jc : Finset κ) (Hc : Matrix κ κ R)
    (hJ : ∀ z∈Jr,∀ y∈Jc,W z y=pi*Hc z y) (Ret : Finset P)
    (A : κ → P → K) (Bv : P → κ → K)
    (hcauchy : ∀ z∈Jr,∀ y∈Jc,phi (Hc z y)=∑ c∈Ret,A z c*Bv c y)
    (KillR KillC : Finset P) [DecidableEq P]
    (hKR : ∀ c∈KillR,∃ t:κ,∃ l:K,l≠0 ∧ ∀ z∈Jr,phi (W z t)=l*A z c)
    (hKC : ∀ c∈KillC,∃ t:κ,∃ l:K,l≠0 ∧ ∀ y∈Jc,phi (W t y)=l*Bv c y) :
    pi^(Fintype.card κ+WrapCount.gain (Jr.card+Jc.card-Fintype.card κ) (Ret\(KillR∪KillC)).card)∣
      (Matrix.fromBlocks Q B C D).det := by
  obtain ⟨T⟩ := exists_twoLevelData_of_jblock_kill phi hker hlift W Jr Jc Hc hJ Ret A Bv hcauchy KillR KillC hKR hKC
  simpa only [WrapCount.gain] using WrapIntegral.block_content phi pi hpi hker hlift Q B C D W hQ hSch _ _ T


/-- The existing mixed Schur displacement with normalized integral loads. -/
theorem normalized_displacement (pi : R) (Q : Matrix ι ι R) (hQ : IsUnit Q.det)
    (B : Matrix ι κ R) (C : Matrix κ ι R) (D : Matrix κ κ R)
    (xr xc LR LC : ι → R) (xx yy Lx Ly : κ → R)
    (hA : ∀ i j,(xc j-xr i)*Q i j=pi*(LC j-LR i))
    (hB : ∀ i y,(yy y-xr i)*B i y=pi*(Ly y-LR i))
    (hC : ∀ z i,(xc i-xx z)*C z i=pi*(LC i-Lx z))
    (hD : ∀ z y,(yy y-xx z)*D z y=pi*(Ly y-Lx z)) (z y : κ) :
    (yy y-xx z)*(D-C*Q⁻¹*B) z y=
      pi*((1-(fun i => C z i) ⬝ᵥ Q⁻¹ *ᵥ 1)*(Ly y-LC ⬝ᵥ Q⁻¹ *ᵥ (fun i => B i y))-
        (Lx z-(fun i => C z i) ⬝ᵥ Q⁻¹ *ᵥ LR)*(1-(1:ι → R) ⬝ᵥ Q⁻¹ *ᵥ (fun i => B i y))) := by
  have he := WrapDisplacement.mixed_cleared_schur_displacement Q Q⁻¹ B C D 1 1
    (by simpa using Matrix.mul_nonsing_inv Q hQ) (by simpa using Matrix.nonsing_inv_mul Q hQ)
    xr xc (pi • LR) (pi • LC) xx (pi • Lx) yy (pi • Ly)
    (by intro i j; simpa only [one_mul,Pi.smul_apply,smul_eq_mul,← mul_sub] using hA i j)
    (by intro i y; simpa only [one_mul,Pi.smul_apply,smul_eq_mul,← mul_sub] using hB i y)
    (by intro z i; simpa only [one_mul,Pi.smul_apply,smul_eq_mul,← mul_sub] using hC z i)
    (by intro z y; simpa only [one_mul,Pi.smul_apply,smul_eq_mul,← mul_sub] using hD z y) z y
  simp only [one_mul,Pi.smul_apply,smul_eq_mul] at he
  have hPC : (∑ j,(∑ k,pi*LC k*Q⁻¹ k j)*B j y)=pi*(LC ⬝ᵥ Q⁻¹ *ᵥ (fun i => B i y)) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [dotProduct,Matrix.vecMul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hPR : (∑ i,C z i*∑ k,Q⁻¹ i k*(pi*LR k))=pi*((fun i => C z i) ⬝ᵥ Q⁻¹ *ᵥ LR) := by
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hOne : (∑ j,(∑ k,Q⁻¹ k j)*B j y)=(1:ι → R) ⬝ᵥ Q⁻¹ *ᵥ (fun i => B i y) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [dotProduct,Matrix.vecMul,Pi.one_apply,one_mul]
  have hRow : (∑ i,C z i*∑ k,Q⁻¹ i k)=(fun i => C z i) ⬝ᵥ Q⁻¹ *ᵥ (1:ι → R) := by
    simp only [dotProduct,Matrix.mulVec,Pi.one_apply,mul_one]
  rw [hPC,hPR,hOne,hRow] at he
  change (yy y-xx z)*(D z y-(C*Q⁻¹*B) z y)=_
  rw [he]
  ring

/-- First-order integrality of a mixed Schur entry, using its actual
nonzero residue coordinate difference. -/
theorem schur_entry_divisible (phi : R →+* K) (pi delta S numerator : R)
    (hker : ∀ a,phi a=0 ↔ pi∣a) (hdelta : phi delta≠0)
    (hdisp : delta*S=pi*numerator) : pi∣S := by
  apply (hker S).mp
  have hp : phi pi=0 := (hker pi).mpr (dvd_refl _)
  have he := congrArg phi hdisp
  simp only [map_mul,hp,zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left hdelta

/-- A joint source gives the second integral order of the actual Schur
entry before reduction. -/
theorem schur_joint_factor (phi : R →+* K) (pi delta W aR aC bR bC direction F G : R)
    (hpi : pi≠0) (hdelta : IsUnit delta)
    (hdisp : delta*(pi*W)=pi*(aR*bC-bR*aC))
    (hR : bR=direction*aR+pi*(aR*F))
    (hC : bC=direction*aC+pi*(aC*G)) :
    ∃ J:R,W=pi*J ∧ phi delta*phi J=phi aR*phi aC*(phi G-phi F) := by
  have he : delta*W=pi*(aR*aC*(G-F)) := by
    apply mul_left_cancel₀ hpi
    linear_combination hdisp - pi*aC*hR + pi*aR*hC
  let J := Ring.inverse delta*(aR*aC*(G-F))
  have hw : W=pi*J := by
    apply mul_left_cancel₀ hdelta.ne_zero
    dsimp only [J]
    rw [he]
    calc pi*(aR*aC*(G-F))=pi*(delta*Ring.inverse delta)*(aR*aC*(G-F)) := by rw [Ring.mul_inverse_cancel _ hdelta,mul_one]
         _=delta*(pi*(Ring.inverse delta*(aR*aC*(G-F)))) := by ring
  refine ⟨J,hw,?_⟩
  have hj : delta*J=aR*aC*(G-F) := by
    dsimp only [J]
    rw [← mul_assoc,Ring.mul_inverse_cancel _ hdelta,one_mul]
  simpa only [map_mul,map_sub] using congrArg phi hj

theorem parameter_domain (phi : R →+* K) : IsDomain (WrapParameter.Extension phi) :=
  IsLocalization.isDomain_of_atPrime _ (WrapParameter.primeIdeal phi)


/-- Finite Cauchy divided-difference identity over the residue field. -/
theorem cauchy_difference (Ret : Finset P) (node : P → K) (weight : P → K)
    (x y : K) (hxy : y-x≠0) (hx : ∀ c∈Ret,node c-x≠0) (hy : ∀ c∈Ret,node c-y≠0) :
    ((∑ c∈Ret,weight c/(node c-y))-(∑ c∈Ret,weight c/(node c-x)))/(y-x)=
      ∑ c∈Ret,weight c/((node c-x)*(node c-y)) := by
  apply (div_eq_iff hxy).mpr
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  field_simp [hx c hc,hy c hc] <;> ring

/-- Outside column couplings of the same actual displacement supply
Cauchy-column kills, whether or not that colour has nonzero weight. -/
theorem column_kill_identity (phi : R →+* K) (pi delta W aR aC bR bC direction F : R)
    (hpi : pi≠0) (hp : phi pi=0) (hd : phi delta≠0)
    (hdisp : delta*(pi*W)=pi*(aR*bC-bR*aC))
    (hR : bR=direction*aR+pi*(aR*F)) :
    phi W=phi (bC-direction*aC)*(phi aR/phi delta) := by
  have he : delta*W=aR*(bC-direction*aC)-pi*(aR*aC*F) := by
    apply mul_left_cancel₀ hpi
    linear_combination hdisp - pi*aC*hR
  have hr := congrArg phi he
  simp only [map_mul,map_sub,hp,zero_mul,sub_zero] at hr
  simp only [map_sub,map_mul]
  field_simp [hd] <;> linear_combination hr

/-- Outside row couplings supply the opposite Cauchy kill. The source
weight is divided only for a retained, nonzero-weight colour. -/
theorem row_kill_identity (phi : R →+* K) (pi delta W aR aC bR bC direction G : R)
    (hpi : pi≠0) (hp : phi pi=0) (hd : phi delta≠0)
    (hdisp : delta*(pi*W)=pi*(aR*bC-bR*aC))
    (hC : bC=direction*aC+pi*(aC*G)) (weight : K) (hw : weight≠0) :
    phi W=(phi (bR-direction*aR)/weight)*(weight*phi aC/(-phi delta)) := by
  have he : delta*W= -(bR-direction*aR)*aC+pi*(aR*aC*G) := by
    apply mul_left_cancel₀ hpi
    linear_combination hdisp + pi*aR*hC
  have hr := congrArg phi he
  simp only [map_mul,map_add,map_neg,hp,zero_mul,add_zero] at hr
  field_simp [hw,hd]
  linear_combination hr


/-- The normalized joint source produces the exact Cauchy factorization
needed by the existing Smith theorem. -/
theorem joint_cauchy (phi : R →+* K) (pi delta W aR aC bR bC direction F G : R)
    (hpi : pi≠0) (hdelta : IsUnit delta)
    (hdisp : delta*(pi*W)=pi*(aR*bC-bR*aC))
    (hR : bR=direction*aR+pi*(aR*F)) (hC : bC=direction*aC+pi*(aC*G))
    (Ret : Finset P) (node weight : P → K) (offset x y : K)
    (hd : phi delta=y-x) (hxy : y-x≠0)
    (hx : ∀ c∈Ret,node c-x≠0) (hy : ∀ c∈Ret,node c-y≠0)
    (hF : phi F=offset+∑ c∈Ret,weight c/(node c-x))
    (hG : phi G=offset+∑ c∈Ret,weight c/(node c-y)) :
    ∃ J:R,W=pi*J ∧ phi J=∑ c∈Ret,(phi aR/(node c-x))*(weight c*phi aC/(node c-y)) := by
  obtain ⟨J,hJ,hr⟩ := schur_joint_factor phi pi delta W aR aC bR bC direction F G hpi hdelta hdisp hR hC
  have hdiff : phi G-phi F=(y-x)*(∑ c∈Ret,weight c/((node c-x)*(node c-y))) := by
    rw [hF,hG]
    have he := (div_eq_iff hxy).mp (cauchy_difference Ret node weight x y hxy hx hy)
    linear_combination he
  have hj : phi J=phi aR*phi aC*(∑ c∈Ret,weight c/((node c-x)*(node c-y))) := by
    apply mul_left_cancel₀ hxy
    rw [hd,hdiff] at hr
    linear_combination hr
  refine ⟨J,hJ,?_⟩
  rw [hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  field_simp [hx c hc,hy c hc] <;> ring

end Algebra

section Reindex
variable {R ι τ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

/-- Independent original row/column permutations preserve scalar
uniformizer divisibility; their determinant signs are units. -/
theorem dvd_det_reindex_iff (A : Matrix ι ι R) (er ec : τ ≃ ι) (a : R) :
    a∣(A.submatrix er ec).det ↔ a∣A.det := by
  have he : (A.submatrix er ec).det=((Equiv.Perm.sign (ec.symm.trans er):ℤ):R)*A.det := by
    simpa only [Matrix.reindex_apply,Equiv.symm_symm] using Matrix.det_reindex er.symm ec.symm A
  have hu : IsUnit (((Equiv.Perm.sign (ec.symm.trans er):ℤ):R)) :=
    (Equiv.Perm.sign (ec.symm.trans er)).isUnit.map (Int.castRingHom R)
  rw [he]
  exact hu.dvd_mul_left

end Reindex

variable (p : ℕ) [Fact p.Prime]

/-- Reuse the existing polynomial fraction lift and original local unit
criterion to lift every original Gauss residue. -/
theorem gauss_residue_surjective : Function.Surjective (res p) := by
  intro z
  obtain ⟨r,d,hd,hr⟩ := phiP_lift p z
  let ar : GaussLoc p := algebraMap (LocRing p)[X] (GaussLoc p) r
  let ad : GaussLoc p := algebraMap (LocRing p)[X] (GaussLoc p) d
  have hunit : IsUnit ad := isUnit_of_res_ne ad (by rw [res_algebraMap]; exact hd)
  refine ⟨ar*Ring.inverse ad,?_⟩
  rw [map_mul,res_inverse _ hunit]
  dsimp only [ar,ad]
  rw [res_algebraMap,res_algebraMap]
  rw [hr]
  simpa only [mul_comm ((phiP p) d) z] using mul_inv_cancel_right₀ hd z

noncomputable def parameter_lift := WrapParameterLift.quotient_lift (R:=GaussLoc p) (K:=RatFunc (ZMod p))
  (res p) (gauss_residue_surjective p)

noncomputable def parameter_prime := WrapParameterLift.uniformizer_prime (R:=GaussLoc p) (K:=RatFunc (ZMod p))
  (res p) (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)

/-- Original scalar descent after independently reordering both actual
axes. Generic pivots are never specialized or used as original units. -/
theorem original_gle_of_mixed_content {ι κ τ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]
    {Fr : Frame} {q o N : ℕ} (T : CatalanCore.Uniform.Content.Smith.TwoTermData Fr q o)
    (D : PoleData Fr p N) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (er ec : τ ≃ (ι ⊕ κ)) (k : ℕ)
    (hcontent : WrapDeform.uniformizer p^k∣((WrapDeformedFamily.matrix p Fr q o c xs ys).submatrix er ec).det) :
    GLE p (2*Fintype.card (ι ⊕ κ)-k) (FullN Fr c xs ys (Polynomial.X:ℚ[X])).det := by
  exact WrapDeformedFamily.original_gle p T D hqp hN hsq c xs ys hc hx hy k
    ((dvd_det_reindex_iff _ er ec _).mp hcontent)


section Actual
variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)
include H

noncomputable def extensionDomain :=
  parameter_domain (R:=GaussLoc p) (K:=RatFunc (ZMod p)) (res p)

attribute [local instance] extensionDomain

noncomputable def rowNode (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) : ℕ := Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i

noncomputable def colNode (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) : ℕ := Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i

noncomputable def surplusRow (z : Fin d) : ℕ :=
  r+2*(WrapPrefixGeometry.rowBorderEquiv (n:=n) (p:=p) H.er (Sum.inr z):ℕ)

noncomputable def surplusCol (y : Fin d) : ℕ :=
  r+2*(WrapPrefixGeometry.colBorderEquiv (n:=n) (Fact.out:p.Prime).pos shift H.ec (Sum.inr y):ℕ)+1

noncomputable def bBlock (u : GaussLoc p) : Matrix (Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) (Fin d) (WrapDeform.Extension p) :=
  Matrix.of fun i y => WrapDeformedEntry.entry p q o u (rowNode H i) (surplusCol H y)

noncomputable def cBlock (u : GaussLoc p) : Matrix (Fin d) (Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) (WrapDeform.Extension p) :=
  Matrix.of fun z i => WrapDeformedEntry.entry p q o u (surplusRow H z) (colNode H i)

noncomputable def dBlock (u : GaussLoc p) : Matrix (Fin d) (Fin d) (WrapDeform.Extension p) :=
  Matrix.of fun z y => WrapDeformedEntry.entry p q o u (surplusRow H z) (surplusCol H y)

noncomputable def full (s u : GaussLoc p) := Matrix.fromBlocks (H.core s u) (bBlock H u) (cBlock H u) (dBlock H u)

noncomputable def schur (s u : GaussLoc p) := dBlock H u-cBlock H u*(H.core s u)⁻¹*bBlock H u

noncomputable def columnSigma (u : GaussLoc p) (t : ℕ) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :=
  WrapDeformedEntry.entry p q o u (rowNode H i) t

noncomputable def rowReference (s u : GaussLoc p) (t : ℕ) := 1-H.sigma u t ⬝ᵥ (H.core s u)⁻¹ *ᵥ 1

noncomputable def colReference (s u : GaussLoc p) (t : ℕ) := 1-(1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p) ⬝ᵥ
  (H.core s u)⁻¹ *ᵥ columnSigma H u t

noncomputable def rowMoment (s u : GaussLoc p) (t : ℕ) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.sigma u t ⬝ᵥ (H.core s u)⁻¹ *ᵥ H.rowLoad u

noncomputable def colMoment (s u : GaussLoc p) (t : ℕ) :=
  WrapOwnCore.constants p u*WrapEntryRelation.load p q o t-H.colLoad u ⬝ᵥ (H.core s u)⁻¹ *ᵥ columnSigma H u t

theorem row_bound (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) : rowNode H i<N := by
  cases i with
  | inl i => exact H.common_bound i
  | inr i => exact H.row_bound i

theorem col_bound (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) : colNode H i<N := by
  cases i with
  | inl i => exact H.common_bound i
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
    rowReference H s u t*colMoment H s u t=rowMoment H s u t*colReference H s u t := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  apply scaled_cross_direction (WrapDeform.uniformizer p) (parameter_prime p).ne_zero
    (H.core s u) (H.core_unit s u hs hu huc)
    (fun i => (rowNode H i:WrapDeform.Extension p)) (fun i => (colNode H i:WrapDeform.Extension p))
    (H.rowLoad u) (H.colLoad u) (H.sigma u t) (columnSigma H u t)
    (t:WrapDeform.Extension p) (WrapOwnCore.constants p u*WrapEntryRelation.load p q o t)
  · exact WrapPrefixSource.core_displacement p q o N s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
      hsingle H.common_bound H.row_bound H.col_bound
  · intro i
    have he := WrapEntryRelation.commutator p q o N u hsingle t (colNode H i) ht (col_bound H i)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,WrapPrefixWindow.Setup.sigma,
      WrapPrefixWindow.Setup.rowLoad,WrapPrefixWindow.Setup.colLoad,columnSigma,rowNode,colNode] using he
  · intro i
    have he := WrapEntryRelation.commutator p q o N u hsingle (rowNode H i) t (row_bound H i) ht
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,WrapPrefixWindow.Setup.sigma,
      WrapPrefixWindow.Setup.rowLoad,WrapPrefixWindow.Setup.colLoad,columnSigma,rowNode,colNode] using he


/-- Reduction of the actual core and border preserves the already proved
own reference; all off-colour entries vanish by original displacement. -/
theorem row_reference_residue (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N) :
    WrapDeform.residue p (rowReference H s u t)=WrapDeform.residue p (H.ownReference s u t) := by
  classical
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  obtain ⟨E,hQE,hD,hE0,hE⟩ := WrapPrefixSource.actual_core_source p q o N s u
    (fun i:Fin r => (i:ℕ)) H.xs H.ys hsingle H.common_bound H.row_bound H.col_bound
    H.same_colour (H.core_unit s u hs hu huc)
  have hpi : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hm : (H.core s u).map (WrapDeform.residue p)=(H.own s u).map (WrapDeform.residue p) := by
    apply Matrix.ext
    intro i j
    have he := congrArg (fun M => WrapDeform.residue p (M i j)) hQE
    simpa only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero,
      Matrix.map_apply,WrapPrefixWindow.Setup.core,WrapPrefixWindow.Setup.own,WrapPrefixWindow.Setup.colour] using he
  obtain ⟨v,hv,hv0,hvr⟩ := WrapPrefixSource.actual_border_source p q o N t u (colNode H)
    hsingle ht (col_bound H)
  have hcol (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) : (colNode H i:ZMod p)=H.colour i := by
    cases i with
    | inl i => rfl
    | inr i => exact (H.same_colour i).symm
  have hb : ∀ i,WrapDeform.residue p (H.sigma u t i)=WrapDeform.residue p (H.ownSigma u t i) := by
    intro i
    have he := congrArg (fun f => WrapDeform.residue p (f i)) hv
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,hpi,zero_mul,add_zero] at he
    rw [hcol i] at he
    simpa only [WrapPrefixWindow.Setup.ownSigma,WrapPrefixWindow.Setup.sigma,colNode] using he
  have he := WrapPrefixType.reference_map_congr (WrapDeform.residue p) (H.core s u) (H.own s u)
    (H.core_unit s u hs hu huc) (H.own_unit s u hs hu huc) (H.sigma u t) (H.ownSigma u t) hm hb
  have ho : H.ownReference s u t=1-H.ownSigma u t ⬝ᵥ (H.own s u)⁻¹ *ᵥ 1 := by
    have hh := Matrix.dotProduct_mulVec (H.ownSigma u t) (H.own s u)⁻¹ (1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → WrapDeform.Extension p)
    simp only [dotProduct,Pi.one_apply,mul_one] at hh
    exact congrArg (fun a:WrapDeform.Extension p => 1-a) hh.symm
  rw [ho]
  exact he

/-- The selected original row reference is an integral unit. -/
theorem row_reference_unit (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    IsUnit (rowReference H s u t) := by
  obtain ⟨G,hG,hr,hne⟩ := H.own_source t ht s u hs hu huc
  apply WrapBalancedTest.unit_ne p
  change WrapDeform.residue p (rowReference H s u t)≠0
  rw [row_reference_residue H s u hs hu huc t (lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN)]
  exact hne

/-- Both actual axes use the same normalized Cauchy source, with no
extra column-source hypothesis. -/
theorem two_sided_source (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t∈Icc H.t0 H.tv) :
    ∃ F : WrapDeform.Extension p,
      rowMoment H s u t=H.anchor s u*rowReference H s u t+
        WrapDeform.uniformizer p*(rowReference H s u t*F) ∧
      colMoment H s u t=H.anchor s u*colReference H s u t+
        WrapDeform.uniformizer p*(colReference H s u t*F) ∧
      WrapDeform.residue p F=H.sourceOffset s u+
        ∑ gamma : ZMod p,H.weight s u gamma/
          (RatFunc.C (RatFunc.C gamma)-RatFunc.C (RatFunc.C (t:ZMod p))) := by
  obtain ⟨F,hF,hr⟩ := H.cauchy_source t ht s u hs hu huc
  refine ⟨F,hF,?_,hr⟩
  exact column_source_of_row _ _ _ _ _ _ _ (row_reference_unit H s u hs hu huc t ht)
    (shared_moments H s u hs hu huc t (lt_of_le_of_lt (mem_Icc.mp ht).2 H.htvN)) hF


/-- The mixed displacement of the actual residual Schur block. -/
theorem actual_displacement (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z y : Fin d) :
    ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))*schur H s u z y=
      WrapDeform.uniformizer p*(rowReference H s u (surplusRow H z)*colMoment H s u (surplusCol H y)-
        rowMoment H s u (surplusRow H z)*colReference H s u (surplusCol H y)) := by
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N H.hq0) H.hN
  apply normalized_displacement (WrapDeform.uniformizer p) (H.core s u) (H.core_unit s u hs hu huc)
    (bBlock H u) (cBlock H u) (dBlock H u)
    (fun i => (rowNode H i:WrapDeform.Extension p)) (fun i => (colNode H i:WrapDeform.Extension p))
    (H.rowLoad u) (H.colLoad u)
    (fun z => (surplusRow H z:WrapDeform.Extension p)) (fun y => (surplusCol H y:WrapDeform.Extension p))
    (fun z => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (surplusRow H z))
    (fun y => WrapOwnCore.constants p u*WrapEntryRelation.load p q o (surplusCol H y))
  · exact WrapPrefixSource.core_displacement p q o N s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
      hsingle H.common_bound H.row_bound H.col_bound
  · intro i y
    have he := WrapEntryRelation.commutator p q o N u hsingle (rowNode H i) (surplusCol H y)
      (row_bound H i) (surplus_col_bound H y)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,bBlock,Matrix.of_apply,
      WrapPrefixWindow.Setup.rowLoad,rowNode] using he
  · intro z i
    have he := WrapEntryRelation.commutator p q o N u hsingle (surplusRow H z) (colNode H i)
      (surplus_row_bound H z) (col_bound H i)
    simpa only [mul_sub,WrapEntryRelation.constants,WrapOwnCore.constants,cBlock,Matrix.of_apply,
      WrapPrefixWindow.Setup.colLoad,colNode] using he
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
    ∃ W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p),schur H s u=WrapDeform.uniformizer p • W := by
  classical
  have he : ∀ z y,∃ w:WrapDeform.Extension p,schur H s u z y=WrapDeform.uniformizer p*w := by
    intro z y
    have hd := difference_unit H (surplusRow H z) (surplusCol H y) (hdist z y)
    have hn : WrapDeform.residue p ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))≠0 :=
      (hd.map (WrapDeform.residue p)).ne_zero
    obtain ⟨w,hw⟩ := schur_entry_divisible (WrapDeform.residue p) (WrapDeform.uniformizer p) _ _ _
      (WrapDeform.residue_zero_iff p) hn (actual_displacement H s u hs hu huc z y)
    exact ⟨w,hw⟩
  choose W hW using he
  exact ⟨Matrix.of W,Matrix.ext (fun z y => hW z y)⟩


noncomputable def retained (s u : GaussLoc p) : Finset (ZMod p) := by
  classical
  exact univ.filter (fun gamma => H.weight s u gamma≠0)

noncomputable def residueNode (p : ℕ) [Fact p.Prime] : ZMod p →+* RatFunc (RatFunc (ZMod p)) :=
  (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp RatFunc.C

theorem retained_source (s u : GaussLoc p) (t : ℕ) :
    (∑ gamma : ZMod p,H.weight s u gamma/(residueNode p gamma-residueNode p (t:ZMod p)))=
      ∑ gamma∈retained H s u,H.weight s u gamma/(residueNode p gamma-residueNode p (t:ZMod p)) := by
  classical
  unfold retained
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro gamma _
  by_cases h : H.weight s u gamma=0
  · simp only [h,ne_eq,not_true_eq_false,↓reduceIte,zero_div]
  · simp only [h,ne_eq,not_false_eq_true,↓reduceIte]

/-- The actual joint entries have the second integral order and the
same finite Cauchy factors as the retained original source. -/
theorem joint_entries (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hz : surplusRow H z∈Icc H.t0 H.tv) (hy : surplusCol H y∈Icc H.t0 H.tv) :
    ∃ J:WrapDeform.Extension p,W z y=WrapDeform.uniformizer p*J ∧
      WrapDeform.residue p J=∑ gamma∈retained H s u,
        (WrapDeform.residue p (rowReference H s u (surplusRow H z))/
          (residueNode p gamma-residueNode p (surplusRow H z:ZMod p)))*
        (H.weight s u gamma*WrapDeform.residue p (colReference H s u (surplusCol H y))/
          (residueNode p gamma-residueNode p (surplusCol H y:ZMod p))) := by
  classical
  obtain ⟨F,hFR,hFC,hF⟩ := two_sided_source H s u hs hu huc (surplusRow H z) hz
  obtain ⟨G,hGR,hGC,hG⟩ := two_sided_source H s u hs hu huc (surplusCol H y) hy
  have hd := difference_unit H (surplusRow H z) (surplusCol H y) (hdist z y)
  have he := actual_displacement H s u hs hu huc z y
  rw [hW] at he
  change ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))*
    (WrapDeform.uniformizer p*W z y)=_ at he
  have hxRet : ∀ gamma∈retained H s u,residueNode p gamma-residueNode p (surplusRow H z:ZMod p)≠0 := by
    intro gamma hg heq
    have hgamma := (residueNode p).injective (sub_eq_zero.mp heq)
    have hw := (mem_filter.mp hg).2
    rw [hgamma,H.weight_zero _ hz s u hs hu huc] at hw
    exact hw rfl
  have hyRet : ∀ gamma∈retained H s u,residueNode p gamma-residueNode p (surplusCol H y:ZMod p)≠0 := by
    intro gamma hg heq
    have hgamma := (residueNode p).injective (sub_eq_zero.mp heq)
    have hw := (mem_filter.mp hg).2
    rw [hgamma,H.weight_zero _ hy s u hs hu huc] at hw
    exact hw rfl
  have hdelta : WrapDeform.residue p ((surplusCol H y:WrapDeform.Extension p)-(surplusRow H z:WrapDeform.Extension p))=
      residueNode p (surplusCol H y:ZMod p)-residueNode p (surplusRow H z:ZMod p) := by
    simp only [map_sub,map_natCast]
  have hxy : residueNode p (surplusCol H y:ZMod p)-residueNode p (surplusRow H z:ZMod p)≠0 := by
    intro heq
    exact (hdist z y) ((residueNode p).injective (sub_eq_zero.mp heq)).symm
  exact joint_cauchy (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H s u (surplusRow H z)) (colReference H s u (surplusCol H y))
    (rowMoment H s u (surplusRow H z)) (colMoment H s u (surplusCol H y)) (H.anchor s u) F G
    (parameter_prime p).ne_zero hd he hFR hGC (retained H s u) (residueNode p) (H.weight s u)
    (H.sourceOffset s u) _ _ hdelta hxy hxRet hyRet
    (hF.trans (congrArg (fun a => H.sourceOffset s u+a) (retained_source H s u _)))
    (hG.trans (congrArg (fun a => H.sourceOffset s u+a) (retained_source H s u _)))


noncomputable def rowCoupling (s u : GaussLoc p) (z : Fin d) :=
  WrapDeform.residue p (rowMoment H s u (surplusRow H z)-H.anchor s u*rowReference H s u (surplusRow H z))

noncomputable def colCoupling (s u : GaussLoc p) (y : Fin d) :=
  WrapDeform.residue p (colMoment H s u (surplusCol H y)-H.anchor s u*colReference H s u (surplusCol H y))

noncomputable def cauchyRow (s u : GaussLoc p) (z : Fin d) (gamma : ZMod p) :=
  WrapDeform.residue p (rowReference H s u (surplusRow H z))/
    (residueNode p gamma-residueNode p (surplusRow H z:ZMod p))

noncomputable def cauchyCol (s u : GaussLoc p) (gamma : ZMod p) (y : Fin d) :=
  H.weight s u gamma*WrapDeform.residue p (colReference H s u (surplusCol H y))/
    (residueNode p gamma-residueNode p (surplusCol H y:ZMod p))

/-- An actual outside column supplies the exact retained-column kill. -/
theorem actual_column_kill (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hz : surplusRow H z∈Icc H.t0 H.tv) :
    WrapDeform.residue p (W z y)=colCoupling H s u y*cauchyRow H s u z (surplusCol H y:ZMod p) := by
  obtain ⟨F,hFR,hFC,hF⟩ := two_sided_source H s u hs hu huc (surplusRow H z) hz
  have he := actual_displacement H s u hs hu huc z y
  rw [hW] at he
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hd := (difference_unit H _ _ (hdist z y)).map (WrapDeform.residue p)
  have hk := column_kill_identity (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H s u (surplusRow H z)) (colReference H s u (surplusCol H y))
    (rowMoment H s u (surplusRow H z)) (colMoment H s u (surplusCol H y)) (H.anchor s u) F
    (parameter_prime p).ne_zero hp hd.ne_zero he hFR
  simpa only [colCoupling,cauchyRow,map_sub,map_natCast] using hk

/-- An actual outside row supplies the opposite kill for each retained
nonzero source colour. -/
theorem actual_row_kill (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (W : Matrix (Fin d) (Fin d) (WrapDeform.Extension p))
    (hW : schur H s u=WrapDeform.uniformizer p • W)
    (z y : Fin d) (hy : surplusCol H y∈Icc H.t0 H.tv)
    (hw : H.weight s u (surplusRow H z:ZMod p)≠0) :
    WrapDeform.residue p (W z y)=
      (rowCoupling H s u z/H.weight s u (surplusRow H z:ZMod p))*
        cauchyCol H s u (surplusRow H z:ZMod p) y := by
  obtain ⟨G,hGR,hGC,hG⟩ := two_sided_source H s u hs hu huc (surplusCol H y) hy
  have he := actual_displacement H s u hs hu huc z y
  rw [hW] at he
  have hp : WrapDeform.residue p (WrapDeform.uniformizer p)=0 :=
    (WrapDeform.residue_zero_iff p _).mpr (dvd_refl _)
  have hd := (difference_unit H _ _ (hdist z y)).map (WrapDeform.residue p)
  have hk := row_kill_identity (WrapDeform.residue p) (WrapDeform.uniformizer p) _ (W z y)
    (rowReference H s u (surplusRow H z)) (colReference H s u (surplusCol H y))
    (rowMoment H s u (surplusRow H z)) (colMoment H s u (surplusCol H y)) (H.anchor s u) G
    (parameter_prime p).ne_zero hp hd.ne_zero he hGC _ hw
  simpa only [rowCoupling,cauchyCol,map_sub,map_natCast,neg_sub] using hk

noncomputable def activeColumns (s u : GaussLoc p) : Finset (Fin d) := by
  classical
  exact univ.filter (fun y => colCoupling H s u y≠0)
noncomputable def activeRows (s u : GaussLoc p) : Finset (Fin d) := by
  classical
  exact univ.filter (fun z => rowCoupling H s u z≠0 ∧ H.weight s u (surplusRow H z:ZMod p)≠0)
noncomputable def killedColumns (s u : GaussLoc p) :=
  (activeColumns H s u).image (fun y => (surplusCol H y:ZMod p))
noncomputable def killedRows (s u : GaussLoc p) :=
  (activeRows H s u).image (fun z => (surplusRow H z:ZMod p))

/-- Full original-prefix integral content, with the retained source and
all nonzero actual outside couplings supplied by the original matrix. -/
theorem actual_content (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u)
    (hdist : ∀ z y,(surplusRow H z:ZMod p)≠(surplusCol H y:ZMod p))
    (Jr Jc : Finset (Fin d)) (hJr : ∀ z∈Jr,surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,surplusCol H y∈Icc H.t0 H.tv) :
    WrapDeform.uniformizer p^(d+WrapCount.gain (Jr.card+Jc.card-d)
      (retained H s u\(killedColumns H s u∪killedRows H s u)).card)∣(full H s u).det := by
  classical
  obtain ⟨W,hW⟩ := exists_divided_schur H s u hs hu huc hdist
  have hJoint : ∀ z∈Jr,∀ y∈Jc,∃ J:WrapDeform.Extension p,W z y=WrapDeform.uniformizer p*J ∧
      WrapDeform.residue p J=∑ gamma∈retained H s u,cauchyRow H s u z gamma*cauchyCol H s u gamma y := by
    intro z hz y hy
    exact joint_entries H s u hs hu huc hdist W hW z y (hJr z hz) (hJc y hy)
  choose! Hc hJ hCauchy using hJoint
  have hKR : ∀ gamma∈killedColumns H s u,∃ y:Fin d,∃ l:RatFunc (RatFunc (ZMod p)),l≠0 ∧
      ∀ z∈Jr,WrapDeform.residue p (W z y)=l*cauchyRow H s u z gamma := by
    intro gamma hg
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hg
    exact ⟨y,colCoupling H s u y,(mem_filter.mp hy).2,
      fun z hz => actual_column_kill H s u hs hu huc hdist W hW z y (hJr z hz)⟩
  have hKC : ∀ gamma∈killedRows H s u,∃ z:Fin d,∃ l:RatFunc (RatFunc (ZMod p)),l≠0 ∧
      ∀ y∈Jc,WrapDeform.residue p (W z y)=l*cauchyCol H s u gamma y := by
    intro gamma hg
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hg
    have hz' := (mem_filter.mp hz).2
    exact ⟨z,rowCoupling H s u z/H.weight s u (surplusRow H z:ZMod p),div_ne_zero hz'.1 hz'.2,
      fun y hy => actual_row_kill H s u hs hu huc hdist W hW z y (hJc y hy) hz'.2⟩
  simpa only [Fintype.card_fin,full] using jblock_kill_content (WrapDeform.residue p)
    (WrapDeform.uniformizer p) (parameter_prime p) (WrapDeform.residue_zero_iff p) (parameter_lift p)
    (H.core s u) (bBlock H u) (cBlock H u) (dBlock H u) W (H.core_unit s u hs hu huc)
    hW Jr Jc (Matrix.of Hc) hJ (retained H s u) (cauchyRow H s u) (cauchyCol H s u)
    hCauchy (killedColumns H s u) (killedRows H s u) hKR hKC


/-- Exact independent reindexing of the ORIGINAL full matrix. Absorbed
cycles remain balanced nodes, and only original common nodes carry X. -/
theorem full_reindex (s u : GaussLoc p) :
    full H s u=(WrapFibreCore.core p q o s u (fun i:Fin r => (i:ℕ))
      (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)).submatrix
        (WrapPrefixGeometry.rowFullEquiv (Fin r) H.er)
        (WrapPrefixGeometry.colFullEquiv (Fin r) (Fact.out:p.Prime).pos shift H.ec) := by
  classical
  apply Matrix.ext
  intro i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j <;>
    simp only [full,WrapPrefixWindow.Setup.core,WrapFibreCore.core,bBlock,cBlock,dBlock,
      Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.submatrix_apply,Matrix.add_apply,Matrix.of_apply,Matrix.zero_apply,add_zero,
      WrapPrefixGeometry.rowFullEquiv,WrapPrefixGeometry.colFullEquiv,Equiv.trans_apply,
      Equiv.sumAssoc_apply_inl_inl,Equiv.sumAssoc_apply_inl_inr,Equiv.sumAssoc_apply_inr,Equiv.sumCongr_apply,Equiv.refl_apply,Equiv.sumCongr,Equiv.coe_fn_mk,Sum.map_inl,Sum.map_inr,
      Sum.elim_inl,Sum.elim_inr,rowNode,colNode,surplusRow,surplusCol,
      WrapPrefixWindow.Setup.xs,WrapPrefixWindow.Setup.ys,WrapPrefixCoreGeometry.xs,WrapPrefixCoreGeometry.ys]

/-- The original deformed-family interface is exactly the concrete
mixed prefix matrix at the original spectral parameter. -/
theorem full_original {Fr : Frame} :
    full H (algebraMap (LocRing p)[X] (GaussLoc p) Polynomial.X) (WrapOriginalEntry.normInv p Fr)=
      (WrapDeformedFamily.matrix p Fr q o (fun i:Fin r => (i:ℕ))
        (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)).submatrix
          (WrapPrefixGeometry.rowFullEquiv (Fin r) H.er)
          (WrapPrefixGeometry.colFullEquiv (Fin r) (Fact.out:p.Prime).pos shift H.ec) := by
  rw [full_reindex H]
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

end Actual

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixSchur

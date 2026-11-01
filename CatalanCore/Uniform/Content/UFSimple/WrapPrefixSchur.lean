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


noncomputable def retained (s u : GaussLoc p) : Finset (ZMod p) := by
  classical
  exact univ.filter (fun gamma => H.weight s u gamma≠0)

noncomputable def residueNode (p : ℕ) [Fact p.Prime] : ZMod p →+* RatFunc (RatFunc (ZMod p)) :=
  (RatFunc.C:RatFunc (ZMod p) →+* RatFunc (RatFunc (ZMod p))).comp RatFunc.C


noncomputable def rowCoupling (s u : GaussLoc p) (z : Fin d) :=
  WrapDeform.residue p (rowMoment H s u (surplusRow H z)-H.anchor s u*rowReference H s u (surplusRow H z))

noncomputable def colCoupling (s u : GaussLoc p) (y : Fin d) :=
  WrapDeform.residue p (colMoment H s u (surplusCol H y)-H.anchor s u*colReference H s u (surplusCol H y))


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


end Actual

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixSchur

module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed
public import CatalanCore.Uniform.Content.BankShared.Reindex

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.BankShared

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer

/-- Complement deletion indexes precisely the original retained common set. -/
def keepEquiv {r : ℕ} (S : Finset (Fin r)) : WrapKeep.Keep (univ\S) ≃ S where
  toFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  invFun i := ⟨i.1,by simpa only [mem_sdiff,mem_univ,true_and,not_not] using i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {p q o r n e b d shift N : ℕ} [Fact p.Prime]
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The explicit original prefix window price on any retained common
minor, including the empty retained set. -/
theorem window_commonMinor_gle {Fr : Frame} (T : TwoTermData Fr q o)
    (D : CatalanCore.Arith.Hybrid.Periodic.PoleData Fr p N)
    (hsq : ∀ t,1≤t → t<N → ¬p^2∣q*t-o)
    (Jr Jc : Finset (Fin d))
    (hinj : Function.Injective (Sum.elim
      (fun z => (WrapPrefixMember.Schur.surplusRow H z:ZMod p))
      (fun y => (WrapPrefixMember.Schur.surplusCol H y:ZMod p))))
    (hJr : ∀ z∈Jr,WrapPrefixMember.Schur.surplusRow H z∈Icc H.t0 H.tv)
    (hJc : ∀ y∈Jc,WrapPrefixMember.Schur.surplusCol H y∈Icc H.t0 H.tv)
    (S : Finset (Fin r)) :
    GLE p (2*(r+n*p+e)-(d+WrapCount.gain (Jr.card+Jc.card-d) (p-(H.tv+1-H.t0))))
      (commonMinorPoly Fr r (n*p+e) S) := by
  have hh := WrapPrefixClosed.window_price_gle H T D hsq Jr Jc hinj hJr hJc (univ\S)
  have he := CatalanCore.Uniform.Content.Wire.det_fullN_reindex Fr
    (fun a:S => (a.1:ℕ)) (WrapPrefixMember.common (univ\S))
    (keepEquiv S) (fun _ => rfl)
    (fun i:Fin (n*p+e) => r+2*(i:ℕ)) (fun i:Fin (n*p+e) => r+2*(i:ℕ)+1)
  rw [he] at hh
  exact hh

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer

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

theorem spectralLast_C3 (k : K) :
    spectralLast (K:=K) (Polynomial.C (Polynomial.C (Polynomial.C k)))=
      Polynomial.C (Polynomial.C (Polynomial.C k)) := by
  simp [spectralLast,Polynomial.Bivariate.swap_C]

theorem ringHom_ext3 {S : Type*} [Semiring S] {f g : K[X][X][X] →+* S}
    (h0 : ∀ k : K,f (Polynomial.C (Polynomial.C (Polynomial.C k)))=g (Polynomial.C (Polynomial.C (Polynomial.C k))))
    (h1 : f (Polynomial.C (Polynomial.C Polynomial.X))=g (Polynomial.C (Polynomial.C Polynomial.X)))
    (h2 : f (Polynomial.C Polynomial.X)=g (Polynomial.C Polynomial.X)) (h3 : f Polynomial.X=g Polynomial.X) :
    f=g := by
  have hCC : (f.comp Polynomial.C).comp Polynomial.C=(g.comp Polynomial.C).comp Polynomial.C :=
    Polynomial.ringHom_ext (fun k => h0 k) h1
  have hC : f.comp Polynomial.C=g.comp Polynomial.C :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun hCC a) h2
  exact Polynomial.ringHom_ext (fun b => RingHom.congr_fun hC b) h3

theorem spectralLast_spectralFirst :
    (spectralLast (K:=K)).comp (spectralFirst (K:=K))=RingHom.id _ := by
  apply ringHom_ext3
  · intro k
    simp only [RingHom.comp_apply,spectralFirst,poleCoefficients,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C,RingHom.id_apply,spectralLast_C3]
  · simp only [RingHom.comp_apply,spectralFirst,poleCoefficients,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C,Polynomial.eval₂_X,RingHom.id_apply,spectralLast_fractional_pole]
  · simp only [RingHom.comp_apply,spectralFirst,poleCoefficients,Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C,Polynomial.eval₂_X,RingHom.id_apply,spectralLast_integer_pole]
  · simp only [RingHom.comp_apply,spectralFirst,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,
      RingHom.id_apply,spectralLast_original_spectral]

theorem spectralFirst_injective : Function.Injective (spectralFirst (K:=K)) := by
  intro a b h
  have := congrArg (spectralLast (K:=K)) h
  simpa only [← RingHom.comp_apply,spectralLast_spectralFirst,RingHom.id_apply] using this

/-- Faithful embedding of spectral-outer cleared polynomials in the actual
two-parameter residue field: outer variable = original spectral `U`. -/
noncomputable def embedU : K[X][X][X] →+* RatFunc (RatFunc (RatFunc K)) :=
  (embedThree (K:=K)).comp (spectralFirst (K:=K))

theorem embedU_injective : Function.Injective (embedU (K:=K)) :=
  embedThree_injective.comp spectralFirst_injective

theorem embedThree_X : embedThree (K:=K) Polynomial.X=(RatFunc.X:RatFunc (RatFunc (RatFunc K))) := by
  simp [embedThree,RatFunc.algebraMap_X]

theorem embedThree_C (f : K[X][X]) :
    embedThree (K:=K) (Polynomial.C f)=RatFunc.C (WrapBivariate.embed f) := by
  simp [embedThree,RatFunc.algebraMap_C]

theorem embed_X : WrapBivariate.embed (K:=K) Polynomial.X=(RatFunc.X:RatFunc (RatFunc K)) := by
  simp [WrapBivariate.embed,RatFunc.algebraMap_X]

theorem embed_C (f : K[X]) :
    WrapBivariate.embed (K:=K) (Polynomial.C f)=RatFunc.C (algebraMap K[X] (RatFunc K) f) := by
  simp [WrapBivariate.embed,RatFunc.algebraMap_C]

theorem embedU_spectral :
    embedU (K:=K) Polynomial.X=RatFunc.C (RatFunc.C (RatFunc.X:RatFunc K)) := by
  simp [embedU,spectralFirst,embedThree_C,embed_C,RatFunc.algebraMap_X]

theorem embedU_integer :
    embedU (K:=K) (Polynomial.C Polynomial.X)=(RatFunc.X:RatFunc (RatFunc (RatFunc K))) := by
  simp [embedU,spectralFirst,poleCoefficients,embedThree_X]

theorem embedU_fractional :
    embedU (K:=K) (Polynomial.C (Polynomial.C Polynomial.X))=
      RatFunc.C (RatFunc.X:RatFunc (RatFunc K)) := by
  simp [embedU,spectralFirst,poleCoefficients,embedThree_C,embed_X]

theorem embedU_const (k : K) :
    embedU (K:=K) (Polynomial.C (Polynomial.C (Polynomial.C k)))=
      RatFunc.C (RatFunc.C (RatFunc.C k)) := by
  simp [embedU,spectralFirst,poleCoefficients,embedThree_C,embed_C,RatFunc.algebraMap_C]

end SpectralOuter


















section ClearedWorld
variable (p : ℕ) [Fact p.Prime]

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

/-- The two ORIGINAL pole parameters and the constants, as cleared
polynomials with the integer parameter outermost. -/
noncomputable def bconst (k : ZMod p) : (ZMod p)[X][X] := Polynomial.C (Polynomial.C k)
noncomputable def bInt : (ZMod p)[X][X] := Polynomial.X
noncomputable def bFrac : (ZMod p)[X][X] := Polynomial.C Polynomial.X

noncomputable def embedB : (ZMod p)[X][X] →+* TwoTermDeformation.Residue p :=
  (embedU (K:=ZMod p)).comp Polynomial.C

theorem embedB_const (k : ZMod p) :
    embedB p (bconst p k)=RatFunc.C (RatFunc.C (RatFunc.C k)) := by
  simp only [embedB,bconst,RingHom.comp_apply]
  exact embedU_const k

theorem embedB_nat (k : ℕ) : embedB p (bconst p (k:ZMod p))=(k:TwoTermDeformation.Residue p) := by
  rw [embedB_const]
  simp only [map_natCast]

theorem embedB_int : embedB p (bInt p)=(RatFunc.X:TwoTermDeformation.Residue p) := by
  simp only [embedB,bInt,RingHom.comp_apply]
  exact embedU_integer

theorem embedB_frac : embedB p (bFrac p)=RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p) := by
  simp only [embedB,bFrac,RingHom.comp_apply]
  exact embedU_fractional

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

theorem embedB_dfac (t : ℕ) :
    embedB p (dfac p q o t)=
      if p∣t then ((t/p:ℕ):TwoTermDeformation.Residue p)+RatFunc.X
      else if p∣q*t-o then ((((q*t-o)/p:ℕ):TwoTermDeformation.Residue p)+
        (q:TwoTermDeformation.Residue p)*RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) else 1 := by
  unfold dfac
  split_ifs <;> simp only [map_add,map_mul,map_one,embedB_nat,embedB_int,embedB_frac]

theorem embedB_injective : Function.Injective (embedB p) :=
  embedU_injective.comp Polynomial.C_injective

theorem dfac_ne (hq : (q:ZMod p)≠0) (t : ℕ) : dfac p q o t≠0 := by
  unfold dfac bconst bInt bFrac
  split_ifs with h1 h2
  · rw [add_comm]
    exact Polynomial.X_add_C_ne_zero _
  · rw [← Polynomial.C_mul,← Polynomial.C_add]
    intro hz
    have h0 := Polynomial.C_eq_zero.mp hz
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 1) h0
    simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_one,
      Polynomial.coeff_zero,mul_one,one_ne_zero,if_false,zero_add] at hc
    exact hq hc
  · exact one_ne_zero

theorem embedB_dfac_ne (hq : (q:ZMod p)≠0) (t : ℕ) : embedB p (dfac p q o t)≠0 := by
  intro hz
  exact dfac_ne p q o hq t (embedB_injective p (by simpa only [map_zero] using hz))

theorem cofactor_mul (M t : ℕ) (ht : t∈Icc 1 M) :
    cofactor p q o M t*dfac p q o t=clearing p q o M := by
  unfold cofactor clearing
  exact Finset.prod_erase_mul _ _ ht

/-- Clearing an ORIGINAL two-parameter increment residue: only elementary
original pole denominators are multiplied out. -/
theorem embedB_clearedDelta (M t : ℕ) (ht : t∈Icc 1 M) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    embedB p (clearedDelta p q o M t)=
      embedB p (clearing p q o M)*TwoTermDeformation.residue p (TwoTermDeformation.delta p q o t) := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    omega
  have hD := embedB_dfac_ne p q o hq t
  have hc := congrArg (embedB p) (cofactor_mul p q o M t ht)
  rw [map_mul] at hc
  rw [TwoTermDeformation.delta_residue p q o t hq0 hqp hle h2,← hc]
  unfold clearedDelta deltaWeight
  have hdf := embedB_dfac p q o t
  by_cases h1 : p∣t
  · have h2' := not_both p q o t hqp ho0 hoq hle h1
    have hdv : embedB p (dfac p q o t)=((t/p:ℕ):TwoTermDeformation.Residue p)+RatFunc.X := by
      rw [hdf,if_pos h1]
    rw [hdv] at hD ⊢
    simp only [if_pos h1,if_neg h2',map_mul,map_one,mul_zero,sub_zero,one_mul]
    field_simp
  · by_cases h3 : p∣q*t-o
    · have hdv : embedB p (dfac p q o t)=((((q*t-o)/p:ℕ):TwoTermDeformation.Residue p)+
          (q:TwoTermDeformation.Residue p)*RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) := by
        rw [hdf,if_neg h1,if_pos h3]
      rw [hdv] at hD ⊢
      simp only [if_neg h1,if_pos h3,map_mul,map_neg,embedB_nat,zero_sub]
      field_simp
    · simp only [if_neg h1,if_neg h3,map_mul,map_zero,zero_mul,mul_zero,sub_zero]

theorem load_terms (M a : ℕ) (haM : a≤M) (hM : M<p*p) (hq0 : 0<q) (hoq : o<q) (t : ℕ)
    (ht : t∈Icc 1 a) : t∈Icc 1 M ∧ o≤q*t ∧ ¬p^2∣t := by
  have h := mem_Icc.mp ht
  refine ⟨mem_Icc.mpr ⟨h.1,h.2.trans haM⟩,?_,Smith.not_sq_dvd_of_lt (by omega) (by omega)⟩
  have := Nat.le_mul_of_pos_right q h.1
  omega

theorem embedB_clearedLoad (M a : ℕ) (haM : a≤M) (hM : M<p*p) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) :
    embedB p (clearedLoad p q o M a)=
      embedB p (clearing p q o M)*TwoTermDeformation.residue p (TwoTermDeformation.load p q o a) := by
  unfold clearedLoad TwoTermDeformation.load
  rw [map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨h1,h2,h3⟩ := load_terms p q o M a haM hM hq0 hoq t ht
  exact embedB_clearedDelta p q o M t h1 hq0 hqp ho0 hoq h2 h3

theorem dsq_residue (t : ℕ) (hq0 : 0<q) (hqp : q<p) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    TwoTermDeformation.residue p (TwoTermDeformation.dsq p q o t)=
      (if p∣t then (1:TwoTermDeformation.Residue p)/(((t/p:ℕ):TwoTermDeformation.Residue p)+RatFunc.X)
        else 0)^2-
      (q:TwoTermDeformation.Residue p)^2*(if p∣q*t-o then
        (1:TwoTermDeformation.Residue p)/((((q*t-o)/p:ℕ):TwoTermDeformation.Residue p)+
          (q:TwoTermDeformation.Residue p)*RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) else 0)^2 := by
  rw [TwoTermDeformation.dsq]
  simp only [map_sub,map_mul,map_pow]
  rw [TwoTermDeformation.integer_residue p t h2,
    TwoTermDeformation.coefficient_residue,TwoTermDeformation.coefficient_residue,
    TwoTermDeformation.first_constant_residue,WrapSimplePole.res_nat]
  simp only [map_natCast,map_pow]
  rw [WrapSimplePole.argument_nat p q o t hle,
    WrapPoleResidue.normalized_nat p (q*t-o) q (WrapSimplePole.q_res_ne p q hq0 hqp)]
  by_cases hi : p∣t <;> by_cases hf : p∣q*t-o <;>
    simp only [hi,hf,↓reduceIte,map_zero,map_div₀,map_add,map_mul,map_one,map_natCast]

theorem embedB_clearedSquare (M t : ℕ) (ht : t∈Icc 1 M) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (hle : o≤q*t) (h2 : ¬p^2∣t) :
    embedB p (clearedSquare p q o M t)=
      embedB p (clearing p q o M)^2*TwoTermDeformation.residue p (TwoTermDeformation.dsq p q o t) := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    omega
  have hD := embedB_dfac_ne p q o hq t
  have hc := congrArg (embedB p) (cofactor_mul p q o M t ht)
  rw [map_mul] at hc
  rw [dsq_residue p q o t hq0 hqp hle h2,← hc]
  unfold clearedSquare squareWeight
  have hdf := embedB_dfac p q o t
  by_cases h1 : p∣t
  · have h2' := not_both p q o t hqp ho0 hoq hle h1
    have hdv : embedB p (dfac p q o t)=((t/p:ℕ):TwoTermDeformation.Residue p)+RatFunc.X := by
      rw [hdf,if_pos h1]
    rw [hdv] at hD ⊢
    simp only [if_pos h1,if_neg h2',map_mul,map_one,map_pow,one_mul]
    field_simp
    ring
  · by_cases h3 : p∣q*t-o
    · have hdv : embedB p (dfac p q o t)=((((q*t-o)/p:ℕ):TwoTermDeformation.Residue p)+
          (q:TwoTermDeformation.Residue p)*RatFunc.C (RatFunc.X:WrapPoleResidue.Residue p)) := by
        rw [hdf,if_neg h1,if_pos h3]
      rw [hdv] at hD ⊢
      simp only [if_neg h1,if_pos h3,map_mul,map_neg,map_pow,embedB_const,zero_pow two_ne_zero,
        zero_sub]
      simp only [map_pow,map_natCast]
      field_simp
    · simp only [if_neg h1,if_neg h3,map_mul,map_zero,zero_mul,mul_zero,sub_zero,
        zero_pow two_ne_zero]

/-- Evaluation of the integer parameter at a central point; the fractional
parameter stays generic. -/
noncomputable def evOuter (c : ZMod p) : (ZMod p)[X][X] →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp (Polynomial.evalRingHom (Polynomial.C c))

/-- Evaluation of the fractional parameter at a central point; the integer
parameter stays generic. -/
noncomputable def evInner (c : ZMod p) : (ZMod p)[X][X] →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp (Polynomial.mapRingHom (Polynomial.evalRingHom c))

theorem alg_ne (P : (ZMod p)[X]) (hP : P≠0) : algebraMap (ZMod p)[X] (RatFunc (ZMod p)) P≠0 := by
  intro hz
  exact hP (RatFunc.algebraMap_injective (ZMod p) (by simpa only [map_zero] using hz))

theorem evOuter_dfac (c : ZMod p) (t : ℕ) :
    evOuter p c (dfac p q o t)=algebraMap (ZMod p)[X] (RatFunc (ZMod p))
      (if p∣t then Polynomial.C (((t/p:ℕ):ZMod p)+c)
       else if p∣q*t-o then Polynomial.C ((((q*t-o)/p:ℕ):ZMod p))+Polynomial.C (q:ZMod p)*Polynomial.X
       else 1) := by
  unfold dfac
  split_ifs <;> simp [evOuter,bconst,bInt,bFrac]

theorem evInner_dfac (c : ZMod p) (t : ℕ) :
    evInner p c (dfac p q o t)=algebraMap (ZMod p)[X] (RatFunc (ZMod p))
      (if p∣t then Polynomial.C ((t/p:ℕ):ZMod p)+Polynomial.X
       else if p∣q*t-o then Polynomial.C ((((q*t-o)/p:ℕ):ZMod p)+(q:ZMod p)*c)
       else 1) := by
  unfold dfac
  split_ifs <;> simp [evInner,bconst,bInt,bFrac]

theorem nat_cast_eq_of_lt (a b : ℕ) (ha : a<p) (hb : b<p) (h : (a:ZMod p)=(b:ZMod p)) : a=b := by
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at this

/-- At the integer central point only the central original denominator vanishes. -/
theorem evOuter_dfac_eq_zero (M ts : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p)
    (hts : p∣ts) (htsM : ts∈Icc 1 M) (t : ℕ) (ht : t∈Icc 1 M) :
    evOuter p (-(((ts/p:ℕ):ZMod p))) (dfac p q o t)=0 ↔ t=ts := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    omega
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  have ht1 := mem_Icc.mp ht
  have hts1 := mem_Icc.mp htsM
  rw [evOuter_dfac]
  constructor
  · intro hz
    split_ifs at hz with h1 h2
    · have h0 := Polynomial.C_eq_zero.mp
        ((RatFunc.algebraMap_injective (ZMod p)) (by simpa only [map_zero] using hz))
      have he : ((t/p:ℕ):ZMod p)=((ts/p:ℕ):ZMod p) := by linear_combination h0
      have hlt : t/p<p := (Nat.div_lt_iff_lt_mul (Fact.out:p.Prime).pos).mpr (by omega)
      have hlts : ts/p<p := (Nat.div_lt_iff_lt_mul (Fact.out:p.Prime).pos).mpr (by omega)
      have hq' := nat_cast_eq_of_lt p _ _ hlt hlts he
      have := Nat.div_mul_cancel h1
      have := Nat.div_mul_cancel hts
      calc t=t/p*p := (Nat.div_mul_cancel h1).symm
        _=ts/p*p := by rw [hq']
        _=ts := Nat.div_mul_cancel hts
    · exfalso
      apply alg_ne p _ _ hz
      intro hP
      have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 1) hP
      simp only [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_C_mul,Polynomial.coeff_X_one,
        Polynomial.coeff_zero,mul_one,one_ne_zero,if_false,zero_add] at hc
      exact hq hc
    · exact absurd hz (by simp)
  · intro he
    subst he
    simp [if_pos hts]

/-- At the fractional central point only the central original denominator vanishes. -/
theorem evInner_dfac_eq_zero (M ts : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p)
    (ho0 : 0<o) (hoq : o<q) (htsI : ¬p∣ts) (hts : p∣q*ts-o) (htsM : ts∈Icc 1 M)
    (t : ℕ) (ht : t∈Icc 1 M) :
    evInner p (-((((q*ts-o)/p:ℕ):ZMod p))/(q:ZMod p)) (dfac p q o t)=0 ↔ t=ts := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    omega
  have ht1 := mem_Icc.mp ht
  have hts1 := mem_Icc.mp htsM
  rw [evInner_dfac]
  constructor
  · intro hz
    split_ifs at hz with h1 h2
    · exfalso
      apply alg_ne p _ _ hz
      rw [add_comm]
      exact Polynomial.X_add_C_ne_zero _
    · have h0 := Polynomial.C_eq_zero.mp
        ((RatFunc.algebraMap_injective (ZMod p)) (by simpa only [map_zero] using hz))
      have he : ((((q*t-o)/p:ℕ)):ZMod p)=((((q*ts-o)/p:ℕ)):ZMod p) := by
        field_simp at h0
        linear_combination h0
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
    · exact absurd hz (by simp)
  · intro he
    subst he
    simp only [if_neg htsI,if_pos hts]
    have : ((((q*t-o)/p:ℕ):ZMod p))+(q:ZMod p)*(-((((q*t-o)/p:ℕ):ZMod p))/(q:ZMod p))=0 := by
      field_simp
      ring
    rw [this]
    simp

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

/-- Exact cleared residue of an actual two-parameter entry at two
original nodes of one colour (divided original displacement). -/
theorem embedB_clearedEntry (M : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (u : GaussLoc p) (u0 : ZMod p)
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (a b : ℕ) (ha : a≤M) (hb : b≤M) (hcol : (a:ZMod p)=(b:ZMod p))
    (hab : ((b/p:ℕ):ZMod p)≠((a/p:ℕ):ZMod p)) :
    embedB p (clearedEntry p q o M u0 a b)=
      embedB p (clearing p q o M)*TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u a b) := by
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  have hd := congrArg (TwoTermDeformation.residue p)
    (TwoTermDeformation.divided_commutator p q o (M+1) u (by nlinarith) a b (by omega) (by omega) hcol)
  simp only [map_mul,map_sub,map_natCast,hu0] at hd
  have hne : ((b/p:ℕ):TwoTermDeformation.Residue p)-((a/p:ℕ):TwoTermDeformation.Residue p)≠0 := by
    intro hz
    apply hab
    have h := sub_eq_zero.mp hz
    have hinj : Function.Injective (fun k : ZMod p =>
        (RatFunc.C (RatFunc.C (RatFunc.C k)) : TwoTermDeformation.Residue p)) :=
      RatFunc.C_injective.comp (RatFunc.C_injective.comp RatFunc.C_injective)
    apply hinj
    simpa only [map_natCast] using h
  unfold clearedEntry
  rw [map_mul,map_sub,embedB_clearedLoad p q o M b hb hMp hq0 hqp ho0 hoq,
    embedB_clearedLoad p q o M a ha hMp hq0 hqp ho0 hoq,embedB_const]
  simp only [map_div₀,map_sub,map_natCast]
  have hE : TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u a b)=
      (((b/p:ℕ):TwoTermDeformation.Residue p)-((a/p:ℕ):TwoTermDeformation.Residue p))⁻¹*
        (RatFunc.C (RatFunc.C (RatFunc.C u0))*(TwoTermDeformation.residue p (TwoTermDeformation.load p q o b)-
          TwoTermDeformation.residue p (TwoTermDeformation.load p q o a))) := by
    rw [← hd,← mul_assoc,rational_inv_mul_cancel _ hne,one_mul]
  rw [rational_div_eq_mul_inv,hE]
  ring

noncomputable def clearedDiag (M : ℕ) (u0 : ZMod p) (a : ℕ) : (ZMod p)[X][X] :=
  -(bconst p u0*∑ t∈Icc 1 a,clearedSquare p q o M t)

theorem embedB_clearedDiag (M : ℕ) (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (u : GaussLoc p) (u0 : ZMod p)
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (a : ℕ) (ha : a≤M) :
    embedB p (clearedDiag p q o M u0 a)=
      embedB p (clearing p q o M)^2*TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u a a) := by
  have hMp : M<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left M hq0) hM
  unfold clearedDiag TwoTermDeformation.entry
  rw [if_pos rfl]
  have hc : TwoTermDeformation.coefficient p (WrapOwnCore.constants p u)=TwoTermDeformation.constants p u := rfl
  rw [hc]
  simp only [map_neg,map_mul,map_sum,hu0,embedB_const,Finset.mul_sum,mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨h1,h2,h3⟩ := load_terms p q o M a ha hMp hq0 hoq t ht
  rw [embedB_clearedSquare p q o M t h1 hq0 hqp ho0 hoq h2 h3]
  ring

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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

/-- The faithful spectral-outer embedding, built from the cleared
coefficient embedding with the default polynomial structure. -/
noncomputable def embedP : (ZMod p)[X][X][X] →+* TwoTermDeformation.Residue p :=
  Polynomial.eval₂RingHom (embedB p) (RatFunc.C (RatFunc.C (RatFunc.X:RatFunc (ZMod p))))

theorem embedP_eq (f : (ZMod p)[X][X][X]) : embedP p f=embedU (K:=ZMod p) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add,map_add,hf,hg]
  | monomial m b =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [embedP,map_mul,map_pow,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
      Polynomial.eval₂_X,embedB,RingHom.comp_apply,embedU_spectral]

theorem embedP_injective : Function.Injective (embedP p) := by
  intro a b h
  apply embedU_injective (K:=ZMod p)
  rw [← embedP_eq,← embedP_eq,h]

theorem embedP_X : embedP p Polynomial.X=RatFunc.C (RatFunc.C (RatFunc.X:RatFunc (ZMod p))) := by
  simp [embedP]

/-- Determinants commute with evaluation of a cleared spectral polynomial
system; stated generically so no concrete instance unfolding is needed. -/
theorem eval₂_det {B K m : Type*} [CommRing B] [CommRing K] [Fintype m] [DecidableEq m]
    (ι : B →+* K) (U : K) (C : Matrix m m B[X]) :
    Polynomial.eval₂RingHom ι U C.det=(C.map (Polynomial.eval₂RingHom ι U)).det :=
  RingHom.map_det _ _

variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)

/-- Bordered row nodes of an actual fibre: balanced rows, then the zone. -/
def bordRow (i : Fin (n+1)) : ℕ := if h : (i:ℕ)<n then xr ⟨i,h⟩ else z

/-- The ORIGINAL two-parameter bordered fibre system: common block with
the original spectral diagonal, balanced columns, and the direction
column (`load` = the cleared moment numerator, otherwise the reference). -/
noncomputable def ringSystem (s u : GaussLoc p) (load : Bool) :
    Matrix (Fin k ⊕ Fin (n+1)) (Fin k ⊕ Fin (n+1)) (TwoTermDeformation.Ring p) :=
  Matrix.fromBlocks
    (Matrix.of fun i j => TwoTermDeformation.entry p q o u (cn i) (cn j)+
      if i=j then TwoTermDeformation.coefficient p (WrapOwnCore.constants p s) else 0)
    (Matrix.of fun i j => if h : (j:ℕ)<n then TwoTermDeformation.entry p q o u (cn i) (yc ⟨j,h⟩)
      else if load then TwoTermDeformation.constants p u*TwoTermDeformation.load p q o (cn i) else 1)
    (Matrix.of fun i j => TwoTermDeformation.entry p q o u (bordRow xr z i) (cn j))
    (Matrix.of fun i j => if h : (j:ℕ)<n then TwoTermDeformation.entry p q o u (bordRow xr z i) (yc ⟨j,h⟩)
      else if load then TwoTermDeformation.constants p u*TwoTermDeformation.load p q o (bordRow xr z i) else 1)

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

/-- Row and column scalings relating the cleared system to the residues
of the ORIGINAL bordered system. -/
noncomputable def rowScale (Δ : TwoTermDeformation.Residue p) : Fin k ⊕ Fin (n+1) → TwoTermDeformation.Residue p :=
  Sum.elim (fun _ => Δ^2) (fun _ => Δ)
noncomputable def colScale (Δ : TwoTermDeformation.Residue p) (load : Bool) :
    Fin k ⊕ Fin (n+1) → TwoTermDeformation.Residue p :=
  Sum.elim (fun _ => 1) (fun j => if (j:ℕ)<n then 1 else if load then 1 else Δ⁻¹)

theorem embedU_clearedSystem {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (s u : GaussLoc p) (u0 : ZMod p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (load : Bool) (i j : Fin k ⊕ Fin (n+1)) :
    embedP p (clearedSystem p q o cn xr yc z M u0 load i j)=
      rowScale (n:=n) (embedB p (clearing p q o M)) i*
        TwoTermDeformation.residue p (ringSystem p q o cn xr yc z s u load i j)*
        colScale (n:=n) (embedB p (clearing p q o M)) load j := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd H.hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    have := H.hqp
    omega
  have hcl : clearing p q o M≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => dfac_ne p q o hq t)
  have hΔ : embedB p (clearing p q o M)≠0 := fun h0 =>
    hcl (embedB_injective p (by simpa only [map_zero] using h0))
  have hC (b : (ZMod p)[X][X]) : embedP p (Polynomial.C b)=embedB p b := by
    simp only [embedP,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
  have hU : TwoTermDeformation.residue p (TwoTermDeformation.coefficient p (WrapOwnCore.constants p s))=
      embedP p Polynomial.X := by
    rw [TwoTermDeformation.coefficient_residue,TwoTermDeformation.first_constant_residue,hs,embedP_X]
  have hLoad (a : ℕ) (ha : a≤M) : embedB p (clearedLoadRow p q o M u0 a)=
      embedB p (clearing p q o M)*TwoTermDeformation.residue p
        (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o a) := by
    unfold clearedLoadRow
    rw [map_mul,embedB_const,embedB_clearedLoad p q o M a ha
      (lt_of_le_of_lt (Nat.le_mul_of_pos_left M H.hq0) H.hM) H.hq0 H.hqp H.ho0 H.hoq,map_mul,hu0]
    ring
  have hEnt (a b : ℕ) (ha : a≤M) (hb : b≤M) (hcol : (a:ZMod p)=(b:ZMod p))
      (hab : ((b/p:ℕ):ZMod p)≠((a/p:ℕ):ZMod p)) :
      embedB p (clearedEntry p q o M u0 a b)=
        embedB p (clearing p q o M)*TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u a b) :=
    embedB_clearedEntry p q o M H.hM H.hq0 H.hqp H.ho0 H.hoq u u0 hu0 a b ha hb hcol hab
  rcases i with i|i <;> rcases j with j|j
  · simp only [clearedSystem,spectralSystem,ringSystem,Matrix.fromBlocks_apply₁₁,Matrix.add_apply,
      Matrix.smul_apply,Matrix.map_apply,Matrix.of_apply,clearedA,rowScale,colScale,Sum.elim_inl,mul_one]
    by_cases hij : i=j
    · subst hij
      simp only [Matrix.one_apply_eq,smul_eq_mul,mul_one,if_true,map_add,map_mul,map_pow,hC,hU]
      rw [embedB_clearedDiag p q o M H.hM H.hq0 H.hqp H.ho0 H.hoq u u0 hu0 _ (H.hcn i)]
      ring
    · simp only [Matrix.one_apply_ne hij,smul_eq_mul,mul_zero,zero_add,if_neg hij,add_zero,map_mul,hC]
      rw [hEnt _ _ (H.hcn i) (H.hcn j) ((H.ccn i).trans (H.ccn j).symm) (H.qcc i j hij)]
      ring
  · simp only [clearedSystem,spectralSystem,ringSystem,Matrix.fromBlocks_apply₁₂,
      Matrix.map_apply,Matrix.of_apply,clearedB,rowScale,colScale,Sum.elim_inl,Sum.elim_inr]
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
  · simp only [clearedSystem,spectralSystem,ringSystem,Matrix.fromBlocks_apply₂₁,
      Matrix.map_apply,Matrix.of_apply,clearedE,rowScale,colScale,Sum.elim_inl,Sum.elim_inr,mul_one,hC]
    rw [hEnt _ _ (H.bord_le i) (H.hcn j) ((H.bord_colour i).trans (H.ccn j).symm) (H.qbc i j)]
  · simp only [clearedSystem,spectralSystem,ringSystem,Matrix.fromBlocks_apply₂₂,
      Matrix.map_apply,Matrix.of_apply,clearedD,rowScale,colScale,Sum.elim_inr]
    by_cases hj : (j:ℕ)<n
    · simp only [dif_pos hj,if_pos hj,mul_one,hC]
      rw [hEnt _ _ (H.bord_le i) (H.hyc _) ((H.bord_colour i).trans (H.cyc _).symm) (H.qbb i _)]
    · simp only [dif_neg hj,if_neg hj]
      cases load
      · simp only [Bool.false_eq_true,↓reduceIte,map_one,mul_one,hC]
        field_simp
      · simp only [↓reduceIte,mul_one,hC]
        rw [hLoad _ (H.bord_le i)]

theorem det_scaled {R m : Type*} [CommRing R] [Fintype m] [DecidableEq m] (r c : m → R) (A : Matrix m m R) :
    (Matrix.of fun i j => r i*A i j*c j).det=(∏ i,r i)*(∏ j,c j)*A.det := by
  have h1 : (Matrix.of fun i j => r i*A i j*c j)=Matrix.of fun i j => c j*(Matrix.of fun i j => r i*A i j) i j := by
    ext i j; simp only [Matrix.of_apply]; ring
  rw [h1,Matrix.det_mul_row,Matrix.det_mul_column]
  ring

/-- The cleared determinant is the residue of the ORIGINAL bordered
determinant times explicit powers of the original clearing factor. -/
theorem embedU_clearedSystem_det {M : ℕ} (H : FibreHyp p q o cn xr yc z M) (s u : GaussLoc p) (u0 : ZMod p)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (load : Bool) :
    embedP p (clearedSystem p q o cn xr yc z M u0 load).det=
      embedB p (clearing p q o M)^(2*k+n)*(if load then embedB p (clearing p q o M) else 1)*
        TwoTermDeformation.residue p (ringSystem p q o cn xr yc z s u load).det := by
  have hq : (q:ZMod p)≠0 := by
    intro hz
    have := Nat.le_of_dvd H.hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz)
    have := H.hqp
    omega
  have hcl : clearing p q o M≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => dfac_ne p q o hq t)
  have hΔ : embedB p (clearing p q o M)≠0 := fun h0 =>
    hcl (embedB_injective p (by simpa only [map_zero] using h0))
  rw [RingHom.map_det (TwoTermDeformation.residue p)]
  have h1 : embedP p (clearedSystem p q o cn xr yc z M u0 load).det=
      ((embedP p).mapMatrix (clearedSystem p q o cn xr yc z M u0 load)).det :=
    eval₂_det (embedB p) _ _
  rw [h1]
  have he : (embedP p).mapMatrix (clearedSystem p q o cn xr yc z M u0 load)=
      Matrix.of fun i j => rowScale (n:=n) (embedB p (clearing p q o M)) i*
        ((TwoTermDeformation.residue p).mapMatrix (ringSystem p q o cn xr yc z s u load)) i j*
        colScale (n:=n) (embedB p (clearing p q o M)) load j := by
    ext i j
    exact embedU_clearedSystem H s u u0 hs hu0 load i j
  rw [he,det_scaled]
  congr 1
  simp only [rowScale,colScale,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Finset.prod_const_one,one_mul,Fin.prod_univ_castSucc,
    Fin.coe_castSucc,Fin.is_lt,↓reduceIte,Fin.val_last,lt_irrefl]
  cases load
  · simp only [Bool.false_eq_true,↓reduceIte,mul_one]
    simp only [one_pow,one_mul]
    field_simp
    ring
  · simp only [↓reduceIte,mul_one,one_pow,one_mul]
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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

/-- The common nonzero central factor of the evaluated cleared systems. -/
noncomputable def centralWeight (ev : (ZMod p)[X][X] →+* RatFunc (ZMod p)) (u0 : ZMod p) (M ts : ℕ) :
    RatFunc (ZMod p) :=
  algebraMap (ZMod p) (RatFunc (ZMod p)) u0*ev (deltaWeight p q o ts)*ev (cofactor p q o M ts)

/-- Two cleared adjacent fibre systems whose central evaluations separate
have distinct ORIGINAL residue directions (cross-multiplied, no pivot). -/
theorem residue_cross_ne {M n k1 k2 : ℕ}
    {cn1 : Fin k1 → ℕ} {xr1 yc1 : Fin n → ℕ} {z1 : ℕ}
    {cn2 : Fin k2 → ℕ} {xr2 yc2 : Fin n → ℕ} {z2 : ℕ}
    (H1 : FibreHyp p q o cn1 xr1 yc1 z1 M) (H2 : FibreHyp p q o cn2 xr2 yc2 z2 M)
    (s u : GaussLoc p) (u0 : ZMod p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (ev : (ZMod p)[X][X] →+* RatFunc (ZMod p)) (ts : ℕ) (htsM : ts∈Icc 1 M)
    (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,ev (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k) (cut1 cut2 : ℕ)
    (hrow1 : ∀ i,ts≤bordRow xr1 z1 i ↔ cut1≤bordRow xr1 z1 i/p) (hcol1 : ∀ c,ts≤yc1 c ↔ cut1≤yc1 c/p)
    (hq1 : ∀ i c,((yc1 c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr1 z1 i/p:ℕ):RatFunc (ZMod p)))
    (hrow2 : ∀ i,ts≤bordRow xr2 z2 i ↔ cut2≤bordRow xr2 z2 i/p) (hcol2 : ∀ c,ts≤yc2 c ↔ cut2≤yc2 c/p)
    (hq2 : ∀ i c,((yc2 c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr2 z2 i/p:ℕ):RatFunc (ZMod p)))
    (hne : (scaledStepLoad (centralWeight p q o ev u0 M ts) cut1 (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p)).det*
        (scaledStep (centralWeight p q o ev u0 M ts) cut2 (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p)).det≠
      (scaledStepLoad (centralWeight p q o ev u0 M ts) cut2 (fun i => bordRow xr2 z2 i/p) (fun c => yc2 c/p)).det*
        (scaledStep (centralWeight p q o ev u0 M ts) cut1 (fun i => bordRow xr1 z1 i/p) (fun c => yc1 c/p)).det) :
    TwoTermDeformation.residue p ((ringSystem p q o cn1 xr1 yc1 z1 s u true).det*
      (ringSystem p q o cn2 xr2 yc2 z2 s u false).det-
      (ringSystem p q o cn2 xr2 yc2 z2 s u true).det*(ringSystem p q o cn1 xr1 yc1 z1 s u false).det)≠0 := by
  intro hres
  have hq : (q:ZMod p)≠0 := by
    intro hz0
    have := Nat.le_of_dvd H1.hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz0)
    have := H1.hqp
    omega
  have hcl : clearing p q o M≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun t _ => dfac_ne p q o hq t)
  have hΔ : embedB p (clearing p q o M)≠0 := fun h0 =>
    hcl (embedB_injective p (by simpa only [map_zero] using h0))
  -- evaluated D-blocks
  have hD (load : Bool) {kk : ℕ} {xr yc : Fin n → ℕ} {zz : ℕ} (cut : ℕ)
      (hr : ∀ i,ts≤bordRow xr zz i ↔ cut≤bordRow xr zz i/p) (hc : ∀ c,ts≤yc c ↔ cut≤yc c/p)
      (hqq : ∀ i c,((yc c/p:ℕ):RatFunc (ZMod p))≠((bordRow xr zz i/p:ℕ):RatFunc (ZMod p))) :
      ev (clearedD p q o xr yc zz M u0 load).det=
        ((if load then scaledStepLoad else scaledStep)
          (centralWeight p q o ev u0 M ts) cut
          (fun i => bordRow xr zz i/p) (fun c => yc c/p)).det := by
    rw [RingHom.map_det]
    exact congrArg Matrix.det (ev_clearedD (q:=q) (o:=o) ev M ts htsM hz hev u0 cut hr hc hqq load)
  have hbr : (clearedD p q o xr1 yc1 z1 M u0 true).det*(clearedD p q o xr2 yc2 z2 M u0 false).det≠
      (clearedD p q o xr2 yc2 z2 M u0 true).det*(clearedD p q o xr1 yc1 z1 M u0 false).det := by
    intro h
    apply hne
    have h' := congrArg ev h
    simp only [map_mul] at h'
    rw [hD true (kk:=k1) cut1 hrow1 hcol1 hq1,hD false (kk:=k2) cut2 hrow2 hcol2 hq2,
      hD true (kk:=k2) cut2 hrow2 hcol2 hq2,hD false (kk:=k1) cut1 hrow1 hcol1 hq1] at h'
    simpa only [↓reduceIte,Bool.false_eq_true] using h'
  obtain ⟨dAN,cAN⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn1 M u0)
    (clearedB p q o cn1 yc1 M u0 true) (clearedE p q o cn1 xr1 z1 M u0) (clearedD p q o xr1 yc1 z1 M u0 true)
  obtain ⟨dAD,cAD⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn1 M u0)
    (clearedB p q o cn1 yc1 M u0 false) (clearedE p q o cn1 xr1 z1 M u0) (clearedD p q o xr1 yc1 z1 M u0 false)
  obtain ⟨dBN,cBN⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn2 M u0)
    (clearedB p q o cn2 yc2 M u0 true) (clearedE p q o cn2 xr2 z2 M u0) (clearedD p q o xr2 yc2 z2 M u0 true)
  obtain ⟨dBD,cBD⟩ := spectral_top_domain (clearing p q o M^2) (clearedA p q o cn2 M u0)
    (clearedB p q o cn2 yc2 M u0 false) (clearedE p q o cn2 xr2 z2 M u0) (clearedD p q o xr2 yc2 z2 M u0 false)
  simp only [Fintype.card_fin] at dAN cAN dAD cAD dBN cBN dBD cBD
  have hP := cross_ne_of_top k1 k2 _ _ _ _ dAN dAD dBN dBD (by
    rw [cAN,cAD,cBN,cBD]
    intro h
    apply hbr
    have hc2 : (clearing p q o M^2)^k1*(clearing p q o M^2)^k2≠0 :=
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hcl)) (pow_ne_zero _ (pow_ne_zero _ hcl))
    apply mul_left_cancel₀ hc2
    linear_combination h)
  apply hP
  apply embedP_injective p
  simp only [map_mul]
  change embedP p (clearedSystem p q o cn1 xr1 yc1 z1 M u0 true).det*
      embedP p (clearedSystem p q o cn2 xr2 yc2 z2 M u0 false).det=
    embedP p (clearedSystem p q o cn2 xr2 yc2 z2 M u0 true).det*
      embedP p (clearedSystem p q o cn1 xr1 yc1 z1 M u0 false).det
  rw [embedU_clearedSystem_det H1 s u u0 hs hu0,embedU_clearedSystem_det H2 s u u0 hs hu0,
    embedU_clearedSystem_det H2 s u u0 hs hu0,embedU_clearedSystem_det H1 s u u0 hs hu0]
  simp only [↓reduceIte,Bool.false_eq_true,mul_one]
  have h0 : TwoTermDeformation.residue p (ringSystem p q o cn1 xr1 yc1 z1 s u true).det*
      TwoTermDeformation.residue p (ringSystem p q o cn2 xr2 yc2 z2 s u false).det=
      TwoTermDeformation.residue p (ringSystem p q o cn2 xr2 yc2 z2 s u true).det*
      TwoTermDeformation.residue p (ringSystem p q o cn1 xr1 yc1 z1 s u false).det := by
    have h := hres
    simp only [map_sub,map_mul] at h
    exact sub_eq_zero.mp h
  linear_combination (embedB p (clearing p q o M)^(2*k1+n)*embedB p (clearing p q o M)*
    embedB p (clearing p q o M)^(2*k2+n))*h0

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

/-- Section 8.3 at the ORIGINAL two-parameter fibre level, for any central
evaluation killing exactly the chosen original pole. -/
theorem profile_separation_ev (γ1 k1 η1 γ2 k2 η2 n M ts cut1 cut2 : ℕ) (s u : GaussLoc p) (u0 : ZMod p)
    (hγ1 : γ1<p) (hγ2 : γ2<p) (hη1 : η1≤1) (hη2 : η2≤1) (hn : 1≤n)
    (hk1 : k1+2*n<p) (hk2 : k2+2*n<p) (hz1 : pz p γ1 k1 n≤M) (hz2 : pz p γ2 k2 n≤M)
    (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (hu00 : u0≠0)
    (ev : (ZMod p)[X][X] →+* RatFunc (ZMod p)) (htsM : ts∈Icc 1 M)
    (hz : ∀ t∈Icc 1 M,ev (dfac p q o t)=0 ↔ t=ts)
    (hev : ∀ k,ev (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k)
    (hwt : ev (deltaWeight p q o ts)≠0)
    (hcase : (cut1=k1+n+1 ∧ cut2=k2+n) ∨ (cut1=k1+n ∧ cut2=k2+n+1))
    (hw1 : γ1+(cut1-1)*p<ts ∧ ts≤γ1+cut1*p) (hw2 : γ2+(cut2-1)*p<ts ∧ ts≤γ2+cut2*p) :
    TwoTermDeformation.residue p
      ((ringSystem p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u true).det*
        (ringSystem p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u false).det-
      (ringSystem p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u true).det*
        (ringSystem p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u false).det)≠0 := by
  have H1 := profileHyp p q o γ1 k1 η1 n M hγ1 hη1 hk1 hz1 hM hq0 hqp ho0 hoq
  have H2 := profileHyp p q o γ2 k2 η2 n M hγ2 hη2 hk2 hz2 hM hq0 hqp ho0 hoq
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
  apply residue_cross_ne p q o H1 H2 s u u0 hs hu0 ev ts htsM hz hev cut1 cut2
    (hrow γ1 k1 η1 cut1 hγ1 hc1 hw1) (hcol γ1 k1 η1 cut1 hγ1 hc1 hw1) (hq γ1 k1 η1 hγ1 hη1 hk1)
    (hrow γ2 k2 η2 cut2 hγ2 hc2 hw2) (hcol γ2 k2 η2 cut2 hγ2 hc2 hw2) (hq γ2 k2 η2 hγ2 hη2 hk2)
  set g := centralWeight p q o ev u0 M ts with hgdef
  have hg : g≠0 := by
    rw [hgdef,centralWeight]
    refine mul_ne_zero (mul_ne_zero ?_ hwt) (ev_cofactor_self p q o ev M ts htsM hz)
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

theorem evOuter_bconst (c k : ZMod p) :
    evOuter p c (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k := by
  rw [IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)[X] (RatFunc (ZMod p)),Polynomial.algebraMap_eq]
  simp [evOuter,bconst]

theorem evInner_bconst (c k : ZMod p) :
    evInner p c (bconst p k)=algebraMap (ZMod p) (RatFunc (ZMod p)) k := by
  rw [IsScalarTower.algebraMap_apply (ZMod p) (ZMod p)[X] (RatFunc (ZMod p)),Polynomial.algebraMap_eq]
  simp [evInner,bconst]

/-- Section 8.3, ORIGINAL two-parameter fibre level: a separating original
pole of EITHER family (each with its own parameter), shifted to the central
threshold, gives distinct directions of two adjacent actual fibres. -/
theorem profile_separation (γ1 k1 η1 γ2 k2 η2 n M ts cut1 cut2 : ℕ) (s u : GaussLoc p) (u0 : ZMod p)
    (hγ1 : γ1<p) (hγ2 : γ2<p) (hη1 : η1≤1) (hη2 : η2≤1) (hn : 1≤n)
    (hk1 : k1+2*n<p) (hk2 : k2+2*n<p) (hz1 : pz p γ1 k1 n≤M) (hz2 : pz p γ2 k2 n≤M)
    (hM : q*M<p*p) (hq0 : 0<q) (hqp : q<p) (ho0 : 0<o) (hoq : o<q)
    (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu0 : TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)))
    (hu00 : u0≠0) (htsM : ts∈Icc 1 M) (hfam : p∣ts ∨ (¬p∣ts ∧ p∣q*ts-o))
    (hcase : (cut1=k1+n+1 ∧ cut2=k2+n) ∨ (cut1=k1+n ∧ cut2=k2+n+1))
    (hw1 : γ1+(cut1-1)*p<ts ∧ ts≤γ1+cut1*p) (hw2 : γ2+(cut2-1)*p<ts ∧ ts≤γ2+cut2*p) :
    TwoTermDeformation.residue p
      ((ringSystem p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u true).det*
        (ringSystem p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u false).det-
      (ringSystem p q o (pcn p γ2 k2) (pxr p γ2 k2 η2 n) (pyc p γ2 k2 η2 n) (pz p γ2 k2 n) s u true).det*
        (ringSystem p q o (pcn p γ1 k1) (pxr p γ1 k1 η1 n) (pyc p γ1 k1 η1 n) (pz p γ1 k1 n) s u false).det)≠0 := by
  have hq : (q:ZMod p)≠0 := by
    intro hz0
    have := Nat.le_of_dvd hq0 ((ZMod.natCast_eq_zero_iff q p).mp hz0)
    omega
  rcases hfam with hI|⟨hI,hF⟩
  · exact profile_separation_ev p q o γ1 k1 η1 γ2 k2 η2 n M ts cut1 cut2 s u u0 hγ1 hγ2 hη1 hη2 hn
      hk1 hk2 hz1 hz2 hM hq0 hqp ho0 hoq hs hu0 hu00 (evOuter p (-((ts/p:ℕ):ZMod p))) htsM
      (fun t ht => evOuter_dfac_eq_zero p q o M ts hM hq0 hqp hI htsM t ht) (evOuter_bconst p _)
      (by simp [deltaWeight,if_pos hI]) hcase hw1 hw2
  · exact profile_separation_ev p q o γ1 k1 η1 γ2 k2 η2 n M ts cut1 cut2 s u u0 hγ1 hγ2 hη1 hη2 hn
      hk1 hk2 hz1 hz2 hM hq0 hqp ho0 hoq hs hu0 hu00
      (evInner p (-((((q*ts-o)/p:ℕ):ZMod p))/(q:ZMod p))) htsM
      (fun t ht => evInner_dfac_eq_zero p q o M ts hM hq0 hqp ho0 hoq hI hF htsM t ht) (evInner_bconst p _)
      (by
        simp only [deltaWeight,if_neg hI,if_pos hF,map_neg,evInner_bconst,ne_eq,neg_eq_zero,
          map_eq_zero_iff _ (algebraMap (ZMod p) (RatFunc (ZMod p))).injective]
        exact hq) hcase hw1 hw2

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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

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

theorem ringSystem_reindex (s u : GaussLoc p) (load : Bool) :
    (ringSystem p q o cn xr yc z s u load).submatrix (bordEquiv k n) (bordEquiv k n)=
      Matrix.fromBlocks (TwoTermDeformation.mixedCore p q o s u cn xr yc)
        (Matrix.of fun i (_:Unit) => if load then TwoTermDeformation.constants p u*
          TwoTermDeformation.load p q o (Sum.elim cn xr i) else 1)
        (Matrix.of fun (_:Unit) j => TwoTermDeformation.entry p q o u z (Sum.elim cn yc j))
        (Matrix.of fun (_:Unit) (_:Unit) => if load then TwoTermDeformation.constants p u*
          TwoTermDeformation.load p q o z else 1) := by
  classical
  have hlt (c : Fin n) : ((Fin.castAdd 1 c:Fin (n+1)):ℕ)<n := by simp
  have hnl : ¬((Fin.last n:Fin (n+1)):ℕ)<n := by simp
  have hbc (c : Fin n) : bordRow xr z (Fin.castAdd 1 c)=xr c := by
    unfold bordRow; rw [dif_pos (hlt c)]; rfl
  have hbl : bordRow xr z (Fin.last n)=z := by unfold bordRow; rw [dif_neg hnl]
  ext i j
  rcases i with (i|i)|i <;> rcases j with (j|j)|j
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,ringSystem,Matrix.fromBlocks_apply₁₁,
      Matrix.of_apply,TwoTermDeformation.mixedCore,Matrix.add_apply,Matrix.map_apply,Sum.elim_inl,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    split_ifs <;> simp
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inl_inr,ringSystem,
      Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₁₁,Matrix.of_apply,dif_pos (hlt j),
      TwoTermDeformation.mixedCore,Matrix.add_apply,Matrix.map_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,map_zero,add_zero]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inr,ringSystem,
      Matrix.fromBlocks_apply₁₂,Matrix.of_apply,dif_neg hnl,Sum.elim_inl]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inl_inr,ringSystem,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₁₁,Matrix.of_apply,hbc,
      TwoTermDeformation.mixedCore,Matrix.add_apply,Matrix.map_apply,Sum.elim_inl,Sum.elim_inr,
      Matrix.zero_apply,map_zero,add_zero]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,ringSystem,Matrix.fromBlocks_apply₂₂,
      Matrix.fromBlocks_apply₁₁,Matrix.of_apply,hbc,dif_pos (hlt j),
      TwoTermDeformation.mixedCore,Matrix.add_apply,Matrix.map_apply,Sum.elim_inr,
      Matrix.zero_apply,map_zero,add_zero]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,bordEquiv_inr,ringSystem,
      Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₁₂,Matrix.of_apply,hbc,dif_neg hnl,Sum.elim_inr]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inl,bordEquiv_inr,ringSystem,
      Matrix.fromBlocks_apply₂₁,Matrix.of_apply,hbl,Sum.elim_inl]
  · simp only [Matrix.submatrix_apply,bordEquiv_inl_inr,bordEquiv_inr,ringSystem,
      Matrix.fromBlocks_apply₂₂,Matrix.fromBlocks_apply₂₁,Matrix.of_apply,hbl,dif_pos (hlt j),Sum.elim_inr]
    rfl
  · simp only [Matrix.submatrix_apply,bordEquiv_inr,ringSystem,Matrix.fromBlocks_apply₂₂,
      Matrix.of_apply,hbl,dif_neg hnl]

end BorderedFibre

section TwoParameterCoupling
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

theorem residue_response {R K α : Type*} [CommRing R] [Field K] [Fintype α] [DecidableEq α]
    (f : R →+* K) (Q : Matrix α α R) (hQ : IsUnit Q.det) (σ y : α → R) :
    f (σ ⬝ᵥ Q⁻¹ *ᵥ y)=(fun i => f (σ i)) ⬝ᵥ (Q.map f)⁻¹ *ᵥ (fun i => f (y i)) := by
  rw [UFMoments.map_inv_of_unit f Q hQ]
  simp only [dotProduct,Matrix.mulVec,map_sum,map_mul,Matrix.map_apply]

theorem residue_uniformizer : TwoTermDeformation.residue p (TwoTermDeformation.uniformizer p)=0 :=
  (WrapParameter.residue_zero_iff (WrapDeform.residue p) (WrapDeform.uniformizer p)
    (WrapDeform.residue_zero_iff p) _).mpr (dvd_refl _)

theorem residue_nat_sub_ne (a b : ℕ) (h : (a:ZMod p)≠(b:ZMod p)) :
    (a:TwoTermDeformation.Residue p)-(b:TwoTermDeformation.Residue p)≠0 := by
  intro hz
  apply h
  have hinj : Function.Injective (fun k : ZMod p =>
      (RatFunc.C (RatFunc.C (RatFunc.C k)) : TwoTermDeformation.Residue p)) :=
    RatFunc.C_injective.comp (RatFunc.C_injective.comp RatFunc.C_injective)
  apply hinj
  simpa only [map_natCast] using sub_eq_zero.mp hz

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Actual two-parameter border of an original node `t` against the
actual original columns. -/
noncomputable def sigma2 (u : GaussLoc p) (t : ℕ) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    TwoTermDeformation.Ring p :=
  TwoTermDeformation.entry p q o u t (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)

noncomputable def rowMoment2 (s u : GaussLoc p) (t : ℕ) :=
  TwoTermDeformation.constants p u*TwoTermDeformation.load p q o t-
    sigma2 H u t ⬝ᵥ (TwoTermDeformation.prefixCore p H s u)⁻¹ *ᵥ TwoTermDeformation.prefixRowLoad p H u

noncomputable def rowRef2 (s u : GaussLoc p) (t : ℕ) :=
  1-sigma2 H u t ⬝ᵥ (TwoTermDeformation.prefixCore p H s u)⁻¹ *ᵥ (1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → TwoTermDeformation.Ring p)

/-- The actual two-parameter outside row coupling against the actual
original anchor. -/
noncomputable def rowCoupling2 (s u : GaussLoc p) (z : Fin d) :=
  TwoTermDeformation.residue p (rowMoment2 H s u (WrapPrefixSchur.surplusRow H z)-
    TwoTermDeformation.prefixAnchor p H s u*rowRef2 H s u (WrapPrefixSchur.surplusRow H z))

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

/-- Original two-parameter displacement kills every cross-colour entry. -/
theorem core_cross_zero (s u : GaussLoc p) (i j : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hij : H.colour i≠H.colour j) :
    TwoTermDeformation.residue p (TwoTermDeformation.prefixCore p H s u i j)=0 := by
  have hc := congrArg (TwoTermDeformation.residue p)
    (TwoTermDeformation.mixedCore_commutator p q o N (single_bound H) s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
      H.common_bound H.row_bound H.col_bound i j)
  rw [map_mul,map_mul,residue_uniformizer,zero_mul,map_sub,map_natCast,map_natCast] at hc
  have hne := residue_nat_sub_ne (p:=p) _ _
    (show ((Sum.elim (fun i:Fin r => (i:ℕ)) H.ys j:ℕ):ZMod p)≠((Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i:ℕ):ZMod p) by
      rw [colNode_colour,rowNode_colour]; exact fun h => hij h.symm)
  exact (mul_eq_zero.mp hc).resolve_left hne

theorem sigma_cross_zero (u : GaussLoc p) (t : ℕ) (ht : t<N) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hi : H.colour i≠(t:ZMod p)) : TwoTermDeformation.residue p (sigma2 H u t i)=0 := by
  have hcol := (UFMember.colNode_lt H.common_bound H.col_bound i)
  have hc := congrArg (TwoTermDeformation.residue p)
    (TwoTermDeformation.commutator p q o N u (single_bound H) t _ ht hcol)
  rw [map_mul,map_mul,residue_uniformizer,zero_mul,map_sub,map_natCast,map_natCast] at hc
  have hne := residue_nat_sub_ne (p:=p) _ _
    (show ((Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i:ℕ):ZMod p)≠(t:ZMod p) by rw [colNode_colour]; exact hi)
  exact (mul_eq_zero.mp hc).resolve_left hne

/-- Reduced actual core: colour-block diagonal, nonsingular. -/
noncomputable def coreBar (s u : GaussLoc p) := (TwoTermDeformation.prefixCore p H s u).map (TwoTermDeformation.residue p)

theorem coreBar_own (s u : GaussLoc p) :
    (TwoTermDeformation.prefixOwn p H s u).map (TwoTermDeformation.residue p)=coreBar H s u := by
  ext i j
  simp only [coreBar,Matrix.map_apply,TwoTermDeformation.prefixOwn,TwoTermDeformation.own,Matrix.of_apply]
  by_cases h : H.colour i=H.colour j
  · rw [if_pos h]
  · rw [if_neg h,map_zero,core_cross_zero H s u i j h]

theorem coreBar_det (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) : (coreBar H s u).det≠0 := by
  have h := ((TwoTermDeformation.prefixCore_unit p H s u hs hu huc).map (TwoTermDeformation.residue p)).ne_zero
  rwa [RingHom.map_det] at h

theorem residue_rowMoment2 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    TwoTermDeformation.residue p (rowMoment2 H s u t)=
      TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o t)-
        (fun i => TwoTermDeformation.residue p (sigma2 H u t i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ
          (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixRowLoad p H u i)) := by
  rw [rowMoment2,map_sub,residue_response _ _ (TwoTermDeformation.prefixCore_unit p H s u hs hu huc)]
  rfl

theorem residue_rowRef2 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    TwoTermDeformation.residue p (rowRef2 H s u t)=
      1-(fun i => TwoTermDeformation.residue p (sigma2 H u t i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1 := by
  rw [rowRef2,map_sub,map_one,residue_response _ _ (TwoTermDeformation.prefixCore_unit p H s u hs hu huc)]
  simp only [Pi.one_apply,map_one]
  rfl

theorem residue_prefixSigma (u : GaussLoc p) (t : ℕ) (ht : t<N) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    TwoTermDeformation.residue p (TwoTermDeformation.prefixSigma p H u t i)=
      TwoTermDeformation.residue p (sigma2 H u t i) := by
  unfold TwoTermDeformation.prefixSigma
  split_ifs with h
  · rfl
  · rw [map_zero,sigma_cross_zero H u t ht i h]

theorem rational_map_inverse {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (f : R →+* RatFunc S) (x : R) (hx : IsUnit x) : f (Ring.inverse x)=(f x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul,Ring.inverse_mul_cancel _ hx,map_one]

set_option maxHeartbeats 1000000 in
theorem residue_anchor (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    TwoTermDeformation.residue p (TwoTermDeformation.prefixAnchor p H s u)=
      (TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o H.t0)-
        (fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ
          (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixRowLoad p H u i)))*
      (1-(fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1)⁻¹ := by
  have ht0 : H.t0<N := lt_of_le_of_lt H.hle H.htvN
  have hO := TwoTermDeformation.prefixOwn_unit p H s u hs hu huc
  have hB := TwoTermDeformation.prefixReference_unit p H s u hs hu huc
  have hinv := rational_map_inverse (TwoTermDeformation.residue p) _ hB
  have hsig : (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixSigma p H u H.t0 i))=
      (fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) :=
    funext (residue_prefixSigma H u H.t0 ht0)
  have href : TwoTermDeformation.residue p (TwoTermDeformation.prefixReference p H s u H.t0)=
      1-(fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1 := by
    rw [TwoTermDeformation.prefixReference,map_sub,map_one,residue_response _ _ hO,coreBar_own,hsig]
    simp only [Pi.one_apply,map_one]
    rfl
  rw [TwoTermDeformation.prefixAnchor,map_mul,hinv,href,map_sub,residue_response _ _ hO,coreBar_own,hsig]

theorem residue_reference0 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    TwoTermDeformation.residue p (TwoTermDeformation.prefixReference p H s u H.t0)=
      1-(fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1 := by
  have ht0 : H.t0<N := lt_of_le_of_lt H.hle H.htvN
  have hO := TwoTermDeformation.prefixOwn_unit p H s u hs hu huc
  have hsig : (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixSigma p H u H.t0 i))=
      (fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) :=
    funext (residue_prefixSigma H u H.t0 ht0)
  rw [TwoTermDeformation.prefixReference,map_sub,map_one,residue_response _ _ hO,coreBar_own,hsig]
  simp only [Pi.one_apply,map_one]
  rfl

theorem reference0_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) :
    1-(fun i => TwoTermDeformation.residue p (sigma2 H u H.t0 i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1≠0 := by
  rw [← residue_reference0 H s u hs hu huc]
  exact ((TwoTermDeformation.prefixReference_unit p H s u hs hu huc).map (TwoTermDeformation.residue p)).ne_zero

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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

variable {k n : ℕ} (cn : Fin k → ℕ) (xr yc : Fin n → ℕ) (z : ℕ)

/-- Residue of the ORIGINAL bordered fibre determinant in Schur form. -/
theorem residue_ringSystem_det (s u : GaussLoc p) (load : Bool)
    (hP : ((TwoTermDeformation.mixedCore p q o s u cn xr yc).map (TwoTermDeformation.residue p)).det≠0) :
    TwoTermDeformation.residue p (ringSystem p q o cn xr yc z s u load).det=
      ((TwoTermDeformation.mixedCore p q o s u cn xr yc).map (TwoTermDeformation.residue p)).det*
        (TwoTermDeformation.residue p (if load then TwoTermDeformation.constants p u*
          TwoTermDeformation.load p q o z else 1)-
          (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u z (Sum.elim cn yc j))) ⬝ᵥ
            ((TwoTermDeformation.mixedCore p q o s u cn xr yc).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
            (fun i => TwoTermDeformation.residue p (if load then TwoTermDeformation.constants p u*
              TwoTermDeformation.load p q o (Sum.elim cn xr i) else 1))) := by
  rw [← Matrix.det_submatrix_equiv_self (bordEquiv k n),ringSystem_reindex]
  exact map_bordered_det (TwoTermDeformation.residue p) _ _ _ _ hP

end BorderedResidueActual

section FibreBinding
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

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

/-- The actual two-parameter colour block is the ORIGINAL two-parameter
profile core, under the exact original fibre equivalence. -/
theorem whole_core2 (γ : ZMod p) (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠γ) (s u : GaussLoc p) :
    (TwoTermDeformation.prefixCore p H s u).submatrix
        (fun i => (fibreEquiv H γ hres i).1)
        (fun j => (fibreEquiv H γ hres j).1)=
      TwoTermDeformation.mixedCore p q o s u
        (fun i:Fin (WrapJointProfile.count p r γ.val) => γ.val+(i:ℕ)*p)
        (fun c:Fin n => WrapJointProfile.rowProfile p r γ.val c)
        (fun c:Fin n => WrapJointProfile.colProfile p r γ.val c) := by
  classical
  have he (i j : Fin (WrapJointProfile.count p r γ.val) ⊕ Fin n) :
      TwoTermDeformation.entry p q o u
        (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.xs p (n:=n) r H.er)
          (WrapJointProfile.wholeEquiv p r n e b d H.hp2 H.er γ hres i).1)
        (Sum.elim (fun i:Fin r => (i:ℕ)) (WrapPrefixCoreGeometry.ys p (n:=n) r (Fact.out:p.Prime).pos shift H.ec)
          (WrapJointProfile.wholeEquiv p r n e b d H.hp2 H.er γ hres j).1)=
      TwoTermDeformation.entry p q o u
        (Sum.elim (fun i:Fin (WrapJointProfile.count p r γ.val) => γ.val+(i:ℕ)*p)
          (fun c:Fin n => WrapJointProfile.rowProfile p r γ.val c) i)
        (Sum.elim (fun i:Fin (WrapJointProfile.count p r γ.val) => γ.val+(i:ℕ)*p)
          (fun c:Fin n => WrapJointProfile.colProfile p r γ.val c) j) := by
    rw [WrapJointProfile.whole_row p r n e b d H.hp2 (hodd H) H.er γ hres i,
      WrapJointProfile.whole_col p r n e b d shift H.hp H.hp2 H.er H.ec γ hres j]
  ext i j
  simp only [TwoTermDeformation.prefixCore,TwoTermDeformation.mixedCore,Matrix.submatrix_apply,
    Matrix.add_apply,Matrix.of_apply,Matrix.map_apply]
  congr 1
  · exact he i j
  rcases i with i|i <;> rcases j with j|j
  · change TwoTermDeformation.coefficient p ((WrapOwnCore.constants p s • (1:Matrix (Fin r) (Fin r) _))
        (WrapJointProfile.commonEquiv p r γ i).1 (WrapJointProfile.commonEquiv p r γ j).1)=
      TwoTermDeformation.coefficient p ((WrapOwnCore.constants p s • (1:Matrix _ _ _)) i j)
    have heq : (WrapJointProfile.commonEquiv p r γ i).1=(WrapJointProfile.commonEquiv p r γ j).1 ↔ i=j :=
      ⟨fun h => (WrapJointProfile.commonEquiv p r γ).injective (Subtype.ext h),fun h => by rw [h]⟩
    simp only [Matrix.smul_apply,Matrix.one_apply,heq]
  · rfl
  · rfl
  · rfl

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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Profile nodes of the actual fibre of an original node `t`. -/
noncomputable def fibreCore (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (s u : GaussLoc p) (t : ℕ) :=
  TwoTermDeformation.mixedCore p q o s u
    (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
    (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (WrapJointProfile.bit p r (t:ZMod p).val) n)
    (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (WrapJointProfile.bit p r (t:ZMod p).val) n)

/-- The reduced actual colour block is the reduced ORIGINAL profile core. -/
theorem fibre_blk (s u : GaussLoc p) (t : ℕ) (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (UFMoments.blk (coreBar H s u) H.colour (t:ZMod p)).submatrix
        (fibreEquiv H (t:ZMod p) hres)
        (fibreEquiv H (t:ZMod p) hres)=
      (fibreCore H s u t).map (TwoTermDeformation.residue p) := by
  rw [UFMoments.blk,Matrix.submatrix_submatrix,coreBar,Matrix.submatrix_map]
  have hw := whole_core2 H (t:ZMod p) hres s u
  rw [show ((Subtype.val ∘ ⇑(fibreEquiv H (t:ZMod p) hres)):_ → _)=
    (fun i => (fibreEquiv H (t:ZMod p) hres i).1) from rfl,hw]
  congr 1
  unfold fibreCore
  congr 1
  · funext c; exact rowProfile_eq (p:=p) _ c
  · funext c; exact colProfile_eq (p:=p) _ c

theorem fibreCore_det_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    ((fibreCore H s u t).map (TwoTermDeformation.residue p)).det≠0 := by
  rw [← fibre_blk H s u t hres,Matrix.det_submatrix_equiv_self]
  have hb : ∀ a c,H.colour a≠H.colour c → coreBar H s u a c=0 := fun a c h => core_cross_zero H s u a c h
  exact (UFMoments.inv_restrict (coreBar H s u) H.colour
    (isUnit_iff_ne_zero.mpr (coreBar_det H s u hs hu huc)) hb (t:ZMod p)).1.ne_zero

/-- The actual reduced response of node `t` is its ORIGINAL profile response. -/
theorem fibre_moment (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) (f : ℕ → TwoTermDeformation.Ring p) :
    (fun i => TwoTermDeformation.residue p (sigma2 H u t i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i)))=
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
            (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
              (WrapJointProfile.bit p r (t:ZMod p).val) n) j))) ⬝ᵥ
        ((fibreCore H s u t).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (f (Sum.elim
          (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
          (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
            (WrapJointProfile.bit p r (t:ZMod p).val) n) i))) := by
  classical
  have hb : ∀ a c,H.colour a≠H.colour c → coreBar H s u a c=0 := by
    intro a c h
    exact core_cross_zero H s u a c h
  have hsz : ∀ a,H.colour a≠(t:ZMod p) → TwoTermDeformation.residue p (sigma2 H u t a)=0 :=
    fun a h => sigma_cross_zero H u t ht a h
  rw [fibre_response (coreBar H s u) H.colour (coreBar_det H s u hs hu huc) hb (t:ZMod p) _ _ hsz]
  rw [← WrapTransport.response_reindex (UFMoments.blk (coreBar H s u) H.colour (t:ZMod p))
    (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)]
  have hl : (fun i:{a // H.colour a=(t:ZMod p)} => TwoTermDeformation.residue p (sigma2 H u t i.1)) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
            (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
              (WrapJointProfile.bit p r (t:ZMod p).val) n) j)) := by
    funext j
    simp only [Function.comp_apply,sigma2]
    rw [fibre_col H (t:ZMod p) hres j]
    rcases j with j|j
    · rfl
    · simp only [Sum.elim_inr]
      rw [colProfile_eq]
  have hr : (fun i:{a // H.colour a=(t:ZMod p)} =>
      TwoTermDeformation.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i.1))) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun i => TwoTermDeformation.residue p (f (Sum.elim
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
  rw [fibre_blk H s u t hres,hl,hr]

/-- Profile border of node `t`. -/
noncomputable def fibreSigma (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (u : GaussLoc p) (t : ℕ) :
    Fin (WrapJointProfile.count p r (t:ZMod p).val) ⊕ Fin n → TwoTermDeformation.Residue p :=
  fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
    (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
      (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
        (WrapJointProfile.bit p r (t:ZMod p).val) n) j))

noncomputable def fibreLoad (_H : WrapPrefixWindow.Setup p q o r n e b d shift N) (u : GaussLoc p) (t : ℕ) :
    Fin (WrapJointProfile.count p r (t:ZMod p).val) ⊕ Fin n → TwoTermDeformation.Residue p :=
  fun i => TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o
    (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val))
      (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)
        (WrapJointProfile.bit p r (t:ZMod p).val) n) i))

theorem fibre_load (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => TwoTermDeformation.residue p (sigma2 H u t i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixRowLoad p H u i))=
      fibreSigma H u t ⬝ᵥ ((fibreCore H s u t).map (TwoTermDeformation.residue p))⁻¹ *ᵥ fibreLoad H u t :=
  fibre_moment H s u hs hu huc t ht hres
    (fun a => TwoTermDeformation.constants p u*TwoTermDeformation.load p q o a)

theorem fibre_one (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => TwoTermDeformation.residue p (sigma2 H u t i)) ⬝ᵥ (coreBar H s u)⁻¹ *ᵥ 1=
      fibreSigma H u t ⬝ᵥ ((fibreCore H s u t).map (TwoTermDeformation.residue p))⁻¹ *ᵥ 1 := by
  have h := fibre_moment H s u hs hu huc t ht hres (fun _ => (1:TwoTermDeformation.Ring p))
  simp only [map_one] at h
  exact h

end RowSeparation


section RowSeparationFinal
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

theorem rfH_eq (z : ZMod p) : CatalanCore.Uniform.Content.Hybrid.rfH p z=RatFunc.C z := by
  simp [CatalanCore.Uniform.Content.Hybrid.rfH,RatFunc.algebraMap_C]

theorem residue_constants (u : GaussLoc p) (u0 : ZMod p) (h : res p u=CatalanCore.Uniform.Content.Hybrid.rfH p u0) :
    TwoTermDeformation.residue p (TwoTermDeformation.constants p u)=RatFunc.C (RatFunc.C (RatFunc.C u0)) := by
  rw [TwoTermDeformation.constants,RingHom.comp_apply,TwoTermDeformation.coefficient_residue,
    TwoTermDeformation.first_constant_residue,h,rfH_eq]

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

set_option maxHeartbeats 2000000 in
/-- Section 8.3 at an actual outside node `v` with fibre bit `η` (the row
fibre has the actual bit, the column fibre the complementary bit): a
separating original pole of either family, each with its own deformation
parameter, makes the actual reduced coupling against the original anchor
nonzero. No inverse pivot is specialized. -/
theorem node_coupling_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (v k η : ℕ) (hη : η≤1)
    (hk : p∣k ∨ p∣q*k-o)
    (hsep : (v<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤v))
    (hvlo : r+2*n*p≤v) (hvhi : v<r+2*n*p+p) (hvN : v<N)
    (hPv : ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p)).det≠0) :
    (TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o v)-
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
      (fun i => TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))-
    TwoTermDeformation.residue p (TwoTermDeformation.prefixAnchor p H s u)*
    (1-(fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ 1)≠0 := by
  classical
  obtain ⟨u0,hu0'⟩ := huc
  have huc : WrapConstant.Has p u := ⟨u0,hu0'⟩
  have hu0 := residue_constants u u0 hu0'
  have hu00 : u0≠0 := by
    intro h; apply hu; rw [hu0',h,map_zero]
  have ht0N : H.t0<N := lt_of_le_of_lt H.hle H.htvN
  have ht0lo := H.hlo
  have ht0hi : H.t0<r+2*n*p+p := lt_of_le_of_lt H.hle H.hhi
  have hres0 : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(H.t0:ZMod p) :=
    fun i => H.hfree H.t0 (mem_Icc.mpr ⟨le_rfl,H.hle⟩) i
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
  have hfam : p∣k-n*p ∨ (¬p∣k-n*p ∧ p∣q*(k-n*p)-o) := by
    have hle : o≤q*(k-n*p) := by
      have := Nat.le_mul_of_pos_right q hts1
      have := H.hoq
      omega
    rcases hk with hI|hF
    · exact Or.inl (Nat.dvd_sub hI (Dvd.intro_left n rfl))
    · have hqk : q*(k-n*p)-o=(q*k-o)-q*n*p := by
        rw [Nat.mul_sub]
        have : q*(n*p)=q*n*p := by ring
        rw [this]
        have : q*n*p≤q*k := by rw [mul_assoc]; exact Nat.mul_le_mul_left q hnp
        omega
      have hF' : p∣q*(k-n*p)-o := by
        rw [hqk]
        exact Nat.dvd_sub hF (Dvd.intro_left (q*n) (by ring))
      refine Or.inr ⟨fun hI => not_both p q o (k-n*p) H.hqp ho0 H.hoq hle hI hF',hF'⟩
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
  have hps := profile_separation p q o (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)
    η (H.t0:ZMod p).val
    (WrapJointProfile.count p r (H.t0:ZMod p).val) (WrapJointProfile.bit p r (H.t0:ZMod p).val)
    n N (k-n*p) cut1 cut2 s u u0 (ZMod.val_lt _) (ZMod.val_lt _) hη (bit_le _) H.hn hkv hk0
    hz1 hz2 H.hN H.hq0 H.hqp ho0 H.hoq hs hu0 hu00 (mem_Icc.mpr ⟨hts1,htsN⟩) hfam hcase hw1 hw2
  rw [hpzv,hpz0] at hps
  have hP0 := fibreCore_det_ne H s u hs hu huc H.t0 hres0
  have hRvT := residue_ringSystem_det p q o _ _ _ v s u true hPv
  have hRvF := residue_ringSystem_det p q o _ _ _ v s u false hPv
  have hR0T := residue_ringSystem_det p q o _ _ _ H.t0 s u true hP0
  have hR0F := residue_ringSystem_det p q o _ _ _ H.t0 s u false hP0
  simp only [↓reduceIte,Bool.false_eq_true,map_one] at hRvT hRvF hR0T hR0F
  have hr0 := reference0_ne H s u hs hu huc
  rw [fibre_one H s u hs hu huc H.t0 ht0N hres0] at hr0
  rw [residue_anchor H s u hs hu huc,fibre_load H s u hs hu huc H.t0 ht0N hres0,
    fibre_one H s u hs hu huc H.t0 ht0N hres0]
  intro hc
  apply hps
  rw [map_sub,map_mul,map_mul]
  have key := coupling_cross ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p)).det
    ((fibreCore H s u H.t0).map (TwoTermDeformation.residue p)).det
    (TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o v)-
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
      (fun i => TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o
        (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val)) (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) i))))
    (TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o H.t0)-
      fibreSigma H u H.t0 ⬝ᵥ ((fibreCore H s u H.t0).map (TwoTermDeformation.residue p))⁻¹ *ᵥ fibreLoad H u H.t0)
    (1-(fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u v (Sum.elim (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n) j))) ⬝ᵥ
      ((TwoTermDeformation.mixedCore p q o s u (pcn p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val))
        (pxr p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)
        (pyc p (v:ZMod p).val (WrapJointProfile.count p r (v:ZMod p).val) η n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ 1)
    (1-fibreSigma H u H.t0 ⬝ᵥ ((fibreCore H s u H.t0).map (TwoTermDeformation.residue p))⁻¹ *ᵥ 1) hr0
  rw [hc,zero_mul,zero_mul,zero_mul] at key
  rw [hRvT,hRvF,hR0T,hR0F]
  exact key.symm

/-- Section 8.3, ACTUAL prefix binding: an outside surplus row separated
from the anchor by an original pole of either family (each family with its
own deformation parameter) has a NONZERO actual two-parameter coupling.
No inverse pivot is specialized; the conclusion is generic nonvanishing. -/
theorem rowCoupling2_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (z : Fin d) (k : ℕ)
    (hk : p∣k ∨ p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusRow H z<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusRow H z))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusRow H z)
    (hvhi : WrapPrefixSchur.surplusRow H z<r+2*n*p+p) :
    rowCoupling2 H s u z≠0 := by
  have hvN : WrapPrefixSchur.surplusRow H z<N := WrapPrefixSchur.surplus_row_bound H z
  have hresv := surplus_not_residual H z
  unfold rowCoupling2
  rw [map_sub,map_mul,residue_rowMoment2 H s u hs hu huc,residue_rowRef2 H s u hs hu huc,
    fibre_load H s u hs hu huc _ hvN hresv,fibre_one H s u hs hu huc _ hvN hresv]
  exact node_coupling_ne H s u hs hu huc _ k _ (bit_le _) hk hsep hvlo hvhi hvN
    (fibreCore_det_ne H s u hs hu huc _ hresv)

end RowSeparationFinal


section ColumnCoupling
variable {p : ℕ} [Fact p.Prime]

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- Actual two-parameter column border of an original node `t`. -/
noncomputable def colSigma2 (u : GaussLoc p) (t : ℕ) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b)) :
    TwoTermDeformation.Ring p :=
  TwoTermDeformation.entry p q o u (Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i) t

noncomputable def colMoment2 (s u : GaussLoc p) (t : ℕ) :=
  TwoTermDeformation.constants p u*TwoTermDeformation.load p q o t-
    TwoTermDeformation.prefixColLoad p H u ⬝ᵥ (TwoTermDeformation.prefixCore p H s u)⁻¹ *ᵥ colSigma2 H u t

noncomputable def colRef2 (s u : GaussLoc p) (t : ℕ) :=
  1-(1:Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b) → TwoTermDeformation.Ring p) ⬝ᵥ
    (TwoTermDeformation.prefixCore p H s u)⁻¹ *ᵥ colSigma2 H u t

/-- The actual two-parameter outside column coupling against the actual
original (row) anchor. -/
noncomputable def colCoupling2 (s u : GaussLoc p) (y : Fin d) :=
  TwoTermDeformation.residue p (colMoment2 H s u (WrapPrefixSchur.surplusCol H y)-
    TwoTermDeformation.prefixAnchor p H s u*colRef2 H s u (WrapPrefixSchur.surplusCol H y))

/-- Two-parameter cleared reference identity at a shared original node:
the row and column directions agree, with no column-reference unit. -/
theorem shared_moments2 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N) :
    rowRef2 H s u t*colMoment2 H s u t=rowMoment2 H s u t*colRef2 H s u t := by
  have hN := single_bound H
  apply WrapPrefixSchur.scaled_cross_direction (R:=TwoTermDeformation.Ring p) (TwoTermDeformation.uniformizer p)
    (TwoTermDeformation.parameterPrime p).ne_zero
    (TwoTermDeformation.prefixCore p H s u) (TwoTermDeformation.prefixCore_unit p H s u hs hu huc)
    (fun i => ((Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i:ℕ):TwoTermDeformation.Ring p))
    (fun i => ((Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i:ℕ):TwoTermDeformation.Ring p))
    (TwoTermDeformation.prefixRowLoad p H u) (TwoTermDeformation.prefixColLoad p H u)
    (sigma2 H u t) (colSigma2 H u t) (t:TwoTermDeformation.Ring p)
    (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o t)
  · intro i j
    have he := TwoTermDeformation.mixedCore_commutator p q o N hN s u (fun i:Fin r => (i:ℕ)) H.xs H.ys
      H.common_bound H.row_bound H.col_bound i j
    simpa only [mul_sub,TwoTermDeformation.prefixRowLoad,TwoTermDeformation.prefixColLoad,
      TwoTermDeformation.prefixCore] using he
  · intro i
    have he := TwoTermDeformation.commutator p q o N u hN t _ ht
      (UFMember.colNode_lt H.common_bound H.col_bound i)
    simp only [UFMember.colNode] at he
    simp only [sigma2,TwoTermDeformation.prefixColLoad,← mul_sub]
    exact he
  · intro i
    have he := TwoTermDeformation.commutator p q o N u hN _ t
      (UFMember.rowNode_lt H.common_bound H.row_bound i) ht
    simp only [UFMember.rowNode] at he
    simp only [colSigma2,TwoTermDeformation.prefixRowLoad,← mul_sub]
    exact he

theorem col_sigma_cross_zero (u : GaussLoc p) (t : ℕ) (ht : t<N) (i : Fin r ⊕ ((Fin n × Fin p) ⊕ Fin b))
    (hi : H.colour i≠(t:ZMod p)) : TwoTermDeformation.residue p (colSigma2 H u t i)=0 := by
  have hrow := (UFMember.rowNode_lt H.common_bound H.row_bound i)
  have hc := congrArg (TwoTermDeformation.residue p)
    (TwoTermDeformation.commutator p q o N u (single_bound H) _ t hrow ht)
  rw [map_mul,map_mul,residue_uniformizer,zero_mul,map_sub,map_natCast,map_natCast] at hc
  have hne := residue_nat_sub_ne (p:=p) _ _
    (show (t:ZMod p)≠((Sum.elim (fun i:Fin r => (i:ℕ)) H.xs i:ℕ):ZMod p) by
      rw [rowNode_colour]; exact fun h => hi h.symm)
  exact (mul_eq_zero.mp hc).resolve_left hne

theorem dot_transpose {K α : Type*} [CommRing K] [Fintype α] (a b : α → K) (M : Matrix α α K) :
    a ⬝ᵥ M *ᵥ b=b ⬝ᵥ Mᵀ *ᵥ a := by
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose,dotProduct_comm]

theorem residue_colMoment2 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    TwoTermDeformation.residue p (colMoment2 H s u t)=
      TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o t)-
        (fun i => TwoTermDeformation.residue p (colSigma2 H u t i)) ⬝ᵥ (coreBar H s u)ᵀ⁻¹ *ᵥ
          (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixColLoad p H u i)) := by
  rw [colMoment2,map_sub,residue_response _ _ (TwoTermDeformation.prefixCore_unit p H s u hs hu huc),
    dot_transpose,Matrix.transpose_nonsing_inv]
  rfl

theorem residue_colRef2 (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) :
    TwoTermDeformation.residue p (colRef2 H s u t)=
      1-(fun i => TwoTermDeformation.residue p (colSigma2 H u t i)) ⬝ᵥ (coreBar H s u)ᵀ⁻¹ *ᵥ 1 := by
  rw [colRef2,map_sub,map_one,residue_response _ _ (TwoTermDeformation.prefixCore_unit p H s u hs hu huc),
    dot_transpose,Matrix.transpose_nonsing_inv]
  simp only [Pi.one_apply,map_one]
  rfl

theorem mixedCore_transpose {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (s u : GaussLoc p) (c : ι → ℕ) (xs ys : κ → ℕ) :
    (TwoTermDeformation.mixedCore p q o s u c xs ys)ᵀ=TwoTermDeformation.mixedCore p q o s u c ys xs := by
  ext i j
  simp only [Matrix.transpose_apply,TwoTermDeformation.mixedCore,Matrix.add_apply,Matrix.of_apply,
    Matrix.map_apply]
  rw [TwoTermDeformation.entry_symm]
  congr 1
  rcases i with i|i <;> rcases j with j|j <;>
    simp [Matrix.fromBlocks_apply₁₁,Matrix.one_apply,eq_comm]

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

attribute [local instance] TwoTermDeformation.coefficientDomain TwoTermDeformation.ringDomain

omit [Fact p.Prime] in
theorem pxr_flip (γ k η n : ℕ) (c : Fin n) : pxr p γ k (1-η) n c=pyc p γ k η n c := rfl

omit [Fact p.Prime] in
theorem pyc_flip (γ k η n : ℕ) (hη : η≤1) (c : Fin n) : pyc p γ k (1-η) n c=pxr p γ k η n c := by
  unfold pyc pxr
  have : 1-(1-η)=η := by omega
  rw [this]

variable {q o r n e b d shift N : ℕ}
variable (H : WrapPrefixWindow.Setup p q o r n e b d shift N)

/-- The transposed actual fibre is the actual fibre with the complementary bit. -/
theorem fibreCore_transpose (s u : GaussLoc p) (t : ℕ) :
    (fibreCore H s u t)ᵀ=TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) := by
  unfold fibreCore
  rw [mixedCore_transpose,_root_.funext (pxr_flip (p:=p) _ _ _ n),_root_.funext (pyc_flip (p:=p) _ _ _ n (bit_le _))]

/-- The actual reduced COLUMN response of node `t` is the ORIGINAL profile
response of its fibre with the complementary bit. -/
theorem col_fibre_moment (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p))
    (f : ℕ → TwoTermDeformation.Ring p) :
    (fun i => TwoTermDeformation.residue p (colSigma2 H u t i)) ⬝ᵥ (coreBar H s u)ᵀ⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i)))=
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (f (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i))) := by
  classical
  have hbT : ∀ a c,H.colour a≠H.colour c → (coreBar H s u)ᵀ a c=0 :=
    fun a c h => core_cross_zero H s u c a (Ne.symm h)
  have hdetT : (coreBar H s u)ᵀ.det≠0 := by
    rw [Matrix.det_transpose]; exact coreBar_det H s u hs hu huc
  have hsz : ∀ a,H.colour a≠(t:ZMod p) → TwoTermDeformation.residue p (colSigma2 H u t a)=0 :=
    fun a h => col_sigma_cross_zero H u t ht a h
  rw [fibre_response (coreBar H s u)ᵀ H.colour hdetT hbT (t:ZMod p) _ _ hsz]
  rw [← WrapTransport.response_reindex (UFMoments.blk (coreBar H s u)ᵀ H.colour (t:ZMod p))
    (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)]
  have hblk : (UFMoments.blk (coreBar H s u)ᵀ H.colour (t:ZMod p)).submatrix
      (fibreEquiv H (t:ZMod p) hres) (fibreEquiv H (t:ZMod p) hres)=
      (TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (TwoTermDeformation.residue p) := by
    have h1 : UFMoments.blk (coreBar H s u)ᵀ H.colour (t:ZMod p)=
        (UFMoments.blk (coreBar H s u) H.colour (t:ZMod p))ᵀ := rfl
    rw [h1,← Matrix.transpose_submatrix,fibre_blk H s u t hres,← Matrix.transpose_map,fibreCore_transpose]
  have hl : (fun i:{a // H.colour a=(t:ZMod p)} => TwoTermDeformation.residue p (colSigma2 H u t i.1)) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j)) := by
    funext j
    simp only [Function.comp_apply,colSigma2]
    rw [fibre_row H (t:ZMod p) hres j,TwoTermDeformation.entry_symm]
    rcases j with j|j
    · rfl
    · simp only [Sum.elim_inr]
      rw [rowProfile_eq,pyc_flip _ _ _ _ (bit_le _)]
  have hr : (fun i:{a // H.colour a=(t:ZMod p)} =>
      TwoTermDeformation.residue p (f (Sum.elim (fun i:Fin r => (i:ℕ)) H.ys i.1))) ∘
      ⇑(fibreEquiv H (t:ZMod p) hres)=
      fun i => TwoTermDeformation.residue p (f (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i)) := by
    funext i
    simp only [Function.comp_apply]
    rw [fibre_col H (t:ZMod p) hres i]
    rcases i with i|i
    · rfl
    · simp only [Sum.elim_inr]
      rw [colProfile_eq,pxr_flip]
  rw [hblk,hl,hr]

theorem col_fibre_load (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => TwoTermDeformation.residue p (colSigma2 H u t i)) ⬝ᵥ (coreBar H s u)ᵀ⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (TwoTermDeformation.prefixColLoad p H u i))=
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ
        (fun i => TwoTermDeformation.residue p (TwoTermDeformation.constants p u*TwoTermDeformation.load p q o
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) i))) :=
  col_fibre_moment H s u hs hu huc t ht hres
    (fun a => TwoTermDeformation.constants p u*TwoTermDeformation.load p q o a)

theorem col_fibre_one (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ) (ht : t<N)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    (fun i => TwoTermDeformation.residue p (colSigma2 H u t i)) ⬝ᵥ (coreBar H s u)ᵀ⁻¹ *ᵥ 1=
      (fun j => TwoTermDeformation.residue p (TwoTermDeformation.entry p q o u t
          (Sum.elim (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) j))) ⬝ᵥ
        ((TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (TwoTermDeformation.residue p))⁻¹ *ᵥ 1 := by
  have h := col_fibre_moment H s u hs hu huc t ht hres (fun _ => (1:TwoTermDeformation.Ring p))
  simp only [map_one] at h
  exact h

/-- The transposed actual fibre stays nonsingular after reduction. -/
theorem colFibre_det_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (t : ℕ)
    (hres : ∀ i:Fin b,(WrapPrefixCoreGeometry.xs p (n:=n) r H.er (Sum.inr i):ZMod p)≠(t:ZMod p)) :
    ((TwoTermDeformation.mixedCore p q o s u (pcn p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val)) (pxr p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n) (pyc p (t:ZMod p).val (WrapJointProfile.count p r (t:ZMod p).val) (1-(WrapJointProfile.bit p r (t:ZMod p).val)) n)).map (TwoTermDeformation.residue p)).det≠0 := by
  rw [← fibreCore_transpose,Matrix.transpose_map,Matrix.det_transpose]
  exact fibreCore_det_ne H s u hs hu huc t hres

/-- Section 8.3, ACTUAL prefix binding for an outside surplus COLUMN:
its independently loaded column fibre is the actual fibre with the
complementary bit, and a separating original pole of either family makes
its actual two-parameter coupling nonzero. -/
theorem colCoupling2_ne (s u : GaussLoc p) (hs : res p s=(RatFunc.X:RatFunc (ZMod p)))
    (hu : res p u≠0) (huc : WrapConstant.Has p u) (y : Fin d) (k : ℕ)
    (hk : p∣k ∨ p∣q*k-o)
    (hsep : (WrapPrefixSchur.surplusCol H y<k ∧ k≤H.t0) ∨ (H.t0<k ∧ k≤WrapPrefixSchur.surplusCol H y))
    (hvlo : r+2*n*p≤WrapPrefixSchur.surplusCol H y)
    (hvhi : WrapPrefixSchur.surplusCol H y<r+2*n*p+p) :
    colCoupling2 H s u y≠0 := by
  have hvN : WrapPrefixSchur.surplusCol H y<N := WrapPrefixSchur.surplus_col_bound H y
  have hresv := surplus_col_not_residual H y
  unfold colCoupling2
  rw [map_sub,map_mul,residue_colMoment2 H s u hs hu huc,residue_colRef2 H s u hs hu huc,
    col_fibre_load H s u hs hu huc _ hvN hresv,col_fibre_one H s u hs hu huc _ hvN hresv]
  exact node_coupling_ne H s u hs hu huc _ k _ (by omega) hk hsep hvlo hvhi hvN
    (colFibre_det_ne H s u hs hu huc _ hresv)

end ColumnSeparation

namespace TwoTermDeformation
section TwoParameterTransport
variable (p : ℕ) [Fact p.Prime]

attribute [local instance] coefficientDomain ringDomain

/-- An ORIGINAL nonpole integer reciprocal keeps its first-order value
under the independent integer deformation, modulo the uniformizer squared. -/
theorem integer_nonpole_congr (t : ℕ) (ht : res p (t:GaussLoc p)≠0) :
    uniformizer p^2∣integerNormalized p (t:GaussLoc p)-
      constants p (WrapPole.originalNormalized p (t:GaussLoc p)) := by
  have hu : IsUnit (WrapOwnCore.constants p (t:GaussLoc p)) := (isUnit_of_res_ne _ ht).map _
  have h := originalScaledPoleInverse_nonpole_congr (WrapDeform.residue p)
    (WrapOwnCore.constants p (UFMoments.piL p)) (WrapOwnCore.constants p (t:GaussLoc p))
    (WrapOwnCore.constants p 1) hu
  rw [integerNormalized,dif_neg ht,WrapPole.originalNormalized,dif_neg ht]
  have he : constants p (UFMoments.piL p*Ring.inverse (t:GaussLoc p))=
      algebraMap (WrapDeform.Extension p)[X] (Ring p)
        (Polynomial.C (WrapOwnCore.constants p (UFMoments.piL p)*
          Ring.inverse (WrapOwnCore.constants p (t:GaussLoc p)))) := by
    have ht' : IsUnit (t:GaussLoc p) := isUnit_of_res_ne _ ht
    have hinv : WrapOwnCore.constants p (Ring.inverse (t:GaussLoc p))=
        Ring.inverse (WrapOwnCore.constants p (t:GaussLoc p)) :=
      map_ring_inverse_of_unit (WrapOwnCore.constants p) (t:GaussLoc p) ht'
    rw [← hinv,← map_mul]
    rfl
  rw [he]
  exact h

/-- Two-parameter regular increments: the coefficient image of the
one-parameter regular increment. -/
noncomputable def regular (q o t : ℕ) : Ring p := coefficient p (WrapPrefixSource.regular p q o t)

theorem delta_congr (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0) :
    uniformizer p^2∣delta p q o t-coefficient p (WrapIncrement.delta p q o t) := by
  have e1 : coefficient p (WrapIncrement.delta p q o t)=
      constants p (WrapPole.originalNormalized p (t:GaussLoc p))-
        coefficient p (WrapOwnCore.constants p (q:GaussLoc p))*
          coefficient p (WrapPole.normalizedInverse p (WrapIncrement.argument p q o t) (q:GaussLoc p)) := by
    unfold WrapIncrement.delta
    rw [map_sub,map_mul]
    rfl
  obtain ⟨z,hz⟩ := integer_nonpole_congr p t ht
  rw [e1]
  refine ⟨z,?_⟩
  unfold delta
  linear_combination hz

theorem delta_factor (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    ∃ e : Ring p,delta p q o t=uniformizer p*regular p q o t+uniformizer p^2*e := by
  obtain ⟨z,hz⟩ := delta_congr p q o t ht
  have hf := congrArg (coefficient p) (WrapPrefixSource.delta_factor p q o t ht ha)
  rw [map_mul] at hf
  refine ⟨z,?_⟩
  change delta p q o t=coefficient p (WrapDeform.uniformizer p)*regular p q o t+
    coefficient p (WrapDeform.uniformizer p)^2*z
  change delta p q o t-coefficient p (WrapIncrement.delta p q o t)=
    coefficient p (WrapDeform.uniformizer p)^2*z at hz
  unfold regular
  linear_combination hz+hf

theorem dsq_dvd (q o t : ℕ) (ht : res p (t:GaussLoc p)≠0)
    (ha : res p (WrapIncrement.argument p q o t)≠0) :
    uniformizer p^2∣dsq p q o t := by
  classical
  obtain ⟨z,hz⟩ := integer_nonpole_congr p t ht
  have h1 : constants p (WrapPole.originalNormalized p (t:GaussLoc p))=
      uniformizer p*constants p (Ring.inverse (t:GaussLoc p)) := by
    unfold WrapPole.originalNormalized
    rw [dif_neg ht,map_mul]
    rfl
  have h2 : coefficient p (WrapPole.normalizedInverse p (WrapIncrement.argument p q o t) (q:GaussLoc p))=
      uniformizer p*coefficient p (Ring.inverse
        (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p))) := by
    unfold WrapPole.normalizedInverse
    rw [dif_neg ha,map_mul]
    rfl
  have hiN : integerNormalized p (t:GaussLoc p)=
      uniformizer p*(constants p (Ring.inverse (t:GaussLoc p))+uniformizer p*z) := by
    linear_combination hz+h1
  unfold dsq
  rw [hiN,h2]
  exact ⟨(constants p (Ring.inverse (t:GaussLoc p))+uniformizer p*z)^2-
    coefficient p (WrapOwnCore.constants p ((q:GaussLoc p)^2))*
      coefficient p (Ring.inverse (WrapPole.denominator p (WrapIncrement.argument p q o t) (q:GaussLoc p)))^2,
    by ring⟩

theorem increment_congr (q o a b : ℕ) (hat : res p (a:GaussLoc p)≠0)
    (hbt : res p (b:GaussLoc p)≠0)
    (haa : res p (WrapIncrement.argument p q o a)≠0)
    (hba : res p (WrapIncrement.argument p q o b)≠0)
    (hcol : (a:ZMod p)=(b:ZMod p)) :
    uniformizer p^2∣delta p q o a-delta p q o b := by
  obtain ⟨za,hza⟩ := delta_congr p q o a hat
  obtain ⟨zb,hzb⟩ := delta_congr p q o b hbt
  obtain ⟨w,hw⟩ := WrapPrefixSource.increment_congr p q o a b hat hbt haa hba hcol
  have hw' := congrArg (coefficient p) hw
  rw [map_sub,map_mul,map_pow] at hw'
  refine ⟨za-zb+coefficient p w,?_⟩
  change _=coefficient p (WrapDeform.uniformizer p)^2*_
  change _=coefficient p (WrapDeform.uniformizer p)^2*_ at hza hzb
  linear_combination hza-hzb+hw'

theorem load_shift_congr (q o a b d : ℕ)
    (hcol : (a:ZMod p)=(b:ZMod p))
    (ha : ∀ h∈Icc 1 d,res p ((a+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (a+h))≠0)
    (hb : ∀ h∈Icc 1 d,res p ((b+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (b+h))≠0) :
    uniformizer p^2∣(load p q o (a+d)-load p q o a)-(load p q o (b+d)-load p q o b) := by
  rw [prefix_sub p q o a (a+d) (by omega),prefix_sub p q o b (b+d) (by omega),
    WrapPrefixSource.window_sum,WrapPrefixSource.window_sum,← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro h hh
  apply increment_congr p q o (a+h) (b+h) (ha h hh).1 (hb h hh).1 (ha h hh).2 (hb h hh).2
  simpa only [Nat.cast_add,hcol]

theorem diagonal_shift_congr (q o a d : ℕ) (u : GaussLoc p)
    (ha : ∀ t∈Ioc a (a+d),res p (t:GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o t)≠0) :
    uniformizer p^2∣entry p q o u (a+d) (a+d)-entry p q o u a a := by
  classical
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by
    ext t; simp only [mem_Icc,mem_Ioc]; omega
  have hs : uniformizer p^2∣∑ t∈Ioc a (a+d),dsq p q o t := by
    apply Finset.dvd_sum
    intro t ht
    exact dsq_dvd p q o t (ha t ht).1 (ha t ht).2
  obtain ⟨z,hz⟩ := hs
  refine ⟨-(coefficient p (WrapOwnCore.constants p u)*z),?_⟩
  simp only [entry,↓reduceIte,he,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) (show a≤a+d by omega)]
  rw [hz]
  ring

theorem entry_shift_congr (q o a b d : ℕ) (u : GaussLoc p)
    (hcol : (a:ZMod p)=(b:ZMod p))
    (ha : ∀ h∈Icc 1 d,res p ((a+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (a+h))≠0)
    (hb : ∀ h∈Icc 1 d,res p ((b+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (b+h))≠0) :
    uniformizer p^2∣entry p q o u (a+d) (b+d)-entry p q o u a b := by
  classical
  have hoff (a b : ℕ) (hab : a<b)
      (hs : uniformizer p^2∣(load p q o (b+d)-load p q o b)-(load p q o (a+d)-load p q o a)) :
      uniformizer p^2∣entry p q o u (a+d) (b+d)-entry p q o u a b := by
    obtain ⟨z,hz⟩ := hs
    have he : b+d-(a+d)=b-a := by omega
    simp only [entry,hab.ne,(show a+d≠b+d by omega),↓reduceIte,
      min_eq_left hab.le,max_eq_right hab.le,
      min_eq_left (show a+d≤b+d by omega),max_eq_right (show a+d≤b+d by omega),he]
    rw [← prefix_sub p q o (a+d) (b+d) (by omega),← prefix_sub p q o a b hab.le]
    refine ⟨coefficient p (WrapOwnCore.constants p u)*
      coefficient p (WrapOwnCore.constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p)))*z,?_⟩
    linear_combination coefficient p (WrapOwnCore.constants p u)*
      coefficient p (WrapOwnCore.constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p)))*hz
  rcases lt_trichotomy a b with hab|hab|hba
  · exact hoff a b hab (load_shift_congr p q o b a d hcol.symm hb ha)
  · subst b
    apply diagonal_shift_congr p q o a d u
    intro t ht
    have h : t-a∈Icc 1 d := by simp only [mem_Ioc] at ht; simp only [mem_Icc]; omega
    have he : a+(t-a)=t := by simp only [mem_Ioc] at ht; omega
    simpa only [he] using ha (t-a) h
  · rw [entry_symm p q o u (a+d) (b+d),entry_symm p q o u a b]
    exact hoff b a hba (load_shift_congr p q o a b d hcol ha hb)

theorem load_shift_factor (q o t d : ℕ) (u : GaussLoc p)
    (ht : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0) :
    ∃ e : Ring p,constants p u*(load p q o (t+d)-load p q o t)=
      uniformizer p*(constants p u*∑ h∈Icc 1 d,regular p q o (t+h))+uniformizer p^2*e := by
  classical
  rw [prefix_sub p q o t (t+d) (by omega),WrapPrefixSource.window_sum]
  have hf : ∀ h∈Icc 1 d,∃ e : Ring p,delta p q o (t+h)=uniformizer p*regular p q o (t+h)+uniformizer p^2*e :=
    fun h hh => delta_factor p q o (t+h) (ht h hh).1 (ht h hh).2
  choose! E hE using hf
  refine ⟨constants p u*∑ h∈Icc 1 d,E h,?_⟩
  rw [Finset.sum_congr rfl hE,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  ring

set_option maxHeartbeats 1000000 in
/-- Two-parameter own-block transport across a regular window: the
two-parameter congruences replace the one-parameter exact load step. -/
theorem actual_own_transport {α : Type*} [Fintype α] [DecidableEq α]
    (q o t d : ℕ) (u : GaussLoc p) (rows cols : α → ℕ)
    (P : Matrix α α (Ring p))
    (hr : ∀ i,(rows i:ZMod p)=(t:ZMod p))
    (hc : ∀ i,(cols i:ZMod p)=(t:ZMod p))
    (ht : ∀ h∈Icc 1 d,res p ((t+h:ℕ):GaussLoc p)≠0 ∧
      res p (WrapIncrement.argument p q o (t+h))≠0)
    (Q0 Q1 : Matrix α α (Ring p))
    (h0 : ∀ i j,Q0 i j=entry p q o u (rows i) (cols j)+P i j)
    (h1 : ∀ i j,Q1 i j=entry p q o u (rows i+d) (cols j+d)+P i j)
    (hQ0 : IsUnit Q0.det) (hQ1 : IsUnit Q1.det) (direction : Ring p)
    (hz : (constants p u*load p q o t-direction)-
      (fun i => entry p q o u t (cols i)) ⬝ᵥ Q0⁻¹ *ᵥ
        (fun i => constants p u*load p q o (rows i)-direction)=0) :
    ∃ e : Ring p,
      (constants p u*load p q o (t+d)-direction)-
        (fun i => entry p q o u (t+d) (cols i+d)) ⬝ᵥ Q1⁻¹ *ᵥ
          (fun i => constants p u*load p q o (rows i+d)-direction)=
      (constants p u*∑ h∈Icc 1 d,regular p q o (t+h))*
        (1-∑ i,((fun j => entry p q o u t (cols j)) ᵥ* Q0⁻¹) i)*
          uniformizer p+uniformizer p^2*e := by
  classical
  have hw (a : ℕ) (hcol : (a:ZMod p)=(t:ZMod p)) :=
    WrapPrefixSource.regular_window_of_colour p q o a t d hcol ht
  have hd : ∀ i j,∃ z,Q1 i j=Q0 i j+uniformizer p^2*z := by
    intro i j
    obtain ⟨z,hz⟩ := entry_shift_congr p q o (rows i) (cols j) d u
      ((hr i).trans (hc j).symm) (hw _ (hr i)) (hw _ (hc j))
    refine ⟨z,?_⟩
    rw [h1,h0]
    linear_combination hz
  have hs : ∀ i,∃ z,entry p q o u (t+d) (cols i+d)=entry p q o u t (cols i)+uniformizer p^2*z := by
    intro i
    obtain ⟨z,hz⟩ := entry_shift_congr p q o t (cols i) d u (hc i).symm ht (hw _ (hc i))
    exact ⟨z,sub_eq_iff_eq_add.mp hz |>.trans (add_comm _ _)⟩
  let step := constants p u*(load p q o (t+d)-load p q o t)
  have hl : ∀ i,∃ z,constants p u*load p q o (rows i+d)=
      constants p u*load p q o (rows i)+step+uniformizer p^2*z := by
    intro i
    obtain ⟨z,hz⟩ := load_shift_congr p q o (rows i) t d (hr i) (hw _ (hr i)) ht
    refine ⟨constants p u*z,?_⟩
    dsimp only [step]
    linear_combination constants p u*hz
  choose ED hED using hd
  choose es hes using hs
  choose el hel using hl
  have hm : Q1=Q0+uniformizer p^2 • Matrix.of ED := by
    ext i j
    exact hED i j
  have hsig : (fun i => entry p q o u (t+d) (cols i+d))=
      (fun i => entry p q o u t (cols i))+uniformizer p^2 • es := by
    funext i
    exact hes i
  have hunit : IsUnit (Q0+uniformizer p^2 • Matrix.of ED).det := by
    rw [← hm]; exact hQ1
  obtain ⟨e,he⟩ := own_shift (uniformizer p) Q0 (Matrix.of ED) hQ0 hunit
    (fun i => entry p q o u t (cols i)) es
    (fun i => constants p u*load p q o (rows i)) el
    (constants p u*load p q o t) 0 direction step
  obtain ⟨e0,he0⟩ := load_shift_factor p q o t d u ht
  refine ⟨e+e0*(1-∑ i,((fun j => entry p q o u t (cols j)) ᵥ* Q0⁻¹) i),?_⟩
  have htload : constants p u*load p q o (t+d)=constants p u*load p q o t+step := by dsimp only [step]; ring
  rw [htload,hm,hsig,Matrix.dotProduct_mulVec,dotProduct]
  simp_rw [hel]
  rw [dotProduct_mulVec,dotProduct] at hz
  simp only [mul_zero,add_zero] at he
  rw [hz] at he
  rw [he,zero_add]
  dsimp only [step]
  rw [he0]
  ring

end TwoParameterTransport
end TwoTermDeformation

namespace TwoTermDeformation
section TwoParameterSource
variable (p : ℕ) [Fact p.Prime]

attribute [local instance] coefficientDomain ringDomain

/-- Residue-field image of an original colour. -/
noncomputable def residueNode : ZMod p →+* Residue p :=
  (RatFunc.C:WrapPoleResidue.Residue p →+* Residue p).comp
    ((RatFunc.C:RatFunc (ZMod p) →+* WrapPoleResidue.Residue p).comp RatFunc.C)

theorem residueNode_injective : Function.Injective (residueNode p) :=
  RatFunc.C_injective.comp (RatFunc.C_injective.comp RatFunc.C_injective)

theorem residueNode_nat (a : ℕ) : residueNode p (a:ZMod p)=(a:Residue p) := map_natCast _ a

theorem residue_zero_iff (a : Ring p) : residue p a=0 ↔ uniformizer p∣a :=
  WrapParameter.residue_zero_iff (WrapDeform.residue p) (WrapDeform.uniformizer p)
    (WrapDeform.residue_zero_iff p) a

theorem unit_of_residue_ne (a : Ring p) (h : residue p a≠0) : IsUnit a :=
  WrapUnits.of_residue_ne (R:=WrapDeform.Extension p) (K:=WrapPoleResidue.Residue p)
    (WrapDeform.residue p) a h

theorem residue_pi : residue p (uniformizer p)=0 := (residue_zero_iff p _).mpr (dvd_refl _)

theorem uniformizer_ne : uniformizer p≠0 := (parameterPrime p).ne_zero

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem split (col : ι → ZMod p) (Q : Matrix ι ι (Ring p))
    (hzero : ∀ i j,col i≠col j → residue p (Q i j)=0) :
    ∃ E : Matrix ι ι (Ring p),Q=own p col Q+uniformizer p • E ∧
      (∀ i j,col i=col j → E i j=0) := by
  classical
  have hz : ∀ i j,uniformizer p∣Q i j-own p col Q i j := by
    intro i j
    apply (residue_zero_iff p _).mp
    by_cases h : col i=col j
    · simp only [own,Matrix.of_apply,if_pos h,sub_self,map_zero]
    · simp only [own,Matrix.of_apply,if_neg h,sub_zero]
      exact hzero i j h
  choose E hE using hz
  refine ⟨Matrix.of E,?_,?_⟩
  · ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
    exact sub_eq_iff_eq_add.mp (hE i j) |>.trans (add_comm _ _)
  · intro i j hij
    have he := hE i j
    simp only [own,Matrix.of_apply,if_pos hij,sub_self] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (uniformizer_ne p)

theorem own_unit (col : ι → ZMod p) (Q : Matrix ι ι (Ring p)) (hQ : IsUnit Q.det)
    (hzero : ∀ i j,col i≠col j → residue p (Q i j)=0) :
    IsUnit (own p col Q).det := by
  classical
  have he : (own p col Q).map (residue p)=Q.map (residue p) := by
    ext i j
    by_cases h : col i=col j
    · simp only [Matrix.map_apply,own,Matrix.of_apply,if_pos h]
    · simp only [Matrix.map_apply,own,Matrix.of_apply,if_neg h,map_zero,hzero i j h]
  apply unit_of_residue_ne p
  have hh := (hQ.map (residue p)).ne_zero
  rw [RingHom.map_det] at hh ⊢
  change ((own p col Q).map (residue p)).det≠0
  rw [he]
  exact hh

theorem cross_residue (col : ι → ZMod p) (Q E : Matrix ι ι (Ring p))
    (hQE : Q=own p col Q+uniformizer p • E)
    (xi : Matrix ι ι (Ring p)) (yR yC : ι → Ring p)
    (hdisp : ∀ i j,xi i j*Q i j=uniformizer p*(yC j-yR i))
    (hxi : ∀ i j,residue p (xi i j)=residueNode p (col j)-residueNode p (col i))
    (i j : ι) (hcol : col i≠col j) :
    residue p (E i j)=(residue p (yC j)-residue p (yR i))/
      (residueNode p (col j)-residueNode p (col i)) := by
  classical
  have he : Q i j=uniformizer p*E i j := by
    rw [hQE]
    simp only [Matrix.add_apply,own,Matrix.of_apply,if_neg hcol,zero_add,
      Matrix.smul_apply,smul_eq_mul]
  have hd := hdisp i j
  rw [he] at hd
  have hc : xi i j*E i j=yC j-yR i := by
    apply mul_left_cancel₀ (uniformizer_ne p)
    calc
      _=xi i j*(uniformizer p*E i j) := by ring
      _=_ := hd
  have hh := congrArg (residue p) hc
  rw [map_mul,hxi,map_sub] at hh
  have hden : residueNode p (col j)-residueNode p (col i)≠0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hcol ((residueNode_injective p heq).symm)
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using hh

theorem nat_residue_ne (a b : ℕ) (h : (a:ZMod p)≠(b:ZMod p)) :
    (a:Residue p)-(b:Residue p)≠0 := by
  intro hz
  apply h
  apply residueNode_injective p
  simpa only [residueNode_nat] using sub_eq_zero.mp hz

set_option maxHeartbeats 1000000 in
theorem entry_source (q o N a b : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (ha : a<N) (hb : b<N) (hcol : (a:ZMod p)≠(b:ZMod p)) :
    ∃ e : Ring p,entry p q o u a b=uniformizer p*e ∧
      residue p e=(residue p (constants p u*load p q o b)-residue p (constants p u*load p q o a))/
        ((b:Residue p)-(a:Residue p)) := by
  have hd := commutator p q o N u hN a b ha hb
  have hne := nat_residue_ne p b a (Ne.symm hcol)
  have hz : residue p (entry p q o u a b)=0 := by
    have h := congrArg (residue p) hd
    rw [map_mul,map_mul,residue_pi,zero_mul,map_sub,map_natCast,map_natCast] at h
    exact (mul_eq_zero.mp h).resolve_left hne
  obtain ⟨e,he⟩ := (residue_zero_iff p _).mp hz
  refine ⟨e,he,?_⟩
  rw [he] at hd
  have hc : ((b:Ring p)-(a:Ring p))*e=constants p u*load p q o b-constants p u*load p q o a := by
    apply mul_left_cancel₀ (uniformizer_ne p)
    linear_combination hd
  have hh := congrArg (residue p) hc
  simp only [map_mul,map_sub,map_natCast] at hh
  apply (eq_div_iff hne).mpr
  simpa only [map_mul,mul_comm] using hh

section Core
variable {β : Type} [Fintype β] [DecidableEq β]

set_option maxHeartbeats 1000000 in
theorem core_cross_residue (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (i j : ι ⊕ β)
    (hij : WrapFibreIndex.colour p c xs i≠WrapFibreIndex.colour p c xs j) :
    residue p (mixedCore p q o s u c xs ys i j)=0 := by
  have hcc : ((Sum.elim c ys j:ℕ):ZMod p)=WrapFibreIndex.colour p c xs j := by
    cases j with
    | inl j => rfl
    | inr j => exact (hcol j).symm
  have hrr : ((Sum.elim c xs i:ℕ):ZMod p)=WrapFibreIndex.colour p c xs i := by cases i <;> rfl
  have h := congrArg (residue p) (mixedCore_commutator p q o N hN s u c xs ys hc hx hy i j)
  rw [map_mul,map_mul,residue_pi,zero_mul,map_sub,map_natCast,map_natCast] at h
  have hne := nat_residue_ne p (Sum.elim c ys j) (Sum.elim c xs i) (by rw [hcc,hrr]; exact Ne.symm hij)
  exact (mul_eq_zero.mp h).resolve_left hne

set_option maxHeartbeats 1000000 in
theorem actual_core_source (q o N : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (mixedCore p q o s u c xs ys).det) :
    ∃ E : Matrix (ι ⊕ β) (ι ⊕ β) (Ring p),
      mixedCore p q o s u c xs ys=own p (WrapFibreIndex.colour p c xs) (mixedCore p q o s u c xs ys)+
        uniformizer p • E ∧
      IsUnit (own p (WrapFibreIndex.colour p c xs) (mixedCore p q o s u c xs ys)).det ∧
      (∀ i j,WrapFibreIndex.colour p c xs i=WrapFibreIndex.colour p c xs j → E i j=0) ∧
      (∀ i j,WrapFibreIndex.colour p c xs i≠WrapFibreIndex.colour p c xs j →
        residue p (E i j)=
          (residue p (constants p u*load p q o (Sum.elim c ys j))-
            residue p (constants p u*load p q o (Sum.elim c xs i)))/
          (residueNode p (WrapFibreIndex.colour p c xs j)-residueNode p (WrapFibreIndex.colour p c xs i))) := by
  classical
  let Q := mixedCore p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  have hz : ∀ i j,col i≠col j → residue p (Q i j)=0 :=
    fun i j hij => core_cross_residue p q o N s u c xs ys hN hc hx hy hcol i j hij
  obtain ⟨E,hE,hE0⟩ := split p col Q hz
  refine ⟨E,hE,own_unit p col Q hQ hz,hE0,?_⟩
  intro i j hij
  apply cross_residue p col Q E hE
    (Matrix.of fun i j => ((Sum.elim c ys j:ℕ):Ring p)-((Sum.elim c xs i:ℕ):Ring p))
    (fun i => constants p u*load p q o (Sum.elim c xs i))
    (fun i => constants p u*load p q o (Sum.elim c ys i))
    (fun i j => by
      simpa only [Matrix.of_apply,mul_sub] using mixedCore_commutator p q o N hN s u c xs ys hc hx hy i j) ?_ i j hij
  intro a b
  have hr : ((Sum.elim c xs a:ℕ):ZMod p)=col a := by cases a <;> rfl
  have hcc : ((Sum.elim c ys b:ℕ):ZMod p)=col b := by
    cases b with
    | inl b => rfl
    | inr b => exact (hcol b).symm
  simp only [Matrix.of_apply,map_sub,map_natCast,← residueNode_nat,hr,hcc]

end Core

theorem actual_border_source {α : Type*} [Fintype α] [DecidableEq α]
    (q o N t : ℕ) (u : GaussLoc p) (cols : α → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,cols i<N) :
    ∃ e : α → Ring p,
      (fun i => entry p q o u t (cols i))=
        (fun i => if (cols i:ZMod p)=(t:ZMod p) then entry p q o u t (cols i) else 0)+uniformizer p • e ∧
      (∀ i,(cols i:ZMod p)=(t:ZMod p) → e i=0) ∧
      (∀ i,(cols i:ZMod p)≠(t:ZMod p) → residue p (e i)=
        (residue p (constants p u*load p q o (cols i))-residue p (constants p u*load p q o t))/
          ((cols i:Residue p)-(t:Residue p))) := by
  classical
  have hs : ∀ i,∃ e : Ring p,
      entry p q o u t (cols i)=(if (cols i:ZMod p)=(t:ZMod p) then entry p q o u t (cols i) else 0)+
        uniformizer p*e ∧
      ((cols i:ZMod p)=(t:ZMod p) → e=0) ∧
      ((cols i:ZMod p)≠(t:ZMod p) → residue p e=
        (residue p (constants p u*load p q o (cols i))-residue p (constants p u*load p q o t))/
          ((cols i:Residue p)-(t:Residue p))) := by
    intro i
    by_cases he : (cols i:ZMod p)=(t:ZMod p)
    · exact ⟨0,by simp only [he,↓reduceIte,mul_zero,add_zero],fun _ => rfl,fun hn => False.elim (hn he)⟩
    · obtain ⟨e,heq,her⟩ := entry_source p q o N t (cols i) u hN ht (hc i) (Ne.symm he)
      refine ⟨e,?_,fun hh => False.elim (he hh),fun _ => her⟩
      simpa only [if_neg he,zero_add] using heq
  choose e he he0 her using hs
  refine ⟨e,?_,he0,her⟩
  funext i
  exact he i

section Node
variable {β : Type} [Fintype β] [DecidableEq β]

set_option maxHeartbeats 1000000 in
theorem actual_node_source (q o N t : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (mixedCore p q o s u c xs ys).det)
    (direction G1 : Ring p) :
    let Q := mixedCore p q o s u c xs ys
    let col := WrapFibreIndex.colour p c xs
    let D := own p col Q
    let sig := fun i => entry p q o u t (Sum.elim c ys i)
    let sigOwn := fun i => if col i=(t:ZMod p) then sig i else 0
    let yR := fun i => constants p u*load p q o (Sum.elim c xs i)-direction
    let yC := fun i => constants p u*load p q o (Sum.elim c ys i)-direction
    let yt := constants p u*load p q o t-direction
    yt-(sigOwn ᵥ* D⁻¹) ⬝ᵥ yR=uniformizer p*G1 →
      ∃ Bk Rem : Ring p,
        yt-sig ⬝ᵥ Q⁻¹ *ᵥ yR=uniformizer p*(G1-Bk+uniformizer p*Rem) ∧
        residue p Bk=residue p (1-∑ j,(sigOwn ᵥ* D⁻¹) j)*
          ∑ colour : ZMod p,if colour=(t:ZMod p) then 0 else
            (∑ a∈univ.filter (fun a => col a=colour),
              residue p ((D⁻¹ *ᵥ yR) a)*residue p (yC a))/
                (residueNode p colour-residueNode p (t:ZMod p)) := by
  classical
  let Q := mixedCore p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  let D := own p col Q
  let sig : ι ⊕ β → Ring p := fun i => entry p q o u t (Sum.elim c ys i)
  let sigOwn : ι ⊕ β → Ring p := fun i => if col i=(t:ZMod p) then sig i else 0
  let yR : ι ⊕ β → Ring p := fun i => constants p u*load p q o (Sum.elim c xs i)-direction
  let yC : ι ⊕ β → Ring p := fun i => constants p u*load p q o (Sum.elim c ys i)-direction
  let yt := constants p u*load p q o t-direction
  change yt-(sigOwn ᵥ* D⁻¹) ⬝ᵥ yR=uniformizer p*G1 → _
  intro hG
  obtain ⟨E,hQE,hD,hE0,hE⟩ := actual_core_source p q o N s u c xs ys hN hc hx hy hcol hQ
  have hcols (i : ι ⊕ β) : ((Sum.elim c ys i:ℕ):ZMod p)=col i := by
    cases i with
    | inl i => rfl
    | inr i => exact (hcol i).symm
  have hcolN : ∀ i:ι ⊕ β,Sum.elim c ys i<N := by
    intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hy i
  obtain ⟨sp,hsp,hsp0,hspr⟩ := actual_border_source p q o N t u (Sum.elim c ys) hN ht hcolN
  have hsplit : sig=sigOwn+uniformizer p • sp := by
    simpa only [hcols] using hsp
  have hxsolve : D *ᵥ (Q⁻¹ *ᵥ yR)+uniformizer p • (E *ᵥ (Q⁻¹ *ᵥ yR))=yR := by
    rw [← Matrix.smul_mulVec,← Matrix.add_mulVec,← hQE,
      Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hQ,Matrix.one_mulVec]
  have hDb : ∀ a b,col a≠col b → D a b=0 := by
    intro a b hab
    exact if_neg hab
  have hs0 : ∀ a,col a≠(t:ZMod p) → sigOwn a=0 := by
    intro a ha
    exact if_neg ha
  have hspr' : ∀ a,col a≠(t:ZMod p) → residue p (sp a)=
      (residue p (yC a)-residue p yt)/(residueNode p (col a)-residueNode p (t:ZMod p)) := by
    intro a ha
    have hh := hspr a (by rw [hcols]; exact ha)
    have heq : ((Sum.elim c ys a:ℕ):Residue p)=residueNode p (col a) := by
      rw [← hcols,residueNode_nat]
    rw [heq,← residueNode_nat p t] at hh
    dsimp only [yC,yt]
    rw [map_sub,map_sub,sub_sub_sub_cancel_right]
    exact hh
  have hE' : ∀ a b,col a≠col b → residue p (E a b)=
      (residue p (yC b)-residue p (yR a))/(residueNode p (col b)-residueNode p (col a)) := by
    intro a b hab
    dsimp only [yC,yR]
    rw [map_sub,map_sub,sub_sub_sub_cancel_right]
    exact hE a b hab
  obtain ⟨Bk,Rem,hm,hr⟩ := WrapMoments.mixed_phi2_expansion (uniformizer p)
    (residue p) (residue_pi p) (residueNode p) (residueNode_injective p) col (t:ZMod p) D E hD hDb yR yC yt hE0 hE'
    sigOwn sp hs0 (fun a ha => hsp0 a (by rw [hcols]; exact ha)) hspr'
    (Q⁻¹ *ᵥ yR) hxsolve G1 hG
  refine ⟨Bk,Rem,?_,hr⟩
  rw [← hsplit] at hm
  exact hm

end Node

theorem normalized_response {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Matrix α α (Ring p)) (sigma y : α → Ring p) (yt direction W : Ring p)
    (hunit : IsUnit (1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1))
    (hm : (yt-direction)-sigma ⬝ᵥ Q⁻¹ *ᵥ (fun i => y i-direction)=uniformizer p*W) :
    ∃ F : Ring p,
      yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*(1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1)+
        uniformizer p*((1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1)*F) ∧
      residue p F=residue p W/residue p (1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1) := by
  let A := 1-sigma ⬝ᵥ Q⁻¹ *ᵥ 1
  have hv : (fun i => y i-direction)=y-direction • (1:α → Ring p) := by
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]
  rw [hv,Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,dotProduct_smul] at hm
  simp only [smul_eq_mul] at hm
  have he : yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*A+uniformizer p*W := by
    dsimp only [A]
    linear_combination hm
  have hi : A*Ring.inverse A=1 := Ring.mul_inverse_cancel A hunit
  refine ⟨W*Ring.inverse A,?_,?_⟩
  · change yt-sigma ⬝ᵥ Q⁻¹ *ᵥ y=direction*A+uniformizer p*(A*(W*Ring.inverse A))
    rw [he]
    have hc : A*(W*Ring.inverse A)=W := by
      calc
        _=W*(A*Ring.inverse A) := by ring
        _=W := by rw [hi,mul_one]
    rw [hc]
  · rw [map_mul,rational_map_inverse (residue p) A hunit,div_eq_mul_inv]

section Normalized
variable {β : Type} [Fintype β] [DecidableEq β]

set_option maxHeartbeats 1000000 in
/-- Two-parameter normalized source of an ACTUAL original prefix node:
the transported own coefficient plus all cross-colour corrections. -/
theorem actual_normalized_source (q o N t : ℕ) (s u : GaussLoc p) (c : ι → ℕ) (xs ys : β → ℕ)
    (hN : N<p*p) (ht : t<N) (hc : ∀ i,c i<N) (hx : ∀ i,xs i<N) (hy : ∀ i,ys i<N)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hQ : IsUnit (mixedCore p q o s u c xs ys).det)
    (direction G1 : Ring p) (K0 : Residue p) :
    let Q := mixedCore p q o s u c xs ys
    let col := WrapFibreIndex.colour p c xs
    let D := own p col Q
    let sig := fun i => entry p q o u t (Sum.elim c ys i)
    let sigOwn := fun i => if col i=(t:ZMod p) then sig i else 0
    let LR := fun i => constants p u*load p q o (Sum.elim c xs i)
    let LC := fun i => constants p u*load p q o (Sum.elim c ys i)
    let Lt := constants p u*load p q o t
    let B := 1-∑ j,(sigOwn ᵥ* D⁻¹) j
    (Lt-direction)-(sigOwn ᵥ* D⁻¹) ⬝ᵥ (fun i => LR i-direction)=uniformizer p*G1 →
    residue p G1=K0*residue p B → residue p B≠0 →
    ∃ F : Ring p,
      Lt-sig ⬝ᵥ Q⁻¹ *ᵥ LR=direction*(1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)+
        uniformizer p*((1-sig ⬝ᵥ Q⁻¹ *ᵥ 1)*F) ∧
      residue p F=K0-
        ∑ colour : ZMod p,if colour=(t:ZMod p) then 0 else
          (∑ a∈univ.filter (fun a => col a=colour),
            residue p ((D⁻¹ *ᵥ (fun i => LR i-direction)) a)*residue p (LC a-direction))/
              (residueNode p colour-residueNode p (t:ZMod p)) := by
  classical
  let Q := mixedCore p q o s u c xs ys
  let col := WrapFibreIndex.colour p c xs
  let D := own p col Q
  let sig : ι ⊕ β → Ring p := fun i => entry p q o u t (Sum.elim c ys i)
  let sigOwn : ι ⊕ β → Ring p := fun i => if col i=(t:ZMod p) then sig i else 0
  let LR : ι ⊕ β → Ring p := fun i => constants p u*load p q o (Sum.elim c xs i)
  let LC : ι ⊕ β → Ring p := fun i => constants p u*load p q o (Sum.elim c ys i)
  let Lt := constants p u*load p q o t
  let B := 1-∑ j,(sigOwn ᵥ* D⁻¹) j
  change (Lt-direction)-(sigOwn ᵥ* D⁻¹) ⬝ᵥ (fun i => LR i-direction)=uniformizer p*G1 →
    residue p G1=K0*residue p B → residue p B≠0 → _
  intro hG hGres hB
  obtain ⟨Bk,Rem,hm,hBk⟩ := actual_node_source p q o N t s u c xs ys
    hN ht hc hx hy hcol hQ direction G1 hG
  obtain ⟨E,hQE,hD,hE0,hE⟩ := actual_core_source p q o N s u c xs ys hN hc hx hy hcol hQ
  have hmap : Q.map (residue p)=D.map (residue p) := by
    ext i j
    have he := congrArg (fun M : Matrix (ι ⊕ β) (ι ⊕ β) (Ring p) => residue p (M i j)) hQE
    simpa only [Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      map_add,map_mul,residue_pi,zero_mul,add_zero] using he
  have hcols (i : ι ⊕ β) : ((Sum.elim c ys i:ℕ):ZMod p)=col i := by
    cases i with
    | inl i => rfl
    | inr i => exact (hcol i).symm
  have hcolN : ∀ i:ι ⊕ β,Sum.elim c ys i<N := by
    intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hy i
  obtain ⟨sp,hsp,hsp0,hspr⟩ := actual_border_source p q o N t u (Sum.elim c ys) hN ht hcolN
  have hsplit : sig=sigOwn+uniformizer p • sp := by simpa only [hcols] using hsp
  have hsig : ∀ i,residue p (sig i)=residue p (sigOwn i) := by
    intro i
    have he := congrArg (fun v : ι ⊕ β → Ring p => residue p (v i)) hsplit
    simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,residue_pi,zero_mul,add_zero] using he
  have hA := WrapPrefixType.reference_map_congr (residue p) Q D hQ hD sig sigOwn hmap hsig
  have hBref : 1-sigOwn ⬝ᵥ D⁻¹ *ᵥ 1=B := by
    rw [dotProduct_mulVec,dotProduct]
    simp only [Pi.one_apply,mul_one]
    rfl
  rw [hBref] at hA
  have hunit : IsUnit (1-sig ⬝ᵥ Q⁻¹ *ᵥ 1) :=
    unit_of_residue_ne p _ (by rw [hA]; exact hB)
  obtain ⟨F,hF,hr⟩ := normalized_response p Q sig LR Lt direction (G1-Bk+uniformizer p*Rem) hunit hm
  refine ⟨F,hF,?_⟩
  rw [hr,map_add,map_sub,map_mul,residue_pi,zero_mul,add_zero,hGres,hBk,hA]
  field_simp [hB]
  <;> ring

end Normalized

end TwoParameterSource
end TwoTermDeformation





#print axioms spectral_top_domain
#print axioms stepBordered_zero
#print axioms stepBordered_one
#print axioms scaled_cross_ne
#print axioms embedB_clearedEntry
#print axioms embedP_injective
#print axioms residue_cross_ne
#print axioms profile_separation
#print axioms ringSystem_reindex
#print axioms residue_anchor
#print axioms coupling_cross
#print axioms rowCoupling2_ne
#print axioms colCoupling2_ne
#print axioms TwoTermDeformation.actual_own_transport
#print axioms TwoTermDeformation.actual_normalized_source
#print axioms shared_moments2
#print axioms residue_ringSystem_det

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixClosed

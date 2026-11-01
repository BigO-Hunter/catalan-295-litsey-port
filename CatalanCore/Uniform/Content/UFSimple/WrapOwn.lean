module

public import CatalanCore.Uniform.Content.UFSimple.WrapDeletion
public import CatalanCore.Uniform.Content.UFSimple.WrapActual
public import CatalanCore.Uniform.Content.UFSimple.WrapBalanced

@[expose] public section

/-! # Divided Loewner relations on an original common colour fibre -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwn

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- Same-colour integer nodes differ by p times their quotient difference. -/
theorem nd_quotient (a b : ℕ) (h : (a : ZMod p)=(b : ZMod p)) :
    nd p b-nd p a=C (p : LocRing p)*(nd p (b/p)-nd p (a/p)) := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  have he : b+p*(a/p)=a+p*(b/p) := by
    have ha := Nat.mod_add_div a p
    have hb := Nat.mod_add_div b p
    omega
  have hh := congrArg (fun n : ℕ => (n : LocRing p)) he
  push_cast at hh
  unfold nd
  rw [← C_sub,← C_sub,← C_mul]
  congr 1
  linear_combination hh

theorem piL_ne : UFMoments.piL p≠0 := by
  intro h
  have hh := algebraMap_injective p (h.trans (map_zero _).symm)
  exact (Polynomial.prime_C_iff.2 (prime_p p)).ne_zero hh


/-- Cancel the uniformizer in the original entry commutator on one
colour fibre. The quotient nodes, rather than the vanishing residues,
are the Loewner coordinates after division. -/
theorem divided_relation (D : PoleData Fr p N) {a b : ℕ} (ha : a<N) (hb : b<N)
    (hab : (a : ZMod p)=(b : ZMod p)) (Q : (LocRing p)[X])
    (hQ : nL p Fr*(nd p b-nd p a)*Q=PF p Fr b-PF p Fr a) :
    (ndL p (b/p)-ndL p (a/p))*algebraMap _ (GaussLoc p) Q=
      ellL p Fr b-ellL p Fr a := by
  have h := congrArg (algebraMap (LocRing p)[X] (GaussLoc p)) hQ
  rw [nd_quotient a b hab,PF_eq D hb,PF_eq D ha] at h
  simp only [map_mul,map_sub,algebraMap_PF1 D] at h
  change algebraMap _ (GaussLoc p) (nL p Fr)*
    (UFMoments.piL p*(ndL p (b/p)-ndL p (a/p)))*algebraMap _ (GaussLoc p) Q=
      UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*ellL p Fr b)-
      UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*ellL p Fr a) at h
  have hn : algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr)≠0 :=
    (isUnit_nL D).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (piL_ne (p:=p)) hn)
  convert h using 1 <;> ring

/-- The divided relation holds for every original common-fibre entry,
including its spectral diagonal. -/
theorem common_relation {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : PoleData Fr p N) (hN : N<p*p) (c : ι → ℕ) (hc : ∀ i,c i<N)
    (hcol : ∀ i j,(c i : ZMod p)=(c j : ZMod p)) (i j : ι) :
    (ndL p (c j/p)-ndL p (c i/p))*
      algebraMap _ (GaussLoc p) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c i j)=
      ellL p Fr (c j)-ellL p Fr (c i) := by
  apply divided_relation D (hc i) (hc j) (hcol i j)
  by_cases hij : i=j
  · subst j; simp
  · have hm := D.square_mem hN (hc i) (hc j)
    have hh := const_commutator D (hc i) (hc j) hm
    have he : Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn (c i) (c j))=⟨_,hm⟩ :=
      Subtype.ext (Hybrid.liftQ_val hm)
    simpa [WrapBalanced.commonLift,Matrix.one_apply,hij,he] using hh

/-- The same divided relation holds for an original border load. -/
theorem border_relation {ι : Type} (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (t : ℕ) (ht : t<N)
    (hcol : ∀ i,(t : ZMod p)=(c i : ZMod p)) (i : ι) :
    (ndL p (c i/p)-ndL p (t/p))*
      algebraMap _ (GaussLoc p) (loewRow p Fr c t i)=
      ellL p Fr (c i)-ellL p Fr t := by
  apply divided_relation D ht (hc i) (hcol i)
  have hm := D.square_mem hN ht (hc i)
  have hh := const_commutator D ht (hc i) hm
  have he : Hybrid.liftQ p ((p:ℚ)^2*Fr.Mn t (c i))=⟨_,hm⟩ :=
    Subtype.ext (Hybrid.liftQ_val hm)
  simpa [loewRow,he] using hh

/-- Distinct same-colour nodes below p squared have distinct quotient
colours, so their divided node difference is a residue unit. -/
theorem quotient_residue_ne {a b : ℕ} (ha : a<p*p) (hb : b<p*p)
    (hab : a≠b) (hcol : (a : ZMod p)=(b : ZMod p)) :
    res p (ndL p (a/p)-ndL p (b/p))≠0 := by
  rw [res_ndL_sub,← map_sub]
  intro h
  have he : (a/p : ℕ)%p=(b/p : ℕ)%p :=
    (ZMod.natCast_eq_natCast_iff' (a/p) (b/p) p).mp
      (sub_eq_zero.mp (rfH_injective (by rw [h,map_zero])))
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hqa : a/p<p := (Nat.div_lt_iff_lt_mul hp).2 ha
  have hqb : b/p<p := (Nat.div_lt_iff_lt_mul hp).2 hb
  rw [Nat.mod_eq_of_lt hqa,Nat.mod_eq_of_lt hqb] at he
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp hcol
  have hda := Nat.mod_add_div a p
  have hdb := Nat.mod_add_div b p
  rw [he] at hda
  exact hab (by omega)

section OneDeletion

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-- The original common response is unchanged by one common deletion
whenever full and deleted own moments vanish in the same direction.
All Loewner, inverse and nonzero-coordinate hypotheses are discharged
from the original frame and its single-level bounds. -/
theorem single_common_moment (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι ⊕ Unit → ℕ) (hc : ∀ i,c i<N) (t : ℕ) (ht : t<N)
    (hcol : ∀ i,colOf (p:=p) c i=(t : ZMod p)) (hne : c (Sum.inr ())≠t)
    (d : GaussLoc p)
    (hfull : res p ((ellL p Fr t-d)-
      (fun i => algebraMap _ (GaussLoc p) (loewRow p Fr c t i)) ⬝ᵥ
        (((WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun i => ellL p Fr (c i)-d))=0)
    (hminor : res p ((ellL p Fr t-d)-
      (fun i => algebraMap _ (GaussLoc p) (loewRow p Fr (fun i => c (Sum.inl i)) t i)) ⬝ᵥ
        (((WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun i => c (Sum.inl i))).map
          (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ fun i => ellL p Fr (c (Sum.inl i))-d))=0) :
    res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr) c d)=
      res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr) (fun i => c (Sum.inl i)) d) := by
  let Q := (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))
  let Qs := (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (fun i => c (Sum.inl i))).map
    (algebraMap _ (GaussLoc p))
  let sigma := fun i => algebraMap (LocRing p)[X] (GaussLoc p) (loewRow p Fr c t i)
  have hQu : IsUnit Q.det := WrapBalanced.commonLift_isUnit D hN c hc
  have hQsu : IsUnit Qs.det := WrapBalanced.commonLift_isUnit D hN _ (fun i => hc (Sum.inl i))
  have hblock : Q.toBlocks₁₁=Qs := by
    apply Matrix.ext; intro i j
    simp [Q,Qs,WrapBalanced.commonLift,Matrix.toBlocks₁₁,Matrix.one_apply]
  have hsym : Qᵀ=Q := by
    rw [show Q=(WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)) from rfl,
      ← Matrix.transpose_map,WrapBalanced.commonLift_symm]
  have hDm : Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)=Q := by
    apply Matrix.ext; intro i j
    simp only [Dmat,Matrix.of_apply,hcol i,hcol j,↓reduceIte]
    rfl
  have hsOwn : sOwn c t (loewRow p Fr c t)=sigma := by
    funext i; simp only [sOwn,hcol i,↓reduceIte]; rfl
  have hBu := WrapBalanced.commonLift_own_unit D hN c hc t ht
  rw [hDm,hsOwn,← Matrix.mulVec_transpose,Matrix.transpose_nonsing_inv,hsym] at hBu
  have hB : 1-∑ i,(((Q.map (res p))⁻¹) *ᵥ fun i => res p (sigma i)) i≠0 := by
    have hh := (hBu.map (res p)).ne_zero
    simpa only [map_sub,map_one,map_sum,RingHom.map_mulVec,← map_inv_of_unit (res p) Q hQu,
      Function.comp_def] using hh
  have hf : (fun i => res p (sigma i)) ⬝ᵥ ((Q.map (res p))⁻¹ *ᵥ
      fun i => res p (ellL p Fr (c i))-res p d)=res p (ellL p Fr t)-res p d := by
    change res p ((ellL p Fr t-d)-sigma ⬝ᵥ (Q⁻¹ *ᵥ fun i => ellL p Fr (c i)-d))=0 at hfull
    rw [map_sub] at hfull
    have hh := sub_eq_zero.mp hfull
    simpa only [map_sub,RingHom.map_dotProduct,RingHom.map_mulVec,
      ← map_inv_of_unit (res p) Q hQu,Function.comp_def] using hh.symm
  have hm : (fun i => res p (sigma (Sum.inl i))) ⬝ᵥ
      ((Q.map (res p)).toBlocks₁₁⁻¹ *ᵥ
        fun i => res p (ellL p Fr (c (Sum.inl i)))-res p d)=res p (ellL p Fr t)-res p d := by
    change res p ((ellL p Fr t-d)-(fun i => sigma (Sum.inl i)) ⬝ᵥ
      (Qs⁻¹ *ᵥ fun i => ellL p Fr (c (Sum.inl i))-d))=0 at hminor
    rw [map_sub] at hminor
    have hh := sub_eq_zero.mp hminor
    have he : (Q.map (res p)).toBlocks₁₁=Qs.map (res p) := by
      rw [← hblock]; rfl
    rw [he]
    simpa only [map_sub,RingHom.map_dotProduct,RingHom.map_mulVec,
      ← map_inv_of_unit (res p) Qs hQsu,Function.comp_def] using hh.symm
  have hdetQ : res p Q.det=(Q.map (res p)).det := by
    have hh := RingHom.map_det (res p) Q
    rw [RingHom.mapMatrix_apply] at hh
    convert hh using 2
  have hdetQs : res p Qs.det=(Qs.map (res p)).det := by
    have hh := RingHom.map_det (res p) Qs
    rw [RingHom.mapMatrix_apply] at hh
    convert hh using 2
  have hunit : IsUnit (Q.map (res p)).toBlocks₁₁.det := by
    have he : (Q.map (res p)).toBlocks₁₁=Qs.map (res p) := by rw [← hblock]; rfl
    rw [he,← hdetQs]; exact hQsu.map (res p)
  have hh := WrapDeletion.single_deletion_moment (Q.map (res p))
    (by rw [← hdetQ]; exact hQu.map (res p)) hunit
    (by rw [← Matrix.transpose_map,hsym])
    (fun i => res p (ndL p (c i/p)-ndL p (t/p)))
    (fun i => res p (ellL p Fr (c i))) (fun i => res p (sigma i))
    (res p (ellL p Fr t)) (res p d)
    (by
      intro i j
      have hd := congrArg (res p) (common_relation D hN c hc (fun i j => (hcol i).trans (hcol j).symm) i j)
      simp only [map_mul,map_sub] at hd ⊢
      change (_-(_-_))*res p (algebraMap _ (GaussLoc p) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c i j))=_
      convert hd using 1 <;> ring)
    (by
      intro i
      have hd := congrArg (res p) (border_relation D hN c hc t ht (fun i => (hcol i).symm) i)
      simpa only [map_mul,map_sub] using hd)
    hf hm hB (quotient_residue_ne ((hc _).trans hN) (ht.trans hN) hne (hcol _))
  have he : (Q.map (res p)).toBlocks₁₁=Qs.map (res p) := by rw [← hblock]; rfl
  rw [he] at hh
  change res p ((fun i => ellL p Fr (c i)-d) ⬝ᵥ (Q⁻¹ *ᵥ fun i => ellL p Fr (c i)-d))=
    res p ((fun i => ellL p Fr (c (Sum.inl i))-d) ⬝ᵥ (Qs⁻¹ *ᵥ fun i => ellL p Fr (c (Sum.inl i))-d))
  simpa only [map_sub,RingHom.map_dotProduct,RingHom.map_mulVec,
    ← map_inv_of_unit (res p) Q hQu,← map_inv_of_unit (res p) Qs hQsu,Function.comp_def] using hh

/-- Original common-fibre own moment in a chosen direction. -/
noncomputable def commonOwn (c : ι → ℕ) (t : ℕ) (d : GaussLoc p) : GaussLoc p :=
  (ellL p Fr t-d)-(fun i => algebraMap _ (GaussLoc p) (loewRow p Fr c t i)) ⬝ᵥ
    (((WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
      fun i => ellL p Fr (c i)-d)


/-- Put any deleted common coordinate last without changing the
original node values or matrix entries. -/
def eraseEquiv (j : ι) : {i : ι // i≠j} ⊕ Unit ≃ ι where
  toFun := Sum.elim Subtype.val (fun _ => j)
  invFun i := if h : i=j then Sum.inr () else Sum.inl ⟨i,h⟩
  left_inv i := by
    rcases i with i|i
    · simp [i.2]
    · cases i; simp
  right_inv i := by
    by_cases h : i=j <;> simp [h]

/-- The original own moment is invariant under common relabelling. -/
theorem commonOwn_reindex {τ : Type} [Fintype τ] [DecidableEq τ]
    (c : ι → ℕ) (e : τ ≃ ι) (t : ℕ) (d : GaussLoc p) :
    commonOwn (Fr:=Fr) (c ∘ e) t d=commonOwn (Fr:=Fr) c t d := by
  unfold commonOwn
  rw [← WrapActual.commonLift_submatrix c e e.injective]
  congr 1
  exact WrapTransport.response_reindex
    ((WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))) e e
      (fun i => ellL p Fr (c i)-d)
      (fun i => algebraMap _ (GaussLoc p) (loewRow p Fr c t i))

/-- Single-coordinate cancellation for an arbitrary original finite
fibre; the deleted coordinate need not already be the last index. -/
theorem single_erase_moment (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (hc : ∀ i,c i<N) (t : ℕ) (ht : t<N)
    (hcol : ∀ i,colOf (p:=p) c i=(t : ZMod p)) (j : ι) (hne : c j≠t)
    (d : GaussLoc p) (hfull : res p (commonOwn (Fr:=Fr) c t d)=0)
    (hminor : res p (commonOwn (Fr:=Fr) (fun i : {i : ι // i≠j} => c i.1) t d)=0) :
    res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr) c d)=
      res p (WrapBalanced.commonResponse (p:=p) (Fr:=Fr) (fun i : {i : ι // i≠j} => c i.1) d) := by
  let e := eraseEquiv j
  have hh := single_common_moment D hN (c ∘ e) (fun i => hc (e i)) t ht
    (fun i => hcol (e i)) hne d
    (by
      change res p (commonOwn (Fr:=Fr) (c ∘ e) t d)=0
      rw [commonOwn_reindex c e t d]
      exact hfull) hminor
  have he : WrapBalanced.commonResponse (p:=p) (Fr:=Fr) (c ∘ e) d=
      WrapBalanced.commonResponse (p:=p) (Fr:=Fr) c d := by
    unfold WrapBalanced.commonResponse
    rw [← WrapActual.commonLift_submatrix c e e.injective]
    exact WrapTransport.response_reindex
      ((WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))) e e
        (fun i => ellL p Fr (c i)-d) (fun i => ellL p Fr (c i)-d)
  rw [he] at hh
  exact hh

end OneDeletion

end CatalanCore.Uniform.Content.UFSimple.WrapOwn

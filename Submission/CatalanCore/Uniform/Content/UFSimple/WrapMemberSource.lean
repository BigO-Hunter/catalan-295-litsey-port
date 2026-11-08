module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapMember

@[expose] public section

/-! # Actual moment sources for arbitrary common-deletion members -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFSimple.WrapMemberSource

variable {p N q o r s l : ℕ} [Fact p.Prime] {Fr : Frame} {T : TwoTermData Fr q o}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (H : WrapClosed.Hyp Fr q o r s l p N T)

/-- The original member representative supplies the actual mixed row
own direction and a nonzero denominator. The common set is arbitrary. -/
theorem representative_row (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (htp : t0<r+p) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ((ellL p Fr t0-d)-(sOwn cr t0 (loewRow p Fr cc t0) ᵥ* (Dmat cr A.toBlocks₁₁)⁻¹) ⬝ᵥ
      (fun i => ellL p Fr (cr i)-d)=0) ∧
      res p (1-∑ j,(sOwn cr t0 (loewRow p Fr cc t0) ᵥ* (Dmat cr A.toBlocks₁₁)⁻¹) j)≠0 := by
  intro A cr cc d
  have htN : t0<N := by have := H.hp; have := H.hl; have := H.hls; have := H.hsize; omega
  have he : (sLift c (WrapActual.xs r) (WrapActual.ys r)
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)).toBlocks₁₁=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr) c :=
    (WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
      hc H.xs_bound H.ys_bound).symm
  have hDo := WrapActual.reference_Dmat_unit H.D H.hN c hc
  have hDa := WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound
  have hB := WrapBalanced.commonLift_own_unit H.D H.hN c hc t0 htN
  have hz := own_dir_zero Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0) hB
  have hr := WrapActual.surplus_own_response c r s l t0 H.hl H.hls H.hp ht0 htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound) (loewRow p Fr cc t0)
    (fun i => ellL p Fr (cr i)-d) hDa (by rw [he]; exact hDo)
  have hr1 := WrapActual.surplus_own_response c r s l t0 H.hl H.hls H.hp ht0 htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound) (loewRow p Fr cc t0)
    (fun _ => 1) hDa (by rw [he]; exact hDo)
  refine ⟨?_,?_⟩
  · rw [hr,he]
    exact hz
  · simp only [dotProduct,mul_one] at hr1
    rw [hr1,he]
    exact (hB.map (res p)).ne_zero

/-- Member type data give the actual original polynomial row source,
with the independent mixed source used by the Smith J-block theorem. -/
theorem row_source (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 t : ℕ) (ht0 : r+2*l-1≤t0) (htp0 : t0<r+p)
    (ht : r+2*l-1≤t) (htp : t<r+p)
    (K0 : RatFunc (ZMod p)) (V : ZMod p → RatFunc (ZMod p))
    (hType : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 V t (loewRow p Fr c t)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let Q := A.toBlocks₁₁
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ∃ Phi : GaussLoc p,
      algebraMap _ (GaussLoc p) (WrapResponse.prefixMomB (Fr:=Fr) Q cr t (loewRow p Fr cc t))=
        algebraMap _ (GaussLoc p) (WrapResponse.prefixMomA Q (loewRow p Fr cc t))*
          (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+UFMoments.piL p^2*Phi) ∧
      res p Phi=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d V) (t:ZMod p) := by
  intro A cr cc Q d
  have htN : t<N := by have := H.hp; have := H.hl; have := H.hls; have := H.hsize; omega
  have hcr : ∀ i,cr i<N := fun i => WrapCoupling.rowCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hcc : ∀ i,cc i<N := fun i => WrapCoupling.colCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hcol := WrapActual.core_colours c r s l H.hl H.hls H.hp
  have hcomm := WrapActual.reordered_commutator H.D H.hN c r s l H.hl H.hls hc H.xs_bound H.ys_bound
  have hdet : phiP p Q.det≠0 := WrapActual.core_primitive T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l H.hl H.hls H.hp H.hsize
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
  have hd := representative_row H c hc t0 ht0 htp0
  have hType' := hType
  rw [WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
    hc H.xs_bound H.ys_bound] at hType'
  have hT := WrapActual.typeData_transfer c r s l t0 t H.hl H.hls H.hp ht0 htp0 ht htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    (loewRow p Fr cc t0) (loewRow p Fr cc t) K0 V hType'
  apply WrapResponse.prefix_source H.D cr cc hcr hcc (fun i => hcol i) Q
    (fun i j => hcomm (Sum.inl i) (Sum.inl j)) hdet t0 (loewRow p Fr cc t0) d
    hd.1 hd.2 K0 V t htN (loewRow p Fr cc t)
    (loewRow_rel H.D H.hN cc hcc t htN) hT

/-- The original member representative supplies the actual mixed column
own direction and a nonzero denominator. The common set is arbitrary. -/
theorem representative_col (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 : ℕ) (ht0 : r+2*l-1≤t0) (htp : t0<r+p) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ((ellL p Fr t0-d)-(sOwn cc t0 (loewRow p Fr cr t0) ᵥ* (Dmat cc A.toBlocks₁₁ᵀ)⁻¹) ⬝ᵥ
      (fun i => ellL p Fr (cc i)-d)=0) ∧
      res p (1-∑ j,(sOwn cc t0 (loewRow p Fr cr t0) ᵥ* (Dmat cc A.toBlocks₁₁ᵀ)⁻¹) j)≠0 := by
  intro A cr cc d
  have htN : t0<N := by have := H.hp; have := H.hl; have := H.hls; have := H.hsize; omega
  have he : (sLift c (WrapActual.xs r) (WrapActual.ys r)
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)).toBlocks₁₁=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr) c :=
    (WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
      hc H.xs_bound H.ys_bound).symm
  have hDo := WrapActual.reference_Dmat_unit H.D H.hN c hc
  have hDa := WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound
  have heT : (sLift c (WrapActual.xs r) (WrapActual.ys r)
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)).toBlocks₁₁ᵀ=
      WrapBalanced.commonLift (p:=p) (Fr:=Fr) c := by rw [he,WrapBalanced.commonLift_symm]
  have hDaT := WrapActual.Dmat_transpose_unit cr cc
    (WrapActual.core_colours c r s l H.hl H.hls H.hp) A.toBlocks₁₁ hDa
  have hB := WrapBalanced.commonLift_own_unit H.D H.hN c hc t0 htN
  have hz := own_dir_zero Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0) hB
  have hr := WrapActual.surplus_col_own_response c r s l t0 H.hl H.hls H.hp ht0 htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound) (loewRow p Fr cr t0)
    (fun i => ellL p Fr (cc i)-d) hDaT (by rw [heT]; exact hDo)
  have hr1 := WrapActual.surplus_col_own_response c r s l t0 H.hl H.hls H.hp ht0 htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound) (loewRow p Fr cr t0)
    (fun _ => 1) hDaT (by rw [heT]; exact hDo)
  refine ⟨?_,?_⟩
  · rw [hr,heT]
    exact hz
  · simp only [dotProduct,mul_one] at hr1
    rw [hr1,heT]
    exact (hB.map (res p)).ne_zero

/-- Member type data give the actual original polynomial column source,
with the independent mixed source used by the Smith J-block theorem. -/
theorem col_source (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 t : ℕ) (ht0 : r+2*l-1≤t0) (htp0 : t0<r+p)
    (ht : r+2*l-1≤t) (htp : t<r+p)
    (K0 : RatFunc (ZMod p)) (V : ZMod p → RatFunc (ZMod p))
    (hType : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 V t (loewRow p Fr c t)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let Q := A.toBlocks₁₁
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ∃ Phi : GaussLoc p,
      algebraMap _ (GaussLoc p) (WrapResponse.prefixMomB (Fr:=Fr) Qᵀ cc t (loewRow p Fr cr t))=
        algebraMap _ (GaussLoc p) (WrapResponse.prefixMomA Qᵀ (loewRow p Fr cr t))*
          (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+UFMoments.piL p^2*Phi) ∧
      res p Phi=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d V) (t:ZMod p) := by
  intro A cr cc Q d
  have htN : t<N := by have := H.hp; have := H.hl; have := H.hls; have := H.hsize; omega
  have hcr : ∀ i,cr i<N := fun i => WrapCoupling.rowCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hcc : ∀ i,cc i<N := fun i => WrapCoupling.colCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hcol := WrapActual.core_colours c r s l H.hl H.hls H.hp
  have hcomm := WrapActual.reordered_commutator H.D H.hN c r s l H.hl H.hls hc H.xs_bound H.ys_bound
  have hdet : phiP p Q.det≠0 := WrapActual.core_primitive T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l H.hl H.hls H.hp H.hsize
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
  have hd := representative_col H c hc t0 ht0 htp0
  have hType' := hType
  rw [WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
    hc H.xs_bound H.ys_bound] at hType'
  have hT := WrapActual.typeData_transfer_col c r s l t0 t H.hl H.hls H.hp ht0 htp0 ht htp
    (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    (loewRow p Fr cr t0) (loewRow p Fr cr t) K0 V hType'
  have hh := WrapResponse.prefix_source H.D cc cr hcc hcr (fun i => (hcol i).symm) Qᵀ
    (fun i j => WrapResponse.commutator_transpose A
      (WrapActual.rowCoords c r s l H.hl H.hls)
      (WrapActual.colCoords c r s l H.hl H.hls) hcomm (Sum.inl i) (Sum.inl j))
    (by simpa only [Matrix.det_transpose] using hdet) t0 (loewRow p Fr cr t0) d
    hd.1 hd.2 K0 V t htN (loewRow p Fr cr t)
    (loewRow_rel H.D H.hN cr hcr t htN) hT
  have hDa := WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound
  rw [WrapResponse.mixedV_transpose cr cc (WrapActual.core_colours c r s l H.hl H.hls H.hp) Q hDa] at hh
  exact hh

/-- Actual member row moments are the original polynomial moments
used by the J-block constructor. -/
theorem row_moment_source (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 t : ℕ) (ht0 : r+2*l-1≤t0) (htp0 : t0<r+p)
    (ht : r+2*l-1≤t) (htp : t<r+p)
    (K0 : RatFunc (ZMod p)) (V : ZMod p → RatFunc (ZMod p))
    (z : Fin (s+1-l))
    (heq : t=WrapActual.rowCoords c r s l H.hl H.hls (Sum.inr z))
    (hType : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 V t (loewRow p Fr c t)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let xx := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inr i)
    let Q := A.toBlocks₁₁
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ∃ Phi : GaussLoc p,
      algebraMap _ (GaussLoc p) (rowMomB A Fr cr xx z)=
        algebraMap _ (GaussLoc p) (rowMomA A z)*
          (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+UFMoments.piL p^2*Phi) ∧
      res p Phi=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d V) (t:ZMod p) := by
  intro A cr cc xx Q d
  have hh := row_source H c hc t0 t ht0 htp0 ht htp K0 V hType
  dsimp only at hh
  let sigma := loewRow p Fr cc t
  have hload := WrapActual.surplus_row_load H.D H.hN c r s l H.hl H.hls hc H.xs_bound H.ys_bound z
  have hσ : sigma=A.toBlocks₂₁ z := by
    dsimp only [sigma]
    rw [heq]
    exact hload.symm
  have hcr : ∀ i,cr i<N := fun i => WrapCoupling.rowCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hxx : ∀ i,xx i<N := fun i => WrapCoupling.rowCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inr i)
  have hA : WrapResponse.prefixMomA Q sigma=rowMomA A z := by rw [hσ]; rfl
  have hB : WrapResponse.prefixMomB (Fr:=Fr) Q cr t sigma=rowMomB A Fr cr xx z := by
    rw [rowMomB_eq H.D A cr xx hcr hxx z]
    unfold WrapResponse.prefixMomB
    rw [heq,hσ]
  rw [hA,hB] at hh
  exact hh

/-- Actual member column moments are the original polynomial moments
used by the J-block constructor. -/
theorem col_moment_source (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 t : ℕ) (ht0 : r+2*l-1≤t0) (htp0 : t0<r+p)
    (ht : r+2*l-1≤t) (htp : t<r+p)
    (K0 : RatFunc (ZMod p)) (V : ZMod p → RatFunc (ZMod p))
    (z : Fin (s+1-l))
    (heq : t=WrapActual.colCoords c r s l H.hl H.hls (Sum.inr z))
    (hType : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 V t (loewRow p Fr c t)) :
    let A := WrapActual.reordered c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound)
    let cr := fun i => WrapActual.rowCoords c r s l H.hl H.hls (Sum.inl i)
    let cc := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inl i)
    let xx := fun i => WrapActual.colCoords c r s l H.hl H.hls (Sum.inr i)
    let Q := A.toBlocks₁₁
    let d := dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t0 (loewRow p Fr c t0)
    ∃ Phi : GaussLoc p,
      algebraMap _ (GaussLoc p) (colMomB A Fr cc xx z)=
        algebraMap _ (GaussLoc p) (colMomA A z)*
          (UFMoments.piL p*(algebraMap _ (GaussLoc p) (nL p Fr)*d)+UFMoments.piL p^2*Phi) ∧
      res p Phi=res p (algebraMap _ (GaussLoc p) (nL p Fr))*K0+
        hDer univ (WrapResponse.mixedV Fr cr cc Q d V) (t:ZMod p) := by
  intro A cr cc xx Q d
  have hh := col_source H c hc t0 t ht0 htp0 ht htp K0 V hType
  dsimp only at hh
  let sigma := loewRow p Fr cr t
  have hload := WrapActual.surplus_col_load H.D H.hN c r s l H.hl H.hls hc H.xs_bound H.ys_bound z
  have hσ : sigma=Aᵀ.toBlocks₂₁ z := by
    dsimp only [sigma]
    rw [heq]
    exact hload.symm
  have hcr : ∀ i,cc i<N := fun i => WrapCoupling.colCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inl i)
  have hxx : ∀ i,xx i<N := fun i => WrapCoupling.colCoords_lt c r s l H.hl H.hls hc H.xs_bound H.ys_bound (Sum.inr i)
  have hA : WrapResponse.prefixMomA Qᵀ sigma=rowMomA Aᵀ z := by rw [hσ]; rfl
  have hB : WrapResponse.prefixMomB (Fr:=Fr) Qᵀ cc t sigma=rowMomB Aᵀ Fr cc xx z := by
    rw [rowMomB_eq H.D Aᵀ cc xx hcr hxx z]
    unfold WrapResponse.prefixMomB
    rw [heq,hσ]
    rfl
  rw [hA,hB] at hh
  rw [WrapResponse.rowMomA_transpose,WrapResponse.rowMomB_transpose] at hh
  exact hh

/-- Original member type data force zero source weight at a selected
surplus colour. No full-matrix source comparison is needed for this step. -/
theorem selected_weight_zero (c : ι → ℕ) (hc : ∀ i,c i<N)
    (t0 t : ℕ) (ht : r+2*l-1≤t) (htp : t<r+p)
    (K0 : RatFunc (ZMod p)) (V : ZMod p → RatFunc (ZMod p))
    (hType : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 V t (loewRow p Fr c t))
    (hstep : wT p q o (t:ZMod p)=wT p q o (t0:ZMod p)) :
    WrapWeights.actualV Fr q o c r s l H.hl H.hls
      (hint_of_poleData H.D H.hN hc H.xs_bound H.ys_bound) t0 (t:ZMod p)=0 := by
  let Qo := WrapBalanced.commonLift (p:=p) (Fr:=Fr) c
  let d := dirOf Fr c Qo t0 (loewRow p Fr c t0)
  have he := WrapBalanced.commonLift_eq_core H.D H.hN c (WrapActual.xs r) (WrapActual.ys r)
    hc H.xs_bound H.ys_bound
  have hDo := WrapActual.reference_Dmat_unit H.D H.hN c hc
  have hDa := WrapActual.actual_Dmat_unit T H.hqp H.hN H.hsq H.hnorm H.hnorm0 c r s l
    H.hl H.hls H.hp H.hsize hc H.xs_bound H.ys_bound
  have hm := TypeData.fibMom_eq H.D c hc Qo
    (by
      rw [show Qo=WrapBalanced.commonLift (p:=p) (Fr:=Fr) c from rfl,he]
      exact sLift_core_rel H.D H.hN c (WrapActual.xs r) (WrapActual.ys r) hc H.xs_bound H.ys_bound)
    (WrapBalanced.commonLift_primitive H.D H.hN c hc) t0 (loewRow p Fr c t0) K0 V t
    (loewRow p Fr c t) d hType
  rw [WrapWeights.surplus_V_eq c r s l t0 t H.hl H.hls H.hp ht htp _ hDa
    (by rw [← he]; exact hDo)]
  rw [← he]
  dsimp only [vS7,vDer]
  rw [hm,hstep]
  ring

end CatalanCore.Uniform.Content.UFSimple.WrapMemberSource

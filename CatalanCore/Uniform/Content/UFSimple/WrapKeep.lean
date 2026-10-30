module

public import CatalanCore.Uniform.Content.UFSimple.WrapCredit
public import CatalanCore.Uniform.Content.UFSimple.WrapOwn
public import CatalanCore.Uniform.Content.UFSimple.WrapRelabel

@[expose] public section

/-! # Original own fibres untouched by common deletion -/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapKeep

variable {p : ℕ} [Fact p.Prime] {Fr : Frame}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The original common coordinates remaining after deletion. -/
abbrev Keep (K : Finset ι) := {i : ι // i∉K}

/-- An unedited colour has precisely its original common fibre. -/
def fibreEquiv (c : ι → ℕ) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (colOf (p:=p) c)) :
    {i : Keep K // colOf (p:=p) (c ∘ Subtype.val) i=u} ≃
      {i : ι // colOf (p:=p) c i=u} where
  toFun i := ⟨i.1.1,i.2⟩
  invFun i := ⟨⟨i.1,by
    intro hk
    exact hu (Finset.mem_image.mpr ⟨i.1,hk,i.2⟩)⟩,i.2⟩
  left_inv i := rfl
  right_inv i := rfl

/-- Quadratic responses of an original common fibre commute with any
finite relabelling, including the canonical untouched-fibre equivalence. -/
theorem response_reindex {τ : Type} [Fintype τ] [DecidableEq τ]
    (c : ι → ℕ) (e : τ ≃ ι) (d : GaussLoc p) :
    WrapBalanced.commonResponse (p:=p) (Fr:=Fr) (c ∘ e) d=
      WrapBalanced.commonResponse (p:=p) (Fr:=Fr) c d := by
  unfold WrapBalanced.commonResponse
  rw [← WrapActual.commonLift_submatrix c e e.injective]
  exact WrapTransport.response_reindex
    ((WrapBalanced.commonLift (p:=p) (Fr:=Fr) c).map (algebraMap _ (GaussLoc p))) e e
      (fun i => ellL p Fr (c i)-d) (fun i => ellL p Fr (c i)-d)

/-- Type transport survives deleting common coordinates of every other
colour. The original entries and both own fibres are retained exactly. -/
theorem typeData_unchanged (c : ι → ℕ) (K : Finset ι) (t0 t : ℕ)
    (h0 : (t0 : ZMod p)∉K.image (colOf (p:=p) c))
    (ht : (t : ZMod p)∉K.image (colOf (p:=p) c))
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (H : TypeData Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
      t0 (loewRow p Fr c t0) K0 W t (loewRow p Fr c t)) :
    TypeData Fr (c ∘ (Subtype.val : Keep K → ι))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ (Subtype.val : Keep K → ι)))
      t0 (loewRow p Fr (c ∘ Subtype.val) t0) K0 W t (loewRow p Fr (c ∘ Subtype.val) t) := by
  obtain ⟨e,kappa,hDD,hss,hell,hkappa,hres⟩ := H
  let F := fibreEquiv c K ((t:ℕ):ZMod p) ht
  let F0 := fibreEquiv c K ((t0:ℕ):ZMod p) h0
  let E := (F.trans e).trans F0.symm
  have he (i : {i : Keep K // colOf (p:=p) (c ∘ Subtype.val) i=(t0:ZMod p)}) :
      F (E.symm i)=e.symm (F0 i) := by simp [E]
  have hmat := WrapActual.commonLift_submatrix (p:=p) (Fr:=Fr) c
    (Subtype.val : Keep K → ι) Subtype.val_injective
  refine ⟨E,kappa,?_,?_,?_,hkappa,hres⟩
  · intro i j
    have hh := hDD (F0 i) (F0 j)
    rw [← he i,← he j] at hh
    rw [← hmat]
    exact hh
  · intro i
    have hh := hss (F0 i)
    rw [← he i] at hh
    exact hh
  · intro i
    have hh := hell (F0 i)
    rw [← he i] at hh
    exact hh

/-- An untouched colour has the same independently loaded inverse
moment after deleting any collection of other colour coordinates. -/
theorem mixed_moment_unchanged (c : ι → ℕ) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (colOf (p:=p) c))
    (Q : Matrix ι ι (GaussLoc p)) (hQ : IsUnit Q.det)
    (hblock : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0)
    (hkeep : IsUnit (Q.submatrix (Subtype.val : Keep K → ι) Subtype.val).det)
    (yR yC : ι → GaussLoc p) :
    WrapNodes.mixedFibMom (c ∘ (Subtype.val : Keep K → ι))
      (Q.submatrix Subtype.val Subtype.val) (yR ∘ Subtype.val) (yC ∘ Subtype.val) u=
      WrapNodes.mixedFibMom c Q yR yC u := by
  let f := (Subtype.val : Keep K → ι)
  let cK := c ∘ f
  let QK := Q.submatrix f f
  have hbK : ∀ i j,colOf (p:=p) cK i≠colOf cK j → QK i j=0 :=
    fun i j hij => hblock (f i) (f j) hij
  change (∑ i∈univ.filter (fun i => colOf (p:=p) cK i=u),
    res p ((QK⁻¹ *ᵥ (yR ∘ f)) i)*res p (yC (f i)))=
    ∑ i∈univ.filter (fun i => colOf (p:=p) c i=u),res p ((Q⁻¹ *ᵥ yR) i)*res p (yC i)
  erw [WrapType.mixed_fiber_moment_response QK (colOf cK) hkeep hbK u (yR ∘ f) (yC ∘ f) (res p),
    WrapType.mixed_fiber_moment_response Q (colOf c) hQ hblock u yR yC (res p)]
  let E := fibreEquiv c K u hu
  exact congrArg (res p) (WrapTransport.response_reindex (blk Q (colOf c) u) E E
    (fun i => yR i.1) (fun i => yC i.1))

/-- Untouched own linear responses are also unchanged, for arbitrary
loads. This includes the own-direction numerator and denominator. -/
theorem own_response_unchanged (c : ι → ℕ) (K : Finset ι) (u : ZMod p)
    (hu : u∉K.image (colOf (p:=p) c))
    (Q : Matrix ι ι (GaussLoc p)) (hQ : IsUnit Q.det)
    (hblock : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0)
    (hkeep : IsUnit (Q.submatrix (Subtype.val : Keep K → ι) Subtype.val).det)
    (sigma y : ι → GaussLoc p)
    (hs : ∀ i,colOf (p:=p) c i≠u → sigma i=0) :
    ((sigma ∘ (Subtype.val : Keep K → ι)) ᵥ*
      (Q.submatrix (Subtype.val : Keep K → ι) (Subtype.val : Keep K → ι))⁻¹) ⬝ᵥ (y ∘ Subtype.val)=
      (sigma ᵥ* Q⁻¹) ⬝ᵥ y := by
  let f := (Subtype.val : Keep K → ι)
  let cK := c ∘ f
  let QK := Q.submatrix f f
  have hbK : ∀ i j,colOf (p:=p) cK i≠colOf cK j → QK i j=0 :=
    fun i j hij => hblock (f i) (f j) hij
  have hsK : ∀ i,colOf (p:=p) cK i≠u → (sigma ∘ f) i=0 := fun i hi => hs (f i) hi
  rw [own_fiber_form QK (colOf cK) hkeep hbK u (sigma ∘ f) (y ∘ f) hsK,
    own_fiber_form Q (colOf c) hQ hblock u sigma y hs]
  let E := fibreEquiv c K u hu
  have hh := WrapTransport.response_reindex (blk Q (colOf c) u) E E
    (fun i => y i.1) (fun i => sigma i.1)
  rw [Matrix.dotProduct_mulVec,Matrix.dotProduct_mulVec] at hh
  exact hh

/-- Changing the common direction by an element of zero residue does
not change any independently loaded fibre source moment. -/
theorem mixed_moment_direction (c cr cc : ι → ℕ) (Q : Matrix ι ι (GaussLoc p))
    (d d' : GaussLoc p) (hd : res p d=res p d') (u : ZMod p) :
    WrapNodes.mixedFibMom c Q (fun i => ellL p Fr (cr i)-d) (fun i => ellL p Fr (cc i)-d) u=
      WrapNodes.mixedFibMom c Q (fun i => ellL p Fr (cr i)-d') (fun i => ellL p Fr (cc i)-d') u := by
  unfold WrapNodes.mixedFibMom
  apply Finset.sum_congr rfl; intro i hi
  simp only [RingHom.map_mulVec,Function.comp_def,map_sub,hd]

/-- Joint-type data can be re-anchored at any other node of the same
regular window, including when the old representative colour is edited.
The new constant is the negative Cauchy sum at the new representative. -/
theorem typeData_reanchor (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X])
    (t0 t1 t2 : ℕ) (sigma0 sigma1 sigma2 : ι → (LocRing p)[X])
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (H1 : TypeData Fr c Q t0 sigma0 K0 W t1 sigma1)
    (H2 : TypeData Fr c Q t0 sigma0 K0 W t2 sigma2) :
    TypeData Fr c Q t1 sigma1
      (-(∑ u : ZMod p,W u*rfH p (u-(t1:ZMod p))⁻¹)) W t2 sigma2 := by
  obtain ⟨e1,k1,hQ1,hs1,hL1,hk1,hr1⟩ := H1
  obtain ⟨e2,k2,hQ2,hs2,hL2,hk2,hr2⟩ := H2
  let E := e2.trans e1.symm
  refine ⟨E,k2-k1,?_,?_,?_,?_,?_⟩
  · intro i j
    obtain ⟨x,hx⟩ := hQ1 (e1 i) (e1 j)
    obtain ⟨y,hy⟩ := hQ2 (e1 i) (e1 j)
    refine ⟨y-x,?_⟩
    simp only [Equiv.symm_apply_apply] at hx
    simp only [E,Equiv.symm_trans_apply,Equiv.symm_symm]
    rw [hx]
    convert hy using 1 <;> ring
  · intro i
    obtain ⟨x,hx⟩ := hs1 (e1 i)
    obtain ⟨y,hy⟩ := hs2 (e1 i)
    refine ⟨y-x,?_⟩
    simp only [Equiv.symm_apply_apply] at hx
    simp only [E,Equiv.symm_trans_apply,Equiv.symm_symm]
    rw [hx]
    convert hy using 1 <;> ring
  · intro i
    obtain ⟨x,hx⟩ := hL1 (e1 i)
    obtain ⟨y,hy⟩ := hL2 (e1 i)
    refine ⟨y-x,?_⟩
    simp only [Equiv.symm_apply_apply] at hx
    simp only [E,Equiv.symm_trans_apply,Equiv.symm_symm]
    rw [hx]
    convert hy using 1 <;> ring
  · calc
      ellL p Fr t2-ellL p Fr t1=(ellL p Fr t2-ellL p Fr t0)-(ellL p Fr t1-ellL p Fr t0) := by ring
      _=_ := by rw [hk2,hk1]; ring
  · rw [map_sub,hr2,hr1]
    ring

/-- The intrinsic representative direction is exactly unchanged when
its own colour is untouched, even if every other common colour is edited. -/
theorem direction_unchanged (c : ι → ℕ) (K : Finset ι) (t : ℕ)
    (ht : (t:ZMod p)∉K.image (colOf (p:=p) c))
    (hD : IsUnit (Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)).det)
    (hDK : IsUnit (Dmat (c ∘ (Subtype.val : Keep K → ι))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ (Subtype.val : Keep K → ι)))).det) :
    dirOf Fr (c ∘ (Subtype.val : Keep K → ι))
      (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ (Subtype.val : Keep K → ι))) t
      (loewRow p Fr (c ∘ Subtype.val) t)=
    dirOf Fr c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c) t (loewRow p Fr c t) := by
  let f := (Subtype.val : Keep K → ι)
  let Q := Dmat c (WrapBalanced.commonLift (p:=p) (Fr:=Fr) c)
  have he : Dmat (c ∘ f) (WrapBalanced.commonLift (p:=p) (Fr:=Fr) (c ∘ f))=
      Q.submatrix f f := by
    rw [← WrapActual.commonLift_submatrix c f Subtype.val_injective]
    rfl
  have hb : ∀ i j,colOf (p:=p) c i≠colOf c j → Q i j=0 := by
    intro i j hij; simp [Q,Dmat,hij]
  have hs : ∀ i,colOf (p:=p) c i≠(t:ZMod p) → sOwn c t (loewRow p Fr c t) i=0 := by
    intro i hi; simp [sOwn,hi]
  have hkeep : IsUnit (Q.submatrix f f).det := by rw [← he]; exact hDK
  have hL := own_response_unchanged c K (t:ZMod p) ht Q hD hb hkeep
    (sOwn c t (loewRow p Fr c t)) (fun i => ellL p Fr (c i)) hs
  have hB := own_response_unchanged c K (t:ZMod p) ht Q hD hb hkeep
    (sOwn c t (loewRow p Fr c t)) (fun _ => 1) hs
  simp only [dotProduct,mul_one,Function.comp_def] at hB
  unfold dirOf
  erw [he,hL,hB]

end CatalanCore.Uniform.Content.UFSimple.WrapKeep

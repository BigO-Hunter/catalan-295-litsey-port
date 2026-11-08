module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapBridge
public import Submission.CatalanCore.Uniform.Content.UFMoments.JType
public import Submission.CatalanCore.Uniform.Content.UFMoments.FibTransport

@[expose] public section

/-! # Joint-type second-order source for an actual mixed core

Own-fibre transport uses one matching residue colouring. The core row and
column nodes and their prefix loads remain independent in the cross source.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapType

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mixed_jtype_node (D : PoleData Fr p N) (c cc : ι → ℕ) (hc : ∀ a, c a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) c a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (c a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0)
    (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) -
      (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹) j) ≠ 0)
    (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (cc a) - nd p t) * σ a = PF p Fr (cc a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = CatalanCore.Uniform.Content.UFMoments.piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (c a))))))
    (e : {a // colOf (p := p) c a = ((t : ℕ) : ZMod p)} ≃
      {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)})
    (hDD : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (Q (e.symm i).1 (e.symm j).1) =
        algebraMap _ (GaussLoc p) (Q i.1 j.1) + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x)
    (hss : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      algebraMap _ (GaussLoc p) (σ (e.symm i).1) =
        algebraMap _ (GaussLoc p) (σ0 i.1) + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x)
    (hℓ : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      ellL p Fr (c (e.symm i).1) = ellL p Fr (c i.1) + (ellL p Fr t - ellL p Fr t0) +
        CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x)
    (κ₁ : GaussLoc p) (hκ : ellL p Fr t - ellL p Fr t0 = CatalanCore.Uniform.Content.UFMoments.piL p * κ₁) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (CatalanCore.Uniform.Content.UFMoments.piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) +
          CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
        (res p κ₁ - ∑ c' : ZMod p,
          WrapNodes.mixedFibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d)
            (fun a => ellL p Fr (cc a) - d) c' *
            rfH p (c' - ((t : ℕ) : ZMod p))⁻¹) := by
  have hDu := WrapNodes.isUnit_mixedDmat_det D c cc hc hcc hcol Q hQ hdet
  have hb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hs : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → sOwn c t σ a = 0 := by
    intro a h; simp [sOwn, h]
  have hs0 : ∀ a, colOf (p := p) c a ≠ ((t0 : ℕ) : ZMod p) → sOwn c t0 σ0 a = 0 := by
    intro a h; simp [sOwn, h]
  have hDD' : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      Dmat c Q (e.symm i).1 (e.symm j).1 = Dmat c Q i.1 j.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i j
    obtain ⟨x, hx⟩ := hDD i j
    refine ⟨x, ?_⟩
    have h1 : colOf (p := p) c (e.symm i).1 = colOf c (e.symm j).1 :=
      ((e.symm i).2).trans ((e.symm j).2).symm
    have h2 : colOf (p := p) c i.1 = colOf c j.1 := i.2.trans j.2.symm
    simp only [Dmat, Matrix.of_apply, h1, h2, ↓reduceIte]
    exact hx
  have hss' : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      sOwn c t σ (e.symm i).1 = sOwn c t0 σ0 i.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i
    obtain ⟨x, hx⟩ := hss i
    refine ⟨x, ?_⟩
    simp only [sOwn, (e.symm i).2, i.2, ↓reduceIte]
    exact hx
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := transport (CatalanCore.Uniform.Content.UFMoments.piL p) (Dmat c Q) (colOf c) hDu hb _ _ e
    (sOwn c t σ) (sOwn c t0 σ0) (fun a => ellL p Fr (c a)) hs hs0 (ellL p Fr t0)
    (ellL p Fr t - ellL p Fr t0) d hDD' hss' hℓ
  set g0 := sOwn c t0 σ0 ᵥ* (Dmat c Q)⁻¹
  set G₁ := κ₁ * (1 - ∑ j, g0 j) + CatalanCore.Uniform.Content.UFMoments.piL p * x
  have hG : (ellL p Fr t - d) - (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a) - d) = CatalanCore.Uniform.Content.UFMoments.piL p * G₁ := by
    have e1 : ellL p Fr t = ellL p Fr t0 + (ellL p Fr t - ellL p Fr t0) := by ring
    rw [e1, hx, hz, hκ]
    simp only [G₁]
    ring
  have hBt : res p (1 - ∑ j, (sOwn c t σ ᵥ* (Dmat c Q)⁻¹) j) = res p (1 - ∑ j, g0 j) := by
    rw [hx']
    simp only [map_sub, map_add, map_mul, map_pow, res_piL, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, add_zero]
  have hOwn : sOwn cc t σ = sOwn c t σ := by
    funext a
    simp only [sOwn, ← hcol a]
  obtain ⟨Φ, h1, h2⟩ := WrapBridge.mixed_node_bridge D c cc hc hcc hcol Q hQ hdet
    t ht σ hσ momA momB hA hB d G₁ (by rw [hOwn]; exact hG)
    (by rw [hOwn, hBt]; exact hB0)
  rw [hOwn] at h2
  refine ⟨Φ, h1, ?_⟩
  rw [h2, hBt, cross_cauchy]
  have hG1 : res p G₁ = res p κ₁ * res p (1 - ∑ j, g0 j) := by
    simp only [G₁, map_add, map_mul, res_piL, zero_mul, add_zero]
  rw [hG1, mul_div_assoc, div_self hB0, mul_one]


/-- A mixed bilinear fibre moment is computed inside its own colour
block. The two load vectors are independent. -/
theorem mixed_fiber_moment {R k α : Type*} [CommRing R] [Field k]
    [Fintype α] [DecidableEq α] (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ a b, col a≠col b → D a b=0)
    (tau : ZMod p) (yR yC : α → R) (f : R →+* k) :
    ∑ a ∈ univ.filter (fun a => col a=tau), f ((D⁻¹ *ᵥ yR) a)*f (yC a) =
      ∑ i : {a // col a=tau},
        f (((blk D col tau)⁻¹ *ᵥ fun j => yR j.1) i)*f (yC i.1) := by
  have hinv := inv_colour_zero D col hD hb
  rw [Finset.sum_subtype (univ.filter (fun a => col a=tau)) (p := fun a => col a=tau)
    (fun a => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [(inv_restrict D col hD hb tau).2]
  simp only [mulVec, dotProduct, blk, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => col a=tau)]
  have h0 : ∑ j : {a // ¬col a=tau}, D⁻¹ i.1 j.1*yR j.1=0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hinv i.1 j.1 (by rw [i.2]; exact Ne.symm j.2),zero_mul]
  rw [h0,add_zero]

/-- The mixed fibre source is the reduced bilinear inverse response
of the actual local block. -/
theorem mixed_fiber_moment_response {R k α : Type*} [CommRing R] [Field k]
    [Fintype α] [DecidableEq α] (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ a b, col a≠col b → D a b=0)
    (tau : ZMod p) (yR yC : α → R) (f : R →+* k) :
    ∑ a ∈ univ.filter (fun a => col a=tau), f ((D⁻¹ *ᵥ yR) a)*f (yC a) =
      f ((fun i : {a // col a=tau} => yC i.1) ⬝ᵥ
        (blk D col tau)⁻¹ *ᵥ (fun i => yR i.1)) := by
  rw [mixed_fiber_moment D col hD hb tau yR yC f]
  simp only [dotProduct,map_sum,map_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Transposition exchanges the two loads in a mixed fibre source. -/
theorem mixed_fiber_moment_transpose {R k α : Type*} [CommRing R] [Field k]
    [Fintype α] [DecidableEq α] (D : Matrix α α R) (col : α → ZMod p)
    (hD : IsUnit D.det) (hb : ∀ a b, col a≠col b → D a b=0)
    (tau : ZMod p) (yR yC : α → R) (f : R →+* k) :
    (∑ a ∈ univ.filter (fun a => col a=tau), f ((Dᵀ⁻¹ *ᵥ yC) a)*f (yR a)) =
      ∑ a ∈ univ.filter (fun a => col a=tau), f ((D⁻¹ *ᵥ yR) a)*f (yC a) := by
  have hDT : IsUnit Dᵀ.det := by rwa [Matrix.det_transpose]
  have hbT : ∀ a b, col a≠col b → Dᵀ a b=0 := fun a b h => hb b a (Ne.symm h)
  rw [mixed_fiber_moment_response Dᵀ col hDT hbT tau yC yR f,
    mixed_fiber_moment_response D col hD hb tau yR yC f]
  exact congrArg f (WrapTransport.response_transpose (blk D col tau)
    (fun a => yR a.1) (fun a => yC a.1)).symm

/-- Transported own-direction moment vanishes after reduction. This
uses only own-fibre data and remains valid for a globally mixed core. -/
theorem own_type_transport (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X])
    (hDu : IsUnit (Dmat c Q).det) (t0 : ℕ) (sigma0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0-d)-(sOwn c t0 sigma0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d)=0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (sigma : ι → (LocRing p)[X])
    (hT : TypeData Fr c Q t0 sigma0 K0 W t sigma) :
    res p ((ellL p Fr t-d)-(sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d))=0 := by
  obtain ⟨e,κ₁,hDD,hss,hℓ,hκ,hres⟩ := hT
  have hb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hs : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → sOwn c t sigma a = 0 := by
    intro a h; simp [sOwn, h]
  have hs0 : ∀ a, colOf (p := p) c a ≠ ((t0 : ℕ) : ZMod p) → sOwn c t0 sigma0 a = 0 := by
    intro a h; simp [sOwn, h]
  have hDD' : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      Dmat c Q (e.symm i).1 (e.symm j).1 = Dmat c Q i.1 j.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i j
    obtain ⟨x, hx⟩ := hDD i j
    refine ⟨x, ?_⟩
    have h1 : colOf (p := p) c (e.symm i).1 = colOf c (e.symm j).1 :=
      ((e.symm i).2).trans ((e.symm j).2).symm
    have h2 : colOf (p := p) c i.1 = colOf c j.1 := i.2.trans j.2.symm
    simp only [Dmat, Matrix.of_apply, h1, h2, ↓reduceIte]
    exact hx
  have hss' : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      sOwn c t sigma (e.symm i).1 = sOwn c t0 sigma0 i.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i
    obtain ⟨x, hx⟩ := hss i
    refine ⟨x, ?_⟩
    simp only [sOwn, (e.symm i).2, i.2, ↓reduceIte]
    exact hx
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := transport (CatalanCore.Uniform.Content.UFMoments.piL p) (Dmat c Q) (colOf c) hDu hb _ _ e
    (sOwn c t sigma) (sOwn c t0 sigma0) (fun a => ellL p Fr (c a)) hs hs0 (ellL p Fr t0)
    (ellL p Fr t - ellL p Fr t0) d hDD' hss' hℓ
  set g0 := sOwn c t0 sigma0 ᵥ* (Dmat c Q)⁻¹
  set G₁ := κ₁ * (1 - ∑ j, g0 j) + CatalanCore.Uniform.Content.UFMoments.piL p * x
  have hG : (ellL p Fr t - d) - (sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a) - d) = CatalanCore.Uniform.Content.UFMoments.piL p * G₁ := by
    have e1 : ellL p Fr t = ellL p Fr t0 + (ellL p Fr t - ellL p Fr t0) := by ring
    rw [e1, hx, hz, hκ]
    simp only [G₁]
    ring
  have hBt : res p (1 - ∑ j, (sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) j) = res p (1 - ∑ j, g0 j) := by
    rw [hx']
    simp only [map_sub, map_add, map_mul, map_pow, res_piL, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, add_zero]
  rw [hG,map_mul,res_piL,zero_mul]

/-- Own transport preserves the reduced own moment for every direction.
This equality can be used in either direction along a regular window. -/
theorem own_type_residue_eq (c : ι → ℕ) (Q : Matrix ι ι (LocRing p)[X])
    (hDu : IsUnit (Dmat c Q).det) (t0 : ℕ) (sigma0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (t : ℕ) (sigma : ι → (LocRing p)[X])
    (hT : TypeData Fr c Q t0 sigma0 K0 W t sigma) :
    res p ((ellL p Fr t-d)-(sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d))=
      res p ((ellL p Fr t0-d)-(sOwn c t0 sigma0 ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (c a)-d)) := by
  obtain ⟨e,κ₁,hDD,hss,hℓ,hκ,hres⟩ := hT
  have hb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hs : ∀ a, colOf (p := p) c a ≠ ((t : ℕ) : ZMod p) → sOwn c t sigma a = 0 := by
    intro a h; simp [sOwn, h]
  have hs0 : ∀ a, colOf (p := p) c a ≠ ((t0 : ℕ) : ZMod p) → sOwn c t0 sigma0 a = 0 := by
    intro a h; simp [sOwn, h]
  have hDD' : ∀ i j : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      Dmat c Q (e.symm i).1 (e.symm j).1 = Dmat c Q i.1 j.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i j
    obtain ⟨x, hx⟩ := hDD i j
    refine ⟨x, ?_⟩
    have h1 : colOf (p := p) c (e.symm i).1 = colOf c (e.symm j).1 :=
      ((e.symm i).2).trans ((e.symm j).2).symm
    have h2 : colOf (p := p) c i.1 = colOf c j.1 := i.2.trans j.2.symm
    simp only [Dmat, Matrix.of_apply, h1, h2, ↓reduceIte]
    exact hx
  have hss' : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, ∃ x,
      sOwn c t sigma (e.symm i).1 = sOwn c t0 sigma0 i.1 + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * x := by
    intro i
    obtain ⟨x, hx⟩ := hss i
    refine ⟨x, ?_⟩
    simp only [sOwn, (e.symm i).2, i.2, ↓reduceIte]
    exact hx
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := transport (CatalanCore.Uniform.Content.UFMoments.piL p) (Dmat c Q) (colOf c) hDu hb _ _ e
    (sOwn c t sigma) (sOwn c t0 sigma0) (fun a => ellL p Fr (c a)) hs hs0 (ellL p Fr t0)
    (ellL p Fr t - ellL p Fr t0) d hDD' hss' hℓ
  set g0 := sOwn c t0 sigma0 ᵥ* (Dmat c Q)⁻¹
  have hG : (ellL p Fr t-d)-(sOwn c t sigma ᵥ* (Dmat c Q)⁻¹) ⬝ᵥ
      (fun a => ellL p Fr (c a)-d)=
      ((ellL p Fr t0-d)-g0 ⬝ᵥ (fun a => ellL p Fr (c a)-d))+
        CatalanCore.Uniform.Content.UFMoments.piL p*
          (κ₁*(1-∑ j,g0 j)+CatalanCore.Uniform.Content.UFMoments.piL p*x) := by
    have e1 : ellL p Fr t=ellL p Fr t0+(ellL p Fr t-ellL p Fr t0) := by ring
    rw [e1,hx,hκ]
    ring
  rw [hG,map_add,map_mul,res_piL,zero_mul,add_zero]

end CatalanCore.Uniform.Content.UFSimple.WrapType

module

public import CatalanCore.Uniform.Content.UFMoments.NodePhi
public import CatalanCore.Uniform.Content.UFSimple.WrapMoments

@[expose] public section

/-! # Actual mixed-node decomposition of a wrapped core

Row and column nodes may differ by multiples of p. The residue colouring
agrees at each paired core index; their prefix values remain independent.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapNodes

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Cross-residue quotients with the actual column and row prefixes. -/
noncomputable def mixedEmat (p : ℕ) [Fact p.Prime] (Fr : Frame) (cr cc : ι → ℕ) :
    Matrix ι ι (GaussLoc p) :=
  Matrix.of fun a b => if colOf (p := p) cr a = colOf cr b then 0 else
    (ellL p Fr (cc b) - ellL p Fr (cr a)) *
      Ring.inverse (ndL p (cc b) - ndL p (cr a))

/-- The actual core splits into its mixed local fibres and a p-divisible
cross-residue part. No symmetry or equality of node families is assumed. -/
theorem mixed_core_split (D : PoleData Fr p N) (cr cc : ι → ℕ)
    (hcr : ∀ a, cr a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (cr a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (cr a)) :
    Q.map (algebraMap (LocRing p)[X] (GaussLoc p)) =
      Dmat cr Q + CatalanCore.Uniform.Content.UFMoments.piL p • mixedEmat p Fr cr cc := by
  ext a b
  by_cases h : colOf (p := p) cr a = colOf cr b
  · simp [Dmat, mixedEmat, h]
  · simp only [Matrix.map_apply, Matrix.add_apply, Dmat, mixedEmat, Matrix.of_apply,
      h, ↓reduceIte, zero_add, Matrix.smul_apply, smul_eq_mul]
    have hab : ((cr a : ℕ) : ZMod p) ≠ ((cc b : ℕ) : ZMod p) := by
      change colOf cr a ≠ colOf cc b
      rw [← hcol b]
      exact h
    exact loewner_split D (hcr a) (hcc b) hab (Q a b) (hQ a b)

/-- Reduction of the mixed cross quotient. -/
theorem res_mixedEmat (cr cc : ι → ℕ)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a) (a b : ι)
    (h : colOf (p := p) cr a ≠ colOf cr b) :
    res p (mixedEmat p Fr cr cc a b) =
      (res p (ellL p Fr (cc b)) - res p (ellL p Fr (cr a))) /
        (rfH p (colOf cr b) - rfH p (colOf cr a)) := by
  have hab : ((cc b : ℕ) : ZMod p) ≠ ((cr a : ℕ) : ZMod p) := by
    change colOf cc b ≠ colOf cr a
    rw [← hcol b]
    exact Ne.symm h
  simp only [mixedEmat, Matrix.of_apply, h, ↓reduceIte]
  rw [map_mul, res_inverse _ (isUnit_ndL_sub hab), res_ndL_sub, map_sub,
    div_eq_mul_inv]
  change _ * (rfH p (colOf cc b) - rfH p (colOf cr a))⁻¹ = _
  rw [← hcol b]

/-- Primitivity of the actual core implies that of its local mixed fibres. -/
theorem isUnit_mixedDmat_det (D : PoleData Fr p N) (cr cc : ι → ℕ)
    (hcr : ∀ a, cr a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (cr a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (cr a))
    (hdet : phiP p Q.det ≠ 0) : IsUnit (Dmat cr Q).det := by
  refine isUnit_of_res_ne _ ?_
  set fL := algebraMap (LocRing p)[X] (GaussLoc p)
  have hm : (Q.map fL).map (res p) = (Dmat cr Q).map (res p) := by
    rw [mixed_core_split D cr cc hcr hcc hcol Q hQ]
    ext a b
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, res_piL, zero_mul, add_zero]
  have h1 : res p (Q.map fL).det = phiP p Q.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, res_algebraMap]
  have h2 : res p (Dmat cr Q).det = ((Dmat cr Q).map (res p)).det := by
    have := RingHom.map_det (res p) (Dmat cr Q)
    rw [RingHom.mapMatrix_apply] at this
    convert this using 2
  have h3 : res p (Q.map fL).det = ((Q.map fL).map (res p)).det := by
    have := RingHom.map_det (res p) (Q.map fL)
    rw [RingHom.mapMatrix_apply] at this
    convert this using 2
  rw [h2, ← hm, ← h3, h1]
  exact hdet

/-- The fiber moment `m(c) = Σ_{c_a ≡ c} res((D⁻¹ y)_a) res(y_a)`. -/
noncomputable def mixedFibMom (cr : ι → ℕ) (Dm : Matrix ι ι (GaussLoc p)) (yR yC : ι → GaussLoc p)
    (c' : ZMod p) : RatFunc (ZMod p) :=
  ∑ a ∈ univ.filter (fun a => colOf (p := p) cr a = c'), res p ((Dm⁻¹ *ᵥ yR) a) * res p (yC a)

theorem mixed_node_phi2 (D : PoleData Fr p N) (cr cc : ι → ℕ) (hcr : ∀ a, cr a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (cr a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (cr a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (cc a) - nd p t) * σ a = PF p Fr (cc a) - PF p Fr t)
    (d G₁ : GaussLoc p)
    (hG : (ellL p Fr t - d) - (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (cr a) - d) =
      CatalanCore.Uniform.Content.UFMoments.piL p * G₁) :
    ∃ Bk Rem : GaussLoc p,
      (ellL p Fr t - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
          ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ fun a => ellL p Fr (cr a))) -
        d * (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
          ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) =
        CatalanCore.Uniform.Content.UFMoments.piL p * (G₁ - Bk + CatalanCore.Uniform.Content.UFMoments.piL p * Rem) ∧
      res p Bk = res p (1 - ∑ j, (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) j) *
        ∑ c' : ZMod p, if c' = ((t : ℕ) : ZMod p) then 0 else
          mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a) - d)
            (fun a => ellL p Fr (cc a) - d) c' /
            (rfH p c' - rfH p ((t : ℕ) : ZMod p)) := by
  classical
  set y : ι → GaussLoc p := fun a => ellL p Fr (cr a) - d
  set yC : ι → GaussLoc p := fun a => ellL p Fr (cc a) - d
  set Qm := Q.map (algebraMap (LocRing p)[X] (GaussLoc p))
  have hsplit := mixed_core_split D cr cc hcr hcc hcol Q hQ
  have hQu := isUnit_map_det Q hdet
  have hD := isUnit_mixedDmat_det D cr cc hcr hcc hcol Q hQ hdet
  set x := Qm⁻¹ *ᵥ y
  have hx : Dmat cr Q *ᵥ x + CatalanCore.Uniform.Content.UFMoments.piL p • (mixedEmat p Fr cr cc *ᵥ x) = y := by
    have h0 : Qm *ᵥ x = y := by
      show Qm *ᵥ (Qm⁻¹ *ᵥ y) = y
      rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
    rw [show Qm = Dmat cr Q + CatalanCore.Uniform.Content.UFMoments.piL p • mixedEmat p Fr cr cc from hsplit, add_mulVec, smul_mulVec] at h0
    exact h0
  have hDb : ∀ a b, colOf (p := p) cr a ≠ colOf cr b → Dmat cr Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  have hE0 : ∀ a b, colOf (p := p) cr a = colOf cr b → mixedEmat p Fr cr cc a b = 0 := by
    intro a b h; simp [mixedEmat, h]
  have hE : ∀ a b, colOf (p := p) cr a ≠ colOf cr b → res p (mixedEmat p Fr cr cc a b) =
      (res p (yC b) - res p (y a)) / (rfH p (colOf cr b) - rfH p (colOf cr a)) := by
    intro a b h
    rw [res_mixedEmat cr cc hcol a b h]
    simp only [y, yC, map_sub]
    ring
  have hs : ∀ a, colOf (p := p) cr a ≠ ((t : ℕ) : ZMod p) → sOwn cc t σ a = 0 := by
    intro a h
    have hh : colOf (p := p) cc a ≠ ((t : ℕ) : ZMod p) := by rwa [← hcol a]
    simp [sOwn, hh]
  have hs'0 : ∀ a, colOf (p := p) cr a = ((t : ℕ) : ZMod p) → sCross p Fr cc t a = 0 := by
    intro a h
    have hh : colOf (p := p) cc a = ((t : ℕ) : ZMod p) := by rwa [← hcol a]
    simp [sCross, hh]
  have hs' : ∀ a, colOf (p := p) cr a ≠ ((t : ℕ) : ZMod p) → res p (sCross p Fr cc t a) =
      (res p (yC a) - res p (ellL p Fr t - d)) / (rfH p (colOf cr a) - rfH p ((t : ℕ) : ZMod p)) := by
    intro a h
    have hh : colOf (p := p) cc a ≠ ((t : ℕ) : ZMod p) := by rwa [← hcol a]
    rw [res_sCross cc t a hh, ← hcol a]
    simp only [yC, map_sub]
    ring
  obtain ⟨Bk, Rem, h1, h2⟩ := WrapMoments.mixed_phi2_expansion (CatalanCore.Uniform.Content.UFMoments.piL p) (res p) (res_piL p) (rfH p) rfH_injective
    (colOf cr) ((t : ℕ) : ZMod p) (Dmat cr Q) (mixedEmat p Fr cr cc) hD hDb y yC (ellL p Fr t - d) hE0 hE
    (sOwn cc t σ) (sCross p Fr cc t) hs hs'0 hs' x hx G₁ hG
  refine ⟨Bk, Rem, ?_, h2⟩
  rw [← h1, ← node_split D cc hcc t ht σ hσ]
  exact lin_shift Qm⁻¹ _ _ d (ellL p Fr t)

theorem mixed_node_alpha_res (D : PoleData Fr p N) (cr cc : ι → ℕ) (hcr : ∀ a, cr a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (cr a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (cr a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (cc a) - nd p t) * σ a = PF p Fr (cc a) - PF p Fr t) :
    res p (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)) =
      res p (1 - ∑ j, (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) j) := by
  set fL := algebraMap (LocRing p)[X] (GaussLoc p)
  set Qm := Q.map fL
  have hsplit := mixed_core_split D cr cc hcr hcc hcol Q hQ
  have hQu := isUnit_map_det Q hdet
  have hD := isUnit_mixedDmat_det D cr cc hcr hcc hcol Q hQ hdet
  set x := Qm⁻¹ *ᵥ (1 : ι → GaussLoc p)
  have hx : Dmat cr Q *ᵥ x + CatalanCore.Uniform.Content.UFMoments.piL p • (mixedEmat p Fr cr cc *ᵥ x) = 1 := by
    have h0 : Qm *ᵥ x = 1 := by
      show Qm *ᵥ (Qm⁻¹ *ᵥ 1) = 1
      rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
    rw [show Qm = Dmat cr Q + CatalanCore.Uniform.Content.UFMoments.piL p • mixedEmat p Fr cr cc from hsplit, add_mulVec, smul_mulVec] at h0
    exact h0
  have hmo := moment_second_order (CatalanCore.Uniform.Content.UFMoments.piL p) (Dmat cr Q) (mixedEmat p Fr cr cc) hD 1 x hx (sOwn cc t σ)
    (sCross p Fr cc t) 1
  rw [← node_split D cc hcc t ht σ hσ] at hmo
  rw [hmo]
  simp only [map_add, map_sub, map_mul, map_pow, res_piL, zero_mul, sub_zero, add_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [dotProduct_mulVec, dotProduct_one]


end CatalanCore.Uniform.Content.UFSimple.WrapNodes

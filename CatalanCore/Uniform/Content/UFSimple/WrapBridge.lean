module

public import CatalanCore.Uniform.Content.UFMoments.NodeBridge
public import CatalanCore.Uniform.Content.UFSimple.WrapNodes
public import CatalanCore.Uniform.Content.UFSimple.WrapTransport

@[expose] public section

/-! # Actual mixed-node moment bridge

Apply this row bridge to the transposed core for column moments. The two
core coordinate families and the two prefix loads remain independent.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFSimple.WrapNodes

namespace CatalanCore.Uniform.Content.UFSimple.WrapBridge

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The second-order function of one node.** -/
theorem mixed_node_bridge (D : PoleData Fr p N) (cr cc : ι → ℕ) (hcr : ∀ a, cr a < N) (hcc : ∀ a, cc a < N)
    (hcol : ∀ a, colOf (p := p) cr a = colOf cc a)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, nL p Fr * (nd p (cc b) - nd p (cr a)) * Q a b =
      PF p Fr (cc b) - PF p Fr (cr a))
    (hdet : phiP p Q.det ≠ 0) (t : ℕ) (ht : t < N) (σ : ι → (LocRing p)[X])
    (hσ : ∀ a, nL p Fr * (nd p (cc a) - nd p t) * σ a = PF p Fr (cc a) - PF p Fr t)
    (momA momB : (LocRing p)[X])
    (hA : algebraMap _ (GaussLoc p) momA = (Q.map (algebraMap _ (GaussLoc p))).det *
      (1 - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ 1)))
    (hB : algebraMap _ (GaussLoc p) momB = CatalanCore.Uniform.Content.UFMoments.piL p * ((Q.map (algebraMap _ (GaussLoc p))).det *
      (algebraMap _ (GaussLoc p) (PF1 p Fr t) - (fun a => algebraMap _ (GaussLoc p) (σ a)) ⬝ᵥ
        ((Q.map (algebraMap _ (GaussLoc p)))⁻¹ *ᵥ
          fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (cr a))))))
    (d G₁ : GaussLoc p)
    (hG : (ellL p Fr t - d) - (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) ⬝ᵥ (fun a => ellL p Fr (cr a) - d) =
      CatalanCore.Uniform.Content.UFMoments.piL p * G₁)
    (hB0 : res p (1 - ∑ j, (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) j) ≠ 0) :
    ∃ Φ : GaussLoc p,
      algebraMap _ (GaussLoc p) momB = algebraMap _ (GaussLoc p) momA *
        (CatalanCore.Uniform.Content.UFMoments.piL p * (algebraMap _ (GaussLoc p) (nL p Fr) * d) + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * Φ) ∧
      res p Φ = res p (algebraMap _ (GaussLoc p) (nL p Fr)) *
        (res p G₁ / res p (1 - ∑ j, (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) j) -
          ∑ c' : ZMod p, if c' = ((t : ℕ) : ZMod p) then 0 else
            mixedFibMom cr (Dmat cr Q) (fun a => ellL p Fr (cr a) - d)
              (fun a => ellL p Fr (cc a) - d) c' /
              (rfH p c' - rfH p ((t : ℕ) : ZMod p))) := by
  obtain ⟨Bk, Rem, h1, h2⟩ := mixed_node_phi2 D cr cc hcr hcc hcol Q hQ hdet t ht σ hσ d G₁ hG
  have hα := mixed_node_alpha_res D cr cc hcr hcc hcol Q hQ hdet t ht σ hσ
  set Qm := Q.map (algebraMap (LocRing p)[X] (GaussLoc p))
  set σm : ι → GaussLoc p := fun a => algebraMap _ (GaussLoc p) (σ a)
  set α := 1 - σm ⬝ᵥ (Qm⁻¹ *ᵥ 1)
  set u := algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr)
  set Bf := res p (1 - ∑ j, (sOwn cc t σ ᵥ* (Dmat cr Q)⁻¹) j)
  have hαu : IsUnit α := isUnit_of_res_ne _ (by rw [hα]; exact hB0)
  set W := G₁ - Bk + CatalanCore.Uniform.Content.UFMoments.piL p * Rem
  refine ⟨u * W * Ring.inverse α, ?_, ?_⟩
  · have hP : (fun a => algebraMap _ (GaussLoc p) (PF1 p Fr (cr a))) =
        fun a => u * ellL p Fr (cr a) := by
      funext a; exact algebraMap_PF1 D (cr a)
    have hs : σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => u * ellL p Fr (cr a)) =
        u * (σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a))) := lin_scale _ _ _ _
    rw [hB, hA, hP, hs, algebraMap_PF1 D t]
    have hinv := Ring.mul_inverse_cancel α hαu
    have e : ellL p Fr t - σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a)) = d * α + CatalanCore.Uniform.Content.UFMoments.piL p * W := by
      rw [← h1]; ring
    calc CatalanCore.Uniform.Content.UFMoments.piL p * (Qm.det * (u * ellL p Fr t - u * (σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a)))))
        = CatalanCore.Uniform.Content.UFMoments.piL p * Qm.det * u * (ellL p Fr t - σm ⬝ᵥ (Qm⁻¹ *ᵥ fun a => ellL p Fr (cr a))) := by
          ring
      _ = CatalanCore.Uniform.Content.UFMoments.piL p * Qm.det * u * (d * α + CatalanCore.Uniform.Content.UFMoments.piL p * W) := by rw [e]
      _ = CatalanCore.Uniform.Content.UFMoments.piL p * Qm.det * u * (d * α + CatalanCore.Uniform.Content.UFMoments.piL p * W * (α * Ring.inverse α)) := by rw [hinv, mul_one]
      _ = Qm.det * α * (CatalanCore.Uniform.Content.UFMoments.piL p * (u * d) + CatalanCore.Uniform.Content.UFMoments.piL p ^ 2 * (u * W * Ring.inverse α)) := by ring
  · rw [map_mul, map_mul, res_inverse _ hαu, hα]
    have hW : res p W = res p G₁ - res p Bk := by
      simp only [W, map_add, map_sub, map_mul, res_piL, zero_mul, add_zero]
    rw [hW, h2]
    field_simp


end CatalanCore.Uniform.Content.UFSimple.WrapBridge

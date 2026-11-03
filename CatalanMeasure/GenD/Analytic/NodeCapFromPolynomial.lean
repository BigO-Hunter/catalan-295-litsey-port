module

public import CatalanMeasure.GenD.Analytic.PolynomialTailCount
public import CatalanMeasure.GenD.Analytic.NodeCapAngle
public import CatalanMeasure.GenD.Signed.MarkedCap

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset Set
noncomputable section

/-- The generic Davis NodeCap transfer. The numerical producer supplies the
tail defect and monotonicity; the midpoint count and endpoint gap are derived. -/
theorem davis_nodeCapAsym_of_polynomial {J N K : ℕ} (hN : 10 ≤ N) (hK0 : 0 < K)
    (hK : 130 * K ≤ 66 * N + 130) (p : ℝ[X]) (τ x : Fin J → ℝ)
    (level : Fin J → Fin K) {gsN gsP t0 : ℝ}
    (hx : ∀ a, x a ∈ Ioo (-1 : ℝ) 1)
    (hsupport : ∀ a, x a ≤ -gsN ∨ gsP ≤ x a)
    (hτ : Function.Injective τ) (hτ1 : ∀ a, τ a ≤ 1)
    (horder : ∀ a b, x a ≤ x b ↔ τ a ≤ τ b)
    (htail : ∀ a, (999 / 1000 : ℝ) ≤ x a → t0 ≤ τ a)
    (hmono : StrictMonoOn p.eval (Icc t0 1))
    (heval : ∀ a, p.eval (τ a) = CatalanMeasure.chebX K (level a))
    (hdefect : ∀ a, (999 / 1000 : ℝ) ≤ x a →
      1 - p.eval (τ a) ≤ 20000 * (1 - x a) ^ 2 / (1 + x a ^ 2)) :
    CatalanMeasure.Signed.NodeCapAsym gsN gsP (999 / 1000) (467829 / 1000000)
      (72 * (N : ℝ)) (1 / (2 * (66 * (N : ℝ) + 130))) x := by
  classical
  have hNR : (10 : ℝ) ≤ N := by exact_mod_cast hN
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK0
  have hKbound : (130 : ℝ) * K ≤ 66 * N + 130 := by exact_mod_cast hK
  have hden : 0 < 2 * (66 * (N : ℝ) + 130) := by positivity
  have hv0 : ∀ a, 0 ≤ 1 - p.eval (τ a) := by
    intro a
    rw [heval]
    linarith [(CatalanMeasure.chebX_mem (level a)).2]
  refine ⟨hsupport, ?_, ?_⟩
  · intro a
    have hxa : 0 ≤ 1 - x a := by linarith [(hx a).2]
    have hu : 1 / (2 * (66 * (N : ℝ) + 130)) ≤ 1 - x a := by
      by_cases hxc : (999 / 1000 : ℝ) ≤ x a
      · have hv := hv0 a
        have hupper := (le_div_iff₀ (by positivity : 0 < 1 + x a ^ 2)).mp (hdefect a hxc)
        have hcoarse : 1 - p.eval (τ a) ≤ 20000 * (1 - x a) ^ 2 := by
          nlinarith [mul_nonneg hv (sq_nonneg (x a))]
        have hgap := one_sub_chebX_ge_midpoint_gap (level a)
        rw [← heval a] at hgap
        have hgap' := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (K : ℝ) ^ 2)).mp hgap
        have hmul := mul_le_mul_of_nonneg_left hcoarse (show 0 ≤ 2 * (K : ℝ) ^ 2 by positivity)
        have hsq : 1 ≤ (200 * (K : ℝ) * (1 - x a)) ^ 2 := by nlinarith
        have h200 : 1 ≤ 200 * (K : ℝ) * (1 - x a) := by
          nlinarith [mul_nonneg (show 0 ≤ 200 * (K : ℝ) by positivity) hxa]
        have hscale : 200 * (K : ℝ) ≤ 2 * (66 * (N : ℝ) + 130) := by nlinarith
        apply (div_le_iff₀ hden).mpr
        nlinarith [mul_le_mul_of_nonneg_right hscale hxa]
      · have hunit : 1 / (2 * (66 * (N : ℝ) + 130)) ≤ (1 / 1000 : ℝ) := by
          apply (div_le_iff₀ hden).mpr
          nlinarith
        linarith [not_le.mp hxc]
    linarith
  · intro a hxc
    have hcount := polynomial_node_tail_count p τ level hτ hτ1 heval hmono (htail a hxc) (hτ1 a)
    have hfilter : Finset.univ.filter (fun b => x a ≤ x b) =
        Finset.univ.filter (fun b => τ a ≤ τ b) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact horder a b
    rw [← hfilter] at hcount
    have hangle := arccos_tail_le_150 hxc (hx a).2.le (hv0 a) (hdefect a hxc)
    have he : 1 - (1 - p.eval (τ a)) = p.eval (τ a) := by ring
    rw [he] at hangle
    have hcoef := davis_tail_count_coefficient hN hK
    have hxa : 0 ≤ 1 - x a := by linarith [(hx a).2]
    calc
      _ ≤ (K : ℝ) * Real.arccos (p.eval (τ a)) / Real.pi + 1 := hcount
      _ ≤ (K : ℝ) * (150 * (1 - x a)) / Real.pi + 1 :=
        add_le_add (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hangle hKR.le) Real.pi_pos.le) le_rfl
      _ = ((K : ℝ) * 150 / Real.pi) * (1 - x a) + 1 := by ring
      _ ≤ (467829 / 1000000 : ℝ) * (72 * (N : ℝ)) * (1 - x a) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_right hcoef hxa) le_rfl

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.davis_nodeCapAsym_of_polynomial

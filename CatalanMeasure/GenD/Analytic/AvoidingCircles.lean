module

public import CatalanMeasure.GenD.Signed.Data.S1.Bridge
public import CatalanMeasure.GenD.Analytic.DeletedCardinal

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Set Polynomial
noncomputable section

/-! Small circles avoiding a bounded exceptional set. The distance is inversely
proportional to the size of that set, independent of the total nodal degree. -/

theorem exists_separated_circle {K : ℕ} (roots : Fin K → ℂ) (center : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ ρ ∈ Icc a b, ∀ z : ℂ, ‖z - center‖ = ρ →
      ∀ i, (b - a) / (2 * ((K : ℝ) + 1)) ≤ ‖z - roots i‖ := by
  obtain ⟨ρ, hρ, hsep⟩ := Signed.Data.S1.exists_sep_radius
    (fun i => ‖roots i - center‖) hab
  refine ⟨ρ, hρ, fun z hz i => ?_⟩
  have h := abs_norm_sub_norm_le (roots i - center) (z - center)
  rw [hz, show (roots i - center) - (z - center) = roots i - z by ring,
    norm_sub_rev (roots i) z] at h
  exact (hsep i).trans h

theorem exists_separated_small_circle {K N : ℕ} (roots : Fin K → ℂ) (center : ℂ)
    (hN : 0 < N) :
    ∃ ρ ∈ Icc (1 / (2 * (N : ℝ) ^ 2)) (1 / (N : ℝ) ^ 2),
      ∀ z : ℂ, ‖z - center‖ = ρ →
        (N : ℝ) ^ 2 * ‖z - center‖ ≤ 1 ∧
        ∀ i, 1 / (4 * ((K : ℝ) + 1) * (N : ℝ) ^ 2) ≤ ‖z - roots i‖ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNsq : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNR
  have ha : 0 < 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have hab : 1 / (2 * (N : ℝ) ^ 2) < 1 / (N : ℝ) ^ 2 := by
    apply (div_lt_div_iff₀ (by positivity) hNsq).mpr
    nlinarith
  obtain ⟨ρ, hρ, hsep⟩ := exists_separated_circle roots center ha hab
  refine ⟨ρ, hρ, fun z hz => ⟨?_, ?_⟩⟩
  · rw [hz]
    have h := (le_div_iff₀ hNsq).mp hρ.2
    nlinarith
  · intro i
    have he : ((1 / (N : ℝ) ^ 2) - 1 / (2 * (N : ℝ) ^ 2)) /
        (2 * ((K : ℝ) + 1)) = 1 / (4 * ((K : ℝ) + 1) * (N : ℝ) ^ 2) := by
      field_simp
      <;> ring
    rw [← he]
    exact hsep z hz i

theorem polynomial_norm_at_center_le_of_sphere (Q : ℂ[X]) {center : ℂ} {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : ∀ z : ℂ, ‖z - center‖ = ρ → ‖Q.eval z‖ ≤ B) :
    ‖Q.eval center‖ ≤ B := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (f := fun z : ℂ => Q.eval z) (U := Metric.ball center ρ) Metric.isBounded_ball
    (Polynomial.differentiable _).diffContOnCl
  · intro z hz
    rw [frontier_ball _ hρ.ne'] at hz
    exact hB z (by simpa only [Metric.mem_sphere, dist_eq_norm] using hz)
  · rw [closure_ball _ hρ.ne']
    simp [hρ.le]

/-- The exceptional-set separation costs a polynomial prefactor only. A local
Green perturbation bound transfers the separated-point estimate to the center,
including centers which themselves are roots. -/
theorem polynomial_center_bound_of_exceptional_set {K N : ℕ}
    (Q : ℂ[X]) (roots : Fin K → ℂ) (center : ℂ) (hN : 0 < N)
    (g : ℂ → ℝ) {σ L B : ℝ} (hB : 0 ≤ B)
    (hperturb : ∀ z : ℂ, (N : ℝ) ^ 2 * ‖z - center‖ ≤ 1 →
      σ * g z ≤ σ * g center + L)
    (hbound : ∀ z : ℂ, (N : ℝ) ^ 2 * ‖z - center‖ ≤ 1 →
      (∀ i, 1 / (4 * ((K : ℝ) + 1) * (N : ℝ) ^ 2) ≤ ‖z - roots i‖) →
      ‖Q.eval z‖ ≤ B * Real.exp (σ * g z)) :
    ‖Q.eval center‖ ≤ (B * Real.exp L) * Real.exp (σ * g center) := by
  obtain ⟨ρ, hρ, hsep⟩ := exists_separated_small_circle roots center hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρ.1
  apply polynomial_norm_at_center_le_of_sphere Q hρ0
  intro z hz
  obtain ⟨hclose, havoid⟩ := hsep z hz
  calc
    ‖Q.eval z‖ ≤ B * Real.exp (σ * g z) := hbound z hclose havoid
    _ ≤ B * Real.exp (σ * g center + L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hperturb z hclose)) hB
    _ = _ := by rw [Real.exp_add]; ring

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.exists_separated_circle
#print axioms CatalanMeasure.GenD.Analytic.exists_separated_small_circle
#print axioms CatalanMeasure.GenD.Analytic.polynomial_norm_at_center_le_of_sphere

#print axioms CatalanMeasure.GenD.Analytic.polynomial_center_bound_of_exceptional_set

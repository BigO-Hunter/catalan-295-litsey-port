module

public import CatalanMeasure.GenD.Analytic.CardinalGreen
public import CatalanMeasure.GenD.Signed.Davis.GeneralNodalWeights
public import CatalanMeasure.GenD.Analytic.WeightedAtom

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

def scaledNodalPhi (P : Parameters) (N k : ℕ) (g : ℂ → ℝ) (z : ℂ) : ℝ :=
  (2 * (P.g N : ℝ) - (k : ℝ)) * Real.log ‖z‖ +
    ((P.h N + P.q N : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
    (((P.n0 - P.g0) * N : ℕ) : ℝ) * g z

theorem filtered_basis_norm_eq (P : Parameters) (N : ℕ) (R : ℝ[X]) (z : ℂ) :
    ‖((((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).map (algebraMap ℝ ℂ))).eval z‖ =
      ‖z‖ ^ (P.A N) * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) *
        ‖(R.map (algebraMap ℝ ℂ)).eval z‖ := by
  simp only [rowCommonFactor, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, eval_mul,
    eval_pow, eval_sub, eval_one, eval_X, norm_mul, norm_pow]
  rw [norm_sub_rev z 1, pow_add]
  ring

theorem filtered_basis_le_scaled_phi (P : Parameters) (N k : ℕ) (R : ℝ[X])
    (g : ℂ → ℝ) {z : ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hz : ‖z‖ ≠ 0) (hfilter : ‖(1 : ℂ) - z‖ ≠ 0)
    (hcard : ‖(R.map (algebraMap ℝ ℂ)).eval z‖ ≤
      B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z)) :
    ‖((((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).map (algebraMap ℝ ℂ))).eval z‖ ≤
      B * Real.exp (scaledNodalPhi P N k g z) *
        ‖z‖ ^ (P.b N + k + P.q N) := by
  have hzpos : 0 < ‖z‖ := (norm_nonneg _).lt_of_ne' hz
  have hfpos : 0 < ‖(1 : ℂ) - z‖ := (norm_nonneg _).lt_of_ne' hfilter
  have hp : ∀ (x : ℝ), 0 < x → ∀ j : ℕ, x ^ j = Real.exp ((j : ℝ) * Real.log x) := by
    intro x hx j
    rw [Real.exp_nat_mul, Real.exp_log hx]
  have he : ‖z‖ ^ P.A N * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) *
      Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z) =
      Real.exp (scaledNodalPhi P N k g z) * ‖z‖ ^ (P.b N + k + P.q N) := by
    rw [hp _ hzpos, hp _ hfpos, hp _ hzpos, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold scaledNodalPhi Parameters.A
    push_cast
    ring
  rw [filtered_basis_norm_eq]
  calc
    _ ≤ (‖z‖ ^ P.A N * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N)) *
        (B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z)) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = B * (‖z‖ ^ P.A N * ‖(1 : ℂ) - z‖ ^ (P.h N + P.q N) *
        Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z)) := by ring
    _ = _ := by rw [he]; ring

theorem filtered_basis_eval_one (P : Parameters) {N : ℕ} (hfilter : 0 < P.h N + P.q N)
    (R : ℝ[X]) :
    (((rowCommonFactor P N * R) * (X - 1) ^ (P.q N))).eval (1 : ℝ) = 0 := by
  by_cases hq : P.q N = 0
  · have hh : P.h N ≠ 0 := by omega
    simp [rowCommonFactor, hq, hh]
  · simp [hq]

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.scaledNodalPhi
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_norm_eq
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_le_scaled_phi
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_eval_one

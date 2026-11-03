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

theorem filtered_basis_le_scaled_phi_all (P : Parameters) (N k : ℕ) (R : ℝ[X])
    (g : ℂ → ℝ) {z : ℂ} {B : ℝ} (hB : 0 ≤ B) (hz : ‖z‖ ≠ 0)
    (hHQ : 0 < P.h N + P.q N)
    (hcard : ‖(R.map (algebraMap ℝ ℂ)).eval z‖ ≤
      B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z)) :
    ‖((((rowCommonFactor P N * R) * (X - 1) ^ (P.q N)).map (algebraMap ℝ ℂ))).eval z‖ ≤
      B * Real.exp (scaledNodalPhi P N k g z) * ‖z‖ ^ (P.b N + k + P.q N) := by
  by_cases hf : ‖(1 : ℂ) - z‖ = 0
  · rw [filtered_basis_norm_eq, hf, zero_pow hHQ.ne', mul_zero, zero_mul]
    positivity
  · exact filtered_basis_le_scaled_phi P N k R g hB hz hf hcard

theorem nodal_functional_le_of_scaled_phi (P : Parameters) (hg : P.g0 ≤ P.n0)
    {N : ℕ} {τ : Fin ((P.n0 - P.g0) * N) → ℝ} (hτ : Function.Injective τ)
    (k : ℕ) (i : Fin ((P.n0 - P.g0) * N)) (g : ℂ → ℝ) {r B F : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hHQ : 0 < P.h N + P.q N)
    (hcard : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
        B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z))
    (hcirc : ∀ z : ℂ, ‖z‖ = r → scaledNodalPhi P N k g z ≤ F)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 → scaledNodalPhi P N k g (x : ℂ) ≤ F) :
    |polynomialFunctional P N k (rowCommonFactor P N * quadBasis τ i)| ≤
      4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) * (B * Real.exp F) := by
  have hpoint : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ 1 → scaledNodalPhi P N k g z ≤ F →
      ‖((((rowCommonFactor P N * quadBasis τ i) * (X - 1) ^ (P.q N)).map
        (algebraMap ℝ ℂ))).eval z‖ ≤ B * Real.exp F * ‖z‖ ^ (P.b N + k + P.q N) := by
    intro z hz0 hz1 hphi
    exact (filtered_basis_le_scaled_phi_all P N k _ g hB hz0.ne' hHQ (hcard z hz1)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphi) hB) (by positivity))
  have hfun := Signed.Keyhole.polynomialFunctional_keyhole_le P N k (quadBasis τ i)
    (general_common_basis_coeff_zero P hg N hτ i) hr0 hr1
    (fun z hz => by simpa only [hz] using hpoint z (by rwa [hz]) (hz.trans_le hr1) (hcirc z hz))
    (fun x hx hx1 => by
      let Q : ℝ[X] := (rowCommonFactor P N * quadBasis τ i) * (X - 1) ^ (P.q N)
      have hx0 : 0 < |x| := hr0.trans_le hx
      have ht := hpoint (x : ℂ) (by simpa using hx0) (by simpa using hx1) (hseg x hx hx1)
      have he : (Q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
        rw [Polynomial.eval_map, show (x : ℂ) = algebraMap ℝ ℂ x from rfl, Polynomial.eval₂_at_apply]
        rfl
      change ‖(Q.map (algebraMap ℝ ℂ)).eval (x : ℂ)‖ ≤ _ at ht
      rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at ht
      exact ht)
  simpa only [max_self] using hfun

theorem restrictedWeight_joint_le_functional (P : Parameters) (N k : ℕ)
    {J : ℕ} (τ : Fin J → ℝ) (i : Fin J) :
    |(rowCommonFactor P N).eval (τ i)| * |restrictedWeight P N k τ i| ≤
      |polynomialFunctional P N k (rowCommonFactor P N * quadBasis τ i)| := by
  unfold restrictedWeight
  rw [abs_div]
  by_cases hc : (rowCommonFactor P N).eval (τ i) = 0
  · simp [hc]
  · have hca := abs_ne_zero.mpr hc
    have he : |(rowCommonFactor P N).eval (τ i)| *
        (|polynomialFunctional P N k (rowCommonFactor P N * quadBasis τ i)| /
          |(rowCommonFactor P N).eval (τ i)|) =
        |polynomialFunctional P N k (rowCommonFactor P N * quadBasis τ i)| := by field_simp
    exact he.le

theorem nodal_weight_joint_le_of_scaled_phi (P : Parameters) (hg : P.g0 ≤ P.n0)
    {N : ℕ} {τ : Fin ((P.n0 - P.g0) * N) → ℝ} (hτ : Function.Injective τ)
    (k : ℕ) (i : Fin ((P.n0 - P.g0) * N)) (g : ℂ → ℝ) {r B F : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hB : 0 ≤ B) (hHQ : 0 < P.h N + P.q N)
    (hcard : ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖((quadBasis τ i).map (algebraMap ℝ ℂ)).eval z‖ ≤
        B * Real.exp ((((P.n0 - P.g0) * N : ℕ) : ℝ) * g z))
    (hcirc : ∀ z : ℂ, ‖z‖ = r → scaledNodalPhi P N k g z ≤ F)
    (hseg : ∀ x : ℝ, r ≤ |x| → |x| ≤ 1 → scaledNodalPhi P N k g (x : ℂ) ≤ F) :
    |(rowCommonFactor P N).eval (τ i)| * |restrictedWeight P N k τ i| ≤
      4 * (1 + ((P.b N + k + P.q N - P.A N : ℕ) : ℝ)) * (B * Real.exp F) := by
  exact (restrictedWeight_joint_le_functional P N k τ i).trans
    (nodal_functional_le_of_scaled_phi P hg hτ k i g hr0 hr1 hB hHQ hcard hcirc hseg)

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.scaledNodalPhi
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_norm_eq
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_le_scaled_phi
#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_eval_one

#print axioms CatalanMeasure.GenD.Analytic.filtered_basis_le_scaled_phi_all

#print axioms CatalanMeasure.GenD.Analytic.nodal_functional_le_of_scaled_phi

#print axioms CatalanMeasure.GenD.Analytic.restrictedWeight_joint_le_functional

#print axioms CatalanMeasure.GenD.Analytic.nodal_weight_joint_le_of_scaled_phi

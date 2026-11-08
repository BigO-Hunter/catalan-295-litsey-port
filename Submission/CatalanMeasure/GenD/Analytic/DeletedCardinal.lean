module

public import Submission.CatalanMeasure.GenD.Signed.Davis.NodalRootDeletion
public import Submission.CatalanMeasure.GenD.Analytic.GapCircleGen
public import Submission.CatalanMeasure.GenD.Analytic.NodalGreen

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset OAI.InternalCatalan
noncomputable section

/-! Arbitrary-point deletion estimates for the sharp Davis keyhole route.
Only the bounded deleted set and the chosen retained root require separation. -/

theorem removedNodal_norm_ge_of_separation {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hSM : S ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (z : ℂ)
    (hsep : ∀ i : Fin S, δ ≤ ‖z - (τ (Fin.natAdd J i) : ℂ)‖) :
    δ ^ M ≤ ‖((removedNodal τ).map (algebraMap ℝ ℂ)).eval z‖ := by
  unfold removedNodal
  rw [Polynomial.map_prod, eval_prod, norm_prod]
  have hp : (∏ _i : Fin S, δ) ≤ ∏ i : Fin S,
      ‖(((X - C (τ (Fin.natAdd J i)) : ℝ[X]).map (algebraMap ℝ ℂ)).eval z)‖ := by
    apply Finset.prod_le_prod₀ (fun _ _ => hδ0.le)
    intro i _
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      eval_sub, eval_X, eval_C, Complex.coe_algebraMap] using hsep i
  have hpow := pow_le_pow_of_le_one hδ0.le hδ1 hSM
  exact hpow.trans (by simpa using hp)

theorem retainedNodal_norm_le_of_separation {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hSM : S ≤ M) {H : ℝ[X]} {c δ : ℝ}
    (hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (z : ℂ)
    (hsep : ∀ i : Fin S, δ ≤ ‖z - (τ (Fin.natAdd J i) : ℂ)‖) :
    ‖((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z‖ ≤
      ‖(H.map (algebraMap ℝ ℂ)).eval z‖ / δ ^ M := by
  have hn := congrArg (fun Q : ℝ[X] => ‖(Q.map (algebraMap ℝ ℂ)).eval z‖)
    (hH.trans (retained_removed_factorization τ c))
  simp only [Polynomial.map_mul, eval_mul, norm_mul] at hn
  apply (le_div_iff₀ (pow_pos hδ0 M)).mpr
  exact (mul_le_mul_of_nonneg_left
    (removedNodal_norm_ge_of_separation hSM hδ0 hδ1 z hsep) (norm_nonneg _)).trans_eq hn.symm

theorem retained_cardinal_norm_le_of_separation {J S M : ℕ} {τ : Fin (J + S) → ℝ}
    (hτ : Function.Injective τ) (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1)
    (hSM : S ≤ M) {H : ℝ[X]} {c d δ : ℝ}
    (hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hd : 0 < d) (hder : ∀ i, d ≤ |H.derivative.eval (τ i)|)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (z : ℂ)
    (hsep : ∀ i : Fin S, δ ≤ ‖z - (τ (Fin.natAdd J i) : ℂ)‖)
    (i : Fin J) (hi : δ ≤ ‖z - (retainedNodes τ i : ℂ)‖) :
    ‖((quadBasis (retainedNodes τ) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      2 ^ M * ‖(H.map (algebraMap ℝ ℂ)).eval z‖ / (d * δ ^ (M + 1)) := by
  have hd' : 0 < d / 2 ^ M := div_pos hd (by positivity)
  have hcard := norm_cardinal_le_of_nodal_sep (retainedNodes_injective hτ) i
    (show retainedNodal τ c = C c * ∏ j : Fin J, (X - C (retainedNodes τ j)) from rfl)
    hd' (retainedNodal_derivative_ge hmem hSM hH hder i) hδ0 z hi
  have hnorm := retainedNodal_norm_le_of_separation hSM hH hδ0 hδ1 z hsep
  calc
    _ ≤ ‖((retainedNodal τ c).map (algebraMap ℝ ℂ)).eval z‖ / ((d / 2 ^ M) * δ) := hcard
    _ ≤ (‖(H.map (algebraMap ℝ ℂ)).eval z‖ / δ ^ M) / ((d / 2 ^ M) * δ) :=
      div_le_div_of_nonneg_right hnorm (mul_pos hd' hδ0).le
    _ = _ := by rw [pow_succ]; field_simp [hd.ne', hδ0.ne']

/-- Specialization to the Chebyshev composition loses no exponential rate. -/
theorem retained_cardinal_norm_le_green {J S M m K : ℕ} {τ : Fin (J + S) → ℝ}
    (hτ : Function.Injective τ) (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1)
    (hSM : S ≤ M) (p : ℝ[X]) (hm : 0 < m) {c d δ : ℝ}
    (hH : (Chebyshev.T ℝ (K : ℤ)).comp p =
      C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hd : 0 < d)
    (hder : ∀ i, d ≤ |((Chebyshev.T ℝ (K : ℤ)).comp p).derivative.eval (τ i)|)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (z : ℂ)
    (hsep : ∀ i : Fin S, δ ≤ ‖z - (τ (Fin.natAdd J i) : ℂ)‖)
    (i : Fin J) (hi : δ ≤ ‖z - (retainedNodes τ i : ℂ)‖) :
    ‖((quadBasis (retainedNodes τ) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
      2 ^ M * Real.exp (((m * K : ℕ) : ℝ) * nodalGreen p m z) / (d * δ ^ (M + 1)) := by
  exact (retained_cardinal_norm_le_of_separation hτ hmem hSM hH hd hder hδ0 hδ1 z hsep i hi).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (chebyshev_comp_norm_le_green p hm K z) (by positivity))
      (mul_pos hd (pow_pos hδ0 _)).le)

end
end CatalanMeasure.GenD.Analytic

#print axioms CatalanMeasure.GenD.Analytic.removedNodal_norm_ge_of_separation
#print axioms CatalanMeasure.GenD.Analytic.retainedNodal_norm_le_of_separation
#print axioms CatalanMeasure.GenD.Analytic.retained_cardinal_norm_le_of_separation
#print axioms CatalanMeasure.GenD.Analytic.retained_cardinal_norm_le_green

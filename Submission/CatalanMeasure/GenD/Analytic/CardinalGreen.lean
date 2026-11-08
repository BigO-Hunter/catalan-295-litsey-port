module

public import Submission.CatalanMeasure.GenD.Analytic.AvoidingCircles

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset OAI.InternalCatalan
noncomputable section

def cardinalExceptionalNodes {J S : ℕ} (τ : Fin (J + S) → ℝ) (i : Fin J) :
    Fin (S + 1) → ℂ :=
  Fin.lastCases (retainedNodes τ i : ℂ) (fun j => (τ (Fin.natAdd J j) : ℂ))

/-- Local-to-center assembly for any full nodal polynomial. Once its growth is
bounded by a Green exponential, deleting S roots costs at most N^(2(M+1)). -/
theorem retained_cardinal_center_bound {J S M N : ℕ} {τ : Fin (J + S) → ℝ}
    (hτ : Function.Injective τ) (hmem : ∀ i, τ i ∈ Set.Ioo (-1 : ℝ) 1)
    (hSM : S ≤ M) {H : ℝ[X]} {c d A L σ : ℝ}
    (hH : H = C c * ∏ i : Fin (J + S), (X - C (τ i)))
    (hd : 0 < d) (hder : ∀ i, d ≤ |H.derivative.eval (τ i)|)
    (hN : 0 < N) (hA : 0 ≤ A) (g : ℂ → ℝ) (center : ℂ) (i : Fin J)
    (hgrowth : ∀ z : ℂ, (N : ℝ) ^ 2 * ‖z - center‖ ≤ 1 →
      ‖(H.map (algebraMap ℝ ℂ)).eval z‖ ≤ A * Real.exp (σ * g z))
    (hperturb : ∀ z : ℂ, (N : ℝ) ^ 2 * ‖z - center‖ ≤ 1 →
      σ * g z ≤ σ * g center + L) :
    ‖((quadBasis (retainedNodes τ) i).map (algebraMap ℝ ℂ)).eval center‖ ≤
      ((2 ^ M * A / (d * (1 / (4 * ((S : ℝ) + 2) * (N : ℝ) ^ 2)) ^ (M + 1))) *
        Real.exp L) * Real.exp (σ * g center) := by
  let δ : ℝ := 1 / (4 * ((S : ℝ) + 2) * (N : ℝ) ^ 2)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNsq : 1 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hp : 2 ≤ ((S : ℝ) + 2) * (N : ℝ) ^ 2 := by
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ ((S : ℝ) + 2) * (N : ℝ) ^ 2 :=
        mul_le_mul (by linarith [Nat.cast_nonneg (α := ℝ) S]) hNsq (by norm_num) (by positivity)
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  let B : ℝ := 2 ^ M * A / (d * δ ^ (M + 1))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply polynomial_center_bound_of_exceptional_set
    ((quadBasis (retainedNodes τ) i).map (algebraMap ℝ ℂ))
    (cardinalExceptionalNodes τ i) center hN g hB hperturb
  intro z hclose havoid
  have havoid' : ∀ k, δ ≤ ‖z - cardinalExceptionalNodes τ i k‖ := by
    intro k
    simpa only [δ, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using havoid k
  have hremoved : ∀ j : Fin S, δ ≤ ‖z - (τ (Fin.natAdd J j) : ℂ)‖ := by
    intro j
    simpa [cardinalExceptionalNodes] using havoid' (Fin.castSucc j)
  have hchosen : δ ≤ ‖z - (retainedNodes τ i : ℂ)‖ := by
    simpa [cardinalExceptionalNodes] using havoid' (Fin.last S)
  have hcard := retained_cardinal_norm_le_of_separation hτ hmem hSM hH hd hder
    hδ0 hδ1 z hremoved i hchosen
  calc
    _ ≤ 2 ^ M * ‖(H.map (algebraMap ℝ ℂ)).eval z‖ / (d * δ ^ (M + 1)) := hcard
    _ ≤ 2 ^ M * (A * Real.exp (σ * g z)) / (d * δ ^ (M + 1)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hgrowth z hclose) (by positivity)) (by positivity)
    _ = B * Real.exp (σ * g z) := by dsimp [B]; ring

/-- Uniform sharp cardinal growth on a fixed disk. All losses are fixed constants
and N^(2(M+1)); the Green exponent is exactly d0*N with no positive rate loss. -/
theorem uniform_retained_cardinal_green_bound (p : ℝ[X]) {m : ℕ} (hm : 0 < m)
    (d0 M padding : ℕ) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (N K S : ℕ) (τ : Fin (d0 * N + S) → ℝ) (c : ℝ),
      0 < N → S ≤ M → Function.Injective τ →
      (∀ j, τ j ∈ Set.Ioo (-1 : ℝ) 1) →
      m * K ≤ d0 * N + padding →
      (Chebyshev.T ℝ (K : ℤ)).comp p = C c * ∏ j, (X - C (τ j)) →
      (∀ j, d ≤ |((Chebyshev.T ℝ (K : ℤ)).comp p).derivative.eval (τ j)|) →
      ∀ z : ℂ, ‖z‖ ≤ R → ∀ i : Fin (d0 * N),
        ‖((quadBasis (retainedNodes τ) i).map (algebraMap ℝ ℂ)).eval z‖ ≤
          C0 * (N : ℝ) ^ (2 * (M + 1)) *
            Real.exp (((d0 * N : ℕ) : ℝ) * nodalGreen p m z) := by
  let s : Set ℂ := Metric.closedBall 0 (R + 1)
  have hs : IsCompact s := isCompact_closedBall _ _
  obtain ⟨A, hA, hpad⟩ := chebyshev_comp_norm_le_green_padded p hm hs padding
  obtain ⟨L, hL, hpert⟩ := nodalGreen_scaled_perturbation p hm hs
  let C0 : ℝ := 2 ^ M * A / d * (4 * ((M : ℝ) + 2)) ^ (M + 1) *
    Real.exp ((d0 : ℝ) * L)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨C0, hC0, fun N K S τ c hN hSM hτ hmem hdeg hfactor hder z hz i => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNsq : 1 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hzin : z ∈ s := by
    change dist z 0 ≤ R + 1
    simpa only [dist_zero_right] using (show ‖z‖ ≤ R + 1 by linarith)
  have hwin : ∀ w : ℂ, (N : ℝ) ^ 2 * ‖w - z‖ ≤ 1 → w ∈ s := by
    intro w hw
    have hdist : ‖w - z‖ ≤ 1 := by
      have hh := mul_nonneg (sub_nonneg.mpr hNsq) (norm_nonneg (w - z))
      nlinarith
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    change dist w 0 ≤ R + 1
    rw [dist_zero_right]
    linarith
  have hgrowth : ∀ w : ℂ, (N : ℝ) ^ 2 * ‖w - z‖ ≤ 1 →
      ‖((((Chebyshev.T ℝ (K : ℤ)).comp p).map (algebraMap ℝ ℂ))).eval w‖ ≤
        A * Real.exp (((d0 * N : ℕ) : ℝ) * nodalGreen p m w) := by
    intro w hw
    exact hpad (d0 * N) K hdeg w (hwin w hw)
  have hperturb : ∀ w : ℂ, (N : ℝ) ^ 2 * ‖w - z‖ ≤ 1 →
      ((d0 * N : ℕ) : ℝ) * nodalGreen p m w ≤
        ((d0 * N : ℕ) : ℝ) * nodalGreen p m z + (d0 : ℝ) * L := by
    intro w hw
    have ht := mul_le_mul_of_nonneg_left (hpert N w (hwin w hw) z hzin hw) (Nat.cast_nonneg d0)
    push_cast
    nlinarith only [ht]
  have hcenter := retained_cardinal_center_bound hτ hmem hSM hfactor hd hder hN hA.le
    (nodalGreen p m) z i hgrowth hperturb
  have hSe : (S : ℝ) ≤ M := by exact_mod_cast hSM
  have hpow : (4 * ((S : ℝ) + 2)) ^ (M + 1) ≤
      (4 * ((M : ℝ) + 2)) ^ (M + 1) := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hid : (2 ^ M * A / (d * (1 / (4 * ((S : ℝ) + 2) * (N : ℝ) ^ 2)) ^ (M + 1))) *
      Real.exp ((d0 : ℝ) * L) =
      (2 ^ M * A / d * (4 * ((S : ℝ) + 2)) ^ (M + 1) * Real.exp ((d0 : ℝ) * L)) *
        (N : ℝ) ^ (2 * (M + 1)) := by
    simp only [mul_pow, div_pow, one_pow, ← pow_mul]
    field_simp
    <;> ring
  rw [hid] at hcenter
  apply hcenter.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [C0]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (Real.exp_pos _).le

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.cardinalExceptionalNodes
#print axioms CatalanMeasure.GenD.Analytic.retained_cardinal_center_bound

#print axioms CatalanMeasure.GenD.Analytic.uniform_retained_cardinal_green_bound

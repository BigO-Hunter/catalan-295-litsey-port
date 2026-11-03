module

public import CatalanMeasure.GenD.Analytic.AvoidingCircles

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

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.cardinalExceptionalNodes
#print axioms CatalanMeasure.GenD.Analytic.retained_cardinal_center_bound

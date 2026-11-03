module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic.GaussianHorner
noncomputable section

def plus (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 + b.1, a.2 + b.2)
def times (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def castPair (a : ℤ × ℤ) : ℂ := ⟨(a.1 : ℝ), (a.2 : ℝ)⟩

theorem castPair_plus (a b : ℤ × ℤ) : castPair (plus a b) = castPair a + castPair b := by
  apply Complex.ext <;> simp [castPair, plus]

theorem castPair_times (a b : ℤ × ℤ) : castPair (times a b) = castPair a * castPair b := by
  apply Complex.ext <;> simp [castPair, times, Complex.mul_re, Complex.mul_im]

theorem castPair_real (a : ℤ) : castPair (a, 0) = (a : ℂ) := by
  apply Complex.ext <;> simp [castPair]

def valueStep (c : ℤ × ℤ) (q : ℤ) (state : (ℤ × ℤ) × ℤ) (a : ℤ) : (ℤ × ℤ) × ℤ :=
  (plus (times c state.1) (a * state.2, 0), state.2 * q)

/-- One general homogeneous-Horner invariant, shared by point evaluation and
the coefficient translation tower. No numerical computation is trusted. -/
theorem homogeneous_fold_invariant {S : Type*} (step : S → ℤ → S)
    (value : S → ℂ) (power : S → ℤ) {q : ℤ} (hq : q ≠ 0) (c : ℂ)
    (hv : ∀ s a, value (step s a) = c * value s + (a : ℂ) * (power s : ℂ))
    (hp : ∀ s a, power (step s a) = power s * q)
    (as : List ℤ) (s : S) (H : ℂ) (h : value s * (q : ℂ) = (power s : ℂ) * H) :
    value (as.foldl step s) * (q : ℂ) = (power (as.foldl step s) : ℂ) *
      as.foldl (fun (v : ℂ) (a : ℤ) => c / (q : ℂ) * v + (a : ℂ)) H := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  induction as generalizing s H with
  | nil => simpa only [List.foldl_nil] using h
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hv, hp, Int.cast_mul]
    calc
      (c * value s + (a : ℂ) * (power s : ℂ)) * (q : ℂ) =
          c * (value s * (q : ℂ)) + (power s : ℂ) * (q : ℂ) * (a : ℂ) := by ring
      _ = c * ((power s : ℂ) * H) + (power s : ℂ) * (q : ℂ) * (a : ℂ) := by rw [h]
      _ = _ := by field_simp [hqC] <;> ring

theorem fold_power {S : Type*} (step : S → ℤ → S) (power : S → ℤ) (q : ℤ)
    (hp : ∀ s a, power (step s a) = power s * q) (as : List ℤ) (s : S) :
    power (as.foldl step s) = power s * q ^ as.length := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.length_cons, ih, hp, pow_succ]
    ring

theorem point_value_sound (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0) (as : List ℤ) :
    castPair (as.foldl (valueStep c q) ((0, 0), 1)).1 * (q : ℂ) =
      (q : ℂ) ^ as.length *
        as.foldl (fun (v : ℂ) (a : ℤ) => castPair c / (q : ℂ) * v + (a : ℂ)) 0 := by
  have hv : ∀ s a, castPair (valueStep c q s a).1 =
      castPair c * castPair s.1 + (a : ℂ) * (s.2 : ℂ) := by
    intro s a
    simp only [valueStep, castPair_plus, castPair_times, castPair_real, Int.cast_mul]
  have hp : ∀ s a, (valueStep c q s a).2 = s.2 * q := fun _ _ => rfl
  have ht := homogeneous_fold_invariant (valueStep c q) (fun s => castPair s.1)
    (fun s => s.2) hq (castPair c) hv hp as ((0, 0), 1) 0 (by rw [castPair_real]; simp)
  have hpower := fold_power (valueStep c q) (fun s => s.2) q hp as ((0, 0), 1)
  rw [hpower, one_mul, Int.cast_pow] at ht
  exact ht

end
end CatalanMeasure.GenD.Analytic.GaussianHorner
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_plus
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_times
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_real
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.homogeneous_fold_invariant
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.fold_power
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.point_value_sound

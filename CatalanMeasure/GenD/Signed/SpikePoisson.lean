module

public import CatalanMeasure.GenD.Signed.CrossDilation
public import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialRat
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Poisson sequences (SIMPLIFY-S2 §2.4)

For `|ρ| < 1` let `β_ρ` be the probability measure on `[0, π]` (the variable `θ`, `u = cos θ`) with
density `poissonQ ρ θ = (1 - ρ²) / (π (1 + 2ρ cos θ + ρ²))`.  Its Chebyshev moments are the Poisson
sequence `∫ T_k dβ_ρ = (-ρ)^k` (`integral_cos_poissonMeasure`), and every closed form of the
balayage of a spike is a geometric series in these moments:

* `integral_crossLog_poissonMeasure`: `∫ l(x, cos θ) dβ_ρ = 2 log (1 - ρ x)` for `|x| < 1`;
* `integral_barrierTrialT_poissonMeasure`: `∫ T_a(cos θ) dβ_ρ = S_a(-ρ)` for summable `a`;
* `neg_row_bound` (Lemma 5): `log ((1+y)/(1+ρy)) ≤ log (2/(1+ρ))` for `y ∈ [0,1]`, `ρ ∈ [0,1)`;
* `crossLog_poisson_antitone` (stochastic order): `ρ ↦ 2 log (1 - ρ x)` is non-increasing for
  `x ≥ 0`.
-/

namespace CatalanMeasure.GenD.Signed

open MeasureTheory Set Real Filter Topology
open CatalanMeasure.Signed

/-! ### Integrals of cosines -/

theorem integral_cos_int (m : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((m : ℝ) * θ) = if m = 0 then π else 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [if_neg hm, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos]
    simp [Real.sin_int_mul_pi]

theorem integral_cos_mul_cos (k j : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((k : ℝ) * θ) * Real.cos ((j : ℝ) * θ) =
      ((if k = j then π else 0) + (if k + j = 0 then π else 0)) / 2 := by
  have h : ∀ θ : ℝ, Real.cos ((k : ℝ) * θ) * Real.cos ((j : ℝ) * θ) =
      (Real.cos ((((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * θ) +
        Real.cos ((((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), integral_cos_int, integral_cos_int]
  have e1 : (((k : ℤ) - (j : ℤ)) = 0) ↔ k = j := by omega
  have e2 : (((k : ℤ) + (j : ℤ)) = 0) ↔ k + j = 0 := by omega
  simp only [e1, e2]

/-! ### The Poisson kernel -/

/-- The Poisson density in `θ`. -/
noncomputable def poissonQ (ρ θ : ℝ) : ℝ := (1 - ρ ^ 2) / (π * (1 + 2 * ρ * Real.cos θ + ρ ^ 2))

theorem poisson_den_pos {ρ : ℝ} (hρ : |ρ| < 1) (θ : ℝ) : 0 < 1 + 2 * ρ * Real.cos θ + ρ ^ 2 := by
  have h1 : |ρ * Real.cos θ| ≤ |ρ| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : -|ρ| ≤ ρ * Real.cos θ := by linarith [neg_abs_le (ρ * Real.cos θ)]
  have h3 : ρ ^ 2 = |ρ| ^ 2 := (sq_abs ρ).symm
  nlinarith [abs_nonneg ρ]

theorem poissonQ_pos {ρ : ℝ} (hρ : |ρ| < 1) (θ : ℝ) : 0 < poissonQ ρ θ := by
  unfold poissonQ
  have : 0 < 1 - ρ ^ 2 := by nlinarith [abs_lt.mp hρ]
  exact div_pos this (mul_pos Real.pi_pos (poisson_den_pos hρ θ))

theorem continuous_poissonQ {ρ : ℝ} (hρ : |ρ| < 1) : Continuous (poissonQ ρ) := by
  unfold poissonQ
  exact continuous_const.div (continuous_const.mul (by fun_prop))
    fun θ => (mul_pos Real.pi_pos (poisson_den_pos hρ θ)).ne'

/-- The Chebyshev coefficients of the Poisson kernel: `1` and `2 (-ρ)^k`. -/
noncomputable def poissonCoef (ρ : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else 2 * (-ρ) ^ k

theorem abs_poissonCoef_le (ρ : ℝ) (k : ℕ) : |poissonCoef ρ k| ≤ 2 * |ρ| ^ k := by
  unfold poissonCoef
  split_ifs with h
  · subst h; simp
  · rw [abs_mul, abs_pow, abs_neg]; simp

theorem poisson_series {ρ : ℝ} (hρ : |ρ| < 1) (θ : ℝ) :
    HasSum (fun k : ℕ => poissonCoef ρ k * Real.cos ((k : ℝ) * θ)) (π * poissonQ ρ θ) := by
  set z : ℂ := (-(ρ : ℂ)) * Complex.exp (θ * Complex.I) with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one]
    simpa using hρ
  have hg := hasSum_geometric_of_norm_lt_one hzn
  have hre := ((Complex.hasSum_iff _ _).mp hg).1
  have hk : ∀ k : ℕ, (z ^ k).re = (-ρ) ^ k * Real.cos ((k : ℝ) * θ) := by
    intro k
    have : z ^ k = (((-ρ) ^ k : ℝ) : ℂ) * Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I) := by
      rw [hz, mul_pow, ← Complex.exp_nat_mul]
      push_cast
      congr 2
      ring
    rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hinv : ((1 - z)⁻¹).re = (1 + ρ * Real.cos θ) / (1 + 2 * ρ * Real.cos θ + ρ ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    have hre1 : (1 - z).re = 1 + ρ * Real.cos θ := by
      simp [hz, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have him1 : (1 - z).im = ρ * Real.sin θ := by
      simp [hz, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    rw [hre1, him1]
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp_rw [hk] at hre
  rw [hinv] at hre
  have h2 := hre.mul_left 2
  have h3 := h2.sub (hasSum_ite_eq 0 (1 : ℝ))
  convert h3 using 1
  · funext k
    unfold poissonCoef
    split_ifs with h
    · subst h; norm_num
    · ring
  · unfold poissonQ
    obtain ⟨D, hDdef⟩ : ∃ D, D = 1 + 2 * ρ * Real.cos θ + ρ ^ 2 := ⟨_, rfl⟩
    have hD : D ≠ 0 := by rw [hDdef]; exact (poisson_den_pos hρ θ).ne'
    rw [← hDdef]
    have hπ := Real.pi_pos.ne'
    field_simp
    rw [hDdef]
    ring

/-! ### The Poisson measure -/

/-- The Poisson probability measure in the variable `θ ∈ [0, π]`. -/
noncomputable def poissonMeasure (ρ : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 π)).withDensity fun θ => ENNReal.ofReal (poissonQ ρ θ)

/-- Termwise integration of a summable series against a bounded continuous function. -/
theorem hasSum_integral_series {c b : ℕ → ℝ} (hb : Summable b) (hcb : ∀ k, |c k| ≤ b k)
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hgB : ∀ θ ∈ Icc (0 : ℝ) π, |g θ| ≤ B) {f : ℝ → ℝ}
    (hf : ∀ θ, HasSum (fun k : ℕ => c k * Real.cos ((k : ℝ) * θ)) (f θ)) :
    HasSum (fun k : ℕ => ∫ θ in (0 : ℝ)..π, c k * Real.cos ((k : ℝ) * θ) * g θ)
      (∫ θ in (0 : ℝ)..π, f θ * g θ) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => b k * B) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · exact ((continuous_const.mul (by fun_prop)).mul hg).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun θ hθ => ?_
    rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
    have hθ' : θ ∈ Icc (0 : ℝ) π := ⟨hθ.1.le, hθ.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0 ⟨le_rfl, Real.pi_pos.le⟩)
    have hbk : 0 ≤ b k := (abs_nonneg _).trans (hcb k)
    calc |c k| * |Real.cos ((k : ℝ) * θ)| * |g θ| ≤ b k * 1 * B :=
          mul_le_mul (mul_le_mul (hcb k) (Real.abs_cos_le_one _) (abs_nonneg _) hbk)
            (hgB θ hθ') (abs_nonneg _) (by positivity)
      _ = b k * B := by ring
  · exact Filter.Eventually.of_forall fun θ _ => hb.mul_right B
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun θ _ => (hf θ).mul_right (g θ)

theorem integral_poisson_cos {ρ : ℝ} (hρ : |ρ| < 1) (j : ℕ) :
    ∫ θ in (0 : ℝ)..π, poissonQ ρ θ * Real.cos ((j : ℝ) * θ) = (-ρ) ^ j := by
  have hb : Summable (fun k : ℕ => 2 * |ρ| ^ k) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_left 2
  have hsum := hasSum_integral_series hb (abs_poissonCoef_le ρ)
    (g := fun θ : ℝ => Real.cos ((j : ℝ) * θ)) (by fun_prop)
    (fun θ _ => Real.abs_cos_le_one _) (poisson_series hρ)
  have hterm : ∀ k : ℕ, ∫ θ in (0 : ℝ)..π, poissonCoef ρ k * Real.cos ((k : ℝ) * θ) *
      Real.cos ((j : ℝ) * θ) = if k = j then π * (-ρ) ^ j else 0 := by
    intro k
    have : ∀ θ : ℝ, poissonCoef ρ k * Real.cos ((k : ℝ) * θ) * Real.cos ((j : ℝ) * θ) =
        poissonCoef ρ k * (Real.cos ((k : ℝ) * θ) * Real.cos ((j : ℝ) * θ)) := fun θ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_cos_mul_cos]
    unfold poissonCoef
    by_cases hkj : k = j
    · subst hkj
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]; ring
    · by_cases hk0 : k = 0
      · subst hk0
        have : j ≠ 0 := fun h => hkj h.symm
        simp [this, hkj]
      · simp [hkj, hk0]
  have hsum2 : HasSum (fun k : ℕ => if k = j then π * (-ρ) ^ j else 0)
      (∫ θ in (0 : ℝ)..π, (π * poissonQ ρ θ) * Real.cos ((j : ℝ) * θ)) := by
    convert hsum using 1
    funext k; exact (hterm k).symm
  have h2 := hsum2.unique (hasSum_ite_eq j (π * (-ρ) ^ j))
  have h3 : ∫ θ in (0 : ℝ)..π, (π * poissonQ ρ θ) * Real.cos ((j : ℝ) * θ) = π * (-ρ) ^ j := h2
  have h4 : ∫ θ in (0 : ℝ)..π, (π * poissonQ ρ θ) * Real.cos ((j : ℝ) * θ) =
      π * ∫ θ in (0 : ℝ)..π, poissonQ ρ θ * Real.cos ((j : ℝ) * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [h4] at h3
  exact mul_left_cancel₀ Real.pi_pos.ne' h3

theorem integral_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) (g : ℝ → ℝ) :
    ∫ θ, g θ ∂(poissonMeasure ρ) = ∫ θ in (0 : ℝ)..π, poissonQ ρ θ * g θ := by
  unfold poissonMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_poissonQ hρ).measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (poissonQ_pos hρ _).le, smul_eq_mul]
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Icc_eq_integral_Ioc]

theorem isProbabilityMeasure_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) :
    IsProbabilityMeasure (poissonMeasure ρ) := by
  refine ⟨?_⟩
  unfold poissonMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ?_ ?_]
  · have := integral_poisson_cos hρ 0
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, pow_zero] at this
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc] at this
    rw [this]
    simp
  · exact (continuous_poissonQ hρ).continuousOn.integrableOn_Icc
  · exact ae_of_all _ fun x => (poissonQ_pos hρ x).le

/-- The Poisson sequence: `∫ cos (kθ) dβ_ρ = (-ρ)^k`, i.e. `∫ T_k dβ_ρ = (-ρ)^k`. -/
theorem integral_cos_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) (k : ℕ) :
    ∫ θ, Real.cos ((k : ℝ) * θ) ∂(poissonMeasure ρ) = (-ρ) ^ k := by
  rw [integral_poissonMeasure hρ]
  exact integral_poisson_cos hρ k

theorem integral_cheb_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) (k : ℕ) :
    ∫ θ, (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval (Real.cos θ) ∂(poissonMeasure ρ) = (-ρ) ^ k := by
  simp_rw [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
  exact integral_cos_poissonMeasure hρ k

/-- Integrating a Chebyshev series against `β_ρ` multiplies the coefficients by `(-ρ)^k`. -/
theorem hasSum_integral_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) {c b : ℕ → ℝ} (hb : Summable b)
    (hcb : ∀ k, |c k| ≤ b k) {f : ℝ → ℝ}
    (hf : ∀ θ, HasSum (fun k : ℕ => c k * Real.cos ((k : ℝ) * θ)) (f θ)) :
    HasSum (fun k : ℕ => c k * (-ρ) ^ k) (∫ θ, f θ ∂(poissonMeasure ρ)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π)).exists_bound_of_continuousOn
    (continuous_poissonQ hρ).continuousOn
  have h := hasSum_integral_series hb hcb (g := poissonQ ρ) (continuous_poissonQ hρ)
    (B := B) (fun θ hθ => by simpa using hB θ hθ) hf
  rw [integral_poissonMeasure hρ]
  have e1 : ∀ k : ℕ, ∫ θ in (0 : ℝ)..π, c k * Real.cos ((k : ℝ) * θ) * poissonQ ρ θ =
      c k * (-ρ) ^ k := by
    intro k
    have : ∀ θ : ℝ, c k * Real.cos ((k : ℝ) * θ) * poissonQ ρ θ =
        c k * (poissonQ ρ θ * Real.cos ((k : ℝ) * θ)) := fun θ => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_poisson_cos hρ]
  have e2 : ∫ θ in (0 : ℝ)..π, poissonQ ρ θ * f θ = ∫ θ in (0 : ℝ)..π, f θ * poissonQ ρ θ :=
    intervalIntegral.integral_congr fun θ _ => by ring
  rw [e2]
  simpa only [e1] using h

/-! ### Closed forms -/

theorem crossLog_series {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (θ : ℝ) :
    HasSum (fun k : ℕ => (if k = 0 then 0 else -2 * (-x) ^ k / (k : ℝ)) *
      Real.cos ((k : ℝ) * θ)) (crossLog x (Real.cos θ)) := by
  have h := crossLog_hasSum hx ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, ite_true, zero_mul, sub_zero]
  convert h using 1
  funext k
  simp only [Nat.succ_ne_zero, ite_false, Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
  push_cast
  ring

theorem integral_crossLog_poissonMeasure {ρ x : ℝ} (hρ : |ρ| < 1) (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ θ, crossLog x (Real.cos θ) ∂(poissonMeasure ρ) = 2 * Real.log (1 - ρ * x) := by
  have hxa : |x| < 1 := abs_lt.mpr hx
  have hb : Summable (fun k : ℕ => 2 * |x| ^ k) :=
    (summable_geometric_of_lt_one (abs_nonneg x) hxa).mul_left 2
  have hcb : ∀ k : ℕ, |(if k = 0 then 0 else -2 * (-x) ^ k / (k : ℝ))| ≤ 2 * |x| ^ k := by
    intro k
    split_ifs with h
    · simp [abs_nonneg, pow_nonneg]
    · have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      rw [abs_div, abs_mul, abs_pow, abs_neg, Nat.abs_cast, abs_neg, abs_two,
        div_le_iff₀ (by linarith)]
      have : 0 ≤ |x| ^ k := pow_nonneg (abs_nonneg _) _
      nlinarith
  have h1 := hasSum_integral_poissonMeasure hρ hb hcb (crossLog_series hx)
  have hρx : |ρ * x| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg ρ, abs_nonneg x]
  have h2 := (Real.hasSum_pow_div_log_of_abs_lt_one hρx).mul_left (-2)
  have h3 : HasSum (fun k : ℕ => (if k = 0 then 0 else -2 * (-x) ^ k / (k : ℝ)) * (-ρ) ^ k)
      (2 * Real.log (1 - ρ * x)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ite_true, zero_mul, sub_zero]
    convert h2 using 1
    · funext k
      simp only [Nat.succ_ne_zero, ite_false]
      push_cast
      have e : (-x) ^ (k + 1) * (-ρ) ^ (k + 1) = (ρ * x) ^ (k + 1) := by
        rw [← mul_pow]; ring_nf
      calc -2 * (-x) ^ (k + 1) / ((k : ℝ) + 1) * (-ρ) ^ (k + 1)
          = -2 * ((-x) ^ (k + 1) * (-ρ) ^ (k + 1)) / ((k : ℝ) + 1) := by ring
        _ = -2 * ((ρ * x) ^ (k + 1) / ((k : ℝ) + 1)) := by rw [e]; ring
    · ring
  exact h1.unique h3

theorem integral_barrierTrialT_poissonMeasure {ρ : ℝ} (hρ : |ρ| < 1) (a : ℕ → ℝ)
    (ha : Summable (fun k => |a k|)) :
    ∫ θ, OAI.InternalCatalan.barrierTrialT a (Real.cos θ) ∂(poissonMeasure ρ) =
      OAI.InternalCatalan.barrierTrialS a (-ρ) := by
  have hcb : ∀ k : ℕ, |(if k = 0 then 0 else a k / (k : ℝ))| ≤ |a k| := by
    intro k
    split_ifs with h
    · simp
    · have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      rw [abs_div, Nat.abs_cast]
      exact div_le_self (abs_nonneg _) hk
  have hser : ∀ θ : ℝ, HasSum (fun k : ℕ => (if k = 0 then 0 else a k / (k : ℝ)) *
      Real.cos ((k : ℝ) * θ)) (OAI.InternalCatalan.barrierTrialT a (Real.cos θ)) := by
    intro θ
    have hx : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h := (OAI.InternalCatalan.barrierTrialT_summable a ha hx).hasSum
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ite_true, zero_mul, sub_zero]
    convert h using 1
    · funext k
      simp only [Nat.succ_ne_zero, ite_false, Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
      push_cast
      ring
    · rfl
  have h1 := hasSum_integral_poissonMeasure hρ ha hcb hser
  have hx : |(-ρ)| ≤ 1 := by rw [abs_neg]; exact hρ.le
  have h2 := (OAI.InternalCatalan.barrierTrialS_summable a ha hx).hasSum
  have h3 : HasSum (fun k : ℕ => (if k = 0 then 0 else a k / (k : ℝ)) * (-ρ) ^ k)
      (OAI.InternalCatalan.barrierTrialS a (-ρ)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, ite_true, zero_mul, sub_zero]
    convert h2 using 1
    · funext k
      simp only [Nat.succ_ne_zero, ite_false]
      push_cast
      ring
    · rfl
  exact h1.unique h3

/-! ### Lemma 5 and the stochastic order -/

/-- Lemma 5: a negative row `x = -y` is never charged more than the endpoint `y = 1`. -/
theorem neg_row_bound {y ρ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    Real.log ((1 + y) / (1 + ρ * y)) ≤ Real.log (2 / (1 + ρ)) := by
  have h1 : 0 < 1 + ρ * y := by nlinarith [hy.1, hρ.1, mul_nonneg hy.1 hρ.1]
  have h2 : 0 < 1 + ρ := by linarith [hρ.1]
  refine Real.log_le_log (div_pos (by linarith [hy.1]) h1) ?_
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hρ.2)]

/-- Stochastic order: for `x ≥ 0`, `ρ ↦ ∫ l(x, cos θ) dβ_ρ` is non-increasing. -/
theorem crossLog_poisson_antitone {ρ σ x : ℝ} (hρ : |ρ| < 1) (hσ : |σ| < 1)
    (hx : x ∈ Ico (0 : ℝ) 1) (h : σ ≤ ρ) :
    ∫ θ, crossLog x (Real.cos θ) ∂(poissonMeasure ρ) ≤
      ∫ θ, crossLog x (Real.cos θ) ∂(poissonMeasure σ) := by
  have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  rw [integral_crossLog_poissonMeasure hρ hx1, integral_crossLog_poissonMeasure hσ hx1]
  have hp1 : 0 < 1 - ρ * x := by nlinarith [abs_lt.mp hρ, hx.1, hx.2, mul_nonneg hx.1 hx.1]
  have : Real.log (1 - ρ * x) ≤ Real.log (1 - σ * x) :=
    Real.log_le_log hp1 (by nlinarith [hx.1])
  linarith

#print axioms integral_cos_poissonMeasure
#print axioms integral_crossLog_poissonMeasure
#print axioms integral_barrierTrialT_poissonMeasure
#print axioms neg_row_bound
#print axioms crossLog_poisson_antitone

end CatalanMeasure.GenD.Signed

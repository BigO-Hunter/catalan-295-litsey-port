module

public import CatalanMeasure.GenD.Signed.LemmaT

/-!
# Lemma T for the free positives (Loewner form with marked rows present)

`lemmaT` bounds `|∑_{x a > 0} B'(x a) (x a)^e (c a)^2|` by `(1 + M/2) Q(c)`, where `B` is the
Blaschke product of ALL nodes and `Q(c) = ∑ c a c b / (1 - x a x b)` is the Gram form of ALL nodes.
When some positive nodes are marked (they carry the same weight in `F(1)` and `F(-5)`), the Schur
step needs the same Loewner form with the residue sum restricted to the FREE positives while the
Blaschke product and the Gram form still contain every node.

**This is false with the constant `3/2` in general.**  For `c` supported at a single free positive
`a`, with all other nodes free to move, the best constant is `x_a^e / β_a`, where
`β_a = ∏_{b ≠ a} |x_a - x_b| / |1 - x_a x_b|`; two adjacent positive nodes `0.5`, `0.55`, `e = 2`
(slope margin `0.86 > 0`, so `M* = 1`) give `3.625`.  The correct statement keeps the marked
positive residues as a separate term:

`|∑_{free positive} B'(x a) (x a)^e (c a)^2| ≤ (1 + M/2 + W) Q(c)`,
`W = ∑_{marked positive a} (x a)^e / ((1 - (x a)^2) |B'(x a)|)`.

The marked terms are bounded one at a time by the reproducing estimate
`(c a B'(x a))^2 (1 - x a^2) ≤ Q(c)`: `ψ_c(x a) = c a B'(x a)` is evaluated by the Cauchy formula on
the unit circle and the circle integral is estimated by AM-GM against `ψ_{e_a}`, using the Gram
identity `gram_integral` of `LemmaT`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Complex Set intervalIntegral Metric Finset
open scoped ComplexConjugate

noncomputable section

section NodeBound

variable {n : ℕ} (x c : Fin n → ℝ)

theorem psi_node (a : Fin n) : psi x c (x a : ℂ) = ((c a * bDeriv x a : ℝ) : ℂ) := by
  unfold psi
  rw [bS_node]
  push_cast
  rw [bDeriv_eq, mul_div_assoc]

theorem psi_single (a : Fin n) (z : ℂ) :
    psi x (Pi.single a 1) z = bNe x a z / bD x z := by
  classical
  unfold psi bS
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem qform_single (a : Fin n) :
    Qform x (Pi.single a 1) = 1 / (1 - x a * x a) := by
  classical
  unfold Qform
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro b' _
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem norm_psi_single_circle (hx1 : ∀ a, |x a| < 1) (a : Fin n) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖psi x (Pi.single a 1) z‖ = ‖(z - (x a : ℂ))⁻¹‖ := by
  rw [psi_single]
  have hN := norm_bN_eq_norm_bD x hz
  rw [bN_eq_mul_bNe x a z, norm_mul] at hN
  have hNe : ‖bNe x a z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    unfold bNe
    rw [Finset.prod_ne_zero_iff]
    intro b _
    exact norm_circle_node x hz (hx1 b)
  have hza : ‖z - (x a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (norm_circle_node x hz (hx1 a))
  rw [norm_div, ← hN, norm_inv]
  field_simp

theorem continuous_psi_exp (hx1 : ∀ a, |x a| < 1) :
    Continuous (fun θ : ℝ => psi x c (Complex.exp ((θ : ℂ) * Complex.I))) := by
  unfold psi
  apply Continuous.div
  · unfold bS bNe; fun_prop
  · unfold bD; fun_prop
  · intro θ; exact bD_ne_zero_circle x hx1 (Complex.norm_exp_ofReal_mul_I θ)

/-- Reproducing estimate at a node: `|ψ_c(x a)|^2 ≤ Q(c) / (1 - x a^2)`, with
`ψ_c(x a) = c a B'(x a)`. -/
theorem node_sq_le (hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0)
    (a : Fin n) : (c a * bDeriv x a) ^ 2 * (1 - x a ^ 2) ≤ Qform x c := by
  classical
  obtain ⟨R, hR1, hR⟩ := exists_radius x hx1 hx0
  have hd : DifferentiableOn ℂ (psi x c) (closedBall 0 1) :=
    (psi_differentiableOn x c hR).mono (fun z hz => by
      simp only [mem_closedBall, dist_zero_right] at hz
      simp only [mem_ball, dist_zero_right]
      linarith)
  have hw : (x a : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa using hx1 a
  have hcau := hd.circleIntegral_sub_inv_smul hw
  unfold circleIntegral at hcau
  simp only [deriv_circleMap, circleMap_zero_one_eq, smul_eq_mul] at hcau
  set u : ℝ → ℝ := fun θ => ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ with hu
  set v : ℝ → ℝ := fun θ => ‖psi x (Pi.single a 1) (Complex.exp ((θ : ℂ) * Complex.I))‖
    with hv
  have hz1 : ∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have hnorm : ∀ θ : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I) * Complex.I *
      ((Complex.exp ((θ : ℂ) * Complex.I) - (x a : ℂ))⁻¹ *
        psi x c (Complex.exp ((θ : ℂ) * Complex.I)))‖ = v θ * u θ := by
    intro θ
    simp only [hu, hv]
    rw [norm_psi_single_circle x hx1 a (hz1 θ), norm_mul, norm_mul, norm_mul, hz1, norm_I]
    ring
  have hrhs : ‖(2 * (Real.pi : ℂ) * Complex.I) * psi x c (x a : ℂ)‖ =
      2 * Real.pi * |c a * bDeriv x a| := by
    rw [psi_node, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      simp
    rw [this]
  have hcu : Continuous u := (continuous_psi_exp x c hx1).norm
  have hcv : Continuous v := (continuous_psi_exp x (Pi.single a 1) hx1).norm
  have hle1 : 2 * Real.pi * |c a * bDeriv x a| ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ * u θ := by
    rw [← hrhs, ← hcau]
    refine (intervalIntegral.norm_integral_le_integral_norm
      (by linarith [Real.pi_pos])).trans (le_of_eq ?_)
    exact intervalIntegral.integral_congr (fun θ _ => hnorm θ)
  have hu2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), (u θ) ^ 2 = 2 * Real.pi * Qform x c :=
    gram_integral x c hx1
  have hv2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), (v θ) ^ 2 = 2 * Real.pi * (1 / (1 - x a * x a)) := by
    rw [← qform_single x a]
    exact gram_integral x (Pi.single a 1) hx1
  have hlam : ∀ l : ℝ, 0 < l →
      2 * l * |c a * bDeriv x a| ≤ l ^ 2 * Qform x c + 1 / (1 - x a * x a) := by
    intro l hl
    have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        v θ * u θ ≤ (l / 2) * (u θ) ^ 2 + (1 / (2 * l)) * (v θ) ^ 2 := by
      intro θ _
      have key : (l / 2) * (u θ) ^ 2 + (1 / (2 * l)) * (v θ) ^ 2 - v θ * u θ =
          (l * u θ - v θ) ^ 2 / (2 * l) := by
        field_simp
        ring
      have : 0 ≤ (l * u θ - v θ) ^ 2 / (2 * l) := by positivity
      linarith
    have hf1 : IntervalIntegrable (fun θ => v θ * u θ) MeasureTheory.volume 0 (2 * Real.pi) :=
      (hcv.mul hcu).intervalIntegrable _ _
    have hf2 : IntervalIntegrable (fun θ => (l / 2) * (u θ) ^ 2 + (1 / (2 * l)) * (v θ) ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      (((hcu.pow 2).const_mul (l / 2)).add ((hcv.pow 2).const_mul (1 / (2 * l)))).intervalIntegrable
        _ _
    have hint := intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hf1 hf2 hpt
    have hf3 : IntervalIntegrable (fun θ => (l / 2) * (u θ) ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) := ((hcu.pow 2).const_mul (l / 2)).intervalIntegrable _ _
    have hf4 : IntervalIntegrable (fun θ => (1 / (2 * l)) * (v θ) ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      ((hcv.pow 2).const_mul (1 / (2 * l))).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hf3 hf4,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hu2, hv2] at hint
    have h2 := hle1.trans hint
    have hpi := Real.pi_pos
    have h3 : 2 * Real.pi * (2 * l * |c a * bDeriv x a|) ≤
        2 * Real.pi * (l ^ 2 * Qform x c + 1 / (1 - x a * x a)) := by
      have e1 : 2 * Real.pi * (l ^ 2 * Qform x c + 1 / (1 - x a * x a)) =
          2 * l * (l / 2 * (2 * Real.pi * Qform x c) +
            1 / (2 * l) * (2 * Real.pi * (1 / (1 - x a * x a)))) := by
        field_simp
      rw [e1]
      nlinarith [h2]
    exact le_of_mul_le_mul_left h3 (by positivity)
  -- optimise in `l`
  have hQ0 : 0 ≤ Qform x c := by
    have h := hu2
    have : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi), (u θ) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => sq_nonneg _)
    rw [h] at this
    have hpi := Real.pi_pos
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hxx : 0 < 1 - x a * x a := by
    have := hx1 a
    have h2 : |x a| * |x a| < 1 := by nlinarith [abs_nonneg (x a)]
    nlinarith [abs_mul_abs_self (x a)]
  set s : ℝ := |c a * bDeriv x a| with hs
  set K : ℝ := 1 / (1 - x a * x a) with hK
  have hK0 : 0 < K := by positivity
  have hsq : s ^ 2 ≤ Qform x c * K := by
    by_contra hcon
    push_neg at hcon
    have hs0 : 0 < s := by
      rcases (abs_nonneg (c a * bDeriv x a)).lt_or_eq with h | h
      · exact h
      · exfalso
        have : s = 0 := h.symm
        rw [this] at hcon
        nlinarith [mul_nonneg hQ0 hK0.le]
    rcases hQ0.lt_or_eq with hq | hq
    · have := hlam (s / Qform x c) (by positivity)
      have e : (s / Qform x c) ^ 2 * Qform x c = s ^ 2 / Qform x c := by field_simp
      have e2 : 2 * (s / Qform x c) * s = 2 * (s ^ 2 / Qform x c) := by ring
      rw [e, e2] at this
      have h4 : s ^ 2 / Qform x c ≤ K := by linarith
      rw [div_le_iff₀ hq] at h4
      linarith
    · have := hlam ((K + 1) / (2 * s)) (by positivity)
      rw [← hq] at this
      have e : 2 * ((K + 1) / (2 * s)) * s = K + 1 := by field_simp
      rw [e] at this
      linarith
  have hfin : (c a * bDeriv x a) ^ 2 ≤ Qform x c * K := by
    rw [← sq_abs]; exact hsq
  have hKe : Qform x c * K * (1 - x a ^ 2) = Qform x c := by
    have hx2 : 1 - x a ^ 2 = 1 - x a * x a := by ring
    have hne : (1 - x a ^ 2) ≠ 0 := by rw [hx2]; exact hxx.ne'
    have hxm : x a * x a = x a ^ 2 := by ring
    rw [hK, hxm]; field_simp
  calc (c a * bDeriv x a) ^ 2 * (1 - x a ^ 2) ≤ Qform x c * K * (1 - x a ^ 2) :=
        mul_le_mul_of_nonneg_right hfin (by nlinarith)
    _ = Qform x c := hKe

theorem bDeriv_ne_zero (hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (a : Fin n) :
    bDeriv x a ≠ 0 := by
  intro h
  have h1 := bDeriv_eq x a
  rw [h] at h1
  have hD : bD x (x a : ℂ) ≠ 0 := by
    unfold bD
    rw [Finset.prod_ne_zero_iff]
    intro b _ hb
    have h1 : (x b : ℂ) * (x a : ℂ) = 1 := by rw [sub_eq_zero] at hb; exact hb.symm
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      norm_one] at h2
    nlinarith [hx1 a, hx1 b, abs_nonneg (x a), abs_nonneg (x b)]
  have := bNe_ne_zero x hxi a
  simp only [Complex.ofReal_zero] at h1
  rw [eq_comm, div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · exact this h1
  · exact hD h1

/-- One marked residue term is bounded by the Gram form: `|B'(x a)| (x a)^e (c a)^2 ≤ w_a Q(c)`
with `w_a = (x a)^e / ((1 - x a^2) |B'(x a)|)`. -/
theorem marked_term_le (hxi : Function.Injective x) (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0)
    (e : ℕ) (a : Fin n) (hpos : 0 < x a) :
    |bDeriv x a * x a ^ e * c a ^ 2| ≤
      x a ^ e / ((1 - x a ^ 2) * |bDeriv x a|) * Qform x c := by
  have hB := abs_pos.mpr (bDeriv_ne_zero x hxi hx1 a)
  have h1 : 0 < 1 - x a ^ 2 := by
    have := hx1 a
    have h2 : |x a| ^ 2 < 1 := by nlinarith [abs_nonneg (x a)]
    rw [sq_abs] at h2
    linarith
  have hxe : 0 < x a ^ e := pow_pos hpos e
  have hnode := node_sq_le x c hxi hx1 hx0 a
  have habs : |bDeriv x a * x a ^ e * c a ^ 2| = |bDeriv x a| * x a ^ e * c a ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hxe, abs_of_nonneg (sq_nonneg (c a))]
  rw [habs, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hsq := sq_abs (bDeriv x a)
  have e1 : |bDeriv x a| * x a ^ e * c a ^ 2 * ((1 - x a ^ 2) * |bDeriv x a|) =
      x a ^ e * ((c a * bDeriv x a) ^ 2 * (1 - x a ^ 2)) := by
    linear_combination (x a ^ e * c a ^ 2 * (1 - x a ^ 2)) * hsq
  rw [e1]
  exact mul_le_mul_of_nonneg_left hnode hxe.le

end NodeBound

section Main

variable {n : ℕ} (x c : Fin n → ℝ)

/-- The total weight of the marked positive nodes. -/
def markedWeight (mk : Fin n → Bool) (e : ℕ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = true),
    x a ^ e / ((1 - x a ^ 2) * |bDeriv x a|)

theorem markedWeight_nonneg (mk : Fin n → Bool) (e : ℕ)
    (hx1 : ∀ a, |x a| < 1) : 0 ≤ markedWeight x mk e := by
  unfold markedWeight
  apply Finset.sum_nonneg
  intro a ha
  have hpos : 0 < x a := (Finset.mem_filter.mp ha).2.1
  have h1 : 0 < 1 - x a ^ 2 := by
    have := hx1 a
    have h2 : |x a| ^ 2 < 1 := by nlinarith [abs_nonneg (x a)]
    rw [sq_abs] at h2
    linarith
  have : 0 ≤ |bDeriv x a| := abs_nonneg _
  have h3 : 0 ≤ (1 - x a ^ 2) * |bDeriv x a| := by positivity
  positivity

/-- **Lemma T for the free positives.**  The Blaschke product and the Gram form contain every
node; the residue sum is restricted to the positive nodes with `mk a = false`; the marked positive
nodes enter through `markedWeight`. -/
theorem lemmaT_free {e : ℕ} (mk : Fin n → Bool) (hx : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ Icc (-1 : ℝ) 1, |y| ^ e ≤ M * ‖blaschke x ((y : ℂ) * Complex.I)‖) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2| ≤
      (1 + M / 2 + markedWeight x mk e) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  classical
  have hall := lemmaT x c hx hx1 hx0 hM0 hM
  have hsplit : ∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
        bDeriv x a * x a ^ e * c a ^ 2 =
      ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2 +
      ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = true),
        bDeriv x a * x a ^ e * c a ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun a => 0 < x a))
      (fun a => mk a = false)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext a; simp
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext a; simp
  have hmk : |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = true),
        bDeriv x a * x a ^ e * c a ^ 2| ≤ markedWeight x mk e * Qform x c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold markedWeight
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    exact marked_term_le x c hx hx1 hx0 e a (Finset.mem_filter.mp ha).2.1
  have htri : |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2| ≤
      |∑ a ∈ Finset.univ.filter (fun a => 0 < x a),
        bDeriv x a * x a ^ e * c a ^ 2| +
      |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = true),
        bDeriv x a * x a ^ e * c a ^ 2| := by
    rw [hsplit]
    set A := ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2
    set Bm := ∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = true),
        bDeriv x a * x a ^ e * c a ^ 2
    have := abs_sub_abs_le_abs_sub (A + Bm) Bm
    have h2 : |A + Bm - Bm| = |A| := by ring_nf
    have := abs_add_le (A + Bm) (-Bm)
    simp only [abs_neg] at this
    have h3 : A + Bm + -Bm = A := by ring
    rw [h3] at this
    exact this
  have hQ : Qform x c = ∑ a, ∑ b, c a * c b / (1 - x a * x b) := rfl
  rw [← hQ] at hall ⊢
  linarith

/-- The `M = 1` form from the slope criterion: `τ = 3/2 + W`. -/
theorem lemmaT_free_of_slope {e : ℕ} (mk : Fin n → Bool) (hx : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) (he : 1 ≤ e)
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2))) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2| ≤
      (3 / 2 + markedWeight x mk e) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  have h := lemmaT_free x c mk hx hx1 hx0 (e := e) (M := 1) zero_le_one
    (pow_le_norm_blaschke_of_slope x he hslope)
  have e1 : (1 : ℝ) + 1 / 2 + markedWeight x mk e = 3 / 2 + markedWeight x mk e := by ring
  rw [e1] at h
  exact h

/-- With no marked positive node the free-positive form is `lemmaT_of_slope`'s `3/2`. -/
theorem lemmaT_free_of_slope_no_marked {e : ℕ} (mk : Fin n → Bool) (hx : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) (he : 1 ≤ e)
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2)))
    (hnone : ∀ a, 0 < x a → mk a = false) :
    |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2| ≤
      (3 / 2) * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  have h := lemmaT_free_of_slope x c mk hx hx1 hx0 he hslope
  have hW : markedWeight x mk e = 0 := by
    unfold markedWeight
    apply Finset.sum_eq_zero
    intro a ha
    have := (Finset.mem_filter.mp ha).2
    rw [hnone a this.1] at this
    exact absurd this.2 (by simp)
  rw [hW, add_zero] at h
  exact h

/-- The form consumed by `abs_det_laurent_le_marked` / `lemmaT_sum_form_marked`, with a general
Loewner constant `τ`: the hypothesis `hT` of `RealPlaceFixed` with `3/2` replaced by `τ` follows as
soon as `3/2 + W ≤ τ`.  (The Gram bound `norm_det_gram_le_gen_full` already takes `τ` as a
parameter.) -/
theorem lemmaT_free_tau {e : ℕ} (mk : Fin n → Bool) (hx : Function.Injective x)
    (hx1 : ∀ a, |x a| < 1) (hx0 : ∀ a, x a ≠ 0) (he : 1 ≤ e)
    (hslope : ∀ t ∈ Ioc (0 : ℝ) 1,
      0 < (e : ℝ) - ∑ a, (t ^ 2 / (t ^ 2 + x a ^ 2) - x a ^ 2 * t ^ 2 / (1 + x a ^ 2 * t ^ 2)))
    {τ : ℝ} (hτ : 3 / 2 + markedWeight x mk e ≤ τ) :
    ∀ c : Fin n → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < x a ∧ mk a = false),
        bDeriv x a * x a ^ e * c a ^ 2| ≤
      τ * ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
  intro c
  refine (lemmaT_free_of_slope x c mk hx hx1 hx0 he hslope).trans ?_
  have hQ : 0 ≤ ∑ a, ∑ b, c a * c b / (1 - x a * x b) := by
    have h := gram_integral x c hx1
    have h0 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖psi x c (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) (fun θ _ => sq_nonneg _)
    rw [h] at h0
    have hpi := Real.pi_pos
    by_contra hneg
    push_neg at hneg
    have : 2 * Real.pi * Qform x c < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    linarith
  exact mul_le_mul_of_nonneg_right hτ hQ

end Main

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.node_sq_le
#print axioms CatalanMeasure.Signed.marked_term_le
#print axioms CatalanMeasure.Signed.lemmaT_free
#print axioms CatalanMeasure.Signed.lemmaT_free_of_slope
#print axioms CatalanMeasure.Signed.lemmaT_free_of_slope_no_marked
#print axioms CatalanMeasure.Signed.lemmaT_free_tau

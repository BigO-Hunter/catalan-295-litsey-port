module

public import CatalanMeasure.GenD.Signed.TiltedTangent
public import CatalanMeasure.GenD.Signed.CrossDilation
public import CatalanMeasure.GenD.Signed.ArcsineDenominator
public import CatalanMeasure.GenD.Signed.ReflectionEnergy
public import CatalanMeasure.GenD.Signed.RatioIdentity
public import CatalanMeasure.GenD.Signed.PickDet
public import CatalanMeasure.GenD.Signed.LemmaT
public import CatalanMeasure.GenD.Signed.LemmaK
public import CatalanMeasure.FreePopulationFields
public import CatalanMeasure.PinSupDual

/-!
# The signed second-sheet energy bound: assembly layer (Phase 1, theorem-only)

Sibling of `Analytic.second_energy`.  See `NOTES-E.md` in the Theorem A plan folder.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators

noncomputable section

/-- Error of the row-Vandermonde-free pin bound. -/
def pinZeroError (ν e : ℝ) : ℝ :=
  (Real.log 2 - Real.log e) / (2 * ν) + (Real.log 2 - 2 * Real.log e) / ν + 12 * e

/-- The pin interaction without the row Vandermonde (`k = 0`), by the 532 lemmas. -/
theorem pin_zero_canonical {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {p : ℕ}
    (hp : (p : ℝ) ≤ ν) {x s : Fin p → ℝ} (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) (hxi : Function.Injective x) (hsi : Function.Injective s)
    (v : ℕ → ℝ) (hv : Summable (fun j => |v j|)) :
    pinOffDiagonalInteraction ν 0 x s ≤ -((p : ℝ) / ν) ^ 2 * Real.log 2 +
      barrierTrialNormSq v / 2 + (∑ i, -barrierTrialS v (x i)) / ν +
      (∑ j, 2 * barrierTrialT v (s j)) / ν -
      (∑ i, Real.log (1 - x i)) / (2 * ν ^ 2) - (∑ j, Real.log (1 - s j)) / ν ^ 2 +
      4 * e * (∑' j, |v j|) + pinZeroError ν e := by
  have h0 : Summable (fun j : ℕ => |(fun _ : ℕ => (0:ℝ)) j|) := by simp
  have hint := pinOffDiagonalInteraction_le_damped hν (le_refl (0:ℝ)) he hx hs hxi hsi
  have hpow := pin_power_diagonal_sum hν he hp hx
  have hsig := pin_sigma_diagonal_sum hν he hp hs
  have hd := pinDampedInteraction_le_canonicalTrials hν (le_refl (0:ℝ)) he hp hx hs
    (fun _ => 0) v h0 hv
  have hc : ((p.choose 2 : ℕ) : ℝ) ≤ ν ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith only [hp, hν, (Nat.cast_nonneg p : (0:ℝ) ≤ p)]
  have hsq : (p : ℝ) ^ 2 ≤ ν ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg p) hp 2
  have he0 := he.1
  have hpair : (4 * 0 + 12) * e * ((p.choose 2 : ℕ) : ℝ) / ν ^ 2 + 6 * e * (p : ℝ) ^ 2 / ν ^ 2
      ≤ 12 * e := by
    have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 12 * e by positivity)
    have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * e by positivity)
    rw [← add_div, div_le_iff₀ (sq_pos_of_pos hν)]
    nlinarith only [h1, h2]
  unfold pinZeroError
  simp only [zero_mul, mul_zero, zero_sub, sub_zero, zero_div, zero_add, add_zero] at hint hd hpair
  simp only [mul_pow] at hint
  simp only [neg_div] at hpow hsig
  ring_nf at hint hd hpow hsig hpair ⊢
  linarith only [hint, hd, hpow, hsig, hpair]

/-! ### Row Vandermonde through D7.1 -/

section Rows

open CatalanMeasure.Signed.ReflectionEnergy

/-- Folded kernel equals `-log |x - y|` for nonzero reals (opposite signs: `a + b = |x - y|`). -/
theorem Kt_abs_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Kt (decide (0 < x)) (decide (0 < y)) |x| |y| = -Real.log |x - y| := by
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · have h1 : decide (0 < x) = false := by simp [not_lt.mpr hx'.le]
    have h2 : decide (0 < y) = false := by simp [not_lt.mpr hy'.le]
    simp only [Kt, h1, h2, if_true, abs_of_neg hx', abs_of_neg hy']
    rw [show -x - -y = -(x - y) by ring, abs_neg]
  · have h1 : decide (0 < x) = false := by simp [not_lt.mpr hx'.le]
    have h2 : decide (0 < y) = true := by simp [hy']
    simp only [Kt, h1, h2, Bool.false_eq_true, if_false, abs_of_neg hx', abs_of_pos hy']
    rw [abs_of_neg (by linarith : x - y < 0)]
    ring_nf
  · have h1 : decide (0 < x) = true := by simp [hx']
    have h2 : decide (0 < y) = false := by simp [not_lt.mpr hy'.le]
    simp only [Kt, h1, h2, Bool.true_eq_false, if_false, abs_of_pos hx', abs_of_neg hy']
    rw [abs_of_pos (by linarith : 0 < x - y)]
    ring_nf
  · have h1 : decide (0 < x) = true := by simp [hx']
    have h2 : decide (0 < y) = true := by simp [hy']
    simp only [Kt, h1, h2, if_true, abs_of_pos hx', abs_of_pos hy']

/-- Reduce the double sum over `i ≠ j` of a symmetric function to the ordered pairs. -/
theorem sum_offdiag_eq_two_mul {p : ℕ} (g : Fin p → Fin p → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, if i = j then 0 else g i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have h1 : ∀ i : Fin p, (∑ j, if i = j then 0 else g i j) =
      (∑ j ∈ Finset.Ioi i, g i j) + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have hu : (Finset.univ.erase i) = Finset.Ioi i ∪ Finset.Iio i := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
        Finset.mem_Iio]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim ne_of_gt ne_of_lt⟩
    have hd : Disjoint (Finset.Ioi i) (Finset.Iio i) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
      exact lt_asymm h1 h2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl, zero_add, hu,
      Finset.sum_union hd]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Finset.mem_Ioi.mp hj).ne]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_neg (Finset.mem_Iio.mp hj).ne']
  simp only [h1, Finset.sum_add_distrib]
  have h2 : (∑ i : Fin p, ∑ j ∈ Finset.Iio i, g i j) = ∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g i j :=
    Finset.sum_comm' (by intro x y; simp [and_comm])
  rw [h2]
  have : (∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g i j) = ∑ j : Fin p, ∑ i ∈ Finset.Ioi j, g j i :=
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hg i j
  rw [this]; ring

/-- The row field of the reference: `x ↦ ∑_τ ∫ K(x, y) dμ_τ(y)` in folded coordinates. -/
def rowRef (μ : Bool → Measure ℝ) (x : ℝ) : ℝ :=
  ∑ τ, ∫ y, Kt (decide (0 < x)) τ |x| y ∂(μ τ)

/-- The constant `∑ ∬ K dμ dμ` of the reference. -/
def refEnergy (μ : Bool → Measure ℝ) : ℝ :=
  ∑ τ, ∑ τ', ∫ x, ∫ y, Kt τ τ' x y ∂(μ τ') ∂(μ τ)

/-- The rows' Vandermonde through D7.1: with weights `1/ν`, the self-energy of the rows is
bounded by the `L`-terms against the reference `μ`, the reference field and constant, the diagonal
cost and the explicit error. -/
theorem rows_vandermonde_le {ν : ℝ} (hν : 0 < ν) {p : ℕ} (x : Fin p → ℝ)
    (hx0 : ∀ i, x i ≠ 0) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hxi : Function.Injective x)
    (μ : Bool → Measure ℝ) {C : ℝ} (h : ∀ τ, BD (μ τ) C) (hC : 0 ≤ C)
    (hmass : (p : ℝ) / ν = ∑ τ, (μ τ).real univ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2 ≤
      -(1 / 2) * (∑ τ, Lpart (fun _ : Fin p => 1 / ν) (fun i => |x i|)
          (fun i => decide (0 < x i)) μ ρ τ)
      + (1 / 2) * (∑ i : Fin p, (1 / ν) ^ 2 * (-Real.log |x i| + Real.log (1 / (1 - ρ))))
      + (1 / 2) * (8 * ((p : ℝ) / ν) * C * (1 - ρ) * (1 + Real.log (1 / (1 - ρ)))
          + 2 * (1 - ρ) * (2 * ((p : ℝ) / ν)) ^ 2)
      - (∑ i, rowRef μ (x i)) / ν + (1 / 2) * refEnergy μ := by
  have hw : ∀ _i : Fin p, (0 : ℝ) < 1 / ν := fun _ => by positivity
  have ha : ∀ i, |x i| ∈ Ioo (0 : ℝ) 1 := fun i =>
    ⟨abs_pos.mpr (hx0 i), abs_lt.mpr ⟨(hx i).1, (hx i).2⟩⟩
  have hinj : ∀ i j, i ≠ j → decide (0 < x i) = decide (0 < x j) → |x i| ≠ |x j| := by
    intro i j hij hs habs
    apply hij
    apply hxi
    have hs' : (0 < x i ↔ 0 < x j) := by simpa using hs
    rcases lt_or_gt_of_ne (hx0 i) with h1 | h1
    · have h2 : x j < 0 := lt_of_le_of_ne (not_lt.mp (fun hh => by
        have := hs'.mpr hh; linarith)) (hx0 j)
      rw [abs_of_neg h1, abs_of_neg h2] at habs; linarith
    · have h2 : 0 < x j := hs'.mp h1
      rw [abs_of_pos h1, abs_of_pos h2] at habs; exact habs
  have hsum : ∑ _i : Fin p, (1 / ν) = (p : ℝ) / ν := by
    simp [div_eq_mul_inv]
  have hm : ∑ _i : Fin p, (1 / ν) = ∑ τ, (μ τ).real univ := by rw [hsum]; exact hmass
  have hD := reflection_energy (w := fun _ : Fin p => 1 / ν) (a := fun i => |x i|)
    (σ := fun i => decide (0 < x i)) (μ := μ) hw ha hinj h hC hm hρ0 hρ1
  unfold Ioff Ex at hD
  simp only [Kt_abs_eq (hx0 _) (hx0 _)] at hD
  have hoff := sum_offdiag_eq_two_mul (p := p)
    (fun i j => 1 / ν * (1 / ν) * -Real.log |x i - x j|)
    (fun i j => by rw [abs_sub_comm])
  rw [hoff] at hD
  have e1 : (∑ i, ∑ j ∈ Finset.Ioi i, 1 / ν * (1 / ν) * -Real.log |x i - x j|) =
      -((∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / ν ^ 2) := by
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_sub_comm]; field_simp
  have e2 : (∑ i : Fin p, 1 / ν * ∑ τ, ∫ y, Kt (decide (0 < x i)) τ |x i| y ∂(μ τ)) =
      (∑ i, rowRef μ (x i)) / ν := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold rowRef; ring
  rw [e1, e2] at hD
  rw [hsum] at hD
  unfold refEnergy
  simp only [← Finset.mul_sum] at hD ⊢
  linarith only [hD]

end Rows

/-! ### Cross tilt against a reference (J2 with a reference field)

The tilt is `crossBeta - r`, where `r` is the tilt of a reference measure (a data sequence) and
`Qref` its τ-damped field, `Qref u = Σ_k r_k τ^k T_k(u)`.  The reference field is carried untilted,
so that the Frostman bound `Qref - 2 T_a ≤ Sup` is available at the particles. -/

/-- The Λ term of the configuration minus the reference, dilated by `τ`. -/
def crossTiltNormRef {n : ℕ} (τ : ℝ) (w y : Fin n → ℝ) (r : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (crossBeta τ w y (k + 1) - r (k + 1)) ^ 2 / 4

theorem pair_log_add_cross_le_tilted_ref {ν e : ℝ} (hν : 0 < ν)
    (he : e ∈ Ioo (0 : ℝ) (1 / 8)) {s n : ℕ} (hs : (s : ℝ) ≤ ν)
    {u : Fin s → ℝ} (hu : ∀ i, u i ∈ Ioo (-1 : ℝ) 1) (hui : Function.Injective u)
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k|)) (w y : Fin n → ℝ) (hy : ∀ l, |y l| < 1)
    (r : ℕ → ℝ) (hr : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * r (k + 1) ^ 2))
    (hra : Summable (fun k : ℕ => r (k + 1) * a (k + 1)))
    (Qref : ℝ → ℝ)
    (hQ : ∀ x ∈ Icc (-1 : ℝ) 1, HasSum (fun k : ℕ => r (k + 1) * realEnergyTau e ^ (k + 1) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x) (Qref x)) :
    (∑ i : Fin s, ∑ j ∈ Finset.Ioi i, Real.log |u j - u i|) / ν ^ 2 +
        (∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν ≤
      -(1 / 2 : ℝ) * ((s : ℝ) / ν) ^ 2 * Real.log 2 + barrierTrialNormSq a +
        (∑ i, (Qref (u i) - 2 * barrierTrialT a (u i))) / ν +
        (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l) -
          ∑' k : ℕ, r (k + 1) * a (k + 1)) +
        crossTiltNormRef (realEnergyTau e) w y r + trialPairError ν e a := by
  have hτ := realEnergyTau_bounds he
  have hτ' : realEnergyTau e ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2⟩
  have hrx := population_cosine_regularization hν he hs hu hui
  have hS : HasSum (fun k : ℕ => pinCosineMoment ν e u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ))
      (-((∑ i : Fin s, ∑ j : Fin s,
          realEnergyCosineKernel (realEnergyTau e ^ 2) (u i) (u j)) / ν ^ 2 +
        ((s : ℝ) / ν) ^ 2 * Real.log 2) / 2) := by
    apply (hasSum_nat_add_iff
      (f := fun k : ℕ => pinCosineMoment ν e u k ^ 2 / (k : ℝ)) 1).2
    simpa using pin_hasSum_first_square hν he hu
  have hΛs := crossBeta_summable hτ' w y hy
  have hβs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      crossBeta (realEnergyTau e) w y (k + 1) ^ 2) := by
    refine (hΛs.mul_left 4).congr (fun k => ?_)
    have := crossBeta_sq (realEnergyTau e) w y (k + 1) (Nat.succ_pos k)
    linarith only [this]
  have hβ' : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => ?_) ((hβs.mul_left 2).add (hr.mul_left 2))
    have hk : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
    nlinarith [mul_nonneg hk (sq_nonneg (crossBeta (realEnergyTau e) w y (k + 1) +
      r (k + 1)))]
  have ht := tilted_energy_tangent a (pinCosineMoment ν e u)
    (fun k => crossBeta (realEnergyTau e) w y k - r k) ha hS hβ'
  have hcross := crossBeta_pairing_hasSum hν he u hu w y hy
  have href : HasSum (fun k : ℕ => r (k + 1) * pinCosineMoment ν e u (k + 1))
      ((∑ i, Qref (u i)) / ν) := by
    have hsum := (hasSum_sum (s := Finset.univ) (fun i _ => hQ (u i)
      ⟨(hu i).1.le, (hu i).2.le⟩)).div_const ν
    convert hsum using 1
    funext k
    unfold pinCosineMoment
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpair : HasSum (fun k : ℕ => (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) *
      pinCosineMoment ν e u (k + 1))
      ((∑ i, ∑ l, w l * crossLog (realEnergyTau e ^ 2 * y l) (u i)) / ν -
        (∑ i, Qref (u i)) / ν) := by
    convert hcross.sub href using 1
    funext k; ring
  have hba : HasSum (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1))
      (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l)) := by
    have hl : ∀ l, HasSum (fun k : ℕ => a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
        ((k + 1 : ℕ) : ℝ)) (barrierTrialS a (-(realEnergyTau e) * y l)) := by
      intro l
      refine (barrierTrialS_summable a ha ?_).hasSum
      rw [abs_mul, abs_neg, abs_of_pos hτ.1]
      calc _ ≤ 1 * |y l| := mul_le_mul_of_nonneg_right hτ.2.le (abs_nonneg _)
        _ ≤ 1 := by linarith [hy l]
    have hsum := hasSum_sum (s := Finset.univ)
      (fun l _ => ((hl l).mul_left (w l)).mul_left (-2 : ℝ))
    have hconv : ∀ k : ℕ, crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1) =
        ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := by
      intro k
      have h1 : ∀ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) = (-2 * (-1) ^ (k + 1) * realEnergyTau e ^ (k + 1) *
            a (k + 1) / ((k + 1 : ℕ) : ℝ)) * (w l * y l ^ (k + 1)) := by
        intro l; rw [mul_pow, neg_pow]; ring
      simp only [h1]
      rw [← mul_sum]
      unfold crossBeta
      ring
    have e1 : (fun k : ℕ => crossBeta (realEnergyTau e) w y (k + 1) * a (k + 1)) =
        fun k : ℕ => ∑ l, -2 * (w l * (a (k + 1) * (-(realEnergyTau e) * y l) ^ (k + 1) /
          ((k + 1 : ℕ) : ℝ))) := funext hconv
    rw [e1]
    convert hsum using 1
    rw [mul_sum]
  have hba' : HasSum (fun k : ℕ => (crossBeta (realEnergyTau e) w y (k + 1) - r (k + 1)) *
      a (k + 1)) (-2 * ∑ l, w l * barrierTrialS a (-(realEnergyTau e) * y l) -
        ∑' k : ℕ, r (k + 1) * a (k + 1)) := by
    convert hba.sub hra.hasSum using 1
    funext k; ring
  rw [hpair.tsum_eq, hba'.tsum_eq, (pin_hasSum_trialTau_average a ha ν he hu).tsum_eq] at ht
  have hq : (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * (crossBeta (realEnergyTau e) w y (k + 1) -
      r (k + 1)) ^ 2 / 4) = crossTiltNormRef (realEnergyTau e) w y r := rfl
  rw [hq] at ht
  have hav := pin_average_le_of_le_add hν hs
    (fun i => -2 * realEnergyTrialTau a e (u i))
    (fun i => -2 * barrierTrialT a (u i))
    (c := 2 * e * (∑' k, |a k|))
    (mul_nonneg (mul_nonneg (by norm_num) he.1.le) (tsum_nonneg fun _ => abs_nonneg _))
    (fun i => by
      have hh := (abs_le.mp (realEnergyTrialTau_sub_le a ha he (hu i))).1
      linarith only [hh])
  have hs1 : -2 * ((∑ i, realEnergyTrialTau a e (u i)) / ν) =
      (∑ i, -2 * realEnergyTrialTau a e (u i)) / ν := by
    rw [← Finset.mul_sum]; ring
  have hsplit : (∑ i, (Qref (u i) - 2 * barrierTrialT a (u i))) / ν =
      (∑ i, Qref (u i)) / ν + (∑ i, -2 * barrierTrialT a (u i)) / ν := by
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold trialPairError
  rw [hsplit]
  ring_nf at hrx ht hav hs1 ⊢
  linarith only [hrx, ht, hav, hs1]

/-! ### The spike hypothesis (A7, Theorem S2′), recorded as a type

`logRatio g` is `log Pref + log Z(φψ) − log Z(ψ)` of the route II ratio as a function of the
positive nodes `g` (negative nodes and particle count fixed).  Capping replaces `g p` by
`min (g p) (1 - θ)`.  The hypothesis says that each spiked positive (one with `1 - θ < g p`)
costs at most `cost` (`= C N + O(1)`, with `C ≤ 0.85` at `θ = 0.001`), uniformly in the depth,
plus a global slack `slack` (`o(N²)`).  The class condition `M ≤ 1.1228 N` on the number of
spikes is a separate hypothesis of the consumer. -/
def SpikeBound {q : ℕ} (logRatio : (Fin q → ℝ) → ℝ) (θ cost slack : ℝ) : Prop :=
  ∀ g : Fin q → ℝ, (∀ p, g p ∈ Ioo (0 : ℝ) 1) →
    logRatio g ≤ logRatio (fun p => min (g p) (1 - θ)) +
      cost * ((Finset.univ.filter (fun p => 1 - θ < g p)).card : ℝ) + slack

end
end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.pin_zero_canonical
#print axioms CatalanMeasure.Signed.rows_vandermonde_le
#print axioms CatalanMeasure.Signed.pair_log_add_cross_le_tilted_ref

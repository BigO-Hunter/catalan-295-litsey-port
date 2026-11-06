module

public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section
set_option Elab.async false

/-!
# Route I `AngularSource`: Jensen / odd-log gas bound and the exact-versus-finite angular field

Data-free (C6, theorem side). For a list of Y-cells with `|Y| >= 2` (`CellAdm`), a kernel
`Q(x) = p - 2 t u x + s x^2` with `t^2 = p s` (direct `(r^2,1,r)`, reflected `(1,r^2,r)`, `u = cos theta`),
`bin_jensen` proves `physL bin (1/2 log Q) <= (m/2)(log D - sum_{k<=n} (alpha u)^k/k)` for odd `n`,
`|u| <= 1`, including the endpoint logarithmic singularities (`sandwich`, `intervalIntegrable_log_Q`).
`Binning` splits a species into bins (slices of its cells), `kernel_le` sums the bins into the gas
polynomial in `u`, `angular_finite_eq` isolates the auxiliary Chebyshev coefficients, and
`angular_dominates` is `Dominates.ang` at every degree `K` (the positive tail `auxTail` counted once).
-/
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.RouteI.AngularSource
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open Real Set MeasureTheory intervalIntegral

noncomputable section

/-- A cell whose Y-range lies in `|Y| >= 2` (the physical branch is real). -/
def CellAdm (c : YCell) : Prop := 2 ≤ c.lo ∨ c.hi ≤ -2

theorem CellAdm.two_le_abs {c : YCell} (h : CellAdm c) {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) :
    2 ≤ |Y| := by
  rcases h with h | h
  · rw [abs_of_nonneg (by linarith [hY.1])]; linarith [hY.1]
  · rw [abs_of_nonpos (by linarith [hY.2])]; linarith [hY.2]

/-- `physX` is the real inverse branch: nonzero, `|X| <= 1`, `X*Y = X^2+1`. -/
theorem physX_spec {Y : ℝ} (hY : 2 ≤ |Y|) :
    YCell.physX Y ≠ 0 ∧ |YCell.physX Y| ≤ 1 ∧ YCell.physX Y * Y = YCell.physX Y ^ 2 + 1 := by
  have key : ∀ Z : ℝ, 2 ≤ Z → (2 / (Z + √(Z ^ 2 - 4)) ≠ 0 ∧ |2 / (Z + √(Z ^ 2 - 4))| ≤ 1 ∧
      (2 / (Z + √(Z ^ 2 - 4))) * Z = (2 / (Z + √(Z ^ 2 - 4))) ^ 2 + 1) := by
    intro Z hZ
    have hs0 : 0 ≤ √(Z ^ 2 - 4) := Real.sqrt_nonneg _
    have hs2 : √(Z ^ 2 - 4) ^ 2 = Z ^ 2 - 4 := Real.sq_sqrt (by nlinarith)
    have hpos : 0 < Z + √(Z ^ 2 - 4) := by linarith
    refine ⟨by positivity, ?_, ?_⟩
    · rw [abs_of_pos (by positivity), div_le_one hpos]; linarith
    · field_simp
      nlinarith [hs2]
  unfold YCell.physX
  by_cases h0 : 0 ≤ Y
  · simp only [h0, if_true]
    rw [abs_of_nonneg h0] at hY
    exact key Y hY
  · simp only [h0, if_false]
    have hneg : Y ≤ -2 := by
      rw [abs_of_neg (not_le.mp h0)] at hY; linarith
    have hk := key (-Y) (by linarith)
    have hsq : (-Y) ^ 2 = Y ^ 2 := by ring
    rw [hsq] at hk
    obtain ⟨h1, h2, h3⟩ := hk
    refine ⟨by simpa using h1, by simpa [abs_neg] using h2, ?_⟩
    have : (-(2 / (-Y + √(Y ^ 2 - 4)))) * Y = (2 / (-Y + √(Y ^ 2 - 4))) * (-Y) := by ring
    rw [this, h3]; ring

theorem continuousOn_physX {c : YCell} (h : CellAdm c) : ContinuousOn YCell.physX (Icc c.lo c.hi) := by
  rcases h with h | h
  · have : ContinuousOn (fun Y : ℝ => 2 / (Y + √(Y ^ 2 - 4))) (Icc c.lo c.hi) := by
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro Y hY
        have := Real.sqrt_nonneg (Y ^ 2 - 4)
        have := hY.1
        intro h0; linarith
    refine this.congr ?_
    intro Y hY
    simp [YCell.physX, if_pos (show 0 ≤ Y by linarith [hY.1])]
  · have : ContinuousOn (fun Y : ℝ => -(2 / (-Y + √(Y ^ 2 - 4)))) (Icc c.lo c.hi) := by
      apply ContinuousOn.neg
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro Y hY
        have := Real.sqrt_nonneg (Y ^ 2 - 4)
        have := hY.2
        intro h0; linarith
    refine this.congr ?_
    intro Y hY
    have : ¬ (0 ≤ Y) := by have := hY.2; linarith
    simp [YCell.physX, if_neg this]

/-- Lower sandwich `kappa |Y - Y0| <= |X(Y) - x0|` on an admissible cell. -/
theorem sandwich {c : YCell} (hc : CellAdm c) {x0 : ℝ} (hx0 : x0 ≠ 0) :
    ∃ κ > 0, ∃ Y0 : ℝ, (∀ Y ∈ Icc c.lo c.hi, κ * |Y - Y0| ≤ |YCell.physX Y - x0|) ∧
      (∀ Y ∈ Icc c.lo c.hi, Y = Y0 → YCell.physX Y = x0) := by
  have hM : 0 < |c.lo| + |c.hi| := by
    rcases hc with h | h
    · have : 0 < |c.lo| := abs_pos.mpr (by linarith)
      positivity
    · have : 0 < |c.hi| := abs_pos.mpr (by linarith)
      positivity
  by_cases hnear : |x0| ≤ 1
  · refine ⟨|x0| / (2 * (|c.lo| + |c.hi|)), by positivity, x0 + x0⁻¹, ?_, ?_⟩
    · intro Y hY
      obtain ⟨hne, hle, hXY⟩ := physX_spec (hc.two_le_abs hY)
      set X := YCell.physX Y with hX
      have hYM : |Y| ≤ |c.lo| + |c.hi| := by
        have h1 : Y ≤ |c.hi| := le_trans hY.2 (le_abs_self _)
        have h2 : -|c.lo| ≤ Y := le_trans (neg_abs_le _) hY.1
        rw [abs_le]; constructor <;> linarith [abs_nonneg c.lo, abs_nonneg c.hi]
      have hkey : (Y - (x0 + x0⁻¹)) * X * x0 = (X - x0) * (X * x0 - 1) := by
        field_simp
        linear_combination x0 * hXY
      have hXa : 1 ≤ |X| * |Y| := by
        have : |X * Y| = X ^ 2 + 1 := by rw [hXY]; exact abs_of_nonneg (by positivity)
        rw [← abs_mul, this]; nlinarith [sq_nonneg X]
      have hprod : |X * x0| ≤ 1 := by
        rw [abs_mul]; exact mul_le_one₀ hle (abs_nonneg _) hnear
      have h2 : |X * x0 - 1| ≤ 2 := by
        calc |X * x0 - 1| ≤ |X * x0| + |(1:ℝ)| := abs_sub _ _
          _ ≤ 2 := by rw [abs_one]; linarith
      have h3 : |Y - (x0 + x0⁻¹)| * |X| * |x0| ≤ 2 * |X - x0| := by
        have := congrArg abs hkey
        rw [abs_mul, abs_mul, abs_mul] at this
        rw [this]
        nlinarith [abs_nonneg (X - x0)]
      have hXM : 1 ≤ |X| * (|c.lo| + |c.hi|) := by
        calc (1:ℝ) ≤ |X| * |Y| := hXa
          _ ≤ _ := mul_le_mul_of_nonneg_left hYM (abs_nonneg _)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have hA := abs_nonneg (Y - (x0 + x0⁻¹))
      have hB := abs_nonneg x0
      calc |x0| * |Y - (x0 + x0⁻¹)| = |Y - (x0 + x0⁻¹)| * |x0| * 1 := by ring
        _ ≤ |Y - (x0 + x0⁻¹)| * |x0| * (|X| * (|c.lo| + |c.hi|)) :=
            mul_le_mul_of_nonneg_left hXM (by positivity)
        _ = (|Y - (x0 + x0⁻¹)| * |X| * |x0|) * (|c.lo| + |c.hi|) := by ring
        _ ≤ 2 * |X - x0| * (|c.lo| + |c.hi|) :=
            mul_le_mul_of_nonneg_right h3 hM.le
        _ = |X - x0| * (2 * (|c.lo| + |c.hi|)) := by ring
    · intro Y hY hYY
      obtain ⟨hne, hle, hXY⟩ := physX_spec (hc.two_le_abs hY)
      set X := YCell.physX Y with hX
      have hkey : (Y - (x0 + x0⁻¹)) * X * x0 = (X - x0) * (X * x0 - 1) := by
        field_simp
        linear_combination x0 * hXY
      rw [hYY, sub_self, zero_mul, zero_mul] at hkey
      rcases mul_eq_zero.mp hkey.symm with h | h
      · linarith
      · have hX1 : X * x0 = 1 := by linarith
        have habs : |X| * |x0| = 1 := by rw [← abs_mul, hX1]; simp
        have hx1 : |x0| = 1 := by
          have := abs_nonneg X
          nlinarith [abs_nonneg x0]
        have hsq : x0 * x0 = 1 := by
          have : |x0| * |x0| = 1 := by rw [hx1]; norm_num
          rwa [← abs_mul, abs_of_nonneg (mul_self_nonneg x0)] at this
        calc X = (X * x0) * x0 := by rw [mul_assoc, hsq, mul_one]
          _ = x0 := by rw [hX1, one_mul]
  · rw [not_le] at hnear
    refine ⟨(|x0| - 1) / (2 * (|c.lo| + |c.hi|)), by apply div_pos <;> linarith, 0, ?_, ?_⟩
    · intro Y hY
      obtain ⟨hne, hle, hXY⟩ := physX_spec (hc.two_le_abs hY)
      have hYM : |Y| ≤ |c.lo| + |c.hi| := by
        have h1 : Y ≤ |c.hi| := le_trans hY.2 (le_abs_self _)
        have h2 : -|c.lo| ≤ Y := le_trans (neg_abs_le _) hY.1
        rw [abs_le]; constructor <;> linarith [abs_nonneg c.lo, abs_nonneg c.hi]
      have h1 : |x0| - 1 ≤ |YCell.physX Y - x0| := by
        have := abs_sub_abs_le_abs_sub x0 (YCell.physX Y)
        rw [abs_sub_comm] at this
        linarith
      rw [sub_zero, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : 0 ≤ |x0| - 1 := by linarith
      nlinarith [abs_nonneg Y, abs_nonneg (YCell.physX Y - x0)]
    · intro Y hY hY0
      have := hc.two_le_abs hY
      rw [hY0] at this; simp at this; linarith

theorem abs_le_M {c : YCell} {Y : ℝ} (hY : Y ∈ Icc c.lo c.hi) : |Y| ≤ |c.lo| + |c.hi| := by
  have h1 : Y ≤ |c.hi| := le_trans hY.2 (le_abs_self _)
  have h2 : -|c.lo| ≤ Y := le_trans (neg_abs_le _) hY.1
  rw [abs_le]; constructor <;> linarith [abs_nonneg c.lo, abs_nonneg c.hi]

theorem M_pos {c : YCell} (hc : CellAdm c) : 0 < |c.lo| + |c.hi| := by
  rcases hc with h | h
  · have : 0 < |c.lo| := abs_pos.mpr (by linarith)
    positivity
  · have : 0 < |c.hi| := abs_pos.mpr (by linarith)
    positivity

/-- The quadratic `Q(x) = p - 2 t u x + s x^2` (squared distance kernel; `u = cos theta`). -/
def Qf (p s t u x : ℝ) : ℝ := p - 2 * t * u * x + s * x ^ 2

theorem Qf_eq {p s t u : ℝ} (hs : 0 < s) (ht : t ^ 2 = p * s) (x : ℝ) :
    Qf p s t u x = s * (x - t * u / s) ^ 2 + p * (1 - u ^ 2) := by
  have hp : p = t ^ 2 / s := by field_simp; linarith
  unfold Qf
  rw [hp]; field_simp; ring

theorem Qf_ge {p s t u : ℝ} (hs : 0 < s) (ht : t ^ 2 = p * s) (x : ℝ) :
    p * (1 - u ^ 2) ≤ Qf p s t u x := by
  rw [Qf_eq hs ht]; nlinarith [mul_nonneg hs.le (sq_nonneg (x - t * u / s))]

theorem Qf_nonneg {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht : t ^ 2 = p * s) (hu : |u| ≤ 1)
    (x : ℝ) : 0 ≤ Qf p s t u x := by
  have : u ^ 2 ≤ 1 := by simpa using sq_le_one_iff_abs_le_one u |>.mpr hu
  have := Qf_ge (u := u) hs ht x
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr ‹u ^ 2 ≤ 1›)]

theorem Qf_le {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht0 : 0 < t) (hu : |u| ≤ 1) {x : ℝ}
    (hx : |x| ≤ 1) : Qf p s t u x ≤ p + 2 * t + s := by
  have h1 : |t * u * x| ≤ t := by
    rw [abs_mul, abs_mul, abs_of_pos ht0]
    have := mul_le_one₀ hu (abs_nonneg _) hx
    nlinarith
  have h2 : x ^ 2 ≤ 1 := by simpa using sq_le_one_iff_abs_le_one x |>.mpr hx
  unfold Qf
  have := (abs_le.mp h1).1
  nlinarith

theorem Q_profile {c : YCell} (hc : CellAdm c) {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s)
    (ht0 : 0 < t) (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) :
    ∃ a > 0, ∃ Y0 : ℝ, (∀ Y ∈ Icc c.lo c.hi, a * (Y - Y0) ^ 2 ≤ Qf p s t u (YCell.physX Y)) ∧
      (∀ Y ∈ Icc c.lo c.hi, Y = Y0 → Qf p s t u (YCell.physX Y) = 0) := by
  have hu2 : u ^ 2 ≤ 1 := by simpa using sq_le_one_iff_abs_le_one u |>.mpr hu
  have hM := M_pos hc
  by_cases h1 : u ^ 2 < 1
  · refine ⟨p * (1 - u ^ 2) / (|c.lo| + |c.hi|) ^ 2, by
      have : 0 < 1 - u ^ 2 := by linarith
      positivity, 0, ?_, ?_⟩
    · intro Y hY
      have hYM := abs_le_M hY
      have hY2 : (Y - 0) ^ 2 ≤ (|c.lo| + |c.hi|) ^ 2 := by
        rw [sub_zero, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hYM 2
      have := Qf_ge (u := u) hs ht (YCell.physX Y)
      calc p * (1 - u ^ 2) / (|c.lo| + |c.hi|) ^ 2 * (Y - 0) ^ 2
          ≤ p * (1 - u ^ 2) / (|c.lo| + |c.hi|) ^ 2 * (|c.lo| + |c.hi|) ^ 2 :=
            mul_le_mul_of_nonneg_left hY2 (by
              have : 0 < 1 - u ^ 2 := by linarith
              positivity)
        _ = p * (1 - u ^ 2) := by field_simp
        _ ≤ _ := this
    · intro Y hY hY0
      have := hc.two_le_abs hY
      rw [hY0] at this; simp at this; linarith
  · have hu1 : u ^ 2 = 1 := le_antisymm hu2 (not_lt.mp h1)
    have hu0 : u ≠ 0 := by rintro rfl; norm_num at hu1
    have hx0 : t * u / s ≠ 0 := by positivity
    obtain ⟨κ, hκ, Y0, hlow, hz⟩ := sandwich hc hx0
    refine ⟨s * κ ^ 2, by positivity, Y0, ?_, ?_⟩
    · intro Y hY
      have h := hlow Y hY
      rw [Qf_eq hs ht, hu1]
      have h2 : (κ * |Y - Y0|) ^ 2 ≤ |YCell.physX Y - t * u / s| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
      rw [sq_abs, mul_pow, sq_abs] at h2
      nlinarith [mul_le_mul_of_nonneg_left h2 hs.le]
    · intro Y hY hY0
      rw [Qf_eq hs ht, hu1, hz Y hY hY0]; ring

theorem contOn_Q {c : YCell} (hc : CellAdm c) (p s t u : ℝ) :
    ContinuousOn (fun Y => Qf p s t u (YCell.physX Y)) (Icc c.lo c.hi) := by
  have h := continuousOn_physX hc
  unfold Qf; fun_prop

theorem intervalIntegrable_log_Q {c : YCell} (hc : CellAdm c) {p s t u : ℝ} (hp : 0 < p)
    (hs : 0 < s) (ht0 : 0 < t) (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) :
    IntervalIntegrable (fun Y => Real.log (Qf p s t u (YCell.physX Y))) volume c.lo c.hi := by
  obtain ⟨a, ha, Y0, hlow, hz⟩ := Q_profile hc hp hs ht0 ht hu
  have hBq : 0 < p + 2 * t + s := by positivity
  set K := |Real.log (p + 2 * t + s)| + |Real.log a| with hK
  have hbound : ∀ Y ∈ Icc c.lo c.hi,
      ‖Real.log (Qf p s t u (YCell.physX Y))‖ ≤ K + 2 * |Real.log (Y - Y0)| := by
    intro Y hY
    have hK0 : 0 ≤ K := by positivity
    rw [Real.norm_eq_abs]
    by_cases h0 : Qf p s t u (YCell.physX Y) = 0
    · rw [h0]; simp; positivity
    · have hpos : 0 < Qf p s t u (YCell.physX Y) :=
        lt_of_le_of_ne (Qf_nonneg hp hs ht hu _) (Ne.symm h0)
      have hne : Y ≠ Y0 := fun h => h0 (hz Y hY h)
      have hY2 : 0 < (Y - Y0) ^ 2 := by positivity
      have hup : Real.log (Qf p s t u (YCell.physX Y)) ≤ Real.log (p + 2 * t + s) :=
        Real.log_le_log hpos (Qf_le hp hs ht0 hu (physX_spec (hc.two_le_abs hY)).2.1)
      have hlo : Real.log (a * (Y - Y0) ^ 2) ≤ Real.log (Qf p s t u (YCell.physX Y)) :=
        Real.log_le_log (by positivity) (hlow Y hY)
      rw [Real.log_mul ha.ne' hY2.ne', Real.log_pow] at hlo
      have h1 := le_abs_self (Real.log (p + 2 * t + s))
      have h2 := neg_abs_le (Real.log a)
      have h3 := neg_abs_le (Real.log (Y - Y0))
      have h4 := abs_nonneg (Real.log (Y - Y0))
      rw [abs_le]; constructor <;> push_cast at hlo <;> nlinarith [abs_nonneg (Real.log a),
        abs_nonneg (Real.log (p + 2 * t + s)), le_abs_self (Real.log (Y - Y0))]
  have hg : IntervalIntegrable (fun Y => K + 2 * |Real.log (Y - Y0)|) volume c.lo c.hi := by
    refine intervalIntegrable_const.add (IntervalIntegrable.const_mul ?_ 2)
    have := (intervalIntegrable_log' (a := c.lo - Y0) (b := c.hi - Y0)).comp_sub_right Y0
    simpa using this.abs
  have hmeas : AEStronglyMeasurable (fun Y => Real.log (Qf p s t u (YCell.physX Y)))
      (volume.restrict (Set.uIoc c.lo c.hi)) := by
    rw [Set.uIoc_of_le c.lo_lt.le]
    have := ((contOn_Q hc p s t u).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable
      (μ := volume) measurableSet_Ioc
    exact (Real.measurable_log.comp_aemeasurable this.aemeasurable).aestronglyMeasurable
  refine hg.mono_fun' hmeas ?_
  rw [Set.uIoc_of_le c.lo_lt.le]
  exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun Y hY =>
    hbound Y (Ioc_subset_Icc_self hY))

theorem integral_Q_pos {c : YCell} (hc : CellAdm c) {p s t u : ℝ} (hp : 0 < p)
    (hs : 0 < s) (ht0 : 0 < t) (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) :
    0 < ∫ Y in c.lo..c.hi, Qf p s t u (YCell.physX Y) := by
  obtain ⟨a, ha, Y0, hlow, hz⟩ := Q_profile hc hp hs ht0 ht hu
  have hint : IntervalIntegrable (fun Y => Qf p s t u (YCell.physX Y)) volume c.lo c.hi :=
    (contOn_Q hc p s t u).intervalIntegrable_of_Icc c.lo_lt.le
  have hg : IntervalIntegrable (fun Y : ℝ => a * (Y - Y0) ^ 2) volume c.lo c.hi := by
    apply Continuous.intervalIntegrable; fun_prop
  have hle := intervalIntegral.integral_mono_on c.lo_lt.le hg hint hlow
  have hval : ∫ Y in c.lo..c.hi, a * (Y - Y0) ^ 2 =
      a * (((c.hi - Y0) ^ 3 - (c.lo - Y0) ^ 3) / 3) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => x ^ 2) Y0, integral_pow]
    norm_num
  have hpos : 0 < a * (((c.hi - Y0) ^ 3 - (c.lo - Y0) ^ 3) / 3) := by
    have hlt := c.lo_lt
    have : (c.lo - Y0) ^ 3 < (c.hi - Y0) ^ 3 :=
      Odd.strictMono_pow (by decide) (by linarith)
    positivity
  linarith

/-- Linear expansion of the cell average of `Q`. -/
theorem phys_Q {c : YCell} (hc : CellAdm c) (p s t u : ℝ) :
    c.phys (Qf p s t u) = p * c.w - 2 * t * u * c.phys (fun x => x) + s * c.phys (fun x => x ^ 2) := by
  have hi1 : IntervalIntegrable (fun Y => YCell.physX Y) volume c.lo c.hi :=
    (continuousOn_physX hc).intervalIntegrable_of_Icc c.lo_lt.le
  have hi2 : IntervalIntegrable (fun Y => YCell.physX Y ^ 2) volume c.lo c.hi :=
    ((continuousOn_physX hc).pow 2).intervalIntegrable_of_Icc c.lo_lt.le
  have hL : c.hi - c.lo ≠ 0 := by linarith [c.lo_lt]
  simp only [YCell.phys, YCell.avg, Qf]
  rw [intervalIntegral.integral_add ((intervalIntegrable_const).sub (hi1.const_mul _))
    (hi2.const_mul _), intervalIntegral.integral_sub intervalIntegrable_const (hi1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  field_simp

/-- Cell Jensen (tangent) inequality with the half-log. -/
theorem phys_jensen {c : YCell} (hc : CellAdm c) {p s t u : ℝ} (hp : 0 < p)
    (hs : 0 < s) (ht0 : 0 < t) (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) {d : ℝ} (hd : 0 < d) :
    c.phys (fun x => 1 / 2 * Real.log (Qf p s t u x)) ≤
      1 / 2 * (c.w * Real.log d + (c.phys (Qf p s t u) - c.w * d) / d) := by
  have hlt := c.lo_lt
  have hL : 0 < c.hi - c.lo := by linarith
  have hIl := intervalIntegrable_log_Q hc hp hs ht0 ht hu
  have hIq : IntervalIntegrable (fun Y => Qf p s t u (YCell.physX Y)) volume c.lo c.hi :=
    (contOn_Q hc p s t u).intervalIntegrable_of_Icc hlt.le
  have hIg : IntervalIntegrable
      (fun Y => Real.log d + (Qf p s t u (YCell.physX Y) - d) / d) volume c.lo c.hi :=
    intervalIntegrable_const.add ((hIq.sub intervalIntegrable_const).div_const d)
  -- almost-everywhere positivity
  obtain ⟨a, ha, Y0, hlow, hz⟩ := Q_profile hc hp hs ht0 ht hu
  have hae0 : ∀ᵐ Y : ℝ ∂volume, Y ≠ Y0 := by
    simpa using (Set.countable_singleton Y0).ae_notMem volume
  have hmono : (fun Y => Real.log (Qf p s t u (YCell.physX Y))) ≤ᵐ[volume.restrict (Icc c.lo c.hi)]
      (fun Y => Real.log d + (Qf p s t u (YCell.physX Y) - d) / d) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae0] with Y hY0 hY
    have hpos : 0 < Qf p s t u (YCell.physX Y) := by
      have h1 := hlow Y hY
      have h2 : 0 < a * (Y - Y0) ^ 2 := by
        have : Y - Y0 ≠ 0 := sub_ne_zero.mpr hY0
        positivity
      linarith
    have := Real.log_le_sub_one_of_pos (div_pos hpos hd)
    rw [Real.log_div hpos.ne' hd.ne'] at this
    have e : Qf p s t u (YCell.physX Y) / d - 1 = (Qf p s t u (YCell.physX Y) - d) / d := by
      field_simp
    linarith
  have hI := intervalIntegral.integral_mono_ae_restrict hlt.le hIl hIg hmono
  rw [intervalIntegral.integral_add intervalIntegrable_const (hIq.sub intervalIntegrable_const |>.div_const d),
    intervalIntegral.integral_div, intervalIntegral.integral_sub hIq intervalIntegrable_const] at hI
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hI
  simp only [YCell.phys, YCell.avg]
  rw [intervalIntegral.integral_const_mul]
  have hk : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg hL.le
  have hw : c.w = c.w / (c.hi - c.lo) * (c.hi - c.lo) := by field_simp
  set k := c.w / (c.hi - c.lo) with hkdef
  set I := ∫ Y in c.lo..c.hi, Real.log (Qf p s t u (YCell.physX Y))
  set J := ∫ Y in c.lo..c.hi, Qf p s t u (YCell.physX Y)
  have h2 := mul_le_mul_of_nonneg_left hI hk
  have : k * (1 / 2 * I) ≤ 1 / 2 * (c.w * Real.log d + (k * J - c.w * d) / d) := by
    have e : 1 / 2 * (c.w * Real.log d + (k * J - c.w * d) / d) =
        1 / 2 * (k * ((c.hi - c.lo) * Real.log d + (J - (c.hi - c.lo) * d) / d)) := by
      rw [hw]; field_simp
    rw [e]; nlinarith [h2]
  exact this

/-! ### Odd-degree logarithm bound -/

theorem log_one_sub_le_odd {n : ℕ} (hn : Odd n) {z : ℝ} (hz : |z| < 1) :
    Real.log (1 - z) ≤ -∑ k ∈ Finset.range n, z ^ (k + 1) / ((k : ℝ) + 1) := by
  set g : ℝ → ℝ := fun z => -(∑ k ∈ Finset.range n, z ^ (k + 1) / ((k : ℝ) + 1)) -
    Real.log (1 - z) with hg
  have hderiv : ∀ y : ℝ, y < 1 → HasDerivAt g (y ^ n / (1 - y)) y := by
    intro y hy
    have h1 : HasDerivAt (fun z : ℝ => ∑ k ∈ Finset.range n, z ^ (k + 1) / ((k : ℝ) + 1))
        (∑ k ∈ Finset.range n, y ^ k) y := by
      have := HasDerivAt.fun_sum (u := Finset.range n)
        (A := fun k z => z ^ (k + 1) / ((k : ℝ) + 1))
        (A' := fun k => y ^ k)
        (fun k _ => by
          have := (hasDerivAt_pow (k + 1) y).div_const ((k : ℝ) + 1)
          convert this using 1
          push_cast
          field_simp)
      simpa using this
    have h2 : HasDerivAt (fun z : ℝ => Real.log (1 - z)) (-1 / (1 - y)) y := by
      have := ((hasDerivAt_id y).const_sub 1).log (by simp; linarith)
      simpa using this
    have := h1.neg.sub h2
    convert this using 1
    have hy1 : (1 - y) ≠ 0 := by linarith
    have := geom_sum_mul_neg y n
    field_simp
    linear_combination (1 : ℝ) * this
  have hg0 : g 0 = 0 := by simp [hg]
  have key : 0 ≤ g z := by
    have hz1 : z < 1 := (abs_lt.mp hz).2
    have hzm : -1 < z := (abs_lt.mp hz).1
    rcases le_total 0 z with h0 | h0
    · have hmono : MonotoneOn g (Set.Icc 0 z) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 z)
        · intro y hy
          exact (hderiv y (by linarith [hy.2])).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          exact (hderiv y (by linarith [hy.2])).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hderiv y (by linarith [hy.2])).deriv]
          have : 0 < 1 - y := by linarith [hy.2]
          have : 0 ≤ y ^ n := pow_nonneg hy.1.le n
          positivity
      have := hmono (Set.left_mem_Icc.mpr h0) (Set.right_mem_Icc.mpr h0) h0
      linarith
    · have hanti : AntitoneOn g (Set.Icc z 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc z 0)
        · intro y hy
          exact (hderiv y (by linarith [hy.2])).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          exact (hderiv y (by linarith [hy.2])).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Icc] at hy
          rw [(hderiv y (by linarith [hy.2])).deriv]
          have hd : 0 < 1 - y := by linarith [hy.2]
          have : y ^ n ≤ 0 := hn.pow_nonpos hy.2.le
          exact div_nonpos_of_nonpos_of_nonneg this hd.le
      have := hanti (Set.left_mem_Icc.mpr h0) (Set.right_mem_Icc.mpr h0) h0
      linarith
  simp only [hg] at key
  linarith

/-! ### Bin sums -/

theorem physL_nil (f : ℝ → ℝ) : physL [] f = 0 := by simp [physL]
theorem physL_cons (c : YCell) (l : List YCell) (f : ℝ → ℝ) :
    physL (c :: l) f = c.phys f + physL l f := by simp [physL]
theorem massL_cons (c : YCell) (l : List YCell) : massL (c :: l) = c.w + massL l := by
  simp [massL]
theorem massL_nonneg (l : List YCell) : 0 ≤ massL l := by
  induction l with
  | nil => simp [massL]
  | cons c l ih => rw [massL_cons]; linarith [c.w_nonneg]

theorem phys_zero_of_w {c : YCell} (h : c.w = 0) (f : ℝ → ℝ) : c.phys f = 0 := by
  simp [YCell.phys, YCell.avg, h]

theorem physL_zero_of_mass (f : ℝ → ℝ) : ∀ bin : List YCell, massL bin = 0 → physL bin f = 0 := by
  intro bin
  induction bin with
  | nil => intro _; exact physL_nil f
  | cons c l ih =>
    intro h
    rw [massL_cons] at h
    have h1 := c.w_nonneg
    have h2 := massL_nonneg l
    rw [physL_cons, phys_zero_of_w (by linarith), ih (by linarith)]; ring

theorem phys_nonneg {c : YCell} {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ c.phys f := by
  unfold YCell.phys YCell.avg
  apply mul_nonneg (div_nonneg c.w_nonneg (by linarith [c.lo_lt]))
  exact intervalIntegral.integral_nonneg c.lo_lt.le fun _ _ => hf _

theorem physL_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : ∀ l : List YCell, 0 ≤ physL l f := by
  intro l
  induction l with
  | nil => simp [physL_nil]
  | cons c l ih => rw [physL_cons]; exact add_nonneg (phys_nonneg hf) ih

theorem physL_Q (p s t u : ℝ) {bin : List YCell} (hadm : ∀ c ∈ bin, CellAdm c) :
    physL bin (Qf p s t u) = p * massL bin - 2 * t * u * physL bin (fun x => x) +
      s * physL bin (fun x => x ^ 2) := by
  induction bin with
  | nil => simp [physL_nil, massL]
  | cons c l ih =>
    rw [physL_cons, physL_cons, physL_cons, massL_cons,
      ih (fun c' hc' => hadm c' (List.mem_cons_of_mem _ hc')),
      phys_Q (hadm c (List.mem_cons_self))]
    ring

theorem physL_Q_pos {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht0 : 0 < t) (ht : t ^ 2 = p * s)
    (hu : |u| ≤ 1) : ∀ bin : List YCell, (∀ c ∈ bin, CellAdm c) → 0 < massL bin →
      0 < physL bin (Qf p s t u) := by
  intro bin
  induction bin with
  | nil => intro _ h; simp [massL] at h
  | cons c l ih =>
    intro hadm hm
    rw [massL_cons] at hm
    have hc := hadm c (List.mem_cons_self)
    have hl := fun c' hc' => hadm c' (List.mem_cons_of_mem _ hc')
    have h0 : 0 ≤ c.phys (Qf p s t u) := phys_nonneg (Qf_nonneg hp hs ht hu)
    have h0' : 0 ≤ physL l (Qf p s t u) := physL_nonneg (Qf_nonneg hp hs ht hu) l
    rw [physL_cons]
    rcases c.w_nonneg.lt_or_eq with hw | hw
    · have : 0 < c.phys (Qf p s t u) := by
        unfold YCell.phys YCell.avg
        exact mul_pos (div_pos hw (by linarith [c.lo_lt])) (integral_Q_pos hc hp hs ht0 ht hu)
      linarith
    · have : 0 < massL l := by rw [← hw] at hm; linarith
      linarith [ih hl this]

/-! ### The Jensen bound for one bin -/

/-- Unnormalized moments and normalized parameters of a bin. -/
def binM1 (bin : List YCell) : ℝ := physL bin fun x => x
def binM2 (bin : List YCell) : ℝ := physL bin fun x => x ^ 2
def binD (bin : List YCell) (p s : ℝ) : ℝ := p + s * binM2 bin / massL bin
def binAlpha (bin : List YCell) (p s t : ℝ) : ℝ :=
  2 * t * (binM1 bin / massL bin) / binD bin p s

theorem physL_jensen_aux {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht0 : 0 < t)
    (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) {d : ℝ} (hd : 0 < d) :
    ∀ bin : List YCell, (∀ c ∈ bin, CellAdm c) →
      physL bin (fun x => 1 / 2 * Real.log (Qf p s t u x)) ≤
        1 / 2 * (massL bin * Real.log d + (physL bin (Qf p s t u) - massL bin * d) / d) := by
  intro bin
  induction bin with
  | nil => intro _; simp [physL_nil, massL]
  | cons c l ih =>
    intro hadm
    have hc := hadm c (List.mem_cons_self)
    have h1 := phys_jensen hc hp hs ht0 ht hu hd
    have h2 := ih fun c' hc' => hadm c' (List.mem_cons_of_mem _ hc')
    rw [physL_cons, physL_cons, massL_cons]
    have e : 1 / 2 * ((c.w + massL l) * Real.log d +
        (c.phys (Qf p s t u) + physL l (Qf p s t u) - (c.w + massL l) * d) / d) =
        1 / 2 * (c.w * Real.log d + (c.phys (Qf p s t u) - c.w * d) / d) +
        1 / 2 * (massL l * Real.log d + (physL l (Qf p s t u) - massL l * d) / d) := by
      field_simp; ring
    rw [e]; linarith

/-- **Jensen bin theorem** (both kernels, any odd degree). With `m` the bin mass, `D, alpha` the
normalized parameters: `int (1/2) log Q <= (m/2)(log D - sum_{k<=n} (alpha u)^k/k)`. -/
theorem bin_jensen {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht0 : 0 < t)
    (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) {n : ℕ} (hn : Odd n) (bin : List YCell)
    (hadm : ∀ c ∈ bin, CellAdm c) :
    physL bin (fun x => 1 / 2 * Real.log (Qf p s t u x)) ≤
      massL bin / 2 * (Real.log (binD bin p s) -
        ∑ k ∈ Finset.range n, (binAlpha bin p s t * u) ^ (k + 1) / ((k : ℝ) + 1)) := by
  rcases (massL_nonneg bin).lt_or_eq with hm | hm
  · have hM2 : 0 ≤ binM2 bin := physL_nonneg (fun x => sq_nonneg x) bin
    have hD : 0 < binD bin p s := by unfold binD; positivity
    have hmu : ∀ v : ℝ, |v| ≤ 1 → physL bin (Qf p s t v) / massL bin = binD bin p s * (1 - binAlpha bin p s t * v) := by
      intro v hv
      rw [physL_Q p s t v hadm]
      have : binD bin p s * binAlpha bin p s t = 2 * t * (binM1 bin / massL bin) := by
        unfold binAlpha; field_simp
      have e : binD bin p s * (1 - binAlpha bin p s t * v) = binD bin p s - (binD bin p s * binAlpha bin p s t) * v := by ring
      rw [e, this]
      simp only [binD, binM1, binM2]
      field_simp
      try ring
    have hdpos : ∀ v : ℝ, |v| ≤ 1 → 0 < binD bin p s * (1 - binAlpha bin p s t * v) := by
      intro v hv
      rw [← hmu v hv]
      exact div_pos (physL_Q_pos hp hs ht0 ht hv bin hadm hm) hm
    have h1 : 0 < 1 - binAlpha bin p s t * u := by
      have := hdpos u hu
      by_contra hc
      have hc' : 1 - binAlpha bin p s t * u ≤ 0 := not_lt.mp hc
      nlinarith
    have h2 : 0 < 1 - binAlpha bin p s t * (-u) := by
      have := hdpos (-u) (by rwa [abs_neg])
      by_contra hc
      have hc' : 1 - binAlpha bin p s t * (-u) ≤ 0 := not_lt.mp hc
      nlinarith
    have hαu : |binAlpha bin p s t * u| < 1 := by rw [abs_lt]; constructor <;> nlinarith
    set d := binD bin p s * (1 - binAlpha bin p s t * u) with hd
    have hdp : 0 < d := hdpos u hu
    have hJ := physL_jensen_aux hp hs ht0 ht hu hdp bin hadm
    have hQd : physL bin (Qf p s t u) = massL bin * d := by
      have := hmu u hu
      field_simp at this; linarith
    rw [hQd, sub_self, zero_div, add_zero] at hJ
    have hlog : Real.log d = Real.log (binD bin p s) + Real.log (1 - binAlpha bin p s t * u) := by
      rw [hd, Real.log_mul hD.ne' h1.ne']
    have hodd := log_one_sub_le_odd hn hαu
    calc _ ≤ _ := hJ
      _ = massL bin / 2 * (Real.log (binD bin p s) + Real.log (1 - binAlpha bin p s t * u)) := by rw [hlog]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  · rw [← hm, physL_zero_of_mass _ bin hm.symm]; simp

/-! ### Splitting cells into bins -/

def cellLeft (c : YCell) (m : ℝ) (h1 : c.lo < m) : YCell where
  lo := c.lo
  hi := m
  w := c.w * (m - c.lo) / (c.hi - c.lo)
  lo_lt := h1
  w_nonneg := div_nonneg (mul_nonneg c.w_nonneg (by linarith)) (by linarith [c.lo_lt])

def cellRight (c : YCell) (m : ℝ) (h2 : m < c.hi) : YCell where
  lo := m
  hi := c.hi
  w := c.w * (c.hi - m) / (c.hi - c.lo)
  lo_lt := h2
  w_nonneg := div_nonneg (mul_nonneg c.w_nonneg (by linarith)) (by linarith [c.lo_lt])

theorem phys_split (c : YCell) {m : ℝ} (h1 : c.lo < m) (h2 : m < c.hi) {f : ℝ → ℝ}
    (hf : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo c.hi) :
    c.phys f = (cellLeft c m h1).phys f + (cellRight c m h2).phys f := by
  have hlo := c.lo_lt
  have hA : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo m :=
    hf.mono_set (by rw [Set.uIcc_of_le h1.le, Set.uIcc_of_le hlo.le]; exact Icc_subset_Icc le_rfl h2.le)
  have hB : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume m c.hi :=
    hf.mono_set (by rw [Set.uIcc_of_le h2.le, Set.uIcc_of_le hlo.le]; exact Icc_subset_Icc h1.le le_rfl)
  simp only [YCell.phys, YCell.avg, cellLeft, cellRight]
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB]
  have : m - c.lo ≠ 0 := by linarith
  have : c.hi - m ≠ 0 := by linarith
  have : c.hi - c.lo ≠ 0 := by linarith
  field_simp

inductive SplitInto : YCell → List YCell → Prop
  | refl (c : YCell) : SplitInto c [c]
  | split (c : YCell) (m : ℝ) (h1 : c.lo < m) (h2 : m < c.hi) (a b : List YCell) :
      SplitInto (cellLeft c m h1) a → SplitInto (cellRight c m h2) b → SplitInto c (a ++ b)

theorem SplitInto.physL_eq {c : YCell} {sl : List YCell} (h : SplitInto c sl) (f : ℝ → ℝ)
    (hf : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo c.hi) :
    physL sl f = c.phys f := by
  induction h with
  | refl c => simp [physL_cons, physL_nil]
  | split c m h1 h2 a b _ _ iha ihb =>
    have hlo := c.lo_lt
    have hA : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo m :=
      hf.mono_set (by rw [Set.uIcc_of_le h1.le, Set.uIcc_of_le hlo.le]; exact Icc_subset_Icc le_rfl h2.le)
    have hB : IntervalIntegrable (fun Y => f (YCell.physX Y)) volume m c.hi :=
      hf.mono_set (by rw [Set.uIcc_of_le h2.le, Set.uIcc_of_le hlo.le]; exact Icc_subset_Icc h1.le le_rfl)
    have e : physL (a ++ b) f = physL a f + physL b f := by simp [physL]
    rw [e, iha hA, ihb hB, phys_split c h1 h2 hf]

theorem SplitInto.adm {c : YCell} {sl : List YCell} (h : SplitInto c sl) (hc : CellAdm c) :
    ∀ x ∈ sl, CellAdm x := by
  induction h with
  | refl c => intro x hx; simp at hx; rw [hx]; exact hc
  | split c m h1 h2 a b _ _ iha ihb =>
    have hl : CellAdm (cellLeft c m h1) := by
      rcases hc with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [cellLeft]; linarith)
    have hr : CellAdm (cellRight c m h2) := by
      rcases hc with h | h
      · exact Or.inl (by simp [cellRight]; linarith)
      · exact Or.inr h
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact iha hl x hx
    · exact ihb hr x hx

inductive Refines : List YCell → List YCell → Prop
  | nil : Refines [] []
  | cons (c : YCell) (l a sl : List YCell) :
      SplitInto c a → Refines l sl → Refines (c :: l) (a ++ sl)

theorem Refines.physL_eq {l sl : List YCell} (h : Refines l sl) (f : ℝ → ℝ)
    (hf : ∀ c ∈ l, IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo c.hi) :
    physL sl f = physL l f := by
  induction h with
  | nil => rfl
  | cons c l a sl hs _ ih =>
    have e : physL (a ++ sl) f = physL a f + physL sl f := by simp [physL]
    rw [e, hs.physL_eq f (hf c (List.mem_cons_self)),
      ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')), physL_cons]

theorem Refines.adm {l sl : List YCell} (h : Refines l sl) (hl : ∀ c ∈ l, CellAdm c) :
    ∀ x ∈ sl, CellAdm x := by
  induction h with
  | nil => simp
  | cons c l a sl hs _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hs.adm (hl c (List.mem_cons_self)) x hx
    · exact ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')) x hx

/-- `bins` is a finite binning of the cell list `l`: its cells are slices of the cells of `l`. -/
def Binning (l : List YCell) (bins : List (List YCell)) : Prop :=
  ∃ sl, Refines l sl ∧ bins.flatten.Perm sl

theorem physL_flatten (f : ℝ → ℝ) : ∀ bins : List (List YCell),
    physL bins.flatten f = (bins.map fun b => physL b f).sum := by
  intro bins
  induction bins with
  | nil => simp [physL]
  | cons b bs ih => simp [physL] at ih ⊢; rw [ih]

theorem Binning.physL_eq {l : List YCell} {bins : List (List YCell)} (h : Binning l bins)
    (f : ℝ → ℝ)
    (hf : ∀ c ∈ l, IntervalIntegrable (fun Y => f (YCell.physX Y)) volume c.lo c.hi) :
    physL l f = (bins.map fun b => physL b f).sum := by
  obtain ⟨sl, hr, hp⟩ := h
  rw [← physL_flatten, ← hr.physL_eq f hf]
  unfold physL
  exact (hp.map _).sum_eq.symm

theorem Binning.adm {l : List YCell} {bins : List (List YCell)} (h : Binning l bins)
    (hl : ∀ c ∈ l, CellAdm c) : ∀ b ∈ bins, ∀ c ∈ b, CellAdm c := by
  obtain ⟨sl, hr, hp⟩ := h
  intro b hb c hc
  exact hr.adm hl c (hp.subset (List.mem_flatten.mpr ⟨b, hb, hc⟩))

/-! ### Gas polynomial of a binned species -/

/-- Constant term `sum_b (m_b/2) log D_b` of the gas polynomial for one kernel. -/
def kernelC (bins : List (List YCell)) (p s : ℝ) : ℝ :=
  (bins.map fun b => massL b / 2 * Real.log (binD b p s)).sum

/-- Coefficient of `u^(k+1)`: `-sum_b (m_b/2) alpha_b^(k+1)/(k+1)`. -/
def kernelCoef (bins : List (List YCell)) (p s t : ℝ) (k : ℕ) : ℝ :=
  -(bins.map fun b => massL b / 2 * binAlpha b p s t ^ (k + 1) / ((k : ℝ) + 1)).sum

theorem rearr (bins : List (List YCell)) (mb Lb ab : List YCell → ℝ) (u : ℝ) (n : ℕ) :
    (bins.map fun b => mb b / 2 * (Lb b -
        ∑ k ∈ Finset.range n, (ab b * u) ^ (k + 1) / ((k : ℝ) + 1))).sum =
      (bins.map fun b => mb b / 2 * Lb b).sum +
        ∑ k ∈ Finset.range n,
          (-(bins.map fun b => mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1)).sum) * u ^ (k + 1) := by
  induction bins with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have h1 : mb b / 2 * ∑ k ∈ Finset.range n, (ab b * u) ^ (k + 1) / ((k : ℝ) + 1) =
        ∑ k ∈ Finset.range n, (mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1)) * u ^ (k + 1) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [mul_pow]; ring
    have h2 : ∑ k ∈ Finset.range n, (-(mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1) +
          (bs.map fun b => mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1)).sum)) * u ^ (k + 1) =
        -∑ k ∈ Finset.range n, (mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1)) * u ^ (k + 1) +
        ∑ k ∈ Finset.range n,
          (-(bs.map fun b => mb b / 2 * ab b ^ (k + 1) / ((k : ℝ) + 1)).sum) * u ^ (k + 1) := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [h2, mul_sub, ← h1]; ring

/-- **Gas polynomial bound** for one kernel `Q = p - 2 t u x + s x^2` on a binned cell list. -/
theorem kernel_le {l : List YCell} {bins : List (List YCell)} (hb : Binning l bins)
    (hl : ∀ c ∈ l, CellAdm c) {p s t u : ℝ} (hp : 0 < p) (hs : 0 < s) (ht0 : 0 < t)
    (ht : t ^ 2 = p * s) (hu : |u| ≤ 1) {n : ℕ} (hn : Odd n) :
    physL l (fun x => 1 / 2 * Real.log (Qf p s t u x)) ≤
      kernelC bins p s + ∑ k ∈ Finset.range n, kernelCoef bins p s t k * u ^ (k + 1) := by
  rw [hb.physL_eq _ (fun c hc =>
    (intervalIntegrable_log_Q (hl c hc) hp hs ht0 ht hu).const_mul (1 / 2))]
  have hadm := hb.adm hl
  have h := List.sum_le_sum (l := bins)
    (f := fun b => physL b (fun x => 1 / 2 * Real.log (Qf p s t u x)))
    (g := fun b => massL b / 2 * (Real.log (binD b p s) -
        ∑ k ∈ Finset.range n, (binAlpha b p s t * u) ^ (k + 1) / ((k : ℝ) + 1)))
    (fun b hbm => bin_jensen hp hs ht0 ht hu hn b (hadm b hbm))
  refine h.trans (le_of_eq ?_)
  rw [rearr bins (fun b => massL b) (fun b => Real.log (binD b p s)) (fun b => binAlpha b p s t) u n]
  rfl

/-! ### The angular field in Chebyshev form -/

section Angular
variable (S : CapSource)

/-- Constant part of the auxiliary term: `sum_e w_e (-sigma_{min(i, rad e)})`. -/
def auxConst (σ : Sign) (i : ℕ) : ℝ :=
  ((S.aux σ).map fun e => e.w * (-S.sigma (min i e.rad))).sum

/-- One auxiliary summand at degree `k` (before the `cos k theta` factor). -/
def auxFun (σ : Sign) (i k : ℕ) (e : AuxEntry) : ℝ :=
  S.coef k * ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
    (if σ = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) * Real.cos (k * e.phase)

/-- True Chebyshev coefficient (of `T_k(cos theta) = cos k theta`) of the auxiliary term. -/
def auxCoefHat (σ : Sign) (i k : ℕ) : ℝ := ((S.aux σ).map fun e => e.w * auxFun S σ i k e).sum

/-- The external term. -/
def extTerm (i : ℕ) : ℝ := (53 * S.sigma i - S.radial i / 2) / 58

/-- The two gas kernels of the angular field, as functions of the cell point `x`. -/
def dirFn (S : CapSource) (i : ℕ) (θ : ℝ) (x : ℝ) : ℝ :=
  1 / 2 * Real.log ((S.rad i) ^ 2 - 2 * S.rad i * x * Real.cos θ + x ^ 2)
def refFn (S : CapSource) (i : ℕ) (θ : ℝ) (x : ℝ) : ℝ :=
  1 / 2 * Real.log (1 - 2 * S.rad i * x * Real.cos θ + (S.rad i) ^ 2 * x ^ 2)

theorem aux_swap (l : List AuxEntry) (a : AuxEntry → ℝ) (G : AuxEntry → ℕ → ℝ) (c : ℕ → ℝ)
    (K : ℕ) :
    (l.map fun e => e.w * (a e + ∑ k ∈ Finset.range K, G e (k + 1) * c (k + 1))).sum =
      (l.map fun e => e.w * a e).sum +
        ∑ k ∈ Finset.range K, (l.map fun e => e.w * G e (k + 1)).sum * c (k + 1) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    have : ∑ k ∈ Finset.range K, ((e.w * G e (k + 1) + (l.map fun e => e.w * G e (k + 1)).sum) *
        c (k + 1)) = e.w * ∑ k ∈ Finset.range K, G e (k + 1) * c (k + 1) +
        ∑ k ∈ Finset.range K, (l.map fun e => e.w * G e (k + 1)).sum * c (k + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [this]; ring

theorem angular_finite_eq (K : ℕ) (σ : Sign) (i : ℕ) (θ : ℝ) :
    S.angular (Trunc.finite K) σ i θ =
      physL (S.gas σ) (dirFn S i θ) + (if σ = Sign.neg then physL (S.gas σ) (refFn S i θ) else 0) +
      (auxConst S σ i + ∑ k ∈ Finset.range K,
        auxCoefHat S σ i (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) +
      extTerm S i + S.auxTail (Trunc.finite K) σ := by
  have h := aux_swap (S.aux σ) (fun e => -S.sigma (min i e.rad)) (fun e k => auxFun S σ i k e)
    (fun k => Real.cos ((k : ℝ) * θ)) K
  unfold CapSource.angular Trunc.sum
  simp only [auxCoefHat, auxConst, extTerm, dirFn, refFn, auxFun] at h ⊢
  rw [h]
  rfl

theorem rad_pos (i : ℕ) : 0 < S.rad i := Real.exp_pos _

end Angular

/-! ### Exact field <= finite field: `Dominates K` for the angular component -/

section Dominance
variable (S : CapSource)

theorem q_pos : 0 < S.q := Real.exp_pos _

theorem q_lt_one (hS : S.Admissible) : S.q < 1 := by
  unfold CapSource.q
  have := hS.eps_pos
  calc Real.exp (-S.eps / 2) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem normalizer_pos (hS : S.Admissible) : 0 < S.normalizer := by
  have hq := q_pos S
  have h1 := q_lt_one S hS
  unfold CapSource.normalizer
  have : 0 < 1 - S.q ^ 2 := by nlinarith
  positivity

theorem strength_nonneg (hS : S.Admissible) : 0 ≤ S.strength := by
  have hq := q_pos S
  have h1 := q_lt_one S hS
  have hn := normalizer_pos S hS
  unfold CapSource.strength
  have : 0 < 1 - S.q ^ 2 := by nlinarith
  positivity

theorem curvature_nonneg (hS : S.Admissible) : 0 ≤ S.curvature := by
  have hn := normalizer_pos S hS
  unfold CapSource.curvature; positivity

theorem rad_le_one (hS : S.Admissible) (i : ℕ) : S.rad i ≤ 1 := by
  unfold CapSource.rad
  rw [Real.exp_le_one_iff]
  linarith [hS.sigma_nonneg i]

theorem rad_anti (hS : S.Admissible) {i j : ℕ} (h : i ≤ j) : S.rad j ≤ S.rad i := by
  unfold CapSource.rad
  rw [Real.exp_le_exp]
  linarith [hS.sigma_mono h]

/-- The summand of the auxiliary series (with the `cos k theta` factor). -/
def auxTerm (σ : Sign) (i : ℕ) (θ : ℝ) (e : AuxEntry) (k : ℕ) : ℝ :=
  S.coef k * ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
    (if σ = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) * Real.cos (k * e.phase) *
    Real.cos (k * θ)

/-- The per-unit-mass tail constant of `auxTail`. -/
def tailUnit (K : ℕ) : ℝ :=
  S.q ^ (K + 1) * ((1 / ((K : ℝ) + 1) + S.strength) * (1 / (1 - S.q)) +
    S.curvature * (((K : ℝ) + 1) * (1 / (1 - S.q)) + S.q * (1 / (1 - S.q)) ^ 2))

theorem tailUnit_nonneg (hS : S.Admissible) (K : ℕ) : 0 ≤ tailUnit S K := by
  have hq := q_pos S
  have h1 := q_lt_one S hS
  have hA := strength_nonneg S hS
  have hB := curvature_nonneg S hS
  have : 0 < 1 - S.q := by linarith
  unfold tailUnit; positivity

theorem auxTail_eq (K : ℕ) (σ : Sign) :
    S.auxTail (Trunc.finite K) σ = tailUnit S K * S.auxMass σ * (if σ = Sign.neg then 2 else 1) := by
  unfold CapSource.auxTail tailUnit; ring

theorem auxTerm_bound (hS : S.Admissible) (σ : Sign) (i : ℕ) (θ : ℝ) (e : AuxEntry)
    (K j : ℕ) :
    |auxTerm S σ i θ e (j + K + 1)| ≤
      (if σ = Sign.neg then 2 else 1) * S.q ^ (j + K + 1) *
        (1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((j : ℝ) + K + 1)) := by
  have hq := q_pos S
  have hA := strength_nonneg S hS
  have hB := curvature_nonneg S hS
  set k := j + K + 1 with hk
  have hkR : ((k : ℕ) : ℝ) = (j : ℝ) + K + 1 := by rw [hk]; push_cast; ring
  have hkpos : (0 : ℝ) < (k : ℝ) := by rw [hkR]; positivity
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hkK : (K : ℝ) + 1 ≤ (k : ℝ) := by rw [hkR]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  -- ratio bounds
  have hrmax : 0 < S.rad (max i e.rad) := rad_pos S _
  have hrmin : 0 < S.rad (min i e.rad) := rad_pos S _
  have hratio1 : S.rad (max i e.rad) / S.rad (min i e.rad) ≤ 1 :=
    (div_le_one hrmin).mpr (rad_anti S hS (min_le_max))
  have hratio0 : 0 ≤ S.rad (max i e.rad) / S.rad (min i e.rad) := by positivity
  have hm1 : S.rad i * S.rad e.rad ≤ 1 :=
    mul_le_one₀ (rad_le_one S hS i) (rad_pos S _).le (rad_le_one S hS _)
  have hm0 : 0 ≤ S.rad i * S.rad e.rad := (mul_pos (rad_pos S i) (rad_pos S _)).le
  have hsum : |(S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
      (if σ = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)| ≤
      (if σ = Sign.neg then 2 else 1) := by
    have h1 : (S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k ≤ 1 := pow_le_one₀ hratio0 hratio1
    have h0 : 0 ≤ (S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k := pow_nonneg hratio0 k
    split_ifs
    · have h2 : (S.rad i * S.rad e.rad) ^ k ≤ 1 := pow_le_one₀ hm0 hm1
      have h3 : 0 ≤ (S.rad i * S.rad e.rad) ^ k := pow_nonneg hm0 k
      rw [abs_of_nonneg (by linarith)]; linarith
    · rw [add_zero, abs_of_nonneg h0]; exact h1
  have hcoef : |S.coef k| = S.q ^ k * (1 / (k : ℝ) + S.strength + S.curvature * k) := by
    unfold CapSource.coef
    rw [abs_neg, abs_of_nonneg (by positivity)]
    field_simp
  have hcoef2 : |S.coef k| ≤ S.q ^ k * (1 / ((K : ℝ) + 1) + S.strength +
      S.curvature * ((j : ℝ) + K + 1)) := by
    rw [hcoef, hkR]
    have : 1 / ((j : ℝ) + K + 1) ≤ 1 / ((K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hK1
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold auxTerm
  rw [abs_mul, abs_mul, abs_mul]
  have hc1 := Real.abs_cos_le_one ((k : ℝ) * e.phase)
  have hc2 := Real.abs_cos_le_one ((k : ℝ) * θ)
  have hcσ : 0 ≤ (if σ = Sign.neg then (2 : ℝ) else 1) := by split_ifs <;> norm_num
  calc |S.coef k| * |_| * |Real.cos (↑k * e.phase)| * |Real.cos (↑k * θ)|
      ≤ |S.coef k| * (if σ = Sign.neg then 2 else 1) * 1 * 1 := by
        gcongr
    _ = (if σ = Sign.neg then 2 else 1) * |S.coef k| := by ring
    _ ≤ (if σ = Sign.neg then 2 else 1) * (S.q ^ k * (1 / ((K : ℝ) + 1) + S.strength +
          S.curvature * ((j : ℝ) + K + 1))) := mul_le_mul_of_nonneg_left hcoef2 hcσ
    _ = _ := by rw [hk]; ring

/-- Entry-level tail: the exact series is at most the degree-`K` sum plus the unit tail. -/
theorem entry_tsum_le (hS : S.Admissible) (σ : Sign) (i : ℕ) (θ : ℝ) (e : AuxEntry) (K : ℕ) :
    ∑' k : ℕ, auxTerm S σ i θ e (k + 1) ≤
      ∑ k ∈ Finset.range K, auxTerm S σ i θ e (k + 1) +
        tailUnit S K * (if σ = Sign.neg then 2 else 1) := by
  have hq := q_pos S
  have h1 := q_lt_one S hS
  have hqn : ‖S.q‖ < 1 := by rw [Real.norm_of_nonneg hq.le]; exact h1
  set c : ℝ := if σ = Sign.neg then 2 else 1 with hc
  set a : ℝ := 1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((K : ℝ) + 1) with ha
  -- majorant m j = c q^(K+1) (a q^j + B j q^j)
  let m : ℕ → ℝ := fun j => c * S.q ^ (K + 1) * (a * S.q ^ j + S.curvature * ((j : ℝ) * S.q ^ j))
  have hm_eq : ∀ j : ℕ, c * S.q ^ (j + K + 1) *
      (1 / ((K : ℝ) + 1) + S.strength + S.curvature * ((j : ℝ) + K + 1)) = m j := by
    intro j; simp only [m, ha]; rw [show j + K + 1 = j + (K + 1) by ring, pow_add]; ring
  have hsg : Summable (fun j : ℕ => S.q ^ j) := summable_geometric_of_lt_one hq.le h1
  have hsj : Summable (fun j : ℕ => (j : ℝ) * S.q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqn
  have hsm : Summable m := by
    simp only [m]
    exact ((hsg.mul_left a).add (hsj.mul_left S.curvature)).mul_left _
  have hbd : ∀ j : ℕ, ‖auxTerm S σ i θ e (j + K + 1)‖ ≤ m j := by
    intro j
    rw [Real.norm_eq_abs, ← hm_eq]
    exact auxTerm_bound S hS σ i θ e K j
  have hshift : Summable (fun j : ℕ => auxTerm S σ i θ e (j + K + 1)) :=
    Summable.of_norm_bounded hsm hbd
  have hG : Summable (fun j : ℕ => auxTerm S σ i θ e (j + 1)) := by
    rw [← summable_nat_add_iff K]
    convert hshift using 2
  rw [← Summable.sum_add_tsum_nat_add K hG]
  have hrem : ∑' j : ℕ, auxTerm S σ i θ e (j + K + 1) ≤ ∑' j : ℕ, m j := by
    refine Summable.tsum_le_tsum (fun j => (le_abs_self _).trans ?_) hshift hsm
    have := hbd j
    rwa [Real.norm_eq_abs] at this
  have hmv : ∑' j : ℕ, m j = tailUnit S K * c := by
    simp only [m]
    rw [tsum_mul_left, Summable.tsum_add (hsg.mul_left a) (hsj.mul_left S.curvature),
      tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq.le h1,
      tsum_coe_mul_geometric_of_norm_lt_one hqn]
    have h1q : (1 : ℝ) - S.q ≠ 0 := by linarith
    unfold tailUnit
    simp only [ha]
    field_simp
    ring
  linarith


theorem aux_list_le (hS : S.Admissible) (σ : Sign) (i : ℕ) (θ : ℝ) (K : ℕ)
    (a : AuxEntry → ℝ) : ∀ l : List AuxEntry,
    (l.map fun e => e.w * (a e + ∑' k : ℕ, auxTerm S σ i θ e (k + 1))).sum ≤
      (l.map fun e => e.w * (a e + ∑ k ∈ Finset.range K, auxTerm S σ i θ e (k + 1))).sum +
        (tailUnit S K * (if σ = Sign.neg then 2 else 1)) * (l.map fun e => e.w).sum := by
  intro l
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h := entry_tsum_le S hS σ i θ e K
    have hw := e.w_nonneg
    have := mul_le_mul_of_nonneg_left h hw
    nlinarith [this, ih]

/-- **`Dominates` for the angular component** at any degree `K`: the exact field is bounded by
the degree-`K` field with its positive geometric tail counted once. -/
theorem angular_dominates (hS : S.Admissible) (K : ℕ) :
    ∀ σ, ∀ i, i < S.nRad → ∀ θ : ℝ,
      S.angular Trunc.exact σ i θ ≤ S.angular (Trunc.finite K) σ i θ := by
  intro σ i _ θ
  have h := aux_list_le S hS σ i θ K (fun e => -S.sigma (min i e.rad)) (S.aux σ)
  have ht := auxTail_eq S K σ
  have hmass : S.auxMass σ = ((S.aux σ).map fun e => e.w).sum := rfl
  unfold CapSource.angular Trunc.sum
  simp only [CapSource.auxTail]
  have hb : (S.aux σ |>.map fun e => e.w * (-S.sigma (min i e.rad) +
      ∑ k ∈ Finset.range K, auxTerm S σ i θ e (k + 1))).sum +
      tailUnit S K * (if σ = Sign.neg then 2 else 1) * ((S.aux σ).map fun e => e.w).sum ≤
      (S.aux σ |>.map fun e => e.w * (-S.sigma (min i e.rad) +
      ∑ k ∈ Finset.range K, auxTerm S σ i θ e (k + 1))).sum + S.auxTail (Trunc.finite K) σ := by
    rw [ht, hmass]; apply le_of_eq; ring
  simp only [CapSource.auxTail] at hb
  simp only [auxTerm] at h hb
  linarith

end Dominance

end

#print axioms bin_jensen
#print axioms kernel_le
#print axioms angular_finite_eq
#print axioms angular_dominates

end CatalanMeasure.GenD.Signed.RouteI.AngularSource

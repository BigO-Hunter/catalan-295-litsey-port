module

public import CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
public import CatalanMeasure.GenD.Signed.RouteI.MomentSource
public import CatalanMeasure.GenD.Signed.RouteI.CapSourceData
public import CatalanMeasure.GenD.Signed.RouteI.CompactHf
public import CatalanMeasure.GenD.Signed.RouteI.MomentInputs
public import CatalanMeasure.GenD.Cert.WLog
public import CatalanMeasure.GenD.Signed.RouteI.AngularCap
public import CatalanMeasure.GenD.Signed.RouteI.CompactInstance
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Route I `OrdHf`: the ordinary compact fields of `capSource` lie below their polynomials

`posHf : PosHf capSource (Trunc.finite 384)` and `negHf : NegHf capSource (Trunc.finite 384)`.

The gas log potential is expanded in Chebyshev polynomials on `[0,1]`: the first 64 terms are exact,
and the tail is bounded by Bessel's inequality from a direct bound on the `L²` energy of the cell
densities. The reflection series is dropped by sign (positive species) or kept through the exact moments
(negative species). The radial field is a sum of 16 blocks, one for each radius. The polynomial part
goes exactly into the Chebyshev variable of the target; the part of degree at most 16 joins the blocks in a
one-dimensional function, bounded by a chord cover with the radii as nodes.

kcost: all `decide +kernel` of this file together measured 293 s of kernel time on 6 Nov, the largest 58 s;
heavy items are the rows (67 x 427 and 131 x 277 cell steps), the class
rows (16 x 94 cosine sums per species), and the node evaluations (62 and 63 nodes, 17 blocks of at most 96
terms each).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The Poisson majorant of the direct kernel -/

theorem lsin_le_reg {r w : ℝ} (h0 : 0 < r) (h1 : r < 1) (hs : Real.sin (w / 2) ≠ 0) :
    lsin w ≤ reg r w + (1 / 2) * Real.log (1 / r) := by
  have hA : 4 * r * Real.sin (w / 2) ^ 2 ≤ 1 - 2 * r * Real.cos w + r ^ 2 := by
    rw [reg_arg]; nlinarith [sq_nonneg (1 - r)]
  have hp : 0 < 4 * r * Real.sin (w / 2) ^ 2 := by positivity
  have hl := Real.log_le_log hp hA
  have e : Real.log (4 * r * Real.sin (w / 2) ^ 2) =
      2 * Real.log 2 + Real.log r + 2 * Real.log (Real.sin (w / 2)) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [this, Real.log_pow]; push_cast; ring
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) h0.ne',
      Real.log_pow, h4]
    push_cast; ring
  rw [e] at hl
  have h3 : Real.log (1 / r) = -Real.log r := by rw [one_div, Real.log_inv]
  unfold lsin reg
  rw [h3]
  linarith

theorem reg_tail {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (w : ℝ) (M : ℕ) :
    |-(reg r w) - ∑ n ∈ Finset.range M, r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1)|
      ≤ r ^ (M + 1) / (1 - r) := by
  have hs := (hasSum_nat_add_iff' (f := fun n : ℕ =>
    r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * w) / ((n : ℝ) + 1)) M).mpr (reg_hasSum h0 h1 w)
  have hg : HasSum (fun n : ℕ => r ^ (M + 1) * r ^ n) (r ^ (M + 1) * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one h0 h1).mul_left _
  have := hs.norm_le_of_bounded hg (fun n => ?_)
  · rw [Real.norm_eq_abs] at this
    rw [div_eq_mul_inv]; exact this
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
    have hn : (1 : ℝ) ≤ |((n + M : ℕ) : ℝ) + 1| := by
      rw [abs_of_nonneg (by positivity)]
      have : (0 : ℝ) ≤ ((n + M : ℕ) : ℝ) := by positivity
      linarith
    have hc := Real.abs_cos_le_one ((((n + M : ℕ) : ℝ) + 1) * w)
    have e : r ^ (n + M + 1) = r ^ (M + 1) * r ^ n := by ring
    rw [e]
    calc r ^ (M + 1) * r ^ n * |Real.cos ((((n + M : ℕ) : ℝ) + 1) * w)| / |((n + M : ℕ) : ℝ) + 1|
        ≤ r ^ (M + 1) * r ^ n * |Real.cos ((((n + M : ℕ) : ℝ) + 1) * w)| := by
          exact div_le_self (by positivity) hn
      _ ≤ r ^ (M + 1) * r ^ n * 1 := by gcongr
      _ = r ^ (M + 1) * r ^ n := by ring

/-- Truncated Poisson majorant of `log|x - s|` on `(0,1]`. -/
theorem kernel_le {x s r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) (hne : s ≠ x)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    Real.log |x - s| + Real.log 4 ≤ Real.log (1 / r) -
      (∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
        (basis (n + 1) (2 * s - 1) * basis (n + 1) (2 * x - 1))) + 2 * (r ^ (M + 1) / (1 - r)) := by
  set θ := Real.arccos (2 * s - 1) with hθ
  set φ := Real.arccos (2 * x - 1) with hφ
  have es : sth θ = s := sth_arccos hs0.le hs1
  have ex : sth φ = x := sth_arccos hx0.le hx1
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg _
  have hθπ : θ ≤ π := Real.arccos_le_pi _
  have hφπ : φ ≤ π := Real.arccos_le_pi _
  have hφlt : φ < π := by
    refine lt_of_le_of_ne hφπ fun h => ?_
    have := sth_arccos hx0.le hx1
    rw [← hφ, h] at this
    have h2 : sth π = 0 := by simp [sth]
    rw [h2] at this
    linarith
  have hdiff : θ ≠ φ := by
    intro h
    apply hne
    rw [← es, ← ex, h]
  have hsub : Real.sin ((θ - φ) / 2) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp h
    have hb1 : (θ - φ) / 2 < π := by nlinarith [Real.pi_pos]
    have hb2 : -π < (θ - φ) / 2 := by nlinarith [Real.pi_pos]
    rw [← hk] at hb1 hb2
    have hp := Real.pi_pos
    have k1 : (k : ℝ) < 1 := by nlinarith
    have k2 : -1 < (k : ℝ) := by nlinarith
    have : k = 0 := by
      have a1 : k < 1 := by exact_mod_cast k1
      have a2 : -1 < k := by exact_mod_cast k2
      omega
    rw [this] at hk
    apply hdiff
    simp only [Int.cast_zero, zero_mul] at hk
    linarith
  have hadd : Real.sin ((θ + φ) / 2) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · rcases hθ0.lt_or_eq with h | h
      · linarith
      · rcases hφ0.lt_or_eq with h' | h'
        · linarith
        · exact absurd (by rw [← h, ← h']) hdiff
    · linarith
  have hk := log_sub_eq_lsin hadd hsub
  rw [es, ex] at hk
  have t1 := reg_tail h0.le h1 (θ + φ) M
  have t2 := reg_tail h0.le h1 (θ - φ) M
  have l1 := lsin_le_reg h0 h1 hadd
  have l2 := lsin_le_reg h0 h1 hsub
  have hpair : ∀ n ∈ Finset.range M,
      r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ + φ)) / ((n : ℝ) + 1) +
        r ^ (n + 1) * Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1) =
      2 * r ^ (n + 1) / ((n : ℝ) + 1) *
        (basis (n + 1) (2 * s - 1) * basis (n + 1) (2 * x - 1)) := by
    intro n _
    have := cos_pair θ φ n
    have c1 : Real.cos θ = 2 * s - 1 := Real.cos_arccos (by linarith) (by linarith)
    have c2 : Real.cos φ = 2 * x - 1 := Real.cos_arccos (by linarith) (by linarith)
    rw [c1, c2] at this
    calc _ = r ^ (n + 1) * (Real.cos (((n : ℝ) + 1) * (θ + φ)) / ((n : ℝ) + 1) +
          Real.cos (((n : ℝ) + 1) * (θ - φ)) / ((n : ℝ) + 1)) := by ring
      _ = _ := by rw [this]; ring
  have hsum := Finset.sum_congr rfl hpair
  rw [Finset.sum_add_distrib] at hsum
  have u1 := (abs_le.mp t1).2
  have u2 := (abs_le.mp t2).2
  have u1' := (abs_le.mp t1).1
  have u2' := (abs_le.mp t2).1
  have h3 : Real.log (1 / r) = (1 / 2) * Real.log (1 / r) + (1 / 2) * Real.log (1 / r) := by ring
  linarith

/-! ### Integrating the majorant -/

/-- `n`-th Chebyshev moment of a cell in the physical variable. -/
def TF (n : ℕ) : ℝ → ℝ := fun s => basis n (2 * s - 1)

theorem phys_log_le {c : YCell} (h2 : 2 ≤ c.lo) {x r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    c.phys (fun s => Real.log |x - s|) + c.w * Real.log 4 ≤
      c.w * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) -
      ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        c.phys (TF (n + 1)) := by
  have hlt := c.lo_lt
  have hd : 0 < c.hi - c.lo := by linarith
  set g := c.w / (c.hi - c.lo) with hg
  have hg0 : 0 ≤ g := div_nonneg c.w_nonneg hd.le
  set A : ℝ := Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r)) - Real.log 4 with hA
  set a : ℕ → ℝ := fun n => 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) with ha
  have hi1 := rowlog2_int h2 hlt hx0 hx1
  have hi2 : ∀ n ∈ Finset.range M, IntervalIntegrable
      (fun y => a n * basis (n + 1) (2 * YCell.physX y - 1)) volume c.lo c.hi :=
    fun n _ => (basisX_int h2 hlt (n + 1)).const_mul _
  have hi3 : IntervalIntegrable
      (fun y => ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1)) volume c.lo c.hi :=
    (IntervalIntegrable.sum (Finset.range M) hi2).congr (by
      intro y _
      simp [Finset.sum_apply])
  have hi4 : IntervalIntegrable
      (fun y => A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1))
      volume c.lo c.hi := intervalIntegrable_const.sub hi3
  have hle : ∫ y in c.lo..c.hi, Real.log |x - YCell.physX y| ≤
      ∫ y in c.lo..c.hi, (A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1)) := by
    apply intervalIntegral.integral_mono_ae_restrict hlt.le hi1 hi4
    have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∉ ({x + 1 / x} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem volume
    have hm := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := c.lo) (b := c.hi))
    filter_upwards [ae_restrict_of_ae (s := Icc c.lo c.hi) hae, hm] with Y hY hYm
    have hY2 : 2 ≤ Y := h2.trans hYm.1
    obtain ⟨p0, p1⟩ := physX_mem hY2
    have hne : YCell.physX Y ≠ x := by
      intro he
      apply hY
      have := physX_add_inv hY2
      rw [he] at this
      exact Set.mem_singleton_iff.mpr this.symm
    have := kernel_le hx0 hx1 p0 p1 hne h0 h1 M
    have e : ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
          (basis (n + 1) (2 * YCell.physX Y - 1) * basis (n + 1) (2 * x - 1)) =
        ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX Y - 1) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [ha]; ring
    rw [e] at this
    simp only [hA]
    linarith
  have hev : ∫ y in c.lo..c.hi, (A - ∑ n ∈ Finset.range M, a n * basis (n + 1) (2 * YCell.physX y - 1))
      = A * (c.hi - c.lo) - ∑ n ∈ Finset.range M, a n * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi3, intervalIntegral.integral_const,
      intervalIntegral.integral_finsetSum hi2]
    simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
    ring
  have hw : c.w = g * (c.hi - c.lo) := by rw [hg]; field_simp
  have hph : ∀ n, c.phys (TF n) = g * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) := fun n => rfl
  have hl : c.phys (fun s => Real.log |x - s|) = g * ∫ y in c.lo..c.hi, Real.log |x - YCell.physX y| := rfl
  rw [hev] at hle
  have := mul_le_mul_of_nonneg_left hle hg0
  rw [hl]
  simp only [hph]
  have e2 : ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        (g * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1)) =
      g * ∑ n ∈ Finset.range M, a n * ∫ y in c.lo..c.hi, basis (n + 1) (2 * YCell.physX y - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha]; ring
  rw [e2]
  have e3 : c.w * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) = g * (c.hi - c.lo) * (A + Real.log 4) := by
    rw [← hw]; simp only [hA]; ring
  rw [e3, hw]
  nlinarith [this]

theorem physL_log_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h0 : 0 < r) (h1 : r < 1) (M : ℕ) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 ≤
      massL l * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) -
      ∑ n ∈ Finset.range M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    have a1 := phys_log_le (h2 c (by simp)) hx0 hx1 h0 h1 M
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    simp only [e1, e2, mul_add, Finset.sum_add_distrib, add_mul]
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### Cauchy-Schwarz tail and the limits -/

theorem sum_inv_sq_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.lt_or_ge M N with h | h
  · rw [Finset.Ico_eq_empty (by omega)]; simp
  have key : ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
    induction M, h using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM]
      have hM0 : (0 : ℝ) < M := lt_of_lt_of_le hN0 (by exact_mod_cast hM)
      have : (1 / ((M : ℝ) + 1)) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ hM0.ne' (by positivity), div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  linarith

theorem tail_cs {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (mu b : ℕ → ℝ) (hb : ∀ n, |b n| ≤ 1) {B T : ℝ}
    (hB : ∑ n ∈ Finset.Ico N M, (mu n) ^ 2 ≤ B) (hT : 0 ≤ T) (hBT : 4 * B ≤ (N : ℝ) * T ^ 2) :
    |∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n| ≤ T := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Ico N M) (fun n : ℕ => 1 / ((n : ℝ) + 1))
    (fun n => 2 * b n * mu n)
  have e1 : ∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1) * (2 * b n * mu n) =
      ∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [e1] at hcs
  have e2 : ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 ≤ 4 * B := by
    calc ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 ≤ ∑ n ∈ Finset.Ico N M, 4 * (mu n) ^ 2 := by
          refine Finset.sum_le_sum fun n _ => ?_
          have : (b n) ^ 2 ≤ 1 := by
            have := hb n
            rw [← sq_abs]
            nlinarith [abs_nonneg (b n)]
          nlinarith [sq_nonneg (mu n)]
      _ = 4 * ∑ n ∈ Finset.Ico N M, (mu n) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 4 * B := by linarith
  have e3 := sum_inv_sq_le hN M
  have hpos : 0 ≤ ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hpos1 : 0 ≤ ∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB0 : 0 ≤ 4 * B := hpos.trans e2
  have e4 : (∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * b n * mu n) ^ 2 ≤ T ^ 2 := by
    calc _ ≤ (∑ n ∈ Finset.Ico N M, (1 / ((n : ℝ) + 1)) ^ 2) *
          ∑ n ∈ Finset.Ico N M, (2 * b n * mu n) ^ 2 := hcs
      _ ≤ (1 / (N : ℝ)) * (4 * B) := mul_le_mul e3 e2 hpos (by positivity)
      _ ≤ T ^ 2 := by
        rw [one_div, inv_mul_le_iff₀ hN0]; exact hBT
  exact abs_le_of_sq_le_sq e4 hT

/-- **Gas direct term.** The truncated Chebyshev upper bound of the direct potential, the tail
being controlled by any `L²` bound `B` of the moment tail. -/
theorem gas_upper {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {B T : ℝ}
    (hB : ∀ M, ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ B) (hT : 0 ≤ T)
    (hBT : 4 * B ≤ (N : ℝ) * T ^ 2) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 ≤
      T - ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
  set m := massL l
  set LHS := physL l (fun s => Real.log |x - s|) + m * Real.log 4 with hLHS
  have hz : 2 * x - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have step : ∀ r : ℝ, 0 < r → r < 1 → LHS ≤ m * Real.log (1 / r) + T -
      ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) := by
    intro r h0 h1
    set Sg := ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1)) with hSg
    have ht : Tendsto (fun M : ℕ => m * (Real.log (1 / r) + 2 * (r ^ (M + 1) / (1 - r))) + T - Sg)
        atTop (𝓝 (m * (Real.log (1 / r) + 2 * (0 / (1 - r))) + T - Sg)) := by
      have p := (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
      exact ((((p.div_const (1 - r)).const_mul 2).const_add _).const_mul m |>.add_const T).sub_const Sg
    have ht' : m * (Real.log (1 / r) + 2 * (0 / (1 - r))) + T - Sg = m * Real.log (1 / r) + T - Sg := by
      simp
    rw [ht'] at ht
    refine ge_of_tendsto ht ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    have a1 := physL_log_le h2 hx0 hx1 h0 h1 M
    have a2 := Finset.sum_range_add_sum_Ico (fun n : ℕ => 2 * r ^ (n + 1) / ((n : ℝ) + 1) *
      basis (n + 1) (2 * x - 1) * physL l (TF (n + 1))) hM
    have a3 := tail_cs hN M (fun n => physL l (TF (n + 1)))
      (fun n => r ^ (n + 1) * basis (n + 1) (2 * x - 1)) (fun n => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg h0.le _)]
        have q1 := abs_basis_le_one (n + 1) hz
        have q2 : r ^ (n + 1) ≤ 1 := pow_le_one₀ h0.le h1.le
        have q3 := abs_nonneg (basis (n + 1) (2 * x - 1))
        have q4 : 0 ≤ r ^ (n + 1) := pow_nonneg h0.le _
        nlinarith) (hB M) hT hBT
    have e : ∑ n ∈ Finset.Ico N M, 2 / ((n : ℝ) + 1) * (r ^ (n + 1) * basis (n + 1) (2 * x - 1)) *
          physL l (TF (n + 1)) =
        ∑ n ∈ Finset.Ico N M, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
          physL l (TF (n + 1)) := Finset.sum_congr rfl fun n _ => by ring
    rw [e] at a3
    have a4 := (abs_le.mp a3).1
    simp only [← hSg] at a2
    simp only [hLHS]
    linarith
  set Q := ∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
      physL l (TF (n + 1)) with hQ
  have hc : ContinuousAt (fun r : ℝ => m * Real.log (1 / r) + T -
      ∑ n ∈ Finset.range N, 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1))) 1 := by
    have h1 : ContinuousAt (fun r : ℝ => Real.log (1 / r)) 1 :=
      ContinuousAt.log (continuousAt_const.div continuousAt_id (by norm_num)) (by norm_num)
    refine ((h1.const_mul m).add continuousAt_const).sub ?_
    refine tendsto_finsetSum _ fun n _ => ?_
    have : ContinuousAt (fun r : ℝ => 2 * r ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
      physL l (TF (n + 1))) 1 := by fun_prop
    exact this
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  have ev : (m * Real.log (1 / (1 : ℝ)) + T -
      ∑ n ∈ Finset.range N, 2 * (1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) *
        physL l (TF (n + 1))) = T - Q := by
    simp [hQ]
  rw [ev] at ht
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with r hr
  exact step r hr.1 hr.2

/-! ### Orthogonality of cosines on `[0,π]` -/

theorem int_cos_int {k : ℤ} (hk : k ≠ 0) : ∫ θ in (0 : ℝ)..π, Real.cos ((k : ℝ) * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hk', integral_cos]
  simp [Real.sin_int_mul_pi]

theorem cos_mul_cos (m n : ℕ) (θ : ℝ) : Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) =
    (Real.cos ((((m : ℤ) - n : ℤ) : ℝ) * θ) + Real.cos ((((m : ℤ) + n : ℤ) : ℝ) * θ)) / 2 := by
  push_cast
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
  ring

theorem cos_int_continuous (k : ℤ) : Continuous fun θ : ℝ => Real.cos ((k : ℝ) * θ) := by fun_prop

theorem int_cos_cos {m n : ℕ} (h : m ≠ n) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((m : ℝ) * θ) * Real.cos ((n : ℝ) * θ) = 0 := by
  simp only [cos_mul_cos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((cos_int_continuous _).intervalIntegrable _ _) ((cos_int_continuous _).intervalIntegrable _ _),
    int_cos_int (by omega), int_cos_int (by omega)]
  simp

theorem int_cos_sq {n : ℕ} (h : n ≠ 0) :
    ∫ θ in (0 : ℝ)..π, Real.cos ((n : ℝ) * θ) * Real.cos ((n : ℝ) * θ) = π / 2 := by
  simp only [cos_mul_cos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    ((cos_int_continuous _).intervalIntegrable _ _) ((cos_int_continuous _).intervalIntegrable _ _),
    int_cos_int (k := (n : ℤ) + n) (by omega)]
  simp

/-- The cosine polynomial. -/
def cosS (b : ℕ → ℝ) (M : ℕ) (θ : ℝ) : ℝ := ∑ n ∈ Finset.range M, b n * Real.cos ((n : ℝ) * θ)

theorem cosS_continuous (b : ℕ → ℝ) (M : ℕ) : Continuous (cosS b M) := by
  unfold cosS; fun_prop

theorem int_cosS_mul (b : ℕ → ℝ) {M k : ℕ} (hk : M ≤ k) :
    ∫ θ in (0 : ℝ)..π, cosS b M θ * Real.cos ((k : ℝ) * θ) = 0 := by
  unfold cosS
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum (fun n _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  refine Finset.sum_eq_zero fun n hn => ?_
  simp only [mul_assoc]
  rw [intervalIntegral.integral_const_mul, int_cos_cos (by have := Finset.mem_range.mp hn; omega)]
  simp

theorem int_cosS_sq (b : ℕ → ℝ) (M : ℕ) :
    ∫ θ in (0 : ℝ)..π, (cosS b (M + 1) θ) ^ 2 =
      π * (b 0) ^ 2 + (π / 2) * ∑ n ∈ Finset.range M, (b (n + 1)) ^ 2 := by
  induction M with
  | zero => simp [cosS]
  | succ M ih =>
    have e : ∀ θ, (cosS b (M + 1 + 1) θ) ^ 2 = (cosS b (M + 1) θ) ^ 2 +
        2 * b (M + 1) * (cosS b (M + 1) θ * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) +
        (b (M + 1)) ^ 2 * (Real.cos (((M + 1 : ℕ) : ℝ) * θ) * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) := by
      intro θ
      have : cosS b (M + 1 + 1) θ = cosS b (M + 1) θ + b (M + 1) * Real.cos (((M + 1 : ℕ) : ℝ) * θ) := by
        unfold cosS; rw [Finset.sum_range_succ _ (M + 1)]
      rw [this]; ring
    simp only [e]
    have c1 := cosS_continuous b (M + 1)
    rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ih,
      int_cosS_mul b le_rfl, int_cos_sq (by omega), Finset.sum_range_succ]
    ring

/-! ### Bessel on the disjoint cells -/

/-- Density of a cell. -/
def gc (c : YCell) : ℝ := c.w / (c.hi - c.lo)

/-- `∫ h² dθ` of the physical density `h = g_c bet`. -/
def G2 (l : List YCell) : ℝ :=
  (l.map fun c => gc c ^ 2 * ∫ θ in Th c.lo..Th c.hi, bet θ ^ 2).sum

/-- Sorted disjoint cells above `a`. -/
def Sep : ℝ → List YCell → Prop
  | _, [] => True
  | a, c :: l => a ≤ c.lo ∧ Sep c.hi l

theorem bet_continuousOn {a b : ℝ} (h0 : 0 ≤ a) (h1 : b < π) : ContinuousOn bet (Icc a b) := by
  unfold bet
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.sub (ContinuousOn.div (by fun_prop) (by fun_prop) ?_)
    (by fun_prop))
  intro θ hθ
  have := cos_half_pos (h0.trans hθ.1) (lt_of_le_of_lt hθ.2 h1)
  positivity

theorem cross {c : YCell} (h2 : 2 ≤ c.lo) (b : ℕ → ℝ) (M : ℕ) :
    ∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ =
      ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) := by
  have hlt := c.lo_lt
  have hs := subst_Y h2 hlt (fun y => ∑ n ∈ Finset.range M, b n * basis n (2 * YCell.physX y - 1))
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hab := Th_lt h2 hlt
  have hc : ∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ = ∫ θ in Th c.lo..Th c.hi, bet θ *
      ∑ n ∈ Finset.range M, b n * basis n (2 * YCell.physX (Yth θ) - 1) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hab.le] at hθ
    have h0 : 0 ≤ θ := ml.1.trans hθ.1
    have h1 : θ < π := lt_of_le_of_lt hθ.2 mh.2
    simp only [cosS]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [physX_Yth h0 h1, two_sth_sub, basis_cos]
  rw [hc, ← hs, intervalIntegral.integral_finsetSum
    (fun n _ => (basisX_int h2 hlt n).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

theorem cell_bessel {c : YCell} (h2 : 2 ≤ c.lo) (b : ℕ → ℝ) (M : ℕ) :
    2 * ∑ n ∈ Finset.range M, b n * c.phys (TF n) ≤
      gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) +
        ∫ θ in Th c.lo..Th c.hi, (cosS b M θ) ^ 2 := by
  have hlt := c.lo_lt
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hab := Th_lt h2 hlt
  have hbc : ContinuousOn bet (uIcc (Th c.lo) (Th c.hi)) := by
    rw [uIcc_of_le hab.le]; exact bet_continuousOn ml.1 mh.2
  have hSc := cosS_continuous b M
  have i1 : IntervalIntegrable (fun θ => gc c ^ 2 * bet θ ^ 2) volume (Th c.lo) (Th c.hi) :=
    (continuousOn_const.mul (hbc.pow 2)).intervalIntegrable
  have i1' : IntervalIntegrable (fun θ => bet θ ^ 2) volume (Th c.lo) (Th c.hi) :=
    (hbc.pow 2).intervalIntegrable
  have i2 : IntervalIntegrable (fun θ => 2 * gc c * (bet θ * cosS b M θ)) volume (Th c.lo) (Th c.hi) :=
    (continuousOn_const.mul (hbc.mul hSc.continuousOn)).intervalIntegrable
  have i2' : IntervalIntegrable (fun θ => bet θ * cosS b M θ) volume (Th c.lo) (Th c.hi) :=
    (hbc.mul hSc.continuousOn).intervalIntegrable
  have i3 : IntervalIntegrable (fun θ => (cosS b M θ) ^ 2) volume (Th c.lo) (Th c.hi) :=
    (hSc.pow 2).intervalIntegrable _ _
  have hnn : 0 ≤ ∫ θ in Th c.lo..Th c.hi, (gc c * bet θ - cosS b M θ) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun θ _ => sq_nonneg _
  have e : ∫ θ in Th c.lo..Th c.hi, (gc c * bet θ - cosS b M θ) ^ 2 =
      gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) -
        2 * gc c * (∫ θ in Th c.lo..Th c.hi, bet θ * cosS b M θ) +
        ∫ θ in Th c.lo..Th c.hi, (cosS b M θ) ^ 2 := by
    have : ∀ θ, (gc c * bet θ - cosS b M θ) ^ 2 = gc c ^ 2 * bet θ ^ 2 -
        2 * gc c * (bet θ * cosS b M θ) + (cosS b M θ) ^ 2 := fun θ => by ring
    simp only [this]
    rw [intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [e, cross h2] at hnn
  have e2 : gc c * ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) =
      ∑ n ∈ Finset.range M, b n * c.phys (TF n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    show _ = b n * (gc c * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1))
    ring
  have e3 : 2 * gc c * ∑ n ∈ Finset.range M, b n * ∫ y in c.lo..c.hi, basis n (2 * YCell.physX y - 1) =
      2 * ∑ n ∈ Finset.range M, b n * c.phys (TF n) := by rw [← e2]; ring
  rw [e3] at hnn
  linarith

theorem Th_le {a b : ℝ} (h2 : 2 ≤ a) (hab : a ≤ b) : Th a ≤ Th b := by
  rcases hab.lt_or_eq with h | rfl
  · exact (Th_lt h2 h).le
  · exact le_rfl

theorem bessel_list {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) (b : ℕ → ℝ) (M : ℕ) :
    2 * ∑ n ∈ Finset.range M, b n * physL l (TF n) ≤
      G2 l + ∫ θ in Th a..π, (cosS b M θ) ^ 2 := by
  have hSc := (cosS_continuous b M).pow 2
  induction l generalizing a with
  | nil =>
    simp only [physL, G2, List.map_nil, List.sum_nil, mul_zero, Finset.sum_const_zero, zero_add]
    exact intervalIntegral.integral_nonneg (Th_mem ha).2.le fun θ _ => sq_nonneg _
  | cons c l ih =>
    obtain ⟨h1, h3⟩ := hs
    have hc2 : 2 ≤ c.lo := ha.trans h1
    have hh2 : 2 ≤ c.hi := hc2.trans c.lo_lt.le
    have A := cell_bessel hc2 b M
    have Bq := ih hh2 h3
    have e1 : ∀ n, physL (c :: l) (TF n) = c.phys (TF n) + physL l (TF n) := fun n => by
      simp [physL]
    have e2 : G2 (c :: l) = gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) + G2 l := by
      simp [G2]
    have i := fun u v => hSc.intervalIntegrable (μ := volume) u v
    have s1 := intervalIntegral.integral_add_adjacent_intervals (i (Th c.lo) (Th c.hi)) (i (Th c.hi) π)
    have s2 := intervalIntegral.integral_add_adjacent_intervals (i (Th a) (Th c.lo)) (i (Th c.lo) π)
    have s3 : 0 ≤ ∫ θ in Th a..Th c.lo, (cosS b M θ) ^ 2 :=
      intervalIntegral.integral_nonneg (Th_le ha h1) fun θ _ => sq_nonneg _
    simp only [e1, mul_add, Finset.sum_add_distrib, e2]
    simp only [Pi.pow_apply] at s1 s2
    linarith

/-- **Bessel inequality** for the physical density on sorted disjoint cells. -/
theorem bessel {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) (M : ℕ) :
    (physL l (TF 0)) ^ 2 / 2 + ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 ≤ π / 2 * G2 l := by
  set b : ℕ → ℝ := fun n => if n = 0 then physL l (TF 0) / π else 2 * physL l (TF n) / π with hb
  have hp := Real.pi_pos
  have A := bessel_list ha hs b (M + 1)
  have hSc := (cosS_continuous b (M + 1)).pow 2
  have i := fun u v => hSc.intervalIntegrable (μ := volume) u v
  have s1 := intervalIntegral.integral_add_adjacent_intervals (i 0 (Th a)) (i (Th a) π)
  have s3 : 0 ≤ ∫ θ in (0 : ℝ)..Th a, (cosS b (M + 1) θ) ^ 2 :=
    intervalIntegral.integral_nonneg (Th_mem ha).1 fun θ _ => sq_nonneg _
  simp only [Pi.pow_apply] at s1
  rw [int_cosS_sq] at s1
  have e0 : b 0 = physL l (TF 0) / π := by simp [hb]
  have e1 : ∀ n, b (n + 1) = 2 * physL l (TF (n + 1)) / π := fun n => by simp [hb]
  rw [Finset.sum_range_succ'] at A
  simp only [e0, e1] at A s1
  have q1 : ∑ n ∈ Finset.range M, (2 * physL l (TF (n + 1)) / π) * physL l (TF (n + 1)) =
      2 / π * ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  have q2 : ∑ n ∈ Finset.range M, (2 * physL l (TF (n + 1)) / π) ^ 2 =
      4 / π ^ 2 * ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [q1] at A
  rw [q2] at s1
  set Q := ∑ n ∈ Finset.range M, (physL l (TF (n + 1))) ^ 2
  set m0 := physL l (TF 0)
  have key : 2 * (2 / π * Q + m0 / π * m0) ≤ G2 l + (π * (m0 / π) ^ 2 + π / 2 * (4 / π ^ 2 * Q)) := by
    linarith
  have r1 : π * (m0 / π) ^ 2 = m0 ^ 2 / π := by field_simp
  have r2 : π / 2 * (4 / π ^ 2 * Q) = 2 / π * Q := by field_simp; ring
  rw [r1, r2] at key
  have r3 : m0 ^ 2 / π + 2 / π * Q ≤ G2 l := by
    have : 2 * (2 / π * Q + m0 / π * m0) = 2 * (2 / π * Q) + 2 * (m0 ^ 2 / π) := by ring
    linarith
  have r4 := mul_le_mul_of_nonneg_left r3 (by positivity : (0 : ℝ) ≤ π / 2)
  have r5 : π / 2 * (m0 ^ 2 / π + 2 / π * Q) = m0 ^ 2 / 2 + Q := by field_simp
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-! ### The `L²` norm of the density on one cell, without roots -/

/-- `W²`, the square of `bet` in the `Y` coordinate. -/
def Wsq (y : ℝ) : ℝ := (y ^ 2 - 4) * (1 / YCell.physX y - 1)

theorem Th_Yth {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < π) : Th (Yth θ) = θ := by
  unfold Th
  rw [physX_Yth h0 h1, two_sth_sub, Real.arccos_cos h0 h1.le]

theorem bet_Th_sq {y : ℝ} (h2 : 2 ≤ y) : bet (Th y) ^ 2 = Wsq y := by
  obtain ⟨p0, p1⟩ := physX_mem h2
  obtain ⟨t0, t1⟩ := Th_mem h2
  rw [bet_eq_bb t0 t1, sth_Th h2]
  unfold Wsq
  have hy := physX_add_inv h2
  set x := YCell.physX y
  have hq : 0 ≤ (1 - x) / x := div_nonneg (by linarith) p0.le
  have hs := Real.sq_sqrt hq
  unfold bb
  rw [mul_pow, mul_pow, hs, ← hy]
  field_simp
  ring

theorem Wsq_eq {y : ℝ} (h2 : 2 ≤ y) :
    Wsq y = (y ^ 2 - 4) * (y - 2) / 2 + (y ^ 2 - 4) ^ (3 / 2 : ℝ) / 2 := by
  have ht : 0 ≤ y ^ 2 - 4 := by nlinarith
  have hx : 1 / YCell.physX y = (y + √(y ^ 2 - 4)) / 2 := by
    unfold YCell.physX
    rw [_root_.if_pos (by linarith)]
    have : 0 < y + √(y ^ 2 - 4) := by have := Real.sqrt_nonneg (y ^ 2 - 4); linarith
    field_simp
  have hr : (y ^ 2 - 4) ^ (3 / 2 : ℝ) = (y ^ 2 - 4) * √(y ^ 2 - 4) := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' ht (by norm_num), Real.rpow_one]
  unfold Wsq
  rw [hx, hr]
  ring

theorem Wsq_convex : ConvexOn ℝ (Ici 2) Wsq := by
  have c1 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => (y ^ 2 - 4) * (y - 2) / 2 := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 2)
      (f' := fun y => (3 * y ^ 2 - 4 * y - 4) / 2) (f'' := fun y => 3 * y - 2) (by fun_prop) ?_ ?_ ?_
    · intro y _
      have : HasDerivAt (fun y : ℝ => (y ^ 2 - 4) * (y - 2) / 2) ((3 * y ^ 2 - 4 * y - 4) / 2) y := by
        have h := (((hasDerivAt_pow 2 y).sub_const 4).mul ((hasDerivAt_id y).sub_const 2)).div_const 2
        refine h.congr_deriv ?_
        try simp only [id]
        push_cast; ring
      exact this.hasDerivWithinAt
    · intro y _
      have : HasDerivAt (fun y : ℝ => (3 * y ^ 2 - 4 * y - 4) / 2) (3 * y - 2) y := by
        have h := ((((hasDerivAt_pow 2 y).const_mul 3).sub ((hasDerivAt_id y).const_mul 4)).sub_const 4).div_const 2
        refine h.congr_deriv ?_
        try simp only [id]
        push_cast; ring
      exact this.hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have : (2 : ℝ) < y := hy
      show 0 ≤ 3 * y - 2
      linarith
  have c2 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => y ^ 2 - 4 := by
    have h := (convexOn_pow (𝕜 := ℝ) 2).subset
      (show Ici (2 : ℝ) ⊆ Ici 0 from fun y (hy : (2 : ℝ) ≤ y) => show (0 : ℝ) ≤ y by linarith) (convex_Ici 2)
    exact (h.add_const (-4)).congr (fun y _ => by show y ^ 2 + (-4) = y ^ 2 - 4; ring)
  have c3 : ConvexOn ℝ (Ici (2 : ℝ)) fun y : ℝ => (y ^ 2 - 4) ^ (3 / 2 : ℝ) := by
    have himg : (fun y : ℝ => y ^ 2 - 4) '' Ici 2 ⊆ Ici 0 := by
      rintro _ ⟨y, hy, rfl⟩
      have : (2 : ℝ) ≤ y := hy
      show 0 ≤ y ^ 2 - 4
      nlinarith
    have hconv : Convex ℝ ((fun y : ℝ => y ^ 2 - 4) '' Ici 2) := by
      have : (fun y : ℝ => y ^ 2 - 4) '' Ici 2 = Ici 0 := by
        refine Subset.antisymm himg ?_
        intro t ht
        have ht' : (0 : ℝ) ≤ t := ht
        refine ⟨√(t + 4), ?_, ?_⟩
        · show (2 : ℝ) ≤ √(t + 4)
          apply Real.le_sqrt_of_sq_le
          linarith
        · show √(t + 4) ^ 2 - 4 = t
          rw [Real.sq_sqrt (by linarith)]; ring
      rw [this]; exact convex_Ici 0
    have g := ((convexOn_rpow (p := 3 / 2) (by norm_num)).subset himg hconv)
    refine g.comp c2 ?_
    intro a ha b hb hab
    exact Real.rpow_le_rpow (himg ha) hab (by norm_num)
  have c4 := (c1.add (c3.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)))
  refine c4.congr ?_
  intro y hy
  have : (2 : ℝ) ≤ y := hy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Wsq_eq this]
  ring

theorem Th_continuousOn {lo hi : ℝ} (h2 : 2 ≤ lo) : ContinuousOn Th (Icc lo hi) := by
  have hc := physX_continuousOn (lo := lo) (hi := hi) (Or.inl h2)
  unfold Th
  exact Real.continuous_arccos.comp_continuousOn ((continuousOn_const.mul hc).sub continuousOn_const)

theorem int_bet_sq {lo hi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) :
    ∫ θ in Th lo..Th hi, bet θ ^ 2 = ∫ y in lo..hi, bet (Th y) := by
  rw [subst_Y h2 hlt (fun y => bet (Th y))]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  rw [uIcc_of_le (Th_lt h2 hlt).le] at hθ
  simp only
  rw [Th_Yth (ml.1.trans hθ.1) (lt_of_le_of_lt hθ.2 mh.2)]
  ring

/-- The cell `L²` integral by AM-GM against any `lam > 0` and the chord of the convex `W²`. -/
theorem cell_bet_sq {lo hi lam Vlo Vhi : ℝ} (h2 : 2 ≤ lo) (hlt : lo < hi) (hl : 0 < lam)
    (h1 : Wsq lo ≤ Vlo) (h3 : Wsq hi ≤ Vhi) :
    ∫ θ in Th lo..Th hi, bet θ ^ 2 ≤ (hi - lo) * (lam / 2 + (Vlo + Vhi) / (4 * lam)) := by
  rw [int_bet_sq h2 hlt]
  have hd : 0 < hi - lo := by linarith
  have ml := Th_mem h2
  have mh := Th_mem (h2.trans hlt.le)
  have hW : ContinuousOn (fun y => bet (Th y)) (Icc lo hi) := by
    refine (bet_continuousOn ml.1 mh.2).comp (Th_continuousOn h2) ?_
    intro y hy
    exact ⟨Th_le h2 hy.1, Th_le (h2.trans hy.1) hy.2⟩
  set A : ℝ → ℝ := fun y => lam / 2 + (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) / (2 * lam) with hA
  have hAc : Continuous A := by simp only [hA]; fun_prop
  have hle : ∫ y in lo..hi, bet (Th y) ≤ ∫ y in lo..hi, A y := by
    apply intervalIntegral.integral_mono_on hlt.le (hW.intervalIntegrable_of_Icc hlt.le)
      (hAc.intervalIntegrable _ _)
    intro y hy
    have hy2 : 2 ≤ y := h2.trans hy.1
    have hsq := bet_Th_sq hy2
    have hch : Wsq y ≤ (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) := by
      have a0 : 0 ≤ (hi - y) / (hi - lo) := div_nonneg (by linarith [hy.2]) hd.le
      have b0 : 0 ≤ (y - lo) / (hi - lo) := div_nonneg (by linarith [hy.1]) hd.le
      have ab : (hi - y) / (hi - lo) + (y - lo) / (hi - lo) = 1 := by field_simp; ring
      have := Wsq_convex.2 (show lo ∈ Ici (2 : ℝ) from h2) (show hi ∈ Ici (2 : ℝ) from h2.trans hlt.le)
        a0 b0 ab
      have e : ((hi - y) / (hi - lo)) • lo + ((y - lo) / (hi - lo)) • hi = y := by
        simp only [smul_eq_mul]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']
        ring
      rw [e] at this
      simp only [smul_eq_mul] at this
      have q1 := mul_le_mul_of_nonneg_left h1 a0
      have q2 := mul_le_mul_of_nonneg_left h3 b0
      calc Wsq y ≤ _ := this
        _ ≤ (hi - y) / (hi - lo) * Vlo + (y - lo) / (hi - lo) * Vhi := by linarith
        _ = _ := by field_simp
    have amgm : bet (Th y) ≤ lam / 2 + Wsq y / (2 * lam) := by
      rw [← hsq]
      have : lam / 2 + bet (Th y) ^ 2 / (2 * lam) - bet (Th y) = (bet (Th y) - lam) ^ 2 / (2 * lam) := by
        field_simp; ring
      have h4 : 0 ≤ (bet (Th y) - lam) ^ 2 / (2 * lam) := by positivity
      linarith
    have : Wsq y / (2 * lam) ≤ (Vlo * (hi - y) + Vhi * (y - lo)) / (hi - lo) / (2 * lam) := by
      gcongr
    simp only [hA]
    linarith
  refine hle.trans (le_of_eq ?_)
  have hpr : ∀ y ∈ uIcc lo hi, HasDerivAt
      (fun y => lam / 2 * y + (Vlo * (hi * y - y ^ 2 / 2) + Vhi * (y ^ 2 / 2 - lo * y)) / (hi - lo) / (2 * lam))
      (A y) y := by
    intro y _
    have d2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
      have := (hasDerivAt_pow 2 y).div_const 2
      refine this.congr_deriv ?_
      push_cast; ring
    have d1 := hasDerivAt_id y
    have h := ((d1.const_mul (lam / 2)).add
      (((((d1.const_mul hi).sub d2).const_mul Vlo).add
        ((d2.sub (d1.const_mul lo)).const_mul Vhi)).div_const (hi - lo) |>.div_const (2 * lam)))
    refine h.congr_deriv ?_
    simp only [hA, id]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hpr (hAc.intervalIntegrable _ _)]
  field_simp
  ring

/-- Bessel gives the moment tail. -/
theorem tail_of_bessel {l : List YCell} {a : ℝ} (ha : 2 ≤ a) (hs : Sep a l) {N : ℕ} {Bq : ℝ}
    (hBq : π / 2 * G2 l - ((physL l (TF 0)) ^ 2 / 2 + ∑ n ∈ Finset.range N, (physL l (TF (n + 1))) ^ 2) ≤ Bq)
    (M : ℕ) : ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ Bq := by
  rcases Nat.lt_or_ge M N with h | h
  · rw [Finset.Ico_eq_empty (by omega)]
    have := bessel ha hs N
    simp only [Finset.sum_empty]
    linarith
  · have := bessel ha hs M
    have e := Finset.sum_range_add_sum_Ico (fun n => (physL l (TF (n + 1))) ^ 2) h
    linarith

/-! ### From the field to the physical kernels -/

theorem avg_rowK {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    c.avg (rowK x) = c.phys (fun s => Real.log |x - s|) + c.phys (fun s => Real.log |1 - s * x|) := by
  unfold YCell.phys YCell.avg
  have i1 := rowlog2_int h2 c.lo_lt hx0 hx1
  have i2 := rowlog_int h2 c.lo_lt hx0 hx1
  rw [← mul_add, ← intervalIntegral.integral_add i1 i2]
  congr 2
  funext y
  unfold rowK
  rw [mul_comm x]

theorem row_cell {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    c.pot (x + 1 / x) + c.phys (fun u => Real.log |u|) + c.w * Real.log |x| =
      c.phys (fun s => Real.log |x - s|) + c.phys (fun s => Real.log |1 - s * x|) := by
  have := cell_row (Or.inl h2) hx0.ne'
  rw [avg_rowK h2 hx0 hx1] at this
  linarith

theorem row_list {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    potL l (x + 1 / x) + physL l (fun u => Real.log |u|) + massL l * Real.log |x| =
      physL l (fun s => Real.log |x - s|) + physL l (fun s => Real.log |1 - s * x|) := by
  induction l with
  | nil => simp [potL, physL, massL]
  | cons c l ih =>
    have a1 := row_cell (h2 c (by simp)) hx0 hx1
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    have e3 : potL (c :: l) (x + 1 / x) = c.pot (x + 1 / x) + potL l (x + 1 / x) := by simp [potL]
    simp only [e1, e2, e3, add_mul]
    linarith

theorem row_cell_neg {c : YCell} (h : c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    c.pot (-u + 1 / (-u)) + c.phys (fun v => Real.log |v|) + c.w * Real.log |-u| =
      c.reflect.phys (fun s => Real.log |u - s|) + c.reflect.phys (fun s => Real.log |1 - s * u|) := by
  have h1 := cell_row (Or.inr h) (x := -u) (neg_ne_zero.mpr hu0.ne')
  have hr2 : 2 ≤ c.reflect.lo := by show 2 ≤ -c.hi; linarith
  have h3 := avg_rowK hr2 hu0 hu1
  have e : c.avg (rowK (-u)) = c.reflect.avg (rowK u) := by
    unfold YCell.avg YCell.reflect
    have ed : -c.lo - -c.hi = c.hi - c.lo := by ring
    simp only [ed]
    congr 1
    have := intervalIntegral.integral_comp_neg (a := c.lo) (b := c.hi) (rowK u)
    rw [← this]
    apply intervalIntegral.integral_congr
    intro Y hY
    rw [uIcc_of_le c.lo_lt.le] at hY
    have hb : 0 < -Y := by linarith [hY.2, c.lo_lt]
    have := rowK_neg_neg u hb
    simp only [neg_neg] at this
    exact this
  rw [e, h3] at h1
  linarith

theorem row_list_neg {l : List YCell} (h : ∀ c ∈ l, c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    potL l (-u + 1 / (-u)) + physL l (fun v => Real.log |v|) + massL l * Real.log |-u| =
      physL (MomentSource.reflectL l) (fun s => Real.log |u - s|) +
        physL (MomentSource.reflectL l) (fun s => Real.log |1 - s * u|) := by
  induction l with
  | nil => simp [potL, physL, massL, MomentSource.reflectL]
  | cons c l ih =>
    have a1 := row_cell_neg (h c (by simp)) hu0 hu1
    have a2 := ih fun d hd => h d (by simp [hd])
    have e1 : ∀ (m : List YCell) (c : YCell) f, physL (c :: m) f = c.phys f + physL m f :=
      fun m c f => by simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    have e3 : potL (c :: l) (-u + 1 / (-u)) = c.pot (-u + 1 / (-u)) + potL l (-u + 1 / (-u)) := by
      simp [potL]
    have e4 : MomentSource.reflectL (c :: l) = c.reflect :: MomentSource.reflectL l := rfl
    simp only [e4, e1, e2, e3, add_mul]
    linarith

/-! ### Reflection by sign -/

theorem log_one_sub_le_sum {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) (K : ℕ) :
    Real.log (1 - z) ≤ -∑ k ∈ Finset.range K, z ^ (k + 1) / ((k : ℝ) + 1) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg h0]; exact h1)
  have := sum_le_hasSum (Finset.range K) (fun i _ => by positivity) hs
  linarith

theorem phys_pow_int {c : YCell} (h2 : 2 ≤ c.lo) (k : ℕ) :
    IntervalIntegrable (fun y => YCell.physX y ^ k) volume c.lo c.hi :=
  ((physX_continuousOn (lo := c.lo) (hi := c.hi) (Or.inl h2)).pow k).intervalIntegrable_of_Icc
    c.lo_lt.le

theorem phys_refl_le {c : YCell} (h2 : 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (K : ℕ) :
    c.phys (fun s => Real.log |1 - s * x|) ≤
      -∑ k ∈ Finset.range K, x ^ (k + 1) / ((k : ℝ) + 1) * c.phys (fun s => s ^ (k + 1)) := by
  have hlt := c.lo_lt
  have hd : 0 < c.hi - c.lo := by linarith
  have hg0 : 0 ≤ c.w / (c.hi - c.lo) := div_nonneg c.w_nonneg hd.le
  set a : ℕ → ℝ := fun k => x ^ (k + 1) / ((k : ℝ) + 1) with ha
  have hi1 := rowlog_int h2 hlt hx0 hx1
  have hi2 : ∀ k ∈ Finset.range K, IntervalIntegrable
      (fun y => a k * YCell.physX y ^ (k + 1)) volume c.lo c.hi :=
    fun k _ => (phys_pow_int h2 (k + 1)).const_mul _
  have hi3 : IntervalIntegrable
      (fun y => ∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1)) volume c.lo c.hi :=
    (IntervalIntegrable.sum (Finset.range K) hi2).congr (by
      intro y _
      simp [Finset.sum_apply])
  have hle : ∫ y in c.lo..c.hi, Real.log |1 - YCell.physX y * x| ≤
      ∫ y in c.lo..c.hi, -∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1) := by
    apply intervalIntegral.integral_mono_ae_restrict hlt.le hi1 hi3.neg
    have hae : ∀ᵐ Y ∂(volume : Measure ℝ), Y ∉ ({2} : Set ℝ) :=
      (Set.countable_singleton _).ae_notMem volume
    have hm := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := c.lo) (b := c.hi))
    filter_upwards [ae_restrict_of_ae (s := Icc c.lo c.hi) hae, hm] with Y hY hYm
    have hY2 : 2 ≤ Y := h2.trans hYm.1
    have hYlt : 2 < Y := lt_of_le_of_ne hY2 fun h => hY (Set.mem_singleton_iff.mpr h.symm)
    obtain ⟨p0, _⟩ := physX_mem hY2
    have p1 := physX_lt_one hYlt
    have hz1 : YCell.physX Y * x < 1 := by nlinarith
    have hz0 : 0 ≤ YCell.physX Y * x := by positivity
    have := log_one_sub_le_sum hz0 hz1 K
    rw [abs_of_pos (by linarith)]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha]
    rw [mul_pow]; ring
  have hev : ∫ y in c.lo..c.hi, -∑ k ∈ Finset.range K, a k * YCell.physX y ^ (k + 1) =
      -∑ k ∈ Finset.range K, a k * ∫ y in c.lo..c.hi, YCell.physX y ^ (k + 1) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_finsetSum hi2]
    simp only [intervalIntegral.integral_const_mul]
  rw [hev] at hle
  have := mul_le_mul_of_nonneg_left hle hg0
  have e2 : ∑ k ∈ Finset.range K, a k * c.phys (fun s => s ^ (k + 1)) =
      c.w / (c.hi - c.lo) * ∑ k ∈ Finset.range K, a k * ∫ y in c.lo..c.hi, YCell.physX y ^ (k + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (c.w / (c.hi - c.lo) * _) = _
    ring
  rw [e2]
  show c.w / (c.hi - c.lo) * ∫ y in c.lo..c.hi, Real.log |1 - YCell.physX y * x| ≤ _
  linarith

theorem physL_refl_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (K : ℕ) :
    physL l (fun s => Real.log |1 - s * x|) ≤
      -∑ k ∈ Finset.range K, x ^ (k + 1) / ((k : ℝ) + 1) * physL l (fun s => s ^ (k + 1)) := by
  induction l with
  | nil => simp [physL]
  | cons c l ih =>
    have a1 := phys_refl_le (h2 c (by simp)) hx0 hx1 K
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    simp only [e1, mul_add, Finset.sum_add_distrib]
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

/-! ### Exact moments of a cell -/

section moments

noncomputable section

def Er (l : List YCell) (j : ℕ) : ℝ := (l.map fun c => gc c * (vY c.lo ^ j - vY c.hi ^ j)).sum

def Lr (l : List YCell) : ℝ :=
  (l.map fun c => gc c * (Real.log (vY c.lo) - Real.log (vY c.hi))).sum

theorem cell_mom2 {c : YCell} (h2 : 2 ≤ c.lo) (k : ℕ) :
    c.phys (fun s => s ^ (k + 2)) = gc c * (vY c.lo ^ (k + 1) - vY c.hi ^ (k + 1)) / ((k : ℝ) + 1) -
      gc c * (vY c.lo ^ (k + 3) - vY c.hi ^ (k + 3)) / ((k : ℝ) + 3) := by
  rw [phys_pos h2, CompactHf.integral_vY_pow k h2 c.lo_lt.le]
  unfold CompactHf.momK gc
  simp only [show k + 2 ≠ 1 by omega, _root_.if_false, show k + 2 - 1 = k + 1 by omega]
  push_cast
  have e1 : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
  have e2 : (k : ℝ) + 2 + 1 = (k : ℝ) + 3 := by ring
  rw [e1, e2, show k + 2 + 1 = k + 3 by omega]
  ring

theorem cell_mom1 {c : YCell} (h2 : 2 ≤ c.lo) :
    c.phys (fun s => s ^ 1) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) -
      gc c * (vY c.lo ^ 2 - vY c.hi ^ 2) / 2 := by
  have := CompactHf.integral_vY_pow' (k := 1) le_rfl h2 c.lo_lt.le
  rw [phys_pos h2, this]
  unfold CompactHf.momK gc MomentSource.H1
  simp only [_root_.if_true]
  ring

theorem mom2 {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (k : ℕ) :
    physL l (fun s => s ^ (k + 2)) = Er l (k + 1) / ((k : ℝ) + 1) - Er l (k + 3) / ((k : ℝ) + 3) := by
  induction l with
  | nil => simp [physL, Er]
  | cons c l ih =>
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : ∀ j, Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := fun j => by simp [Er]
    rw [e1, a2, cell_mom2 (h2 c (by simp)), e2, e2]
    ring

theorem mom1 {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) :
    physL l (fun s => s ^ 1) = Lr l - Er l 2 / 2 := by
  induction l with
  | nil => simp [physL, Er, Lr]
  | cons c l ih =>
    have a2 := ih fun d hd => h2 d (by simp [hd])
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    have e2 : ∀ j, Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := fun j => by simp [Er]
    have e3 : Lr (c :: l) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) + Lr l := by simp [Lr]
    rw [e1, a2, cell_mom1 (h2 c (by simp)), e2, e3]
    ring

theorem stream_close {P a : ℕ} {x : ℝ} (ha : a ≤ 2 ^ P) (h1 : (a : ℝ) / 2 ^ P ≤ x)
    (h2 : x ≤ ((a : ℝ) + 1) / 2 ^ P) (hx1 : x ≤ 1) (j : ℕ) :
    |x ^ j - (MomentInputs.stream P a (2 ^ P) j : ℝ) / 2 ^ P| ≤ 2 * j / 2 ^ P := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have ht0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
  have ht1 : (a : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one hd]; exact_mod_cast ha
  have u := MomentInputs.stream_upper P a (2 ^ P) j
  have l := MomentInputs.stream_lower P a (2 ^ P) ha j
  have e1 : (((2 ^ P : ℕ) : ℝ)) / 2 ^ P = 1 := by push_cast; field_simp
  rw [e1, one_mul] at u l
  have p := MomentInputs.abs_pow_sub_pow_le_unit (ht0.trans h1) hx1 ht0 ht1 j
  have q : |x - (a : ℝ) / 2 ^ P| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((a : ℝ) + 1) / 2 ^ P = (a : ℝ) / 2 ^ P + 1 / 2 ^ P := by ring
    linarith
  have r : |x ^ j - ((a : ℝ) / 2 ^ P) ^ j| ≤ j / 2 ^ P := by
    refine p.trans ?_
    calc (j : ℝ) * |x - (a : ℝ) / 2 ^ P| ≤ j * (1 / 2 ^ P) := by gcongr
      _ = j / 2 ^ P := by ring
  have r' := abs_le.mp r
  rw [abs_le]
  have e2 : 2 * (j : ℝ) / 2 ^ P = j / 2 ^ P + j / 2 ^ P := by ring
  rw [e2]
  constructor <;> linarith [r'.1, r'.2]

end

/-! ### Kernel records -/

/-- One gas cell of the certificate: `[a,b]/10^12`, integer mass `p`, endpoint enclosures
`al/2^P ≤ X(lo) ≤ (al+1)/2^P`, `ah/2^P ≤ X(hi) ≤ (ah+1)/2^P`, and the AM-GM parameter `lam/2^32`. -/
structure GD where
  a : ℕ
  b : ℕ
  p : ℕ
  al : ℕ
  ah : ℕ
  lam : ℕ

/-- `t + 1/t ≥ Y` at `t = A/2^P`. -/
def lowOK (P Yn A : ℕ) : Bool := decide (Yn * A * 2 ^ P ≤ (A * A + 4 ^ P) * 10 ^ 12)
/-- `t + 1/t ≤ Y` at `t = (A+1)/2^P`, or `t ≥ 1`. -/
def upOK (P Yn A : ℕ) : Bool :=
  decide (2 ^ P ≤ A + 1) || decide (((A + 1) * (A + 1) + 4 ^ P) * 10 ^ 12 ≤ Yn * (A + 1) * 2 ^ P)

def GD.ok (P : ℕ) (d : GD) : Bool :=
  decide (2 * 10 ^ 12 ≤ d.a) && decide (d.a < d.b) && decide (0 < d.ah) && decide (d.ah ≤ d.al) &&
    decide (d.al ≤ 2 ^ P) && decide (0 < d.lam) && lowOK P d.a d.al && upOK P d.a d.al &&
    lowOK P d.b d.ah && upOK P d.b d.ah

/-- `⌊gc · 2^P⌋`. -/
def GD.g (P T : ℕ) (d : GD) : ℕ := d.p * 10 ^ 12 * 2 ^ P / (T * (d.b - d.a))

/-- Stream state of a cell. -/
structure St where
  g : ℕ
  al : ℕ
  ah : ℕ
  u : ℕ
  v : ℕ

def St.step (P : ℕ) (s : St) : St := ⟨s.g, s.al, s.ah, s.u * s.al / 2 ^ P, s.v * s.ah / 2 ^ P⟩

def stAt (P T : ℕ) (j : ℕ) (d : GD) : St :=
  ⟨d.g P T, d.al, d.ah, MomentInputs.stream P d.al (2 ^ P) j, MomentInputs.stream P d.ah (2 ^ P) j⟩

theorem stAt_step (P T j : ℕ) (d : GD) : (stAt P T j d).step P = stAt P T (j + 1) d := rfl

def eVal (S : List St) : ℤ := (S.map fun s => (s.g : ℤ) * ((s.u : ℤ) - s.v)).sum

/-- The rows `E_j`, `j = j0, ..., j0+n-1`, one pass per `j`. -/
def rows (P : ℕ) : ℕ → List St → List ℤ
  | 0, _ => []
  | n + 1, S => eVal S :: rows P n (S.map (St.step P))

/-- Sequential closeness to a real sequence, with lists of values and errors. -/
def CloseL (m : ℕ → ℝ) : ℕ → List ℚ → List ℚ → Prop
  | _, [], _ => True
  | _, _ :: _, [] => False
  | k, a :: as, d :: ds => |m k - (a : ℝ)| ≤ (d : ℝ) ∧ CloseL m (k + 1) as ds

section spec

variable {P T : ℕ}

/-- A real cell and its record. -/
structure Rel (P T : ℕ) (c : YCell) (d : GD) : Prop where
  lo : c.lo = (d.a : ℝ) / 10 ^ 12
  hi : c.hi = (d.b : ℝ) / 10 ^ 12
  w : c.w = (d.p : ℝ) / (T : ℝ)
  ok : d.ok P = true

theorem enc_low {t Y : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hY : 2 ≤ Y) (h : Y ≤ t + 1 / t) :
    t ≤ vY Y := by
  have := physX_anti hY h
  rw [physX_inv h0 h1, physX_pos hY] at this
  exact this

theorem enc_up {t Y : ℝ} (h0 : 0 < t) (hY : 2 ≤ Y) (h : t + 1 / t ≤ Y ∨ 1 ≤ t) : vY Y ≤ t := by
  rcases h with h | h
  · rcases le_or_gt t 1 with h1 | h1
    · have h3 : 2 ≤ t + 1 / t := by
        have e : t + 1 / t - 2 = (t - 1) ^ 2 / t := by field_simp; ring
        have : 0 ≤ (t - 1) ^ 2 / t := by positivity
        linarith
      have := physX_anti h3 h
      rw [physX_inv h0 h1, physX_pos hY] at this
      exact this
    · exact (vY_le_one hY).trans h1.le
  · exact (vY_le_one hY).trans h

theorem t_add_inv {A D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    A / D + 1 / (A / D) = (A * A + D * D) / (A * D) := by
  field_simp

theorem low_real {P Yn A : ℕ} (hA : 0 < A) (hA1 : A ≤ 2 ^ P) (hY : 2 ≤ (Yn : ℝ) / 10 ^ 12)
    (h : lowOK P Yn A = true) : (A : ℝ) / 2 ^ P ≤ vY ((Yn : ℝ) / 10 ^ 12) := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have h' : Yn * A * 2 ^ P ≤ (A * A + 4 ^ P) * 10 ^ 12 := of_decide_eq_true h
  have h'' : (Yn : ℝ) * A * 2 ^ P ≤ ((A : ℝ) * A + 4 ^ P) * 10 ^ 12 := by exact_mod_cast h'
  refine enc_low (by positivity) ?_ hY ?_
  · rw [div_le_one hd]; exact_mod_cast hA1
  · have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
    rw [e4] at h''
    rw [t_add_inv hA0 hd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem up_real {P Yn A : ℕ} (hY : 2 ≤ (Yn : ℝ) / 10 ^ 12)
    (h : upOK P Yn A = true) : vY ((Yn : ℝ) / 10 ^ 12) ≤ ((A : ℝ) + 1) / 2 ^ P := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hA0 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  refine enc_up (by positivity) hY ?_
  unfold upOK at h
  rcases Bool.or_eq_true _ _ |>.mp h with h | h
  · right
    have h' : 2 ^ P ≤ A + 1 := of_decide_eq_true h
    have h'' : (2 : ℝ) ^ P ≤ (A : ℝ) + 1 := by exact_mod_cast h'
    rw [le_div_iff₀ hd]; linarith
  · left
    have h' : ((A + 1) * (A + 1) + 4 ^ P) * 10 ^ 12 ≤ Yn * (A + 1) * 2 ^ P := of_decide_eq_true h
    have h'' : (((A : ℝ) + 1) * ((A : ℝ) + 1) + 4 ^ P) * 10 ^ 12 ≤ (Yn : ℝ) * ((A : ℝ) + 1) * 2 ^ P := by
      exact_mod_cast h'
    have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
    rw [e4] at h''
    rw [t_add_inv hA0 hd, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- Facts extracted from one record. -/
structure Facts (P : ℕ) (c : YCell) (d : GD) : Prop where
  two : 2 ≤ c.lo
  al1 : d.al ≤ 2 ^ P
  ah0 : 0 < d.ah
  ahl : d.ah ≤ d.al
  lam0 : 0 < d.lam
  ll : (d.al : ℝ) / 2 ^ P ≤ vY c.lo
  lu : vY c.lo ≤ ((d.al : ℝ) + 1) / 2 ^ P
  hl : (d.ah : ℝ) / 2 ^ P ≤ vY c.hi
  hu : vY c.hi ≤ ((d.ah : ℝ) + 1) / 2 ^ P
  dab : d.a < d.b

theorem Rel.facts {c : YCell} {d : GD} (h : Rel P T c d) : Facts P c d := by
  have hk := h.ok
  simp only [GD.ok, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩, k9⟩, k10⟩ := hk
  have h2 : 2 ≤ (d.a : ℝ) / 10 ^ 12 := by
    rw [le_div_iff₀ (by norm_num)]
    have : ((2 * 10 ^ 12 : ℕ) : ℝ) ≤ d.a := by exact_mod_cast k1
    push_cast at this
    linarith
  have h3 : 2 ≤ (d.b : ℝ) / 10 ^ 12 := by
    have : (d.a : ℝ) ≤ d.b := by exact_mod_cast k2.le
    refine h2.trans ?_
    gcongr
  have hah2 : d.ah ≤ 2 ^ P := k4.trans k5
  rw [← h.lo] at h2
  refine ⟨h2, k5, k3, k4, k6, ?_, ?_, ?_, ?_, k2⟩
  · rw [h.lo]; refine low_real (lt_of_lt_of_le k3 k4) k5 (h.lo ▸ h2) k7
  · rw [h.lo]; exact up_real (h.lo ▸ h2) k8
  · rw [h.hi]; exact low_real k3 hah2 h3 k9
  · rw [h.hi]; exact up_real h3 k10

end spec

end moments

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

/-! ### Rounding -/

def fl (q : ℚ) : ℤ := q.num / (q.den : ℤ)
def ce (q : ℚ) : ℤ := -fl (-q)

theorem fl_eq (q : ℚ) : fl q = ⌊q⌋ := Rat.floor_def'.symm

theorem fl_le (q : ℚ) : ((fl q : ℤ) : ℚ) ≤ q := by rw [fl_eq]; exact Int.floor_le q
theorem lt_fl (q : ℚ) : q < (fl q : ℚ) + 1 := by rw [fl_eq]; exact Int.lt_floor_add_one q
theorem le_ce (q : ℚ) : q ≤ (ce q : ℚ) := by
  have := fl_le (-q); unfold ce; push_cast; linarith
theorem ce_lt (q : ℚ) : (ce q : ℚ) < q + 1 := by
  have := lt_fl (-q); unfold ce; push_cast; linarith

theorem fl_real (q : ℚ) (Q : ℕ) : ((fl (q * 2 ^ Q) : ℤ) : ℝ) ≤ (q : ℝ) * 2 ^ Q ∧
    (q : ℝ) * 2 ^ Q < ((fl (q * 2 ^ Q) : ℤ) : ℝ) + 1 := by
  have h1 := fl_le (q * 2 ^ Q)
  have h2 := lt_fl (q * 2 ^ Q)
  have h1' : (((fl (q * 2 ^ Q) : ℤ) : ℚ) : ℝ) ≤ ((q * 2 ^ Q : ℚ) : ℝ) := Rat.cast_le.mpr h1
  have h2' : ((q * 2 ^ Q : ℚ) : ℝ) < ((((fl (q * 2 ^ Q) : ℤ) : ℚ) + 1 : ℚ) : ℝ) := Rat.cast_lt.mpr h2
  push_cast at h1' h2'
  exact ⟨h1', h2'⟩

theorem ce_real (q : ℚ) (Q : ℕ) : (q : ℝ) * 2 ^ Q ≤ ((ce (q * 2 ^ Q) : ℤ) : ℝ) := by
  have h1 := le_ce (q * 2 ^ Q)
  have h1' : ((q * 2 ^ Q : ℚ) : ℝ) ≤ (((ce (q * 2 ^ Q) : ℤ) : ℚ) : ℝ) := Rat.cast_le.mpr h1
  push_cast at h1'
  exact h1'

section spec

variable {P T Q : ℕ}

noncomputable section

theorem Rel.gc_close {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    (d.g P T : ℝ) / 2 ^ P ≤ gc c ∧ gc c ≤ ((d.g P T : ℝ) + 1) / 2 ^ P := by
  have f := h.facts
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hM : 0 < T * (d.b - d.a) := Nat.mul_pos hT (by have := f.dab; omega)
  have hcast : ((T * (d.b - d.a) : ℕ) : ℝ) = (T : ℝ) * ((d.b : ℝ) - d.a) := by
    rw [Nat.cast_mul, Nat.cast_sub f.dab.le]
  have hg : gc c = (d.p : ℝ) * 10 ^ 12 / ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    unfold gc
    rw [h.w, h.lo, h.hi]
    field_simp
  have h1 : d.g P T * (T * (d.b - d.a)) ≤ d.p * 10 ^ 12 * 2 ^ P := Nat.div_mul_le_self _ _
  have h2 : d.p * 10 ^ 12 * 2 ^ P < (d.g P T + 1) * (T * (d.b - d.a)) := by
    have := Nat.lt_succ_iff.mpr (le_refl (d.g P T))
    exact (Nat.div_lt_iff_lt_mul hM).mp this
  have h1' : (d.g P T : ℝ) * ((T : ℝ) * ((d.b : ℝ) - d.a)) ≤ (d.p : ℝ) * 10 ^ 12 * 2 ^ P := by
    rw [← hcast]; exact_mod_cast h1
  have h2' : (d.p : ℝ) * 10 ^ 12 * 2 ^ P < ((d.g P T : ℝ) + 1) * ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    rw [← hcast]; exact_mod_cast h2
  have hM' : (0 : ℝ) < (T : ℝ) * ((d.b : ℝ) - d.a) := by positivity
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  rw [hg]
  constructor
  · rw [div_le_div_iff₀ hd hM']; linarith
  · rw [div_le_div_iff₀ hM' hd]; linarith

theorem cell_E {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) (j : ℕ) :
    |gc c * (vY c.lo ^ j - vY c.hi ^ j) -
        ((d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
          (MomentInputs.stream P d.ah (2 ^ P) j : ℝ))) / 4 ^ P| ≤
      (1 + 4 * j * ((d.g P T : ℝ) / 2 ^ P)) / 2 ^ P := by
  have f := h.facts
  obtain ⟨g1, g2⟩ := h.gc_close hT
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have h2' : 2 ≤ c.hi := f.two.trans c.lo_lt.le
  have hx1 := vY_le_one f.two
  have hy1 := vY_le_one h2'
  have hx0 := (vY_pos f.two).le
  have hy0 := (vY_pos h2').le
  have s1 := stream_close f.al1 f.ll f.lu hx1 j
  have s2 := stream_close (f.ahl.trans f.al1) f.hl f.hu hy1 j
  set G := (d.g P T : ℝ) / 2 ^ P with hG
  have hG0 : 0 ≤ G := by positivity
  set u := (MomentInputs.stream P d.al (2 ^ P) j : ℝ) / 2 ^ P
  set v := (MomentInputs.stream P d.ah (2 ^ P) j : ℝ) / 2 ^ P
  set D := vY c.lo ^ j - vY c.hi ^ j with hD
  have e4 : (4 : ℝ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
  have e : ((d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
      (MomentInputs.stream P d.ah (2 ^ P) j : ℝ))) / 4 ^ P = G * (u - v) := by
    simp only [hG, u, v]; rw [e4]; field_simp
  rw [e]
  have hD1 : |D| ≤ 1 := by
    have a1 : vY c.lo ^ j ≤ 1 := pow_le_one₀ hx0 hx1
    have a2 : vY c.hi ^ j ≤ 1 := pow_le_one₀ hy0 hy1
    have a3 : 0 ≤ vY c.lo ^ j := pow_nonneg hx0 j
    have a4 : 0 ≤ vY c.hi ^ j := pow_nonneg hy0 j
    rw [abs_le]; constructor <;> linarith
  have hDd : |D - (u - v)| ≤ 4 * j / 2 ^ P := by
    have q1 := abs_le.mp s1
    have q2 := abs_le.mp s2
    have e2 : 4 * (j : ℝ) / 2 ^ P = 2 * j / 2 ^ P + 2 * j / 2 ^ P := by ring
    rw [abs_le, e2]
    constructor <;> linarith [q1.1, q1.2, q2.1, q2.2]
  have hgg : |gc c - G| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((d.g P T : ℝ) + 1) / 2 ^ P = G + 1 / 2 ^ P := by simp only [hG]; ring
    linarith
  have split : gc c * D - G * (u - v) = (gc c - G) * D + G * (D - (u - v)) := by ring
  rw [split]
  calc |(gc c - G) * D + G * (D - (u - v))| ≤ |gc c - G| * |D| + G * |D - (u - v)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hG0]
    _ ≤ 1 / 2 ^ P * 1 + G * (4 * j / 2 ^ P) := by
        gcongr
    _ = _ := by ring

def eV (P T : ℕ) (L : List GD) (j : ℕ) : ℤ := eVal (L.map (stAt P T j))
def SG (P T : ℕ) (L : List GD) : ℕ := (L.map (GD.g P T)).sum

theorem Er_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) (j : ℕ) :
    |Er l j - (eV P T L j : ℝ) / 4 ^ P| ≤
      ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by
  induction h with
  | nil => simp [Er, eV, eVal, SG]
  | @cons c d l L hr hl ih =>
    have a := cell_E hr hT j
    have e1 : Er (c :: l) j = gc c * (vY c.lo ^ j - vY c.hi ^ j) + Er l j := by simp [Er]
    have e2 : ((eV P T (d :: L) j : ℤ) : ℝ) = (d.g P T : ℝ) * ((MomentInputs.stream P d.al (2 ^ P) j : ℝ) -
          (MomentInputs.stream P d.ah (2 ^ P) j : ℝ)) + (eV P T L j : ℝ) := by
      simp [eV, eVal, stAt]
    have e3 : ((SG P T (d :: L) : ℕ) : ℝ) = (d.g P T : ℝ) + (SG P T L : ℝ) := by simp [SG]
    rw [e1, e2, e3, List.length_cons]
    have q1 := abs_le.mp a
    have q2 := abs_le.mp ih
    push_cast
    have e4 : ∀ A B : ℝ, (A + B) / 4 ^ P = A / 4 ^ P + B / 4 ^ P := fun A B => add_div _ _ _
    rw [e4]
    have e5 : (((L.length : ℝ) + 1 + 4 * j * (((d.g P T : ℝ) + (SG P T L : ℝ)) / 2 ^ P)) / 2 ^ P) =
        (1 + 4 * j * ((d.g P T : ℝ) / 2 ^ P)) / 2 ^ P +
          ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by ring
    rw [e5, abs_le]
    constructor <;> linarith [q1.1, q1.2, q2.1, q2.2]

/-- Sequential closeness of an integer row list. -/
def CloseZ (m : ℕ → ℝ) (S : ℝ) (err : ℕ → ℝ) : ℕ → List ℤ → Prop
  | _, [] => True
  | k, e :: es => |m k - (e : ℝ) / S| ≤ err k ∧ CloseZ m S err (k + 1) es

theorem rows_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T)
    (n j : ℕ) :
    CloseZ (Er l) (4 ^ P) (fun j => ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P) j
      (rows P n (L.map (stAt P T j))) := by
  induction n generalizing j with
  | zero => trivial
  | succ n ih =>
    refine ⟨Er_close h hT j, ?_⟩
    have : (L.map (stAt P T j)).map (St.step P) = L.map (stAt P T (j + 1)) := by
      rw [List.map_map]; rfl
    rw [this]
    exact ih (j + 1)

end

/-- Moments from the row list: entry `i` is the moment `k+2+i`; the row list starts at `E_(k+1)`. -/
def mB (S : ℚ) : ℕ → List ℤ → List ℚ
  | k, e :: e2 :: e3 :: r =>
    ((e : ℚ) / S / ((k : ℚ) + 1) - (e3 : ℚ) / S / ((k : ℚ) + 3)) :: mB S (k + 1) (e2 :: e3 :: r)
  | _, _ => []

def dB (err : ℕ → ℚ) : ℕ → List ℤ → List ℚ
  | k, _ :: e2 :: e3 :: r =>
    (err (k + 1) / ((k : ℚ) + 1) + err (k + 3) / ((k : ℚ) + 3)) :: dB err (k + 1) (e2 :: e3 :: r)
  | _, _ => []

theorem mB_close {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {S : ℚ} {err : ℕ → ℚ}
    (R : List ℤ) (k : ℕ) (h : CloseZ (Er l) (S : ℝ) (fun j => (err j : ℝ)) (k + 1) R) :
    CloseL (fun i => physL l (fun s => s ^ i)) (k + 2) (mB S k R) (dB err k R) := by
  induction R generalizing k with
  | nil => simp [mB, CloseL]
  | cons e R ih =>
    cases R with
    | nil => simp [mB, CloseL]
    | cons e2 R =>
      cases R with
      | nil => simp [mB, CloseL]
      | cons e3 R =>
        obtain ⟨c1, c2, c3, c4⟩ := h
        simp only [mB, dB, CloseL]
        refine ⟨?_, ?_⟩
        · rw [mom2 h2 k]
          have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by positivity
          push_cast
          have split : Er l (k + 1) / ((k : ℝ) + 1) - Er l (k + 3) / ((k : ℝ) + 3) -
              ((e : ℝ) / (S : ℝ) / ((k : ℝ) + 1) - (e3 : ℝ) / (S : ℝ) / ((k : ℝ) + 3)) =
              (Er l (k + 1) - (e : ℝ) / (S : ℝ)) / ((k : ℝ) + 1) -
                (Er l (k + 3) - (e3 : ℝ) / (S : ℝ)) / ((k : ℝ) + 3) := by ring
          rw [split]
          refine (abs_sub _ _).trans ?_
          rw [abs_div, abs_div, abs_of_pos hk1, abs_of_pos hk3]
          gcongr
        · exact ih (k + 1) ⟨c2, c3, c4⟩

/-! ### The first logarithmic moment -/

def GD.t (d : GD) : ℚ := ((d.al : ℚ) - d.ah) / ((d.al : ℚ) + d.ah)
def serQ (t : ℚ) : ℚ := 2 * t * (1 + t ^ 2 / 3 + t ^ 4 / 5 + t ^ 6 / 7)
def GD.le (d : GD) : ℚ := 2 * d.t ^ 9 / (1 - d.t ^ 2) + 1 / (d.ah : ℚ)
def GD.ghat (P T : ℕ) (d : GD) : ℚ := (d.g P T : ℚ) / 2 ^ P
def GD.lV (P T : ℕ) (d : GD) : ℚ := d.ghat P T * serQ d.t
def GD.lE (P T : ℕ) (d : GD) : ℚ := d.ghat P T * d.le + (serQ d.t + d.le) / 2 ^ P
def GD.lI (P T Q : ℕ) (d : GD) : ℤ := fl (d.lV P T * 2 ^ Q)
def GD.lEI (P T Q : ℕ) (d : GD) : ℤ := ce (d.lE P T * 2 ^ Q)

noncomputable section

theorem log_enc {x a δ : ℝ} (ha : 0 < a) (h1 : a ≤ x) (h2 : x ≤ a + δ) :
    0 ≤ Real.log x - Real.log a ∧ Real.log x - Real.log a ≤ δ / a := by
  have hx : 0 < x := lt_of_lt_of_le ha h1
  constructor
  · have := Real.log_le_log ha h1; linarith
  · rw [← Real.log_div hx.ne' ha.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx ha)
    refine this.trans ?_
    rw [div_sub_one ha.ne']
    gcongr
    linarith

theorem cell_L {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    |gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) - ((d.lV P T : ℚ) : ℝ)| ≤ ((d.lE P T : ℚ) : ℝ) := by
  have f := h.facts
  obtain ⟨g1, g2⟩ := h.gc_close hT
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hah : (0 : ℝ) < d.ah := by exact_mod_cast f.ah0
  have hal : (0 : ℝ) < d.al := lt_of_lt_of_le hah (by exact_mod_cast f.ahl)
  have hle : (d.ah : ℝ) ≤ d.al := by exact_mod_cast f.ahl
  set tq : ℝ := ((d.al : ℝ) - d.ah) / ((d.al : ℝ) + d.ah) with ht
  have htq : ((d.t : ℚ) : ℝ) = tq := by simp [GD.t, ht]
  have t0 : 0 ≤ tq := div_nonneg (by linarith) (by positivity)
  have t1 : tq < 1 := by rw [ht, div_lt_one (by positivity)]; linarith
  have at' := CatalanMeasure.WLog.atanh_tail t0 t1 4
  have elog : (1 + tq) / (1 - tq) = (d.al : ℝ) / d.ah := by
    have hs : (d.al : ℝ) + d.ah ≠ 0 := by positivity
    have a1 : 1 + tq = 2 * (d.al : ℝ) / ((d.al : ℝ) + d.ah) := by rw [ht]; field_simp; ring
    have a2 : 1 - tq = 2 * (d.ah : ℝ) / ((d.al : ℝ) + d.ah) := by rw [ht]; field_simp; ring
    rw [a1, a2, div_div_div_cancel_right₀ hs]
    field_simp
  rw [elog] at at'
  have ser : 2 * tq * ∑ i ∈ Finset.range 4, (tq ^ 2) ^ i / ((1 + 2 * i : ℕ) : ℝ) = ((serQ d.t : ℚ) : ℝ) := by
    simp only [serQ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    rw [htq]
    ring
  rw [ser] at at'
  have l1 := log_enc (a := (d.al : ℝ) / 2 ^ P) (x := vY c.lo) (δ := 1 / 2 ^ P) (by positivity) f.ll
    (by have := f.lu; rw [add_div] at this; exact this)
  have l2 := log_enc (a := (d.ah : ℝ) / 2 ^ P) (x := vY c.hi) (δ := 1 / 2 ^ P) (by positivity) f.hl
    (by have := f.hu; rw [add_div] at this; exact this)
  have r1 : (1 / 2 ^ P) / ((d.al : ℝ) / 2 ^ P) = 1 / (d.al : ℝ) := by field_simp
  have r2 : (1 / 2 ^ P) / ((d.ah : ℝ) / 2 ^ P) = 1 / (d.ah : ℝ) := by field_simp
  rw [r1] at l1
  rw [r2] at l2
  have r3 : 1 / (d.al : ℝ) ≤ 1 / (d.ah : ℝ) := by gcongr
  have elg : Real.log ((d.al : ℝ) / d.ah) =
      Real.log ((d.al : ℝ) / 2 ^ P) - Real.log ((d.ah : ℝ) / 2 ^ P) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  set ℓ := Real.log (vY c.lo) - Real.log (vY c.hi) with hℓ
  set Sg : ℝ := ((serQ d.t : ℚ) : ℝ) with hSg
  set ee : ℝ := ((d.le : ℚ) : ℝ) with hee
  have eex : ee = 2 * tq ^ 9 / (1 - tq ^ 2) + 1 / (d.ah : ℝ) := by
    simp only [hee, GD.le]; push_cast; rw [htq]
  have hclose : |ℓ - Sg| ≤ ee := by
    have q := abs_le.mp at'
    have : 2 * tq ^ (2 * 4 + 1) / (1 - tq ^ 2) = 2 * tq ^ 9 / (1 - tq ^ 2) := by norm_num
    rw [this] at q
    rw [eex, abs_le]
    rw [elg] at q
    constructor <;> linarith [q.1, q.2, l1.1, l1.2, l2.1, l2.2]
  have hS0 : 0 ≤ Sg := by
    simp only [hSg, serQ]
    push_cast
    rw [htq]
    positivity
  have hee0 : 0 ≤ ee := (abs_nonneg _).trans hclose
  set G : ℝ := (d.g P T : ℝ) / 2 ^ P with hG
  have hG0 : 0 ≤ G := by positivity
  have eV : ((d.lV P T : ℚ) : ℝ) = G * Sg := by simp [GD.lV, GD.ghat, hG, hSg]
  have eE : ((d.lE P T : ℚ) : ℝ) = G * ee + (Sg + ee) / 2 ^ P := by
    simp [GD.lE, GD.ghat, hG, hSg, hee]
  rw [eV, eE]
  have hgg : |gc c - G| ≤ 1 / 2 ^ P := by
    rw [abs_of_nonneg (by linarith)]
    have : ((d.g P T : ℝ) + 1) / 2 ^ P = G + 1 / 2 ^ P := by simp only [hG]; ring
    linarith
  have hl : |ℓ| ≤ Sg + ee := by
    have q := abs_le.mp hclose
    rw [abs_le]; constructor <;> linarith [q.1, q.2]
  have split : gc c * ℓ - G * Sg = (gc c - G) * ℓ + G * (ℓ - Sg) := by ring
  rw [split]
  calc |(gc c - G) * ℓ + G * (ℓ - Sg)| ≤ |gc c - G| * |ℓ| + G * |ℓ - Sg| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hG0]
    _ ≤ 1 / 2 ^ P * (Sg + ee) + G * ee := by gcongr
    _ = _ := by ring

end

end spec

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos phys_pos)

section spec

variable {P T Q : ℕ}

noncomputable section

def LI (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.lI P T Q)).sum
def LEI (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.lEI P T Q)).sum

theorem cast_sum_cons {β : Type*} (f : β → ℤ) (d : β) (L : List β) :
    ((((d :: L).map f).sum : ℤ) : ℝ) = (f d : ℝ) + ((L.map f).sum : ℤ) := by
  simp

theorem Lr_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) :
    |Lr l - (LI P T Q L : ℝ) / 2 ^ Q| ≤ ((LEI P T Q L : ℝ) + L.length) / 2 ^ Q := by
  have hq : (0 : ℝ) < 2 ^ Q := by positivity
  induction h with
  | nil => simp [Lr, LI, LEI]
  | @cons c d l L hr hl ih =>
    have a := abs_le.mp (cell_L hr hT)
    have e1 : Lr (c :: l) = gc c * (Real.log (vY c.lo) - Real.log (vY c.hi)) + Lr l := by simp [Lr]
    have e2 : ((LI P T Q (d :: L) : ℤ) : ℝ) = (d.lI P T Q : ℝ) + (LI P T Q L : ℝ) :=
      cast_sum_cons (GD.lI P T Q) d L
    have e3 : ((LEI P T Q (d :: L) : ℤ) : ℝ) = (d.lEI P T Q : ℝ) + (LEI P T Q L : ℝ) :=
      cast_sum_cons (GD.lEI P T Q) d L
    obtain ⟨f1, f2⟩ : ((d.lI P T Q : ℤ) : ℝ) ≤ ((d.lV P T : ℚ) : ℝ) * 2 ^ Q ∧
        ((d.lV P T : ℚ) : ℝ) * 2 ^ Q < (d.lI P T Q : ℝ) + 1 := fl_real _ Q
    have f3 : ((d.lE P T : ℚ) : ℝ) * 2 ^ Q ≤ (d.lEI P T Q : ℝ) := ce_real _ Q
    have g1 : ((d.lV P T : ℚ) : ℝ) ≤ ((d.lI P T Q : ℝ) + 1) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    have g2 : (d.lI P T Q : ℝ) / 2 ^ Q ≤ ((d.lV P T : ℚ) : ℝ) := by
      rw [div_le_iff₀ hq]; linarith
    have g3 : ((d.lE P T : ℚ) : ℝ) ≤ (d.lEI P T Q : ℝ) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    rw [e1, e2, e3, List.length_cons]
    have q2 := abs_le.mp ih
    push_cast
    have s1 : ((d.lI P T Q : ℝ) + (LI P T Q L : ℝ)) / 2 ^ Q =
        (d.lI P T Q : ℝ) / 2 ^ Q + (LI P T Q L : ℝ) / 2 ^ Q := add_div _ _ _
    have s2 : ((d.lEI P T Q : ℝ) + (LEI P T Q L : ℝ) + ((L.length : ℝ) + 1)) / 2 ^ Q =
        (d.lEI P T Q : ℝ) / 2 ^ Q + 1 / 2 ^ Q + ((LEI P T Q L : ℝ) + (L.length : ℝ)) / 2 ^ Q := by ring
    have s3 : ((d.lI P T Q : ℝ) + 1) / 2 ^ Q = (d.lI P T Q : ℝ) / 2 ^ Q + 1 / 2 ^ Q := add_div _ _ _
    rw [s1, s2, abs_le]
    constructor <;> linarith [a.1, a.2, q2.1, q2.2]

/-! ### The density norm -/

end

def vQ (P : ℕ) (Yn A : ℕ) : ℚ :=
  ((Yn : ℚ) ^ 2 / 10 ^ 24 - 4) * ((Yn : ℚ) / 10 ^ 12 - (A : ℚ) / 2 ^ P - 1)

def GD.cg (P T : ℕ) (d : GD) : ℚ :=
  ((d.p : ℚ) / (T : ℚ)) ^ 2 * (10 ^ 12 / ((d.b : ℚ) - d.a)) *
    ((d.lam : ℚ) / 2 ^ 32 / 2 + (vQ P d.a d.al + vQ P d.b d.ah) / (4 * ((d.lam : ℚ) / 2 ^ 32)))

def GD.cgI (P T Q : ℕ) (d : GD) : ℤ := ce (d.cg P T * 2 ^ Q)

def G2I (P T Q : ℕ) (L : List GD) : ℤ := (L.map (GD.cgI P T Q)).sum

noncomputable section

theorem Wsq_le {y t : ℝ} (hy : 2 ≤ y) (ht : t ≤ vY y) : Wsq y ≤ (y ^ 2 - 4) * (y - t - 1) := by
  have h := MomentSource.vY_add_inv hy
  have hx := vY_pos hy
  unfold Wsq
  rw [physX_pos hy, one_div]
  have : (vY y)⁻¹ = y - vY y := by linarith
  rw [this]
  have : 0 ≤ y ^ 2 - 4 := by nlinarith
  apply mul_le_mul_of_nonneg_left _ this
  linarith

theorem cell_G2 {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    gc c ^ 2 * ∫ θ in Th c.lo..Th c.hi, bet θ ^ 2 ≤ ((d.cg P T : ℚ) : ℝ) := by
  have f := h.facts
  have hlt := c.lo_lt
  have hh2 : 2 ≤ c.hi := f.two.trans hlt.le
  have hlam : (0 : ℝ) < (d.lam : ℝ) / 2 ^ 32 := by
    have : (0 : ℝ) < d.lam := by exact_mod_cast f.lam0
    positivity
  set vlo : ℝ := ((vQ P d.a d.al : ℚ) : ℝ) with hvlo
  set vhi : ℝ := ((vQ P d.b d.ah : ℚ) : ℝ) with hvhi
  have e1 : Wsq c.lo ≤ vlo := by
    refine (Wsq_le f.two f.ll).trans (le_of_eq ?_)
    simp only [hvlo, vQ, h.lo]
    push_cast
    ring
  have e2 : Wsq c.hi ≤ vhi := by
    refine (Wsq_le hh2 f.hl).trans (le_of_eq ?_)
    simp only [hvhi, vQ, h.hi]
    push_cast
    ring
  have := cell_bet_sq f.two hlt hlam e1 e2
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hgg : gc c ^ 2 * (c.hi - c.lo) = ((d.p : ℝ) / T) ^ 2 * (10 ^ 12 / ((d.b : ℝ) - d.a)) := by
    unfold gc
    rw [h.w, h.lo, h.hi]
    field_simp
  calc _ ≤ gc c ^ 2 * ((c.hi - c.lo) * ((d.lam : ℝ) / 2 ^ 32 / 2 + (vlo + vhi) / (4 * ((d.lam : ℝ) / 2 ^ 32)))) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
    _ = _ := by
        rw [← mul_assoc, hgg]
        simp only [GD.cg, hvlo, hvhi]
        push_cast
        ring

theorem G2_le {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T) :
    G2 l ≤ (G2I P T Q L : ℝ) / 2 ^ Q := by
  have hq : (0 : ℝ) < 2 ^ Q := by positivity
  induction h with
  | nil => simp [G2, G2I]
  | @cons c d l L hr hl ih =>
    have a := cell_G2 hr hT
    have e1 : G2 (c :: l) = gc c ^ 2 * (∫ θ in Th c.lo..Th c.hi, bet θ ^ 2) + G2 l := by simp [G2]
    have e2 : ((G2I P T Q (d :: L) : ℤ) : ℝ) = (d.cgI P T Q : ℝ) + (G2I P T Q L : ℝ) :=
      cast_sum_cons (GD.cgI P T Q) d L
    have f3 : ((d.cg P T : ℚ) : ℝ) * 2 ^ Q ≤ (d.cgI P T Q : ℝ) := ce_real _ Q
    have g3 : ((d.cg P T : ℚ) : ℝ) ≤ (d.cgI P T Q : ℝ) / 2 ^ Q := by
      rw [le_div_iff₀ hq]; linarith
    rw [e1, e2, add_div]
    linarith

end

end spec

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real MeasureTheory Filter Set intervalIntegral Topology
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceBound
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### Shifted Chebyshev polynomials in the monomial basis -/

theorem Pz_addZ (a b : List ℤ) (x : ℝ) : Pz (addZ a b) x = Pz a x + Pz b x := by
  induction a generalizing b with
  | nil => simp [addZ, Pz]
  | cons a t ih =>
    cases b with
    | nil => simp [addZ, Pz]
    | cons b r => simp only [addZ, Pz, ih]; push_cast; ring

theorem Pz_smulZ (a : ℤ) (b : List ℤ) (x : ℝ) : Pz (smulZ a b) x = (a : ℝ) * Pz b x := by
  induction b with
  | nil => simp [smulZ, Pz]
  | cons b t ih =>
    have : smulZ a (b :: t) = (a * b) :: smulZ a t := rfl
    rw [this]
    simp only [Pz, ih]; push_cast; ring

theorem Pz_continuous (L : List ℤ) : Continuous (Pz L) := by
  induction L with
  | nil => exact continuous_const
  | cons a t ih =>
    have : Pz (a :: t) = fun x => (a : ℝ) + x * Pz t x := rfl
    rw [this]; fun_prop

theorem len_addZ (a b : List ℤ) : (addZ a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [addZ]
  | cons a t ih =>
    cases b with
    | nil => simp [addZ]
    | cons b r => simp [addZ, ih]

theorem len_smulZ (a : ℤ) (b : List ℤ) : (smulZ a b).length = b.length := by simp [smulZ]

/-- `T_(n+2)(2x-1) = (4x-2) T_(n+1)(2x-1) - T_n(2x-1)` on coefficient lists. -/
def tNext (a b : List ℤ) : List ℤ :=
  addZ (addZ (0 :: smulZ 4 b) (smulZ (-2) b)) (smulZ (-1) a)

theorem Pz_tNext {a b : List ℤ} {k : ℕ} (ha : ∀ s, Pz a s = basis k (2 * s - 1))
    (hb : ∀ s, Pz b s = basis (k + 1) (2 * s - 1)) (s : ℝ) :
    Pz (tNext a b) s = basis (k + 2) (2 * s - 1) := by
  simp only [tNext, Pz_addZ, Pz_smulZ, Pz, ha, hb]
  rw [basis_add_two]
  push_cast
  ring

theorem len_tNext {a b : List ℤ} {k : ℕ} (ha : a.length ≤ k + 1) (hb : b.length ≤ k + 2) :
    (tNext a b).length ≤ k + 3 := by
  simp only [tNext, len_addZ, len_smulZ, List.length_cons]
  omega

theorem Pz_t0 (s : ℝ) : Pz [1] s = basis 0 (2 * s - 1) := by simp [Pz, basis_zero]
theorem Pz_t1 (s : ℝ) : Pz [-1, 2] s = basis 1 (2 * s - 1) := by
  simp only [Pz, basis_one']; push_cast; ring

noncomputable section

/-- Linear functional on a coefficient list. -/
def Mev (m : ℕ → ℝ) : List ℤ → ℕ → ℝ
  | [], _ => 0
  | a :: t, k => (a : ℝ) * m k + Mev m t (k + 1)

theorem Mev_add (m1 m2 : ℕ → ℝ) (L : List ℤ) (k : ℕ) :
    Mev (fun i => m1 i + m2 i) L k = Mev m1 L k + Mev m2 L k := by
  induction L generalizing k with
  | nil => simp [Mev]
  | cons a t ih => simp only [Mev, ih]; ring

theorem Mev_zero (L : List ℤ) (k : ℕ) : Mev (fun _ => 0) L k = 0 := by
  induction L generalizing k with
  | nil => simp [Mev]
  | cons a t ih => simp [Mev, ih]

theorem phys_cont_int {c : YCell} (h2 : 2 ≤ c.lo) {f : ℝ → ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun y => f (YCell.physX y)) volume c.lo c.hi :=
  (hf.comp_continuousOn (physX_continuousOn (lo := c.lo) (hi := c.hi) (Or.inl h2))).intervalIntegrable_of_Icc
    c.lo_lt.le

theorem phys_add {c : YCell} (h2 : 2 ≤ c.lo) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    c.phys (fun s => f s + g s) = c.phys f + c.phys g := by
  unfold YCell.phys YCell.avg
  rw [intervalIntegral.integral_add (phys_cont_int h2 hf) (phys_cont_int h2 hg)]
  ring

theorem phys_Pz {c : YCell} (h2 : 2 ≤ c.lo) (L : List ℤ) (k : ℕ) :
    c.phys (fun s => s ^ k * Pz L s) = Mev (fun i => c.phys fun s => s ^ i) L k := by
  induction L generalizing k with
  | nil =>
    have : (fun s : ℝ => s ^ k * Pz [] s) = fun s => (0 : ℝ) * s := by funext s; simp [Pz]
    rw [this, MomentSource.phys_const_mul]
    simp [Mev]
  | cons a t ih =>
    have e : (fun s : ℝ => s ^ k * Pz (a :: t) s) = fun s => (a : ℝ) * s ^ k + s ^ (k + 1) * Pz t s := by
      funext s; simp only [Pz]; ring
    have hc := Pz_continuous t
    rw [e, phys_add h2 (by fun_prop) (by fun_prop), MomentSource.phys_const_mul, ih]
    rfl

theorem physL_Pz {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (L : List ℤ) (k : ℕ) :
    physL l (fun s => s ^ k * Pz L s) = Mev (fun i => physL l fun s => s ^ i) L k := by
  induction l with
  | nil =>
    simp only [physL, List.map_nil, List.sum_nil]
    exact (Mev_zero L k).symm
  | cons c l ih =>
    have e1 : ∀ f, physL (c :: l) f = c.phys f + physL l f := fun f => by simp [physL]
    simp only [e1]
    rw [Mev_add, phys_Pz (h2 c (by simp)), ih fun d hd => h2 d (by simp [hd])]

theorem physL_TF {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {L : List ℤ} {n : ℕ}
    (h : ∀ s, Pz L s = basis n (2 * s - 1)) :
    physL l (TF n) = Mev (fun i => physL l fun s => s ^ i) L 0 := by
  rw [← physL_Pz h2 L 0]
  congr 1
  funext s
  simp [TF, h]

end

/-- Exact pairing with a value list. -/
def dotQ : List ℤ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: t, m :: ms => (a : ℚ) * m + dotQ t ms

/-- The error of the pairing. -/
def dotA : List ℤ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: t, d :: ds => |(a : ℚ)| * d + dotA t ds

theorem dot_close {m : ℕ → ℝ} : ∀ (L : List ℤ) (k : ℕ) (mL dL : List ℚ), CloseL m k mL dL →
    L.length ≤ mL.length → |Mev m L k - (dotQ L mL : ℝ)| ≤ (dotA L dL : ℝ)
  | [], k, mL, dL, _, _ => by simp [Mev, dotQ, dotA]
  | _ :: _, _, [], _, _, h => by simp at h
  | _ :: _, _, _ :: _, [], hc, _ => by simp [CloseL] at hc
  | a :: t, k, v :: vs, d :: ds, hc, h => by
    obtain ⟨h1, h2⟩ := hc
    have ih := dot_close t (k + 1) vs ds h2 (by simpa using h)
    simp only [Mev, dotQ, dotA]
    push_cast
    have e : (a : ℝ) * m k + Mev m t (k + 1) - ((a : ℝ) * (v : ℝ) + (dotQ t vs : ℝ)) =
        (a : ℝ) * (m k - v) + (Mev m t (k + 1) - dotQ t vs) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    gcongr

def muV (mL : List ℚ) : ℕ → List ℤ → List ℤ → List ℚ
  | 0, _, _ => []
  | n + 1, a, b => dotQ a mL :: muV mL n b (tNext a b)

def muE (dL : List ℚ) : ℕ → List ℤ → List ℤ → List ℚ
  | 0, _, _ => []
  | n + 1, a, b => dotA a dL :: muE dL n b (tNext a b)

theorem mu_close {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {mL dL : List ℚ}
    (hm : CloseL (fun i => physL l fun s => s ^ i) 0 mL dL) (n k : ℕ) (a b : List ℤ)
    (ha : ∀ s, Pz a s = basis k (2 * s - 1)) (hb : ∀ s, Pz b s = basis (k + 1) (2 * s - 1))
    (la : a.length ≤ k + 1) (lb : b.length ≤ k + 2) (hlen : k + n ≤ mL.length) :
    CloseL (fun i => physL l (TF i)) k (muV mL n a b) (muE dL n a b) := by
  induction n generalizing k a b with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · show |physL l (TF k) - _| ≤ _
      rw [physL_TF h2 ha]
      exact dot_close a 0 mL dL hm (by omega)
    · exact ih (k + 1) b (tNext a b) hb (fun s => Pz_tNext ha hb s) lb (len_tNext la lb) (by omega)

/-- Replace values and errors by shorter ones. -/
def relax : List ℚ → List ℚ → List ℚ → List ℚ → Bool
  | [], _, _, _ => true
  | _ :: _, [], _, _ => false
  | _ :: _, _ :: _, [], _ => false
  | _ :: _, _ :: _, _ :: _, [] => false
  | v :: vs, e :: es, w :: ws, f :: fs => decide (|v - w| + e ≤ f) && relax vs es ws fs

theorem relax_close {m : ℕ → ℝ} : ∀ (k : ℕ) (v e w f : List ℚ), CloseL m k v e → relax v e w f = true →
    v.length = w.length → CloseL m k w f
  | _, [], _, [], _, _, _, _ => by simp [CloseL]
  | _, [], _, _ :: _, _, _, _, hl => by simp at hl
  | _, _ :: _, [], _, _, _, h, _ => by simp [relax] at h
  | _, _ :: _, _ :: _, [], _, _, h, _ => by simp [relax] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, h, _ => by simp [relax] at h
  | k, v :: vs, e :: es, w :: ws, f :: fs, hc, h, hl => by
    obtain ⟨h1, h2⟩ := hc
    simp only [relax, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, relax_close (k + 1) vs es ws fs h2 h.2 (by simpa using hl)⟩
    have q : ((|v - w| + e : ℚ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast h.1
    push_cast at q
    calc |m k - (w : ℝ)| = |(m k - v) + ((v : ℝ) - w)| := by ring_nf
      _ ≤ |m k - v| + |(v : ℝ) - w| := abs_add_le _ _
      _ ≤ _ := by linarith

/-- Lower bound of a sum of squares. -/
def sqLow : List ℚ → List ℚ → ℚ
  | [], _ => 0
  | _ :: _, [] => 0
  | v :: vs, e :: es => (v ^ 2 - 2 * |v| * e) + sqLow vs es

theorem sq_ge {a v e : ℝ} (h : |a - v| ≤ e) : v ^ 2 - 2 * |v| * e ≤ a ^ 2 := by
  have h1 : a ^ 2 - v ^ 2 = (a - v) ^ 2 + 2 * v * (a - v) := by ring
  have h2 : -(2 * |v| * e) ≤ 2 * v * (a - v) := by
    have : |2 * v * (a - v)| ≤ 2 * |v| * e := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    exact (abs_le.mp this).1
  nlinarith [sq_nonneg (a - v)]

theorem sqLow_le {m : ℕ → ℝ} : ∀ (k : ℕ) (v e : List ℚ), CloseL m k v e →
    (sqLow v e : ℝ) ≤ ∑ i ∈ Finset.range v.length, (m (k + i)) ^ 2
  | _, [], _, _ => by simp [sqLow]
  | _, _ :: _, [], hc => by simp [CloseL] at hc
  | k, v :: vs, e :: es, hc => by
    obtain ⟨h1, h2⟩ := hc
    have ih := sqLow_le (k + 1) vs es h2
    simp only [sqLow, List.length_cons]
    rw [Finset.sum_range_succ']
    have h3 := sq_ge h1
    push_cast
    have e2 : ∑ i ∈ Finset.range vs.length, (m (k + (i + 1))) ^ 2 =
        ∑ i ∈ Finset.range vs.length, (m (k + 1 + i)) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by congr 2; omega
    rw [e2]
    simp only [add_zero]
    linarith

/-- Sum of a list. -/
def sumQ : List ℚ → ℚ
  | [] => 0
  | a :: t => a + sumQ t

theorem close_cheb {A : ℕ → ℝ} {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : ∀ (k : ℕ) (c e : List ℚ),
    CloseL A k c e → c.length = e.length →
    |∑ i ∈ Finset.range c.length, A (k + i) * basis (k + i) z - rawQ c k z| ≤ (sumQ e : ℝ)
  | k, [], [], _, _ => by simp [rawQ, sumQ]
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h
  | k, c :: cs, e :: es, hc, h => by
    obtain ⟨h1, h2⟩ := hc
    have ih := close_cheb hz (k + 1) cs es h2 (by simpa using h)
    have hb := abs_basis_le_one k hz
    rw [List.length_cons, Finset.sum_range_succ']
    have e1 : ∑ i ∈ Finset.range cs.length, A (k + (i + 1)) * basis (k + (i + 1)) z =
        ∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z :=
      Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]
    rw [e1]
    simp only [rawQ, sumQ, add_zero]
    have e2 : ∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z + A k * basis k z -
        ((c : ℝ) * basis k z + rawQ cs (k + 1) z) =
        (∑ i ∈ Finset.range cs.length, A (k + 1 + i) * basis (k + 1 + i) z - rawQ cs (k + 1) z) +
        (A k - c) * basis k z := by ring
    rw [e2]
    push_cast
    refine (abs_add_le _ _).trans ?_
    have h3 : |(A k - c) * basis k z| ≤ (e : ℝ) := by
      rw [abs_mul]
      have := abs_nonneg (A k - c)
      calc |A k - c| * |basis k z| ≤ |A k - c| * 1 := by gcongr
        _ ≤ _ := by linarith
    linarith

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail (hasDeriv_basis abs_U_le)
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

noncomputable section

/-! ### Chord errors -/

/-- `f` lies below its chord on `[b,a]` up to `e`. -/
def CE (f : ℝ → ℝ) (b a e : ℝ) : Prop :=
  ∀ x ∈ Icc b a, f x ≤ ((a - x) * f b + (x - b) * f a) / (a - b) + e

theorem CE.add {f g : ℝ → ℝ} {b a e1 e2 : ℝ} (hab : b < a) (h1 : CE f b a e1) (h2 : CE g b a e2) :
    CE (fun x => f x + g x) b a (e1 + e2) := by
  intro x hx
  have q1 := h1 x hx
  have q2 := h2 x hx
  have e : ((a - x) * (f b + g b) + (x - b) * (f a + g a)) / (a - b) =
      ((a - x) * f b + (x - b) * f a) / (a - b) + ((a - x) * g b + (x - b) * g a) / (a - b) := by
    rw [← add_div]; ring_nf
  simp only [e]
  linarith

theorem CE.congr {f g : ℝ → ℝ} {b a e : ℝ} (h : CE f b a e) (hb : b ≤ a) (hfg : ∀ x ∈ Icc b a, g x = f x) :
    CE g b a e := by
  intro x hx
  rw [hfg x hx, hfg b ⟨le_rfl, hb⟩, hfg a ⟨hb, le_rfl⟩]
  exact h x hx

theorem CE.mono {f : ℝ → ℝ} {b a e e' : ℝ} (h : CE f b a e) (he : e ≤ e') : CE f b a e' :=
  fun x hx => (h x hx).trans (by linarith)

theorem CE_const {b a : ℝ} (hab : b < a) (c : ℝ) : CE (fun _ => c) b a 0 := by
  intro x _
  have : a - b ≠ 0 := by linarith
  have e : ((a - x) * c + (x - b) * c) / (a - b) = c := by field_simp; ring
  simp only [e]
  linarith

theorem CE.const_mul {f : ℝ → ℝ} {b a e c : ℝ} (hab : b < a) (hc : 0 ≤ c) (h : CE f b a e) :
    CE (fun x => c * f x) b a (c * e) := by
  intro x hx
  have q := mul_le_mul_of_nonneg_left (h x hx) hc
  refine q.trans (le_of_eq ?_)
  have : a - b ≠ 0 := by linarith
  field_simp

theorem CE_of_deriv2 {f f' f'' : ℝ → ℝ} {b a M : ℝ} (hab : b < a) (hM0 : 0 ≤ M)
    (hf : ∀ x ∈ Icc b a, HasDerivAt f (f' x) x) (hf' : ∀ x ∈ Icc b a, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc b a, -M ≤ f'' x) : CE f b a (M * (a - b) ^ 2 / 8) := by
  set g : ℝ → ℝ := fun x => f x + M / 2 * ((x - b) * (x - a)) with hg
  have hconv : ConvexOn ℝ (Icc b a) g := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc b a)
      (f' := fun x => f' x + M / 2 * (2 * x - b - a)) (f'' := fun x => f'' x + M) ?_ ?_ ?_ ?_
    · intro x hx
      have := (hf x hx).continuousAt.continuousWithinAt (s := Icc b a)
      exact this.add (by fun_prop)
    · intro x hx
      have hx' := interior_subset hx
      have h2 : HasDerivAt (fun x : ℝ => M / 2 * ((x - b) * (x - a))) (M / 2 * (2 * x - b - a)) x := by
        have h := (((hasDerivAt_id x).sub_const b).mul ((hasDerivAt_id x).sub_const a)).const_mul (M / 2)
        refine h.congr_deriv ?_
        simp only [id]; ring
      exact ((hf x hx').add h2).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      have h2 : HasDerivAt (fun x : ℝ => M / 2 * (2 * x - b - a)) M x := by
        have h := ((((hasDerivAt_id x).const_mul 2).sub_const b).sub_const a).const_mul (M / 2)
        refine h.congr_deriv ?_
        ring
      exact ((hf' x hx').add h2).hasDerivWithinAt
    · intro x hx
      have := hM x (interior_subset hx)
      show 0 ≤ f'' x + M
      linarith
  intro x hx
  have hd : 0 < a - b := by linarith
  have a0 : 0 ≤ (a - x) / (a - b) := div_nonneg (by linarith [hx.2]) hd.le
  have b0 : 0 ≤ (x - b) / (a - b) := div_nonneg (by linarith [hx.1]) hd.le
  have ab : (a - x) / (a - b) + (x - b) / (a - b) = 1 := by field_simp; ring
  have := hconv.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) a0 b0 ab
  have e : ((a - x) / (a - b)) • b + ((x - b) / (a - b)) • a = x := by
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd.ne']
    ring
  rw [e] at this
  simp only [smul_eq_mul, hg] at this
  have e2 : (a - x) / (a - b) * (f b + M / 2 * ((b - b) * (b - a))) +
      (x - b) / (a - b) * (f a + M / 2 * ((a - b) * (a - a))) =
      ((a - x) * f b + (x - b) * f a) / (a - b) := by
    field_simp; ring
  rw [e2] at this
  have h3 : M / 2 * ((x - b) * (a - x)) ≤ M * (a - b) ^ 2 / 8 := by
    have : (x - b) * (a - x) ≤ (a - b) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
    nlinarith
  nlinarith

/-! ### Base terms -/

/-- `c (x/ρ)^n` with `(x/ρ)^n ≤ 1`: only a negative `c` costs anything. -/
theorem CE_zpow {c ρ b a : ℝ} {n : ℤ} (hb : 0 < b) (hab : b < a) (hρ : 0 < ρ)
    (hy : ∀ x ∈ Icc b a, (x / ρ) ^ n ≤ 1) :
    CE (fun x => c * (x / ρ) ^ n) b a
      (max (-c) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) := by
  have hnn : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have : 0 ≤ n * (n - 1) := by
      rcases le_or_gt n 0 with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
      · exact mul_nonneg h.le (by omega)
    exact_mod_cast this
  have hpos : ∀ x ∈ Icc b a, 0 < x := fun x hx => lt_of_lt_of_le hb hx.1
  set C := c * (ρ ^ n)⁻¹ with hC
  have hform : ∀ x, x ≠ 0 → c * (x / ρ) ^ n = C * x ^ n := by
    intro x _
    rw [div_zpow, hC]; ring
  have hmain : CE (fun x => C * x ^ n) b a
      (max (-c) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) := by
    refine CE_of_deriv2 (f' := fun x => C * ((n : ℝ) * x ^ (n - 1)))
      (f'' := fun x => C * ((n : ℝ) * (((n - 1 : ℤ) : ℝ) * x ^ (n - 1 - 1)))) hab (by positivity) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_zpow n x (Or.inl (hpos x hx).ne')).const_mul C
    · intro x hx
      exact ((hasDerivAt_zpow (n - 1) x (Or.inl (hpos x hx).ne')).const_mul (n : ℝ)).const_mul C
    · intro x hx
      have hx0 := hpos x hx
      have hyy := hy x hx
      have hy0 : 0 ≤ (x / ρ) ^ n := by positivity
      have e : C * ((n : ℝ) * (((n - 1 : ℤ) : ℝ) * x ^ (n - 1 - 1))) =
          c * ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) := by
        have : x ^ (n - 1 - 1) = x ^ n / x ^ 2 := by
          rw [show n - 1 - 1 = n - 2 by ring, zpow_sub₀ hx0.ne']
          norm_cast
        rw [this, div_zpow, hC]
        push_cast
        field_simp
      rw [e]
      have h1 : (x / ρ) ^ n / x ^ 2 ≤ 1 / b ^ 2 := by
        apply div_le_div₀ zero_le_one hyy (by positivity)
        have := hx.1
        gcongr
      have h0 : 0 ≤ (x / ρ) ^ n / x ^ 2 := by positivity
      rcases le_or_gt 0 c with hc | hc
      · have : 0 ≤ c * ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) := by positivity
        rw [max_eq_right (by linarith)]
        simp only [zero_mul, neg_zero]
        exact this
      · rw [max_eq_left (by linarith)]
        have h3 : ((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2) ≤
            ((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2) := by gcongr
        have h4 : -c * (((n : ℝ) * ((n : ℝ) - 1)) * ((x / ρ) ^ n / x ^ 2)) ≤
            -c * (((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
        have e5 : -c * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) =
            -c * (((n : ℝ) * ((n : ℝ) - 1)) * (1 / b ^ 2)) := by ring
        rw [e5]
        nlinarith
  exact hmain.congr hab.le fun x hx => hform x (hpos x hx).ne'

theorem CE_log {m b a : ℝ} (hm : 0 ≤ m) (hb : 0 < b) (hab : b < a) :
    CE (fun x => m * Real.log x) b a ((m / b ^ 2) * (a - b) ^ 2 / 8) := by
  have hpos : ∀ x ∈ Icc b a, 0 < x := fun x hx => lt_of_lt_of_le hb hx.1
  refine CE_of_deriv2 (f' := fun x => m * x⁻¹) (f'' := fun x => m * (-(x ^ 2)⁻¹)) hab (by positivity) ?_ ?_ ?_
  · intro x hx
    exact (Real.hasDerivAt_log (hpos x hx).ne').const_mul m
  · intro x hx
    have := (hasDerivAt_inv (hpos x hx).ne').const_mul m
    exact this
  · intro x hx
    have hx0 := hpos x hx
    have h1 : (x ^ 2)⁻¹ ≤ 1 / b ^ 2 := by
      rw [one_div]
      have := hx.1
      gcongr
    have : m * (x ^ 2)⁻¹ ≤ m * (1 / b ^ 2) := mul_le_mul_of_nonneg_left h1 hm
    have e : m / b ^ 2 = m * (1 / b ^ 2) := by ring
    rw [e]
    linarith

theorem CE_log1 {s b a : ℝ} (hs : 0 ≤ s) (hab : b < a) :
    CE (fun x => -s * Real.log (1 + x ^ 2)) b a ((2 * s) * (a - b) ^ 2 / 8) := by
  have hp : ∀ x : ℝ, 0 < 1 + x ^ 2 := fun x => by positivity
  refine CE_of_deriv2 (f' := fun x => -s * (2 * x / (1 + x ^ 2)))
    (f'' := fun x => -s * ((2 * (1 + x ^ 2) - 2 * x * (2 * x)) / (1 + x ^ 2) ^ 2)) hab (by positivity) ?_ ?_ ?_
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_add 1)
      refine this.congr_deriv ?_
      push_cast; ring
    exact (h1.log (hp x).ne').const_mul (-s)
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
      have := ((hasDerivAt_pow 2 x).const_add 1)
      refine this.congr_deriv ?_
      push_cast; ring
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
      have := (hasDerivAt_id x).const_mul 2
      refine this.congr_deriv ?_
      ring
    exact (h2.div h1 (hp x).ne').const_mul (-s)
  · intro x _
    have h3 : (2 * (1 + x ^ 2) - 2 * x * (2 * x)) / (1 + x ^ 2) ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    nlinarith

/-- Derivative of `U_n`. -/
def dU (n : ℕ) (z : ℝ) : ℝ :=
  (Polynomial.derivative (Polynomial.Chebyshev.U ℝ (n : ℤ))).eval z

theorem hasDeriv_U (n : ℕ) (z : ℝ) :
    HasDerivAt (fun z => (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval z) (dU n z) z :=
  (Polynomial.Chebyshev.U ℝ (n : ℤ)).hasDerivAt z

theorem dU_add_two (n : ℕ) (z : ℝ) :
    dU (n + 2) z = 2 * (((n : ℝ) + 2) * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z) + dU n z := by
  unfold dU
  have h := Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (n : ℤ)
  have hd := Polynomial.Chebyshev.T_derivative_eq_U (R := ℝ) ((n : ℤ) + 2)
  push_cast
  rw [h, Polynomial.derivative_add, Polynomial.derivative_mul, hd]
  simp only [Polynomial.derivative_ofNat, zero_mul, zero_add, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_intCast]
  have e : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by ring
  rw [e]
  simp

theorem abs_dU_le {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (n : ℕ) :
    |dU n z| ≤ ((n : ℝ) + 1) ^ 3 ∧ |dU (n + 1) z| ≤ ((n : ℝ) + 2) ^ 3 := by
  induction n with
  | zero =>
    constructor
    · simp [dU]
    · have : dU 1 z = 2 := by simp [dU, Polynomial.Chebyshev.U_one]
      rw [this]; norm_num
  | succ n ih =>
    refine ⟨by push_cast; convert ih.2 using 2; ring, ?_⟩
    rw [show n + 1 + 1 = n + 2 by ring, dU_add_two]
    have hU := abs_U_le hz (n + 1)
    have hn : (0 : ℝ) ≤ n := by positivity
    calc |2 * (((n : ℝ) + 2) * (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z) + dU n z|
        ≤ 2 * (((n : ℝ) + 2) * ((n : ℝ) + 2)) + ((n : ℝ) + 1) ^ 3 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
          have h1 : |(Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval z| ≤ (n : ℝ) + 2 := by
            refine hU.trans (le_of_eq ?_); push_cast; ring
          have := ih.1
          gcongr
      _ ≤ _ := by push_cast; nlinarith [hn, mul_nonneg hn hn, mul_nonneg (mul_nonneg hn hn) hn]

/-- The affine pullback of one Chebyshev term. -/
theorem CE_basis {c α β b a : ℝ} (n : ℕ) (hab : b < a) (hz : ∀ x ∈ Icc b a, α * x + β ∈ Icc (-1 : ℝ) 1) :
    CE (fun x => c * basis n (α * x + β)) b a ((|c| * (n : ℝ) ^ 4 * α ^ 2) * (a - b) ^ 2 / 8) := by
  rcases n with _ | n
  · have := CE_const hab c
    refine (this.congr hab.le fun x _ => by simp [basis_zero]).mono ?_
    simp
  have hin : ∀ x : ℝ, HasDerivAt (fun x => α * x + β) α x := fun x => by
    have := ((hasDerivAt_id x).const_mul α).add_const β
    refine this.congr_deriv ?_
    ring
  refine CE_of_deriv2 (f' := fun x => c * ((((n : ℝ) + 1) *
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (α * x + β)) * α))
    (f'' := fun x => c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α)) hab (by positivity) ?_ ?_ ?_
  · intro x _
    exact ((hasDeriv_basis n (α * x + β)).comp x (hin x)).const_mul c
  · intro x _
    have h1 := (hasDeriv_U n (α * x + β)).comp x (hin x)
    exact (((h1.const_mul ((n : ℝ) + 1))).mul_const α).const_mul c
  · intro x hx
    have hU := (abs_dU_le (hz x hx) n).1
    have hb : |c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α)| ≤
        |c| * (((n + 1 : ℕ) : ℝ)) ^ 4 * α ^ 2 := by
      have e : c * ((((n : ℝ) + 1) * (dU n (α * x + β) * α)) * α) =
          c * (((n : ℝ) + 1) * dU n (α * x + β)) * α ^ 2 := by ring
      rw [e, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1),
        abs_of_nonneg (sq_nonneg α)]
      have : ((n : ℝ) + 1) * |dU n (α * x + β)| ≤ (((n + 1 : ℕ) : ℝ)) ^ 4 := by
        push_cast
        calc ((n : ℝ) + 1) * |dU n (α * x + β)| ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ 3 := by gcongr
          _ = _ := by ring
      gcongr
    exact (abs_le.mp hb).1

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.MarkedSourceTail (basis_add_two basis_one')
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### Radial blocks -/

/-- One radial block: `M log max(x,ρ) + 2^-W Σ_j D_j ψ^(j+1)`. -/
structure Blk where
  rho : ℚ
  sg : ℚ
  M : ℚ
  D : List ℤ

/-- `Σ_j d_j y^(k+j+1)`. -/
noncomputable def polK : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | d :: t, k, y => (d : ℝ) * y ^ (k + 1) + polK t (k + 1) y

theorem polK_eq (y : ℝ) : ∀ (D : List ℤ) (k : ℕ), polK D k y = y ^ (k + 1) * Pz D y
  | [], _ => by simp [polK, Pz]
  | d :: t, k => by
    simp only [polK, Pz, polK_eq y t (k + 1)]
    ring

noncomputable def psiR (ρ x : ℝ) : ℝ := if ρ < x then ρ / x else x / ρ

noncomputable def blkF (W : ℕ) (B : Blk) (x : ℝ) : ℝ :=
  (B.M : ℝ) * Real.log (max x B.rho) + polK B.D 0 (psiR B.rho x) / 2 ^ W

/-- The negative part of the second-derivative weight of a block. -/
def S2 : List ℤ → ℕ → ℤ
  | [], _ => 0
  | d :: t, k => max (-d) 0 * (((k : ℤ) + 1) * ((k : ℤ) + 2)) + S2 t (k + 1)

theorem S2_nonneg : ∀ (D : List ℤ) (k : ℕ), 0 ≤ S2 D k
  | [], _ => le_rfl
  | d :: t, k => by
    have := S2_nonneg t (k + 1)
    have h1 : 0 ≤ max (-d) 0 := le_max_right _ _
    have : 0 ≤ max (-d) 0 * (((k : ℤ) + 1) * ((k : ℤ) + 2)) := by positivity
    simp only [S2]
    omega

noncomputable section

theorem CE_polK {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {ρ b a : ℝ} (hb : 0 < b) (hab : b < a) (hρ : 0 < ρ)
    (hy : ∀ x ∈ Icc b a, (x / ρ) ^ ε ≤ 1) : ∀ (D : List ℤ) (k : ℕ),
    CE (fun x => polK D k ((x / ρ) ^ ε)) b a (((S2 D k : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8)
  | [], k => by
    have := CE_const hab 0
    simpa [polK, S2] using this
  | d :: t, k => by
    have ih := CE_polK hε hb hab hρ hy t (k + 1)
    set n : ℤ := ε * ((k : ℤ) + 1) with hn
    have hpw : ∀ x ∈ Icc b a, ((x / ρ) ^ ε) ^ (k + 1) = (x / ρ) ^ n := by
      intro x _
      rw [hn, zpow_mul]
      norm_cast
    have h1 : ∀ x ∈ Icc b a, (x / ρ) ^ n ≤ 1 := by
      intro x hx
      rw [← hpw x hx]
      have h0 : 0 ≤ (x / ρ) ^ ε := by
        have : 0 < x := lt_of_lt_of_le hb hx.1
        positivity
      exact pow_le_one₀ h0 (hy x hx)
    have hz := CE_zpow (c := (d : ℝ)) hb hab hρ h1
    have hz' : CE (fun x => (d : ℝ) * ((x / ρ) ^ ε) ^ (k + 1)) b a
        (max (-(d : ℝ)) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8) :=
      hz.congr hab.le fun x hx => by rw [hpw x hx]
    have hsum := hz'.add hab ih
    refine (hsum.congr hab.le fun x _ => by simp only [polK]).mono ?_
    have hnn : (n : ℝ) * ((n : ℝ) - 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      have hk : (0 : ℝ) ≤ k := by positivity
      rcases hε with rfl | rfl
      · simp only [hn]; push_cast; nlinarith
      · simp only [hn]; push_cast; nlinarith
    have hS : ((S2 (d :: t) k : ℤ) : ℝ) =
        max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) + ((S2 t (k + 1) : ℤ) : ℝ) := by
      simp only [S2]
      push_cast
      ring
    rw [hS]
    have hm : 0 ≤ max (-(d : ℝ)) 0 := le_max_right _ _
    have hb2 : 0 < b ^ 2 := by positivity
    have hd2 : 0 ≤ (a - b) ^ 2 / 8 := by positivity
    have e1 : max (-(d : ℝ)) 0 * (((n : ℝ) * ((n : ℝ) - 1)) / b ^ 2) * (a - b) ^ 2 / 8 =
        (max (-(d : ℝ)) 0 * ((n : ℝ) * ((n : ℝ) - 1))) / b ^ 2 * ((a - b) ^ 2 / 8) := by ring
    have e2 : ((max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) + ((S2 t (k + 1) : ℤ) : ℝ))) / b ^ 2 *
        (a - b) ^ 2 / 8 = (max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) / b ^ 2 * ((a - b) ^ 2 / 8) +
        ((S2 t (k + 1) : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 := by ring
    rw [e1, e2]
    have : (max (-(d : ℝ)) 0 * ((n : ℝ) * ((n : ℝ) - 1))) / b ^ 2 * ((a - b) ^ 2 / 8) ≤
        (max (-(d : ℝ)) 0 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) / b ^ 2 * ((a - b) ^ 2 / 8) := by
      gcongr
    linarith

/-- Weight of one block on a cell. -/
def blkE (W : ℕ) (B : Blk) : ℝ := (B.M : ℝ) + ((S2 B.D 0 : ℤ) : ℝ) / 2 ^ W

theorem CE_blk (W : ℕ) (B : Blk) {b a : ℝ} (hb : 0 < b) (hab : b < a) (hρ : (0 : ℝ) < B.rho)
    (hM : (0 : ℝ) ≤ B.M) (hsep : (B.rho : ℝ) ≤ b ∨ a ≤ B.rho) :
    CE (blkF W B) b a (blkE W B / b ^ 2 * (a - b) ^ 2 / 8) := by
  have hq : (0 : ℝ) ≤ 1 / 2 ^ W := by positivity
  have hb2 : 0 < b ^ 2 := by positivity
  rcases hsep with h | h
  · have hpsi : ∀ x ∈ Icc b a, psiR B.rho x = (x / B.rho) ^ (-1 : ℤ) := by
      intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      unfold psiR
      split_ifs with hl
      · rw [zpow_neg_one, inv_div]
      · have : x = B.rho := le_antisymm (not_lt.mp hl) hxr
        rw [this, div_self hρ.ne']; simp
    have h1 := CE_log hM hb hab
    have hy : ∀ x ∈ Icc b a, (x / (B.rho : ℝ)) ^ (-1 : ℤ) ≤ 1 := by
      intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      have hx0 : 0 < x := lt_of_lt_of_le hb hx.1
      rw [zpow_neg_one, inv_div, div_le_one hx0]
      exact hxr
    have h2 := (CE_polK (Or.inr rfl) hb hab hρ hy B.D 0).const_mul hab hq
    refine ((h1.add hab h2).congr hab.le ?_).mono (le_of_eq ?_)
    · intro x hx
      have hxr : (B.rho : ℝ) ≤ x := h.trans hx.1
      simp only [blkF, max_eq_left hxr, hpsi x hx]
      ring
    · unfold blkE
      ring
  · have hpsi : ∀ x ∈ Icc b a, psiR B.rho x = (x / B.rho) ^ (1 : ℤ) := by
      intro x hx
      have hxr : x ≤ B.rho := hx.2.trans h
      unfold psiR
      rw [if_neg (not_lt.mpr hxr), zpow_one]
    have h1 := CE_const hab ((B.M : ℝ) * Real.log B.rho)
    have hy : ∀ x ∈ Icc b a, (x / (B.rho : ℝ)) ^ (1 : ℤ) ≤ 1 := by
      intro x hx
      rw [zpow_one, div_le_one hρ]
      exact hx.2.trans h
    have h2 := (CE_polK (Or.inl rfl) hb hab hρ hy B.D 0).const_mul hab hq
    refine (((h1.add hab h2).congr hab.le ?_).mono ?_)
    · intro x hx
      have hxr : x ≤ B.rho := hx.2.trans h
      simp only [blkF, max_eq_right hxr, hpsi x hx]
      ring
    · unfold blkE
      have hd : 0 ≤ (B.M : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 := by positivity
      have e : ((B.M : ℝ) + ((S2 B.D 0 : ℤ) : ℝ) / 2 ^ W) / b ^ 2 * (a - b) ^ 2 / 8 =
          (B.M : ℝ) / b ^ 2 * (a - b) ^ 2 / 8 +
            1 / 2 ^ W * (((S2 B.D 0 : ℤ) : ℝ) / b ^ 2 * (a - b) ^ 2 / 8) := by ring
      rw [e]
      linarith

def sumF (W : ℕ) (Bs : List Blk) (x : ℝ) : ℝ := (Bs.map fun B => blkF W B x).sum

def sumE (W : ℕ) (Bs : List Blk) : ℝ := (Bs.map fun B => blkE W B).sum

theorem CE_sum (W : ℕ) {b a : ℝ} (hb : 0 < b) (hab : b < a) : ∀ (Bs : List Blk),
    (∀ B ∈ Bs, (0 : ℝ) < B.rho ∧ (0 : ℝ) ≤ B.M ∧ ((B.rho : ℝ) ≤ b ∨ a ≤ B.rho)) →
    CE (sumF W Bs) b a (sumE W Bs / b ^ 2 * (a - b) ^ 2 / 8)
  | [], _ => by
    have := CE_const hab 0
    exact (this.congr hab.le fun x _ => by simp [sumF]).mono (by simp [sumE])
  | B :: t, h => by
    have h1 := h B (by simp)
    have ih := CE_sum W hb hab t fun B hB => h B (List.mem_cons_of_mem _ hB)
    have := (CE_blk W B hb hab h1.1 h1.2.1 h1.2.2).add hab ih
    refine (this.congr hab.le fun x _ => by simp [sumF]).mono (le_of_eq ?_)
    simp only [sumE, List.map_cons, List.sum_cons]
    ring

/-- Fourth-power weight of a Chebyshev list. -/
def mc4 : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: t, k => |c| * (k : ℚ) ^ 4 + mc4 t (k + 1)

theorem CE_rawQ {α β b a : ℝ} (hab : b < a) (hz : ∀ x ∈ Icc b a, α * x + β ∈ Icc (-1 : ℝ) 1) :
    ∀ (l : List ℚ) (k : ℕ),
    CE (fun x => -rawQ l k (α * x + β)) b a (((mc4 l k : ℚ) : ℝ) * α ^ 2 * (a - b) ^ 2 / 8)
  | [], k => by
    have := CE_const hab 0
    simpa [rawQ, mc4] using this
  | c :: t, k => by
    have ih := CE_rawQ hab hz t (k + 1)
    have h1 := CE_basis (c := -(c : ℝ)) k hab hz
    refine ((h1.add hab ih).congr hab.le fun x _ => ?_).mono (le_of_eq ?_)
    · simp only [rawQ]; ring
    · simp only [mc4]
      push_cast
      rw [abs_neg]
      ring

/-- The cover function. -/
structure Cov where
  W : ℕ
  Bs : List Blk
  s : ℚ
  Cl : List ℚ
  α : ℚ
  β : ℚ

def Cov.Phi (C : Cov) (x : ℝ) : ℝ :=
  sumF C.W C.Bs x + (-(C.s : ℝ) * Real.log (1 + x ^ 2)) + -rawQ C.Cl 0 ((C.α : ℝ) * x + C.β)

theorem Cov.CE (C : Cov) {b a : ℝ} (hb : 0 < b) (hab : b < a) (hs : (0 : ℝ) ≤ C.s)
    (hz : ∀ x ∈ Icc b a, (C.α : ℝ) * x + C.β ∈ Icc (-1 : ℝ) 1)
    (h : ∀ B ∈ C.Bs, (0 : ℝ) < B.rho ∧ (0 : ℝ) ≤ B.M ∧ ((B.rho : ℝ) ≤ b ∨ a ≤ B.rho)) :
    OrdHf.CE C.Phi b a ((a - b) ^ 2 / 8 * (sumE C.W C.Bs / b ^ 2 + (2 * (C.s : ℝ) +
      ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2))) := by
  have h1 := CE_sum C.W hb hab C.Bs h
  have h2 := CE_log1 hs hab
  have h3 := CE_rawQ hab hz C.Cl 0
  refine (((h1.add hab h2).add hab h3).congr hab.le fun x _ => rfl).mono (le_of_eq ?_)
  ring

theorem CE.le_max {f : ℝ → ℝ} {b a e vb va : ℝ} (hab : b < a) (h : OrdHf.CE f b a e)
    (hb : f b ≤ vb) (ha : f a ≤ va) : ∀ x ∈ Icc b a, f x ≤ max va vb + e := by
  intro x hx
  have q := h x hx
  have hd : 0 < a - b := by linarith
  have h1 : (a - x) * f b ≤ (a - x) * max va vb :=
    mul_le_mul_of_nonneg_left (hb.trans (le_max_right _ _)) (by linarith [hx.2])
  have h2 : (x - b) * f a ≤ (x - b) * max va vb :=
    mul_le_mul_of_nonneg_left (ha.trans (le_max_left _ _)) (by linarith [hx.1])
  have h3 : ((a - x) * f b + (x - b) * f a) / (a - b) ≤ max va vb := by
    rw [div_le_iff₀ hd]
    nlinarith
  linarith

end

/-! ### Node values -/

/-- `⌈p t / q⌉` Horner with rounding up. -/
def hU (p q : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: t => d + -((-(p * hU p q t)) / q)

theorem hU_spec {p q : ℤ} (hp : 0 ≤ p) (hq : 0 < q) : ∀ D : List ℤ,
    Pz D ((p : ℝ) / q) ≤ (hU p q D : ℝ)
  | [] => by simp [Pz, hU]
  | d :: t => by
    have ih := hU_spec hp hq t
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have h1 : (-(p * hU p q t)) / q * q ≤ -(p * hU p q t) := by
      have := Int.mul_ediv_add_emod (-(p * hU p q t)) q
      have h2 := Int.emod_nonneg (-(p * hU p q t)) hq.ne'
      nlinarith
    have h1' : (((-(p * hU p q t)) / q : ℤ) : ℝ) * q ≤ -((p : ℝ) * (hU p q t : ℝ)) := by
      exact_mod_cast h1
    simp only [Pz, hU]
    push_cast
    have h3 : (p : ℝ) / q * Pz t ((p : ℝ) / q) ≤ -(((-(p * hU p q t)) / q : ℤ) : ℝ) := by
      calc (p : ℝ) / q * Pz t ((p : ℝ) / q) ≤ (p : ℝ) / q * (hU p q t : ℝ) := by gcongr
        _ ≤ _ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hq']
          linarith
    push_cast at h3
    linarith

/-- Rational forward Chebyshev evaluation. -/
def evT (z : ℚ) : ℚ → ℚ → List ℚ → ℚ
  | _, _, [] => 0
  | t0, t1, c :: l => c * t0 + evT z t1 (2 * z * t1 - t0) l

theorem evT_spec (z : ℚ) : ∀ (l : List ℚ) (k : ℕ) (t0 t1 : ℚ),
    (t0 : ℝ) = basis k z → (t1 : ℝ) = basis (k + 1) z →
    ((evT z t0 t1 l : ℚ) : ℝ) = rawQ l k z
  | [], _, _, _, _, _ => by simp [evT, rawQ]
  | c :: l, k, t0, t1, h0, h1 => by
    have := evT_spec z l (k + 1) t1 (2 * z * t1 - t0) h1 (by
      rw [show k + 1 + 1 = k + 2 by ring, basis_add_two]
      push_cast
      rw [h0, h1])
    simp only [evT, rawQ]
    push_cast
    rw [this, h0]

/-- `log x` enclosure from `Cert.WLog`; a failed call has negative error. -/
def logE (x : ℚ) : ℚ × ℚ :=
  match CatalanMeasure.WLog.expPQ x.num.toNat x.den with
  | some (m, P, Q) =>
    match CatalanMeasure.WLog.lnQP 6 m P Q with
    | some r => r
    | none => (0, -1)
  | none => (0, -1)

theorem logE_spec {x : ℚ} (hx : 0 < x) (he : 0 ≤ (logE x).2) :
    |Real.log x - ((logE x).1 : ℝ)| ≤ ((logE x).2 : ℝ) := by
  unfold logE at he ⊢
  split at he
  · rename_i m P Q h1
    split at he
    · rename_i r h2
      first | rw [h2] | skip
      obtain ⟨hQ, h3, h4, h5⟩ := CatalanMeasure.WLog.expPQ_spec h1
      have := CatalanMeasure.WLog.lnQP_spec (v := r.1) (e := r.2) hQ h3 h4 (by simpa using h2)
      rw [← h5] at this
      have hn : ((x.num.toNat : ℕ) : ℝ) = (x.num : ℝ) := by
        have : ((x.num.toNat : ℕ) : ℤ) = x.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx.le)
        exact_mod_cast this
      have hxr : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
        have := Rat.num_div_den x
        conv_lhs => rw [← this]
        push_cast
        rfl
      rw [hn, ← hxr] at this
      simpa using this
    · simp at he; norm_num at he
  · simp at he; norm_num at he

def logHi (x : ℚ) : ℚ := (logE x).1 + (logE x).2
def logLo (x : ℚ) : ℚ := (logE x).1 - (logE x).2

/-- Node value of a block, given an upper bound `Lx` for `log x`. -/
def blkV (W : ℕ) (x Lx : ℚ) (B : Blk) : ℚ :=
  if B.rho < x then
    let y := B.rho / x
    B.M * Lx + y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W
  else
    let y := x / B.rho
    B.M * B.sg + y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W

def sumV (W : ℕ) (x Lx : ℚ) : List Blk → ℚ
  | [] => 0
  | B :: t => blkV W x Lx B + sumV W x Lx t

def Cov.evC (C : Cov) (x : ℚ) : ℚ := evT (C.α * x + C.β) 1 (C.α * x + C.β) C.Cl

def Cov.V (C : Cov) (x : ℚ) : ℚ :=
  sumV C.W x (logHi x) C.Bs + -C.s * logLo (1 + x ^ 2) +
    -C.evC x

/-- A node is valid when both logarithm calls succeeded and the value is below `v`. -/
def Cov.nodeOK (C : Cov) (n : ℚ × ℚ) : Bool :=
  decide (0 ≤ (logE n.1).2) && decide (0 ≤ (logE (1 + n.1 ^ 2)).2) && decide (C.V n.1 ≤ n.2)

noncomputable section

theorem blkV_spec (W : ℕ) {x Lx : ℚ} (B : Blk) (hx : 0 < x) (hL : Real.log x ≤ Lx) (hρ : 0 < B.rho)
    (hM : 0 ≤ B.M) (hsg : Real.log B.rho ≤ B.sg) : blkF W B x ≤ ((blkV W x Lx B : ℚ) : ℝ) := by
  have hq : (0 : ℝ) < 2 ^ W := by positivity
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have hρr : (0 : ℝ) < B.rho := by exact_mod_cast hρ
  have hMr : (0 : ℝ) ≤ B.M := by exact_mod_cast hM
  have key : ∀ y : ℚ, 0 ≤ y → (y : ℝ) ≤ 1 → polK B.D 0 (y : ℝ) / 2 ^ W ≤
      (((y * (hU y.num (y.den : ℤ) B.D : ℚ) / 2 ^ W : ℚ)) : ℝ) := by
    intro y hy _
    have hyr : (0 : ℝ) ≤ y := by exact_mod_cast hy
    have h1 := hU_spec (p := y.num) (q := (y.den : ℤ)) (Rat.num_nonneg.mpr hy)
      (by exact_mod_cast y.den_pos) B.D
    have hyy : ((y.num : ℤ) : ℝ) / (((y.den : ℤ)) : ℝ) = y := by
      have := Rat.num_div_den y
      conv_rhs => rw [← this]
      push_cast
      rfl
    rw [hyy] at h1
    rw [polK_eq]
    have h2 := mul_le_mul_of_nonneg_left h1 hyr
    simp only [zero_add, pow_one]
    push_cast
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr h2
  unfold blkF blkV
  by_cases h : B.rho < x
  · have hr : (B.rho : ℝ) < x := by exact_mod_cast h
    have hps : psiR B.rho x = ((B.rho / x : ℚ) : ℝ) := by
      unfold psiR
      rw [if_pos hr]
      push_cast
      rfl
    rw [if_pos h, max_eq_left hr.le, hps]
    have := key (B.rho / x) (by positivity) (by push_cast; rw [div_le_one hxr]; exact hr.le)
    have h2 := mul_le_mul_of_nonneg_left hL hMr
    simp only
    push_cast at this ⊢
    linarith
  · have hr : (x : ℝ) ≤ B.rho := by exact_mod_cast not_lt.mp h
    have hps : psiR B.rho x = ((x / B.rho : ℚ) : ℝ) := by
      unfold psiR
      rw [if_neg (not_lt.mpr hr)]
      push_cast
      rfl
    rw [if_neg h, max_eq_right hr, hps]
    have := key (x / B.rho) (by positivity) (by push_cast; rw [div_le_one hρr]; exact hr)
    have h2 := mul_le_mul_of_nonneg_left hsg hMr
    simp only
    push_cast at this ⊢
    linarith

theorem sumV_spec (W : ℕ) {x Lx : ℚ} (hx : 0 < x) (hL : Real.log x ≤ Lx) : ∀ (Bs : List Blk),
    (∀ B ∈ Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) →
    sumF W Bs x ≤ ((sumV W x Lx Bs : ℚ) : ℝ)
  | [], _ => by simp [sumF, sumV]
  | B :: t, h => by
    have h1 := h B (by simp)
    have ih := sumV_spec W hx hL t fun B hB => h B (List.mem_cons_of_mem _ hB)
    have := blkV_spec W B hx hL h1.1 h1.2.1 h1.2.2
    simp only [sumF, sumV, List.map_cons, List.sum_cons] at ih ⊢
    push_cast
    linarith

theorem Cov.node_le (C : Cov) {n : ℚ × ℚ} (hx : 0 < n.1) (h : C.nodeOK n = true) (hs : 0 ≤ C.s)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg) :
    C.Phi n.1 ≤ n.2 := by
  simp only [Cov.nodeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have l1 := abs_le.mp (logE_spec hx h1)
  have hy : 0 < 1 + n.1 ^ 2 := by positivity
  have l2 := abs_le.mp (logE_spec hy h2)
  have hL : Real.log n.1 ≤ logHi n.1 := by
    unfold logHi; push_cast; linarith [l1.2]
  have hS : ((logLo (1 + n.1 ^ 2) : ℚ) : ℝ) ≤ Real.log (1 + (n.1 : ℝ) ^ 2) := by
    unfold logLo
    have := l2.1
    push_cast at this ⊢
    linarith
  have h4 := sumV_spec C.W hx hL C.Bs hB
  have hsr : (0 : ℝ) ≤ C.s := by exact_mod_cast hs
  have h5 := mul_le_mul_of_nonneg_left hS hsr
  have hz : ((C.evC n.1 : ℚ) : ℝ) = rawQ C.Cl 0 ((C.α : ℝ) * n.1 + C.β) := by
    have := evT_spec (C.α * n.1 + C.β) C.Cl 0 1 (C.α * n.1 + C.β)
      (by simp [basis_zero]) (by push_cast; rw [basis_one'])
    push_cast at this
    exact this
  have h3' : ((C.V n.1 : ℚ) : ℝ) ≤ n.2 := by exact_mod_cast h3
  unfold Cov.V at h3'
  unfold Cov.Phi
  push_cast at h3' hz
  rw [← hz]

  linarith

/-- The bottom node. -/
def bot : ℚ × ℚ → List (ℚ × ℚ) → ℚ
  | n, [] => n.1
  | _, m :: t => bot m t

/-- Consecutive nodes: separation from every radius, range of the Chebyshev variable, and the
chord bound. -/
def Cov.chain (C : Cov) (E K Bud : ℚ) : ℚ × ℚ → List (ℚ × ℚ) → Bool
  | n, [] => decide (n.2 ≤ Bud)
  | a, b :: t =>
    decide (0 < b.1) && decide (b.1 < a.1) && decide (-1 ≤ C.α * b.1 + C.β) &&
    decide (C.α * a.1 + C.β ≤ 1) &&
    C.Bs.all (fun B => decide (B.rho ≤ b.1) || decide (a.1 ≤ B.rho)) &&
    decide (max a.2 b.2 + (a.1 - b.1) ^ 2 / 8 * (E / b.1 ^ 2 + K) ≤ Bud) &&
    Cov.chain C E K Bud b t

theorem Cov.cover (C : Cov) {E K Bud : ℚ} (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumE C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) :
    ∀ (t : List (ℚ × ℚ)) (n : ℚ × ℚ), 0 < n.1 → C.chain E K Bud n t = true →
      (∀ m ∈ n :: t, C.nodeOK m = true) →
      ∀ x ∈ Icc ((bot n t : ℚ) : ℝ) n.1, C.Phi x ≤ Bud
  | [], n, h0, hc, hn => by
    intro x hx
    have hxe : x = n.1 := le_antisymm hx.2 hx.1
    have h1 := C.node_le h0 (hn n (by simp)) hs hB
    have h2 : (n.2 : ℝ) ≤ Bud := by
      have : n.2 ≤ Bud := by simpa [Cov.chain] using hc
      exact_mod_cast this
    rw [hxe]
    linarith
  | b :: t, a, h0, hc, hn => by
    simp only [Cov.chain, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      Bool.or_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨⟨hb0, hba⟩, hz1⟩, hz2⟩, hsep⟩, hmax⟩, hrest⟩ := hc
    have ih := Cov.cover C hs hα hB hE hK t b hb0 hrest fun m hm => hn m (List.mem_cons_of_mem _ hm)
    intro x hx
    rcases le_or_gt (b.1 : ℝ) x with hxb | hxb
    · have hb0' : (0 : ℝ) < b.1 := by exact_mod_cast hb0
      have hba' : (b.1 : ℝ) < a.1 := by exact_mod_cast hba
      have hαr : (0 : ℝ) ≤ C.α := by exact_mod_cast hα
      have hz : ∀ y ∈ Icc (b.1 : ℝ) a.1, (C.α : ℝ) * y + C.β ∈ Icc (-1 : ℝ) 1 := by
        intro y hy
        have g1 : (-1 : ℝ) ≤ C.α * b.1 + C.β := by exact_mod_cast hz1
        have g2 : (C.α : ℝ) * a.1 + C.β ≤ 1 := by exact_mod_cast hz2
        have g3 := mul_le_mul_of_nonneg_left hy.1 hαr
        have g4 := mul_le_mul_of_nonneg_left hy.2 hαr
        constructor <;> linarith
      have hsr : (0 : ℝ) ≤ C.s := by exact_mod_cast hs
      have hce := C.CE hb0' hba' hsr hz fun B hBm => by
        obtain ⟨p1, p2, _⟩ := hB B hBm
        refine ⟨by exact_mod_cast p1, by exact_mod_cast p2, ?_⟩
        rcases hsep B hBm with q | q
        · left; exact_mod_cast q
        · right; exact_mod_cast q
      have hva := C.node_le h0 (hn a (by simp)) hs hB
      have hvb := C.node_le hb0 (hn b (by simp)) hs hB
      have hfin := CE.le_max hba' hce hvb hva x ⟨hxb, hx.2⟩
      have hmax' : (max (a.2 : ℝ) b.2) + ((a.1 : ℝ) - b.1) ^ 2 / 8 * ((E : ℝ) / (b.1 : ℝ) ^ 2 + K) ≤ Bud := by
        exact_mod_cast hmax
      have hE' : sumE C.W C.Bs ≤ (E : ℝ) := hE
      have hK' : 2 * (C.s : ℝ) + ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2 ≤ K := by exact_mod_cast hK
      have : ((a.1 : ℝ) - b.1) ^ 2 / 8 * (sumE C.W C.Bs / (b.1 : ℝ) ^ 2 + (2 * (C.s : ℝ) +
          ((mc4 C.Cl 0 : ℚ) : ℝ) * (C.α : ℝ) ^ 2)) ≤
          ((a.1 : ℝ) - b.1) ^ 2 / 8 * ((E : ℝ) / (b.1 : ℝ) ^ 2 + K) := by
        gcongr
      linarith
    · exact ih x ⟨hx.1, hxb.le⟩

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs (abs_pow_sub_pow_le_unit)

noncomputable section

/-! ### Grouping the auxiliary list by radius -/

/-- The cosine moment of radius class `i`. -/
def aC (l : List AuxEntry) (i k : ℕ) : ℝ :=
  (l.map fun e => if e.rad = i then e.w * Real.cos ((k : ℝ) * e.phase) else 0).sum

theorem aC_cons (e : AuxEntry) (t : List AuxEntry) (i k : ℕ) :
    aC (e :: t) i k = (if e.rad = i then e.w * Real.cos ((k : ℝ) * e.phase) else 0) + aC t i k := by
  simp [aC]

theorem group_sum (n K : ℕ) (L : ℕ → ℝ) (f : ℕ → ℕ → ℝ) : ∀ l : List AuxEntry, (∀ e ∈ l, e.rad < n) →
    (l.map fun e => e.w * (L e.rad +
        ∑ k ∈ Finset.range K, f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase))).sum =
      ∑ i ∈ Finset.range n, (aC l i 0 * L i + ∑ k ∈ Finset.range K, f i (k + 1) * aC l i (k + 1))
  | [], _ => by simp [aC]
  | e :: t, h => by
    have ih := group_sum n K L f t fun e he => h e (List.mem_cons_of_mem _ he)
    have hlt : e.rad < n := h e (by simp)
    have key : ∀ i, aC (e :: t) i 0 * L i +
        ∑ k ∈ Finset.range K, f i (k + 1) * aC (e :: t) i (k + 1) =
        (if e.rad = i then e.w * (L e.rad + ∑ k ∈ Finset.range K,
            f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) else 0) +
        (aC t i 0 * L i + ∑ k ∈ Finset.range K, f i (k + 1) * aC t i (k + 1)) := by
      intro i
      simp only [aC_cons]
      split_ifs with hi
      · subst hi
        simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, mul_add, add_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
        have : ∑ k ∈ Finset.range K, f e.rad (k + 1) * (e.w * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) =
            ∑ k ∈ Finset.range K, e.w * (f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) :=
          Finset.sum_congr rfl fun k _ => by ring
        rw [this]
        ring
      · simp
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.sum_congr rfl fun i _ => key i]
    generalize e.w * (L e.rad + ∑ k ∈ Finset.range K,
      f e.rad (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase)) = X
    have h2 : ∑ i ∈ Finset.range n, (if e.rad = i then X else 0) = X := by
      rw [Finset.sum_ite_eq (Finset.range n) e.rad, if_pos (Finset.mem_range.mpr hlt)]
    conv_rhs => rw [Finset.sum_add_distrib, h2]

theorem psi_pos (r : ℝ) {x : ℝ} (hx : 0 < x) : psi r x = psiR r x := by
  unfold psi psiR
  rw [abs_of_pos hx]

theorem psi_neg (r : ℝ) {u : ℝ} (hu : 0 < u) : psi r (-u) = -psiR r u := by
  unfold psi psiR
  rw [abs_neg, abs_of_pos hu]
  split_ifs <;> ring

theorem radialA_pos (S : CapSource) (K n : ℕ) {x : ℝ} (hx : 0 < x)
    (hl : ∀ e ∈ S.aux Sign.pos, e.rad < n) :
    S.radialA (Trunc.finite K) Sign.pos x = ∑ i ∈ Finset.range n,
      (aC (S.aux Sign.pos) i 0 * Real.log (max x (S.rad i)) +
        ∑ k ∈ Finset.range K, S.coef (k + 1) * psiR (S.rad i) x ^ (k + 1) * aC (S.aux Sign.pos) i (k + 1)) := by
  rw [← group_sum n K (fun i => Real.log (max x (S.rad i)))
    (fun i k => S.coef k * psiR (S.rad i) x ^ k) _ hl]
  unfold radialA
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp [Trunc.sum, abs_of_pos hx, psi_pos _ hx]

theorem radialA_neg (S : CapSource) (K n : ℕ) {u : ℝ} (hu : 0 < u)
    (hl : ∀ e ∈ S.aux Sign.neg, e.rad < n) :
    S.radialA (Trunc.finite K) Sign.neg (-u) = ∑ i ∈ Finset.range n,
      (aC (S.aux Sign.neg) i 0 * Real.log (max u (S.rad i)) +
        ∑ k ∈ Finset.range K, ((-1) ^ (k + 1) * S.coef (k + 1)) *
          (psiR (S.rad i) u ^ (k + 1) + (S.rad i * u) ^ (k + 1)) * aC (S.aux Sign.neg) i (k + 1)) := by
  rw [← group_sum n K (fun i => Real.log (max u (S.rad i)))
    (fun i k => ((-1) ^ k * S.coef k) * (psiR (S.rad i) u ^ k + (S.rad i * u) ^ k)) _ hl]
  unfold radialA
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Trunc.sum, abs_neg, abs_of_pos hu, if_true]
  have key : ∀ k : ℕ, S.coef (k + 1) * psi (S.rad e.rad) (-u) ^ (k + 1) *
        Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) +
      S.coef (k + 1) * (S.rad e.rad * -u) ^ (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) =
      (-1) ^ (k + 1) * S.coef (k + 1) * (psiR (S.rad e.rad) u ^ (k + 1) + (S.rad e.rad * u) ^ (k + 1)) *
        Real.cos (((k + 1 : ℕ) : ℝ) * e.phase) := by
    intro k
    rw [psi_neg _ hu, neg_pow, mul_neg, neg_pow (S.rad e.rad * u)]
    ring
  rw [add_assoc, ← Finset.sum_add_distrib (s := Finset.range K)]
  exact congrArg (fun z => e.w * (Real.log (max u (S.rad e.rad)) + z))
    (Finset.sum_congr rfl fun k _ => key k)

/-! ### One radial series against one block list -/

/-- `Σ_{j<m} t(k+j+1) y^(k+j+1)`. -/
def serR (t : ℕ → ℝ) (y : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | k, m + 1 => t (k + 1) * y ^ (k + 1) + serR t y (k + 1) m

theorem serR_eq (t : ℕ → ℝ) (y : ℝ) (m : ℕ) :
    serR t y 0 m = ∑ k ∈ Finset.range m, t (k + 1) * y ^ (k + 1) := by
  have : ∀ (m k : ℕ), serR t y k m = ∑ j ∈ Finset.range m, t (k + j + 1) * y ^ (k + j + 1) := by
    intro m
    induction m with
    | zero => intro k; rfl
    | succ m ih =>
      intro k
      rw [serR, ih, Finset.sum_range_succ']
      simp only [add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show k + 1 + j + 1 = k + (j + 1) + 1 by ring]
  simpa using this m 0

/-- Closeness of an integer list to a sequence. -/
def CLz (t : ℕ → ℝ) (sc e : ℝ) : ℕ → List ℤ → Prop
  | _, [] => True
  | k, d :: D => |t (k + 1) - (d : ℝ) / sc| ≤ e ∧ CLz t sc e (k + 1) D

/-- `ℓ¹` norm of an integer list. -/
def abs1 : List ℤ → ℤ
  | [] => 0
  | d :: t => |d| + abs1 t

theorem abs1_nonneg : ∀ l : List ℤ, 0 ≤ abs1 l
  | [] => le_rfl
  | d :: t => by
    have := abs1_nonneg t
    have := abs_nonneg d
    simp only [abs1]
    omega

/-- The first `n` entries, shortened by `sh` bits. -/
def truncD (sh n : ℕ) (F : List ℤ) : List ℤ := (F.take n).map (· / 2 ^ sh)

theorem floor_close (d : ℤ) (W sh : ℕ) :
    |(d : ℝ) / 2 ^ (W + sh) - ((d / 2 ^ sh : ℤ) : ℝ) / 2 ^ W| ≤ 1 / 2 ^ W := by
  have hs : (0 : ℤ) < 2 ^ sh := by positivity
  have h1 : d / 2 ^ sh * 2 ^ sh ≤ d := Int.ediv_mul_le d hs.ne'
  have h2 : d < (d / 2 ^ sh + 1) * 2 ^ sh := by
    have := Int.lt_ediv_add_one_mul_self d hs
    exact this
  have hs' : (0 : ℝ) < 2 ^ sh := by positivity
  have hw : (0 : ℝ) < 2 ^ W := by positivity
  have h1' : ((d / 2 ^ sh : ℤ) : ℝ) * 2 ^ sh ≤ d := by exact_mod_cast h1
  have h2' : (d : ℝ) < (((d / 2 ^ sh : ℤ) : ℝ) + 1) * 2 ^ sh := by exact_mod_cast h2
  have e : (d : ℝ) / 2 ^ (W + sh) = (d : ℝ) / 2 ^ sh / 2 ^ W := by
    rw [pow_add]; field_simp
  rw [e, ← sub_div, abs_div, abs_of_pos hw]
  apply div_le_div_of_nonneg_right _ hw.le
  rw [abs_le]
  constructor
  · have : ((d / 2 ^ sh : ℤ) : ℝ) ≤ (d : ℝ) / 2 ^ sh := by rw [le_div_iff₀ hs']; exact h1'
    linarith
  · have : (d : ℝ) / 2 ^ sh < ((d / 2 ^ sh : ℤ) : ℝ) + 1 := by rw [div_lt_iff₀ hs']; exact h2'
    linarith

theorem ser_le {t : ℕ → ℝ} {y yh η e : ℝ} (W sh K : ℕ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hh0 : 0 ≤ yh) (hh1 : yh ≤ 1) (hη : |y - yh| ≤ η) (he : 0 ≤ e) :
    ∀ (F : List ℤ) (n k : ℕ), CLz t (2 ^ (W + sh)) e k F → k + F.length ≤ K →
    serR t y k F.length ≤ polK (truncD sh n F) k yh / 2 ^ W +
      (((abs1 (F.drop n) : ℤ) : ℝ) / 2 ^ (W + sh) + (F.length : ℝ) * (e + 1 / 2 ^ W) +
        ((abs1 (truncD sh n F) : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * η))
  | [], n, k, _, _ => by
    simp [serR, truncD, polK, abs1]
  | d :: F, 0, k, hc, hk => by
    obtain ⟨h1, h2⟩ := hc
    have ih := ser_le W sh K hy0 hy1 hh0 hh1 hη he F 0 (k + 1) h2 (by simp at hk; omega)
    simp only [truncD, List.take_zero, List.map_nil, polK, zero_div, zero_add, abs1, Int.cast_zero,
      zero_mul, add_zero, List.drop_zero] at ih ⊢
    rw [List.length_cons, serR]
    have hsc : (0 : ℝ) < 2 ^ (W + sh) := by positivity
    have hw : (0 : ℝ) ≤ 1 / 2 ^ W := by positivity
    have hp0 : 0 ≤ y ^ (k + 1) := by positivity
    have hp1 : y ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have ht : |t (k + 1)| ≤ |(d : ℝ)| / 2 ^ (W + sh) + e := by
      have q := abs_le.mp h1
      have : |(d : ℝ) / 2 ^ (W + sh)| = |(d : ℝ)| / 2 ^ (W + sh) := by rw [abs_div, abs_of_pos hsc]
      rw [← this]
      have r := abs_sub_abs_le_abs_sub (t (k + 1)) ((d : ℝ) / 2 ^ (W + sh))
      linarith
    have h3 : t (k + 1) * y ^ (k + 1) ≤ |(d : ℝ)| / 2 ^ (W + sh) + e := by
      calc t (k + 1) * y ^ (k + 1) ≤ |t (k + 1)| * y ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hp0
        _ ≤ |t (k + 1)| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
        _ ≤ _ := by linarith
    push_cast
    have e1 : (|(d : ℝ)| + ((abs1 F : ℤ) : ℝ)) / 2 ^ (W + sh) =
        |(d : ℝ)| / 2 ^ (W + sh) + ((abs1 F : ℤ) : ℝ) / 2 ^ (W + sh) := add_div _ _ _
    rw [e1]
    nlinarith
  | d :: F, n + 1, k, hc, hk => by
    obtain ⟨h1, h2⟩ := hc
    have ih := ser_le W sh K hy0 hy1 hh0 hh1 hη he F n (k + 1) h2 (by simp at hk; omega)
    have hD : truncD sh (n + 1) (d :: F) = (d / 2 ^ sh) :: truncD sh n F := by simp [truncD]
    rw [hD, List.drop_succ_cons, List.length_cons, serR]
    simp only [polK, abs1]
    set d' := d / 2 ^ sh with hd'
    set D := truncD sh n F
    have hw : (0 : ℝ) < 2 ^ W := by positivity
    have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
    have hf := floor_close d W sh
    have hp0 : 0 ≤ y ^ (k + 1) := by positivity
    have hp1 : y ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hpw := abs_pow_sub_pow_le_unit hy0 hy1 hh0 hh1 (k + 1)
    have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by
      have : k + 1 ≤ K := by simp at hk; omega
      exact_mod_cast this
    have hpw2 : |y ^ (k + 1) - yh ^ (k + 1)| ≤ (K : ℝ) * η := by
      refine hpw.trans ?_
      have := abs_nonneg (y - yh)
      calc ((k + 1 : ℕ) : ℝ) * |y - yh| ≤ (K : ℝ) * |y - yh| := by gcongr
        _ ≤ _ := by gcongr
    have hc1 : |t (k + 1) - (d' : ℝ) / 2 ^ W| ≤ e + 1 / 2 ^ W := by
      have := abs_sub_le (t (k + 1)) ((d : ℝ) / 2 ^ (W + sh)) ((d' : ℝ) / 2 ^ W)
      linarith
    have h4 : t (k + 1) * y ^ (k + 1) - (d' : ℝ) / 2 ^ W * yh ^ (k + 1) ≤
        (e + 1 / 2 ^ W) + |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) := by
      have ex : t (k + 1) * y ^ (k + 1) - (d' : ℝ) / 2 ^ W * yh ^ (k + 1) =
          (t (k + 1) - (d' : ℝ) / 2 ^ W) * y ^ (k + 1) +
            (d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1)) := by ring
      rw [ex]
      have g1 : (t (k + 1) - (d' : ℝ) / 2 ^ W) * y ^ (k + 1) ≤ e + 1 / 2 ^ W := by
        calc _ ≤ |t (k + 1) - (d' : ℝ) / 2 ^ W| * y ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hp0
          _ ≤ |t (k + 1) - (d' : ℝ) / 2 ^ W| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ ≤ _ := by linarith
      have g2 : (d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1)) ≤
          |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) := by
        calc _ ≤ |(d' : ℝ) / 2 ^ W * (y ^ (k + 1) - yh ^ (k + 1))| := le_abs_self _
          _ = |(d' : ℝ)| / 2 ^ W * |y ^ (k + 1) - yh ^ (k + 1)| := by
              rw [abs_mul, abs_div, abs_of_pos hw]
          _ ≤ _ := by gcongr
      linarith
    have e2 : ((d' : ℝ) * yh ^ (k + 1) + polK D (k + 1) yh) / 2 ^ W =
        (d' : ℝ) / 2 ^ W * yh ^ (k + 1) + polK D (k + 1) yh / 2 ^ W := by ring
    rw [e2]
    push_cast
    have e3 : (|(d' : ℝ)| + ((abs1 D : ℤ) : ℝ)) / 2 ^ W * ((K : ℝ) * η) =
        |(d' : ℝ)| / 2 ^ W * ((K : ℝ) * η) + ((abs1 D : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * η) := by ring
    rw [e3]
    linarith

/-! ### Comparing radii -/

theorem psiR_close {r ρ x : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hx : 0 < x) :
    |psiR r x - psiR ρ x| ≤ (ρ - r) / r := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hd : 0 ≤ (ρ - r) / r := div_nonneg (by linarith) hr.le
  unfold psiR
  split_ifs with h1 h2 h2
  · -- r < x, ρ < x
    rw [← sub_div, abs_div, abs_of_pos hx, abs_sub_comm, abs_of_nonneg (by linarith)]
    gcongr
  · -- r < x ≤ ρ : both in [r/ρ, 1]
    have hx2 : x ≤ ρ := not_lt.mp h2
    have a1 : r / x ≤ 1 := by rw [div_le_one hx]; exact h1.le
    have a2 : x / ρ ≤ 1 := by rw [div_le_one hρ]; exact hx2
    have a3 : r / ρ ≤ r / x := by gcongr
    have a4 : r / ρ ≤ x / ρ := by gcongr
    have a5 : 1 - r / ρ ≤ (ρ - r) / r := by
      have : 1 - r / ρ = (ρ - r) / ρ := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_left (by linarith) hr hrρ
    rw [abs_le]
    constructor <;> linarith
  · -- x ≤ r, ρ < x : impossible
    exfalso
    have := not_lt.mp h1
    linarith
  · -- x ≤ r ≤ ρ
    have hx1 : x ≤ r := not_lt.mp h1
    have e : x / r - x / ρ = x / r * ((ρ - r) / ρ) := by field_simp
    have a1 : x / r ≤ 1 := by rw [div_le_one hr]; exact hx1
    have a2 : (ρ - r) / ρ ≤ (ρ - r) / r :=
      div_le_div_of_nonneg_left (by linarith) hr hrρ
    have a3 : 0 ≤ (ρ - r) / ρ := div_nonneg (by linarith) hρ.le
    rw [e, abs_of_nonneg (by positivity)]
    calc x / r * ((ρ - r) / ρ) ≤ 1 * ((ρ - r) / ρ) := by gcongr
      _ ≤ _ := by linarith

theorem psiR_mem {r x : ℝ} (hr : 0 < r) (hx : 0 < x) : 0 ≤ psiR r x ∧ psiR r x ≤ 1 := by
  unfold psiR
  split_ifs with h
  · exact ⟨by positivity, by rw [div_le_one hx]; exact h.le⟩
  · exact ⟨by positivity, by rw [div_le_one hr]; exact not_lt.mp h⟩

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-! ### Exponential enclosures -/

def expS (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expS y n + y ^ n / (n.factorial : ℚ)

def expE (y : ℚ) (n : ℕ) : ℚ := expS y n + y ^ n * ((n : ℚ) + 1) / ((n.factorial : ℚ) * n)

theorem expS_cast (y : ℚ) (n : ℕ) :
    ((expS y n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (y : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp [expS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [expS]

theorem exp_lo {y : ℚ} (h : 0 ≤ y) (n : ℕ) : ((expS y n : ℚ) : ℝ) ≤ Real.exp y := by
  rw [expS_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast h) n

theorem exp_hi {y : ℚ} (h : 0 ≤ y) (h1 : y ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp y ≤ ((expE y n : ℚ) : ℝ) := by
  have := Real.exp_bound' (x := (y : ℝ)) (by exact_mod_cast h) (by exact_mod_cast h1) hn
  unfold expE
  push_cast
  rw [expS_cast]
  exact this

theorem expNeg_enc {a : ℚ} (h0 : 0 ≤ a) (h4 : a ≤ 4) {n : ℕ} (hn : 0 < n)
    (hp : 0 < expS (a / 4) n) :
    ((1 / expE (a / 4) n ^ 4 : ℚ) : ℝ) ≤ Real.exp (-(a : ℝ)) ∧
      Real.exp (-(a : ℝ)) ≤ ((1 / expS (a / 4) n ^ 4 : ℚ) : ℝ) := by
  have hy0 : 0 ≤ a / 4 := by positivity
  have hy1 : a / 4 ≤ 1 := by linarith
  have l := exp_lo hy0 n
  have u := exp_hi hy0 hy1 hn
  have hp' : (0 : ℝ) < expS (a / 4) n := by exact_mod_cast hp
  have e : Real.exp (-(a : ℝ)) = 1 / Real.exp ((a / 4 : ℚ) : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    push_cast
    ring_nf
  have hE : 0 < Real.exp ((a / 4 : ℚ) : ℝ) := Real.exp_pos _
  rw [e]
  push_cast at l u hp' ⊢
  constructor
  · gcongr
  · gcongr

/-! ### Cosines of multiples of `π/93` -/

def cT (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => cT x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℚ)

theorem cT_cast (x : ℚ) (n : ℕ) : ((cT x n : ℚ) : ℝ) =
    ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction n with
  | zero => simp [cT]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [cT]

theorem cos_taylor_re (x : ℝ) : ∀ N : ℕ,
    (∑ m ∈ Finset.range (2 * N), ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
      ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Complex.add_re, Complex.add_re, ih, Finset.sum_range_succ]
    have e1 : ((x : ℂ) * Complex.I) ^ (2 * N) / ((2 * N).factorial : ℂ) =
        (((-1 : ℝ) ^ N * x ^ (2 * N) / ((2 * N).factorial : ℝ) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
      push_cast
      ring
    have e2 : (((x : ℂ) * Complex.I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ)).re = 0 := by
      have : ((x : ℂ) * Complex.I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ) =
          (((-1 : ℝ) ^ N * x ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) : ℝ) : ℂ) * Complex.I := by
        rw [mul_pow, pow_succ Complex.I, pow_succ (x : ℂ), pow_mul Complex.I, Complex.I_sq]
        push_cast
        ring
      rw [this]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [e2, e1, Complex.ofReal_re]
    ring

theorem cos_taylor (x : ℝ) (hx : |x| ≤ 1) (N : ℕ) (hN : 0 < N) :
    |Real.cos x - ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)| ≤
      |x| ^ (2 * N) * (((2 * N).succ : ℝ) / (((2 * N).factorial : ℝ) * ((2 * N : ℕ) : ℝ))) := by
  have hxc : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
  have hb := Complex.exp_bound hxc (n := 2 * N) (by omega)
  have hre : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x := Complex.exp_ofReal_mul_I_re x
  have h1 := Complex.abs_re_le_norm (Complex.exp ((x : ℂ) * Complex.I) -
    ∑ m ∈ Finset.range (2 * N), ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ))
  rw [Complex.sub_re, hre, cos_taylor_re] at h1
  refine h1.trans ?_
  refine hb.trans (le_of_eq ?_)
  have hn : ‖(x : ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [hn]
  push_cast
  ring

/-- `|cos(2x) - (2c²-1)| ≤ 5 e` from `|cos x - c| ≤ e ≤ 1/2`. -/
theorem cos_double {x c e : ℝ} (h : |Real.cos x - c| ≤ e) (he : e ≤ 1 / 2) :
    |Real.cos (2 * x) - (2 * c ^ 2 - 1)| ≤ 5 * e := by
  have e0 : 0 ≤ e := (abs_nonneg _).trans h
  have hc := Real.cos_le_one x
  have hc' := Real.neg_one_le_cos x
  have hb := abs_le.mp h
  have ex : Real.cos (2 * x) - (2 * c ^ 2 - 1) = 2 * (Real.cos x - c) * (Real.cos x + c) := by
    rw [Real.cos_two_mul]; ring
  rw [ex, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 : |Real.cos x + c| ≤ 5 / 2 := by
    rw [abs_le]; constructor <;> linarith [hb.1, hb.2]
  calc 2 * |Real.cos x - c| * |Real.cos x + c| ≤ 2 * e * (5 / 2) := by gcongr
    _ = 5 * e := by ring

/-- Rational approximation of `π`, `|π - PIQ| ≤ 10^-20`. -/
def PIQ : ℚ := 314159265358979323846 / 10 ^ 20

theorem pi_close : |Real.pi - (PIQ : ℝ)| ≤ 1 / 10 ^ 20 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  unfold PIQ
  push_cast
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- `cos(m π/93)` from Taylor at `m π/372` and two doublings. -/
def cos93 (m : ℕ) : ℚ :=
  let c0 := cT ((m : ℚ) * PIQ / 372) 12
  let c1 := 2 * c0 ^ 2 - 1
  2 * c1 ^ 2 - 1

theorem cos93_close {m : ℕ} (hm : m ≤ 93) :
    |Real.cos ((m : ℝ) * (Real.pi / 93)) - ((cos93 m : ℚ) : ℝ)| ≤ 1 / 10 ^ 17 := by
  set xh : ℚ := (m : ℚ) * PIQ / 372 with hxh
  set x : ℝ := (m : ℝ) * Real.pi / 372 with hx
  have hmr : (m : ℝ) ≤ 93 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hxe : |x - (xh : ℝ)| ≤ 1 / 10 ^ 20 := by
    have e : x - (xh : ℝ) = (m : ℝ) / 372 * (Real.pi - PIQ) := by
      rw [hx, hxh]; push_cast; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : (m : ℝ) / 372 ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
    calc (m : ℝ) / 372 * |Real.pi - PIQ| ≤ 1 * (1 / 10 ^ 20) := by
          have := pi_close
          gcongr
      _ = _ := one_mul _
  have hxq : |(xh : ℝ)| ≤ 1 := by
    have h0 : (0 : ℝ) ≤ xh := by
      rw [hxh]; unfold PIQ; push_cast; positivity
    rw [abs_of_nonneg h0, hxh]
    unfold PIQ
    push_cast
    nlinarith
  have ht := cos_taylor (xh : ℝ) hxq 12 (by norm_num)
  rw [← cT_cast] at ht
  have hrem : |(xh : ℝ)| ^ (2 * 12) * (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ)))
      ≤ 1 / 10 ^ 23 := by
    have h1 : |(xh : ℝ)| ^ (2 * 12) ≤ 1 := pow_le_one₀ (abs_nonneg _) hxq
    have h2 : (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) ≤ 1 / 10 ^ 23 := by
      norm_num [Nat.factorial]
    have h3 : (0 : ℝ) ≤ (((2 * 12).succ : ℝ) / (((2 * 12).factorial : ℝ) * ((2 * 12 : ℕ) : ℝ))) := by
      positivity
    exact (mul_le_mul h1 h2 h3 zero_le_one).trans (le_of_eq (one_mul _))
  have h0 : |Real.cos x - ((cT xh 12 : ℚ) : ℝ)| ≤ 2 / 10 ^ 20 := by
    have a := Real.abs_cos_sub_cos_le x xh
    have b := abs_sub_le (Real.cos x) (Real.cos xh) ((cT xh 12 : ℚ) : ℝ)
    have c := ht.trans hrem
    norm_num at c hxe a ⊢
    linarith
  have h1 := cos_double h0 (by norm_num)
  have h2 := cos_double h1 (by norm_num)
  have e4 : 2 * (2 * x) = (m : ℝ) * (Real.pi / 93) := by rw [hx]; ring
  rw [e4] at h2
  unfold cos93
  simp only
  push_cast
  rw [← hxh]
  refine h2.trans ?_
  norm_num

/-- The period-186 even fold of an index. -/
def fold186 (n : ℕ) : ℕ := if n % 186 ≤ 93 then n % 186 else 186 - n % 186

theorem fold186_le (n : ℕ) : fold186 n ≤ 93 := by
  unfold fold186
  have : n % 186 < 186 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega

theorem cos_fold (k j : ℕ) :
    Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / 93)) =
      Real.cos ((fold186 k : ℝ) * (Real.pi * (j : ℝ) / 93)) := by
  have hk : (k : ℝ) = 186 * ((k / 186 : ℕ) : ℝ) + ((k % 186 : ℕ) : ℝ) := by
    have := Nat.div_add_mod k 186
    exact_mod_cast this.symm
  have e1 : Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / 93)) =
      Real.cos (((k % 186 : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93)) := by
    have : (k : ℝ) * (Real.pi * (j : ℝ) / 93) =
        ((k % 186 : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93) + (((k / 186) * j : ℕ) : ℝ) * (2 * Real.pi) := by
      rw [hk]; push_cast; ring
    rw [this, Real.cos_add_nat_mul_two_pi]
  rw [e1]
  unfold fold186
  split_ifs with h
  · rfl
  · have hlt : k % 186 < 186 := Nat.mod_lt _ (by norm_num)
    have hc : ((186 - k % 186 : ℕ) : ℝ) = 186 - ((k % 186 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlt.le]; norm_num
    have : ((186 - k % 186 : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93) =
        (j : ℝ) * (2 * Real.pi) - ((k % 186 : ℕ) : ℝ) * (Real.pi * (j : ℝ) / 93) := by
      rw [hc]; ring
    rw [this, Real.cos_nat_mul_two_pi_sub]

/-- Packed cosine table: slot `m` holds `(cos(mπ/93)+1) 2^80`. -/
def cosI (CT : ℕ) (m : ℕ) : ℤ := (((CT >>> (96 * m)) % 2 ^ 96 : ℕ) : ℤ) - 2 ^ 80

def cosChk (CT : ℕ) (m : ℕ) : Bool :=
  decide (|cos93 m - (cosI CT m : ℚ) / 2 ^ 80| ≤ 1 / 10 ^ 17)

/-- The table error. -/
def Ecos : ℚ := 2 / 10 ^ 17

theorem cosI_close {CT : ℕ} (h : ∀ m ≤ 93, cosChk CT m = true) (k j : ℕ) :
    |Real.cos ((k : ℝ) * (Real.pi * (j : ℝ) / 93)) -
      ((cosI CT (fold186 (k * j)) : ℤ) : ℝ) / 2 ^ 80| ≤ (Ecos : ℝ) := by
  have e1 : (k : ℝ) * (Real.pi * (j : ℝ) / 93) = ((k * j : ℕ) : ℝ) * (Real.pi * ((1 : ℕ) : ℝ) / 93) := by
    push_cast; ring
  rw [e1, cos_fold]
  set m := fold186 (k * j) with hm
  have hle : m ≤ 93 := fold186_le _
  have h1 := cos93_close hle
  have h2 := h m hle
  simp only [cosChk, decide_eq_true_eq] at h2
  have h3 : |((cos93 m : ℚ) : ℝ) - ((cosI CT m : ℤ) : ℝ) / 2 ^ 80| ≤ 1 / 10 ^ 17 := by
    have := (Rat.cast_le (K := ℝ)).mpr h2
    push_cast at this
    exact this
  have e2 : (m : ℝ) * (Real.pi * ((1 : ℕ) : ℝ) / 93) = (m : ℝ) * (Real.pi / 93) := by
    push_cast; ring
  rw [e2]
  have := abs_sub_le (Real.cos ((m : ℝ) * (Real.pi / 93))) ((cos93 m : ℚ) : ℝ)
    (((cosI CT m : ℤ) : ℝ) / 2 ^ 80)
  unfold Ecos
  push_cast
  linarith

/-! ### Radius classes of a `Tr` list -/

theorem mkAux_eq {g : ℝ} {M : ℤ} {t : Tr} (hp : 0 ≤ t.2.2) (hM : 0 ≤ M) (hg : 0 ≤ g) :
    (mkAux g M t).rad = t.1.toNat ∧ (mkAux g M t).phase = Real.pi * (t.2.1 : ℝ) / 93 ∧
      (mkAux g M t).w = g * (t.2.2 : ℝ) / (M : ℝ) := by
  have h : 0 ≤ t.2.2 ∧ 0 ≤ M ∧ 0 ≤ g := ⟨hp, hM, hg⟩
  unfold mkAux
  rw [dif_pos h]
  exact ⟨rfl, rfl, rfl⟩

/-- Entries `(j, p)` of radius class `i`. -/
def grp (T : List Tr) (i : ℕ) : List (ℕ × ℕ) :=
  (T.filter fun t => t.1.toNat == i).map fun t => (t.2.1.toNat, t.2.2.toNat)

noncomputable def cS (G : List (ℕ × ℕ)) (m : ℕ) : ℝ :=
  (G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))).sum

def pS (G : List (ℕ × ℕ)) : ℕ := (G.map fun e => e.2).sum

theorem aC_map {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g) (i m : ℕ) : ∀ T : List Tr,
    (∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2) →
    aC (T.map (mkAux g M)) i m = g / M * cS (grp T i) m
  | [], _ => by simp [aC, cS, grp]
  | t :: T, h => by
    have ih := aC_map hM hg i m T fun t ht => h t (List.mem_cons_of_mem _ ht)
    obtain ⟨h1, h2⟩ := h t (by simp)
    obtain ⟨e1, e2, e3⟩ := mkAux_eq (t := t) h2 hM hg
    have hj : ((t.2.1.toNat : ℕ) : ℝ) = (t.2.1 : ℝ) := by
      have : ((t.2.1.toNat : ℕ) : ℤ) = t.2.1 := Int.toNat_of_nonneg h1
      exact_mod_cast this
    have hp : ((t.2.2.toNat : ℕ) : ℝ) = (t.2.2 : ℝ) := by
      have : ((t.2.2.toNat : ℕ) : ℤ) = t.2.2 := Int.toNat_of_nonneg h2
      exact_mod_cast this
    rw [List.map_cons, aC_cons, ih, e1, e2, e3]
    by_cases hi : t.1.toNat = i
    · have : grp (t :: T) i = (t.2.1.toNat, t.2.2.toNat) :: grp T i := by
        simp [grp, hi]
      rw [this, if_pos hi]
      simp only [cS, List.map_cons, List.sum_cons]
      rw [hj, hp]
      ring
    · have : grp (t :: T) i = grp T i := by
        simp [grp, hi]
      rw [this, if_neg hi, zero_add]

theorem cS_fold (G : List (ℕ × ℕ)) (k : ℕ) : cS G k = cS G (fold186 k) := by
  unfold cS
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [cos_fold]

theorem abs_cS_le (G : List (ℕ × ℕ)) (m : ℕ) : |cS G m| ≤ (pS G : ℝ) := by
  induction G with
  | nil => simp [cS, pS]
  | cons e G ih =>
    simp only [cS, pS, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add]
    refine (abs_add_le _ _).trans ?_
    have : |(e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))| ≤ (e.2 : ℝ) := by
      rw [abs_mul, Nat.abs_cast]
      have := Real.abs_cos_le_one ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))
      have h0 : (0 : ℝ) ≤ e.2 := by positivity
      nlinarith
    linarith

theorem cS_zero (G : List (ℕ × ℕ)) : cS G 0 = (pS G : ℝ) := by
  induction G with
  | nil => simp [cS, pS]
  | cons e G ih =>
    simp only [cS, pS, List.map_cons, List.sum_cons] at ih ⊢
    rw [Nat.cast_add, ← ih]
    simp

/-- Integer cosine sum over a class, scale `2^80`. -/
def rI (CT : ℕ) (G : List (ℕ × ℕ)) (m : ℕ) : ℤ :=
  (G.map fun e => (e.2 : ℤ) * cosI CT (fold186 (m * e.1))).sum

theorem cS_close {CT : ℕ} (h : ∀ m ≤ 93, cosChk CT m = true) (G : List (ℕ × ℕ)) (m : ℕ) :
    |cS G m - ((rI CT G m : ℤ) : ℝ) / 2 ^ 80| ≤ (pS G : ℝ) * (Ecos : ℝ) := by
  induction G with
  | nil => simp [cS, pS, rI]
  | cons e G ih =>
    simp only [cS, pS, rI, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := cosI_close h m e.1
    set c := Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))
    set ci := cosI CT (fold186 (m * e.1))
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_add]
    have ex : (e.2 : ℝ) * c + (G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))).sum -
        ((e.2 : ℝ) * (ci : ℝ) + (((G.map fun e => (e.2 : ℤ) * cosI CT (fold186 (m * e.1))).sum : ℤ) : ℝ)) / 2 ^ 80 =
        (e.2 : ℝ) * (c - (ci : ℝ) / 2 ^ 80) +
        ((G.map fun e => (e.2 : ℝ) * Real.cos ((m : ℝ) * (Real.pi * (e.1 : ℝ) / 93))).sum -
          (((G.map fun e => (e.2 : ℤ) * cosI CT (fold186 (m * e.1))).sum : ℤ) : ℝ) / 2 ^ 80) := by
      ring
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.abs_cast, add_mul]
    have : (e.2 : ℝ) * |c - (ci : ℝ) / 2 ^ 80| ≤ (e.2 : ℝ) * (Ecos : ℝ) := by gcongr
    linarith

/-- The table of a class: `A_m ≈ h · Σ p cos`, scale `2^80`. -/
def rowA (CT : ℕ) (hq : ℚ) (G : List (ℕ × ℕ)) : List ℤ :=
  (List.range 94).map fun m => fl (hq * (rI CT G m : ℚ))

theorem rowA_close {CT : ℕ} (h : ∀ m ≤ 93, cosChk CT m = true) {hq : ℚ} (hq0 : 0 ≤ hq)
    (G : List (ℕ × ℕ)) (k : ℕ) :
    |(hq : ℝ) * cS G k - (((rowA CT hq G).getD (fold186 k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤
      (hq : ℝ) * ((pS G : ℝ) * (Ecos : ℝ)) + 1 / 2 ^ 80 := by
  rw [cS_fold]
  set m := fold186 k with hm
  have hle : m < 94 := Nat.lt_succ_of_le (fold186_le k)
  have hg : (rowA CT hq G).getD m 0 = fl (hq * (rI CT G m : ℚ)) := by
    unfold rowA
    simp [List.getD, hle]
  rw [hg]
  have h1 := cS_close h G m
  have hq0' : (0 : ℝ) ≤ hq := by exact_mod_cast hq0
  have hf1 := fl_le (hq * (rI CT G m : ℚ))
  have hf2 := lt_fl (hq * (rI CT G m : ℚ))
  set v := fl (hq * (rI CT G m : ℚ))
  have g1 : (v : ℝ) ≤ (hq : ℝ) * ((rI CT G m : ℤ) : ℝ) := by exact_mod_cast hf1
  have g2 : (hq : ℝ) * ((rI CT G m : ℤ) : ℝ) < (v : ℝ) + 1 := by exact_mod_cast hf2
  have ex : (hq : ℝ) * cS G m - (v : ℝ) / 2 ^ 80 = (hq : ℝ) * (cS G m - ((rI CT G m : ℤ) : ℝ) / 2 ^ 80) +
      ((hq : ℝ) * ((rI CT G m : ℤ) : ℝ) - (v : ℝ)) / 2 ^ 80 := by ring
  rw [ex]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hq0', abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 80)]
  have h2 : |(hq : ℝ) * ((rI CT G m : ℤ) : ℝ) - (v : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have h3 : (hq : ℝ) * |cS G m - ((rI CT G m : ℤ) : ℝ) / 2 ^ 80| ≤ (hq : ℝ) * ((pS G : ℝ) * (Ecos : ℝ)) := by
    gcongr
  have h4 : |(hq : ℝ) * ((rI CT G m : ℤ) : ℝ) - (v : ℝ)| / 2 ^ 80 ≤ 1 / 2 ^ 80 := by gcongr
  linarith

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-! ### Kernel coefficients -/

/-- Closed forms of strength and curvature in `r = q²`. -/
def Afun (r : ℚ) : ℚ := 3 * (1 - r ^ 2) / (2 * (1 + 4 * r + r ^ 2))
def Bfun (r : ℚ) : ℚ := (1 - r) ^ 2 / (2 * (1 + 4 * r + r ^ 2))

structure CoefEnc where
  ql : ℚ
  qh : ℚ
  Al : ℚ
  Ah : ℚ
  Bl : ℚ
  Bh : ℚ

def CoefEnc.cLo (E : CoefEnc) (k : ℕ) : ℚ := -(E.qh ^ k * (1 + E.Ah * k + E.Bh * (k : ℚ) ^ 2) / k)
def CoefEnc.cHi (E : CoefEnc) (k : ℕ) : ℚ := -(E.ql ^ k * (1 + E.Al * k + E.Bl * (k : ℚ) ^ 2) / k)

/-- `E` encloses the three constants of `S`. -/
structure CoefEnc.Valid (E : CoefEnc) (S : CapSource) : Prop where
  ql0 : 0 ≤ E.ql
  Al0 : 0 ≤ E.Al
  Bl0 : 0 ≤ E.Bl
  ql : (E.ql : ℝ) ≤ S.q
  qh : S.q ≤ E.qh
  Al : (E.Al : ℝ) ≤ S.strength
  Ah : S.strength ≤ E.Ah
  Bl : (E.Bl : ℝ) ≤ S.curvature
  Bh : S.curvature ≤ E.Bh

theorem CoefEnc.coef_mem {E : CoefEnc} {S : CapSource} (h : E.Valid S) {k : ℕ} (hk : 0 < k) :
    ((E.cLo k : ℚ) : ℝ) ≤ S.coef k ∧ S.coef k ≤ ((E.cHi k : ℚ) : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have q0 : (0 : ℝ) ≤ E.ql := by exact_mod_cast h.ql0
  have A0 : (0 : ℝ) ≤ E.Al := by exact_mod_cast h.Al0
  have B0 : (0 : ℝ) ≤ E.Bl := by exact_mod_cast h.Bl0
  have s0 : 0 ≤ S.q := q0.trans h.ql
  have a1 : (0 : ℝ) ≤ S.strength := A0.trans h.Al
  have b1 : (0 : ℝ) ≤ S.curvature := B0.trans h.Bl
  have h1 : (E.ql : ℝ) ^ k ≤ S.q ^ k := pow_le_pow_left₀ q0 h.ql k
  have h2 : S.q ^ k ≤ (E.qh : ℝ) ^ k := pow_le_pow_left₀ s0 h.qh k
  have p1 : 1 + (E.Al : ℝ) * k + E.Bl * (k : ℝ) ^ 2 ≤ 1 + S.strength * k + S.curvature * (k : ℝ) ^ 2 := by
    have := h.Al; have := h.Bl; gcongr
  have p2 : 1 + S.strength * k + S.curvature * (k : ℝ) ^ 2 ≤ 1 + (E.Ah : ℝ) * k + E.Bh * (k : ℝ) ^ 2 := by
    have := h.Ah; have := h.Bh; gcongr
  have p0 : 0 ≤ 1 + (E.Al : ℝ) * k + E.Bl * (k : ℝ) ^ 2 := by positivity
  unfold CapSource.coef CoefEnc.cLo CoefEnc.cHi
  push_cast
  constructor
  · apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hkr.le
    exact mul_le_mul h2 p2 (p0.trans p1) (pow_nonneg (s0.trans h.qh) k)
  · apply neg_le_neg
    apply div_le_div_of_nonneg_right _ hkr.le
    exact mul_le_mul h1 p1 p0 (pow_nonneg s0 k)

def coefChk (E : CoefEnc) (δ : ℚ) : List ℤ → ℕ → Bool
  | [], _ => true
  | d :: t, k => decide (|E.cLo (k + 1) - (d : ℚ) / 2 ^ 80| ≤ δ) &&
      decide (|E.cHi (k + 1) - (d : ℚ) / 2 ^ 80| ≤ δ) && coefChk E δ t (k + 1)

theorem coef_close {E : CoefEnc} {S : CapSource} (h : E.Valid S) {δ : ℚ} :
    ∀ (Cq : List ℤ) (k : ℕ), coefChk E δ Cq k = true →
    CLz S.coef (2 ^ 80) (δ : ℝ) k Cq
  | [], _, _ => trivial
  | d :: t, k, hc => by
    simp only [coefChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    refine ⟨?_, coef_close h t (k + 1) h3⟩
    obtain ⟨m1, m2⟩ := CoefEnc.coef_mem h (Nat.succ_pos k)
    have g1 : |((E.cLo (k + 1) : ℚ) : ℝ) - (d : ℝ) / 2 ^ 80| ≤ (δ : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    have g2 : |((E.cHi (k + 1) : ℚ) : ℝ) - (d : ℝ) / 2 ^ 80| ≤ (δ : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h2
      push_cast at this
      exact this
    have g1' := abs_le.mp g1
    have g2' := abs_le.mp g2
    rw [abs_le]
    constructor <;> linarith [g1'.1, g2'.2]

/-! ### A full coefficient row -/

/-- `s^k c_k A[fold k]`, scale `2^160`. -/
def tRow (s : ℤ) (A : List ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, c :: cs => (s ^ (k + 1) * c * A.getD (fold186 (k + 1)) 0) :: tRow s A (k + 1) cs

theorem tRow_len (s : ℤ) (A : List ℤ) : ∀ (Cq : List ℤ) (k : ℕ), (tRow s A k Cq).length = Cq.length
  | [], _ => rfl
  | _ :: t, k => by simp [tRow, tRow_len s A t (k + 1)]

theorem tRow_close {c a : ℕ → ℝ} {s : ℤ} (hs : |(s : ℝ)| = 1) {A : List ℤ} {δc δa Ab : ℝ}
    (hA : ∀ k, |a k - ((A.getD (fold186 k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤ δa)
    (hAb : ∀ k, |a k| ≤ Ab) :
    ∀ (Cq : List ℤ) (k : ℕ), CLz c (2 ^ 80) δc k Cq → (∀ d ∈ Cq, |(d : ℝ)| ≤ 2 ^ 81) →
    CLz (fun k => (s : ℝ) ^ k * c k * a k) (2 ^ 160) (δc * Ab + 2 * δa) k (tRow s A k Cq)
  | [], _, _, _ => trivial
  | d :: t, k, hc, hb => by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, tRow_close hs hA hAb t (k + 1) h2 fun d hd => hb d (List.mem_cons_of_mem _ hd)⟩
    have hd := hb d (by simp)
    set al := ((A.getD (fold186 (k + 1)) 0 : ℤ) : ℝ) with hal
    have e1 := hA (k + 1)
    have e2 := hAb (k + 1)
    have ex : (s : ℝ) ^ (k + 1) * c (k + 1) * a (k + 1) -
        (((s ^ (k + 1) * d * A.getD (fold186 (k + 1)) 0 : ℤ)) : ℝ) / 2 ^ 160 =
        (s : ℝ) ^ (k + 1) * ((c (k + 1) - (d : ℝ) / 2 ^ 80) * a (k + 1) +
          (d : ℝ) / 2 ^ 80 * (a (k + 1) - al / 2 ^ 80)) := by
      push_cast
      rw [← hal]
      ring
    rw [ex, abs_mul, abs_pow, hs, one_pow, one_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have g1 : |(d : ℝ) / 2 ^ 80| ≤ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 80), div_le_iff₀ (by positivity)]
      refine hd.trans (le_of_eq ?_)
      norm_num
    have δ0 : 0 ≤ δa := (abs_nonneg _).trans e1
    have h3 : |c (k + 1) - (d : ℝ) / 2 ^ 80| * |a (k + 1)| ≤ δc * Ab :=
      mul_le_mul h1 e2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    have h4 : |(d : ℝ) / 2 ^ 80| * |a (k + 1) - al / 2 ^ 80| ≤ 2 * δa :=
      mul_le_mul g1 e1 (abs_nonneg _) (by norm_num)
    linarith

/-! ### One radius class against one block -/

noncomputable section

theorem block_le {t : ℕ → ℝ} {r e a0 : ℝ} {B : Blk} (W sh n K : ℕ) {F : List ℤ}
    (hr : 0 < r) (hrρ : r ≤ B.rho) (hM : (B.M : ℝ) = a0) (ha0 : 0 ≤ a0)
    (hD : B.D = truncD sh n F) (hF : CLz t (2 ^ (W + sh)) e 0 F) (hK : F.length = K)
    (he : 0 ≤ e) {x : ℝ} (hx : 0 < x) :
    a0 * Real.log (max x r) + ∑ k ∈ Finset.range K, t (k + 1) * psiR r x ^ (k + 1) ≤
      blkF W B x + (((abs1 (F.drop n) : ℤ) : ℝ) / 2 ^ (W + sh) + (K : ℝ) * (e + 1 / 2 ^ W) +
        ((abs1 B.D : ℤ) : ℝ) / 2 ^ W * ((K : ℝ) * (((B.rho : ℝ) - r) / r))) := by
  have hρ : (0 : ℝ) < B.rho := lt_of_lt_of_le hr hrρ
  obtain ⟨y0, y1⟩ := psiR_mem hr hx
  obtain ⟨z0, z1⟩ := psiR_mem hρ hx
  have hs := ser_le W sh K y0 y1 z0 z1 (psiR_close hr hrρ hx) he F n 0 hF (by omega)
  rw [hK, serR_eq, ← hD] at hs
  have hl : Real.log (max x r) ≤ Real.log (max x (B.rho : ℝ)) :=
    Real.log_le_log (lt_max_of_lt_left hx) (max_le_max le_rfl hrρ)
  have := mul_le_mul_of_nonneg_left hl ha0
  unfold blkF
  rw [hM]
  linarith

theorem sum_getD {α : Type*} (d : α) (f : α → ℝ) : ∀ l : List α,
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum
  | [] => by simp
  | a :: t => by
    have := sum_getD d f t
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← this, add_comm]
    simp

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-! ### From the literal moment list to the Chebyshev moments -/

variable {P T Q : ℕ}

/-- Row error, as a rational function of the index. -/
def rowErr (P Ln Sg : ℕ) (j : ℕ) : ℚ :=
  ((Ln : ℚ) + 4 * j * ((Sg : ℚ) / 2 ^ P)) / 2 ^ P

/-- Exact gas mass. -/
def massQ (T : ℕ) (L : List GD) : ℚ := ((L.map GD.p).sum : ℚ) / T

theorem massL_rel {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) :
    massL l = ((massQ T L : ℚ) : ℝ) := by
  induction h with
  | nil => simp [massL, massQ]
  | @cons c d l L hr _ ih =>
    have e : massL (c :: l) = c.w + massL l := by simp [massL]
    rw [e, ih, hr.w]
    simp only [massQ, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem physL_one (l : List YCell) : physL l (fun s => s ^ 0) = massL l := by
  induction l with
  | nil => simp [physL, massL]
  | cons c l ih =>
    have e1 : physL (c :: l) (fun s => s ^ 0) = c.phys (fun _ => 1) + physL l (fun s => s ^ 0) := by
      simp [physL]
    have e2 : massL (c :: l) = c.w + massL l := by simp [massL]
    rw [e1, e2, ih, MomentSource.phys_one]

theorem moments_close {l : List YCell} {L : List GD} (h : List.Forall₂ (Rel P T) l L) (hT : 0 < T)
    (h2 : ∀ c ∈ l, 2 ≤ c.lo) {R r : List ℤ} {n : ℕ} {e1 e2 : ℤ}
    (hR : rows P n (L.map (stAt P T 1)) = R) (hR' : R = e1 :: e2 :: r) {Ln Sg : ℕ} {LIv LEIv : ℤ}
    (hLn : L.length = Ln) (hSg : SG P T L = Sg) (hLI : LI P T Q L = LIv)
    (hLEI : LEI P T Q L = LEIv) :
    CloseL (fun i => physL l (fun s => s ^ i)) 0
      (massQ T L :: ((LIv : ℚ) / 2 ^ Q - (e2 : ℚ) / 4 ^ P / 2) ::
        mB (4 ^ P) 0 R)
      (0 :: (((LEIv : ℚ) + Ln) / 2 ^ Q + rowErr P Ln Sg 2 / 2) ::
        dB (rowErr P Ln Sg) 0 R) := by
  subst hLI hLEI hLn hSg
  have hc := rows_close h hT n 1
  rw [hR] at hc
  have hc' : CloseZ (Er l) (((4 ^ P : ℚ)) : ℝ) (fun j => ((rowErr P L.length (SG P T L) j : ℚ) : ℝ)) (0 + 1) R := by
    have e : (fun j : ℕ => ((rowErr P L.length (SG P T L) j : ℚ) : ℝ)) =
        fun j : ℕ => ((L.length : ℝ) + 4 * j * ((SG P T L : ℝ) / 2 ^ P)) / 2 ^ P := by
      funext j
      unfold rowErr
      push_cast
      rfl
    rw [e]
    push_cast
    exact hc
  have hm := mB_close h2 (S := 4 ^ P) (err := rowErr P L.length (SG P T L)) R 0 hc'
  have hE : |Er l 2 - (e2 : ℝ) / 4 ^ P| ≤ ((rowErr P L.length (SG P T L) 2 : ℚ) : ℝ) := by
    rw [hR'] at hc'
    have := hc'.2.1
    simpa using this
  refine ⟨?_, ?_, hm⟩
  · show |physL l (fun s => s ^ 0) - _| ≤ _
    rw [physL_one, massL_rel h]
    simp
  · show |physL l (fun s => s ^ 1) - _| ≤ _
    rw [mom1 h2]
    have hL := Lr_close (Q := Q) h hT
    have ex : Lr l - Er l 2 / 2 - (((LI P T Q L : ℚ) / 2 ^ Q - (e2 : ℚ) / 4 ^ P / 2 : ℚ) : ℝ) =
        (Lr l - (LI P T Q L : ℝ) / 2 ^ Q) - (Er l 2 - (e2 : ℝ) / 4 ^ P) / 2 := by
      push_cast
      ring
    rw [ex]
    refine (abs_sub _ _).trans ?_
    have g : |(Er l 2 - (e2 : ℝ) / 4 ^ P) / 2| ≤ ((rowErr P L.length (SG P T L) 2 : ℚ) : ℝ) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    push_cast at g ⊢
    linarith

/-! ### Gas bound -/

/-- Scale `-2/n · μ_n` and shorten. -/
def chkC (W : ℕ) : ℕ → List ℚ → List ℚ → List ℤ → List ℚ → Bool
  | _, [], _, _, _ => true
  | _, _ :: _, [], _, _ => false
  | _, _ :: _, _ :: _, [], _ => false
  | _, _ :: _, _ :: _, _ :: _, [] => false
  | k, v :: vs, e :: es, c :: cs, f :: fs =>
    decide (|(-2 / (k : ℚ)) * v - (c : ℚ) / 2 ^ W| + 2 / (k : ℚ) * e ≤ f) && chkC W (k + 1) vs es cs fs

noncomputable section

theorem chkC_spec {μ : ℕ → ℝ} (W : ℕ) : ∀ (k : ℕ) (v e : List ℚ) (c : List ℤ) (f : List ℚ), 0 < k →
    CloseL μ k v e → chkC W k v e c f = true → v.length = c.length →
    CloseL (fun n => -2 / (n : ℝ) * μ n) k (c.map fun d : ℤ => (d : ℚ) / 2 ^ W) f
  | _, [], _, [], _, _, _, _, _ => trivial
  | _, [], _, _ :: _, _, _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, _, hc, _, _ => by simp [CloseL] at hc
  | _, _ :: _, _ :: _, [], _, _, _, h, _ => by simp [chkC] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, _, h, _ => by simp [chkC] at h
  | k, v :: vs, e :: es, c :: cs, f :: fs, hk, hc, h, hl => by
    simp only [chkC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := hc
    refine ⟨?_, chkC_spec W (k + 1) vs es cs fs (Nat.succ_pos k) g2 h2 (by simpa using hl)⟩
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have h1' : |(-2 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W| + 2 / (k : ℝ) * (e : ℝ) ≤ (f : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    have ex : -2 / (k : ℝ) * μ k - (((c : ℚ) / 2 ^ W : ℚ) : ℝ) =
        (-2 / (k : ℝ)) * (μ k - v) + ((-2 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W) := by
      push_cast
      ring
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_of_pos hkr]
    have g : (|(-2 : ℝ)| / (k : ℝ)) * |μ k - (v : ℝ)| ≤ 2 / (k : ℝ) * (e : ℝ) := by
      have : |(-2 : ℝ)| = 2 := by norm_num
      rw [this]
      gcongr
    linarith

theorem rawQ_map (W : ℕ) (z : ℝ) : ∀ (c : List ℤ) (k : ℕ),
    rawQ (c.map fun d : ℤ => (d : ℚ) / 2 ^ W) k z = rawSum c k z / 2 ^ W
  | [], _ => by simp [rawQ]
  | d :: t, k => by
    simp only [List.map_cons, rawQ, rawSum_cons, rawQ_map W z t (k + 1)]
    push_cast
    ring

/-- Chebyshev rows folded into a monomial list. -/
def comb : List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | [], _, _, acc => acc
  | c :: cs, a, b, acc => comb cs b (tNext a b) (addZ acc (smulZ c a))

theorem comb_spec (x : ℝ) : ∀ (cs a b acc : List ℤ) (k : ℕ),
    (∀ s, Pz a s = basis k (2 * s - 1)) → (∀ s, Pz b s = basis (k + 1) (2 * s - 1)) →
    Pz (comb cs a b acc) x = Pz acc x + rawSum cs k (2 * x - 1)
  | [], _, _, acc, _, _, _ => by simp [comb]
  | c :: cs, a, b, acc, k, ha, hb => by
    have := comb_spec x cs b (tNext a b) (addZ acc (smulZ c a)) (k + 1) hb (fun s => Pz_tNext ha hb s)
    simp only [comb, this, Pz_addZ, Pz_smulZ, ha, rawSum_cons]
    ring

/-- The whole gas bound: Poisson, Bessel and the moment list. -/
theorem gas_main {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) (hS : Sep 2 l) {W N : ℕ} (hN : 1 ≤ N)
    {v0 e0 : ℚ} {vs es : List ℚ} (hμ : CloseL (fun n => physL l (TF n)) 0 (v0 :: vs) (e0 :: es))
    (hlen : vs.length = N) {Gb Bq Tb : ℚ} (hG : G2 l ≤ Gb)
    (hBq : 31415926536 / 10 ^ 10 / 2 * Gb - ((v0 ^ 2 - 2 * |v0| * e0) / 2 + sqLow vs es) ≤ Bq)
    (hGb : 0 ≤ Gb) (hT0 : 0 ≤ Tb) (hBT : 4 * Bq ≤ (N : ℚ) * Tb ^ 2)
    {cN : List ℤ} {f : List ℚ} (hc : chkC W 1 vs es cN f = true) (hcl : cN.length = N)
    (hfl : f.length = N) (acc : List ℤ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 + Pz acc x / 2 ^ W ≤
      (Tb : ℝ) + Pz (comb cN [-1, 2] (tNext [1] [-1, 2]) acc) x / 2 ^ W + (sumQ f : ℝ) := by
  obtain ⟨c0, c1⟩ := hμ
  have hB : ∀ M, ∑ n ∈ Finset.Ico N M, (physL l (TF (n + 1))) ^ 2 ≤ (Bq : ℝ) := by
    refine tail_of_bessel (le_refl 2) hS ?_
    have hs := sqLow_le 1 vs es c1
    rw [hlen] at hs
    have e : ∑ i ∈ Finset.range N, (physL l (TF (1 + i))) ^ 2 =
        ∑ n ∈ Finset.range N, (physL l (TF (n + 1))) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [add_comm]
    rw [e] at hs
    have h0 := sq_ge c0
    have hpi : Real.pi ≤ 31415926536 / 10 ^ 10 := by
      have := Real.pi_lt_d20
      norm_num at this ⊢
      linarith
    have hBq' : (31415926536 / 10 ^ 10 / 2 : ℝ) * (Gb : ℝ) -
        (((v0 : ℝ) ^ 2 - 2 * |(v0 : ℝ)| * e0) / 2 + (sqLow vs es : ℝ)) ≤ Bq := by
      have := (Rat.cast_le (K := ℝ)).mpr hBq
      push_cast at this
      exact this
    have hGb' : (0 : ℝ) ≤ Gb := by exact_mod_cast hGb
    have g1 : Real.pi / 2 * G2 l ≤ (31415926536 / 10 ^ 10 / 2 : ℝ) * (Gb : ℝ) := by
      have h3 : Real.pi / 2 ≤ (31415926536 / 10 ^ 10 / 2 : ℝ) := by linarith
      have h4 : 0 ≤ Real.pi / 2 := by positivity
      calc Real.pi / 2 * G2 l ≤ Real.pi / 2 * (Gb : ℝ) := mul_le_mul_of_nonneg_left hG h4
        _ ≤ _ := mul_le_mul_of_nonneg_right h3 hGb'
    linarith
  have hT0' : (0 : ℝ) ≤ Tb := by exact_mod_cast hT0
  have hBT' : 4 * (Bq : ℝ) ≤ (N : ℝ) * (Tb : ℝ) ^ 2 := by exact_mod_cast hBT
  have hg := gas_upper h2 hx0 hx1 hN hB hT0' hBT'
  have hz : 2 * x - 1 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcl' := chkC_spec (μ := fun n => physL l (TF n)) W 1 vs es cN f one_pos c1 hc (by omega)
  have hcc := close_cheb hz 1 _ f hcl' (by simp [hcl, hfl])
  rw [rawQ_map, List.length_map, hcl] at hcc
  have hs : ∑ i ∈ Finset.range N, -2 / ((1 + i : ℕ) : ℝ) * physL l (TF (1 + i)) * basis (1 + i) (2 * x - 1) =
      -∑ n ∈ Finset.range N, 2 / ((n : ℝ) + 1) * basis (n + 1) (2 * x - 1) * physL l (TF (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm 1 i]
    push_cast
    ring
  rw [hs] at hcc
  have hb := (abs_le.mp hcc).2
  have hcomb := comb_spec x cN [-1, 2] (tNext [1] [-1, 2]) acc 1 Pz_t1
    (fun s => Pz_tNext (k := 0) Pz_t0 Pz_t1 s)
  rw [hcomb, add_div]
  linarith [(abs_le.mp hcc).1]

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)

/-- Integer list as dyadic rationals. -/
def dyL (W : ℕ) (c : List ℤ) : List ℚ := c.map fun d : ℤ => (d : ℚ) / 2 ^ W

/-- The literal gas record: every stage of the gas computation, stored once. -/
structure GasLit where
  P : ℕ
  T : ℕ
  Q : ℕ
  Qm : ℕ
  Qv : ℕ
  W : ℕ
  N : ℕ
  Ln : ℕ
  Sg : ℕ
  LIv : ℤ
  LEIv : ℤ
  L : List GD
  R : List ℤ
  Mi : List ℤ
  Me : List ℤ
  v0 : ℤ
  e0 : ℤ
  Vi : List ℤ
  Ve : List ℤ
  G2v : ℤ
  Bq : ℚ
  Tb : ℚ
  cN : List ℤ
  f : List ℤ

/-- Moments from the rows. -/
def GasLit.mL (g : GasLit) : List ℚ :=
  massQ g.T g.L :: ((g.LIv : ℚ) / 2 ^ g.Q - (g.R.getD 1 0 : ℚ) / 4 ^ g.P / 2) :: mB (4 ^ g.P) 0 g.R

def GasLit.dL (g : GasLit) : List ℚ :=
  0 :: (((g.LEIv : ℚ) + g.Ln) / 2 ^ g.Q + rowErr g.P g.Ln g.Sg 2 / 2) ::
    dB (rowErr g.P g.Ln g.Sg) 0 g.R

def GasLit.chkM (g : GasLit) : Bool :=
  relax g.mL g.dL (dyL g.Qm g.Mi) (dyL g.Qm g.Me) && (g.mL.length == g.Mi.length)

/-- Chebyshev moments from the shortened moments. -/
def GasLit.chkV (g : GasLit) : Bool :=
  relax (muV (dyL g.Qm g.Mi) (g.N + 1) [1] [-1, 2]) (muE (dyL g.Qm g.Me) (g.N + 1) [1] [-1, 2])
    (dyL g.Qv (g.v0 :: g.Vi)) (dyL g.Qv (g.e0 :: g.Ve)) && decide (g.N + 1 ≤ g.Mi.length)

/-- Scalar checks. -/
def GasLit.chkS (g : GasLit) : Bool :=
  decide (31415926536 / 10 ^ 10 / 2 * ((g.G2v : ℚ) / 2 ^ g.Q) -
      (((((g.v0 : ℚ) / 2 ^ g.Qv)) ^ 2 - 2 * |(g.v0 : ℚ) / 2 ^ g.Qv| * ((g.e0 : ℚ) / 2 ^ g.Qv)) / 2 +
        sqLow (dyL g.Qv g.Vi) (dyL g.Qv g.Ve)) ≤ g.Bq) &&
  decide (0 ≤ g.G2v) && decide (0 ≤ g.Tb) && decide (4 * g.Bq ≤ (g.N : ℚ) * g.Tb ^ 2) &&
  decide (1 ≤ g.N) && decide (g.Vi.length = g.N) && decide (g.cN.length = g.N) &&
  decide (g.f.length = g.N)

def GasLit.chkC (g : GasLit) : Bool :=
  OrdHf.chkC g.W 1 (dyL g.Qv g.Vi) (dyL g.Qv g.Ve) g.cN (dyL 40 g.f)

/-- The monomial list of a gas record with an extra list `acc`. -/
def GasLit.G (g : GasLit) (acc : List ℤ) : List ℤ := comb g.cN [-1, 2] (tNext [1] [-1, 2]) acc

/-- Separation check on the record. -/
def sepL : ℕ → List GD → Bool
  | _, [] => true
  | a, d :: t => decide (a ≤ d.a) && sepL d.b t

noncomputable section

theorem sep_of {P T : ℕ} : ∀ {l : List YCell} {L : List GD} (a : ℕ), List.Forall₂ (Rel P T) l L →
    sepL a L = true → Sep ((a : ℝ) / 10 ^ 12) l
  | _, _, _, .nil, _ => trivial
  | c :: l, d :: L, a, .cons hr hl, h => by
    simp only [sepL, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, ?_⟩
    · rw [hr.lo]
      have : (a : ℝ) ≤ d.a := by exact_mod_cast h.1
      gcongr
    · rw [hr.hi]
      exact sep_of d.b hl h.2

theorem len_dyL (W : ℕ) (c : List ℤ) : (dyL W c).length = c.length := by simp [dyL]

/-- All gas checks together give the gas bound. -/
theorem gas_of_lit (g : GasLit) {l : List YCell} (h : List.Forall₂ (Rel g.P g.T) l g.L)
    (hT : 0 < g.T) (h2 : ∀ c ∈ l, 2 ≤ c.lo) (hS : sepL (2 * 10 ^ 12) g.L = true)
    {nR : ℕ} (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true) (acc : List ℤ) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    physL l (fun s => Real.log |x - s|) + massL l * Real.log 4 + Pz acc x / 2 ^ g.W ≤
      (g.Tb : ℝ) + Pz (g.G acc) x / 2 ^ g.W + (sumQ (dyL 40 g.f) : ℝ) := by
  simp only [GasLit.chkS, Bool.and_eq_true, decide_eq_true_eq] at cS
  obtain ⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩ := cS
  simp only [GasLit.chkM, Bool.and_eq_true, beq_iff_eq] at cM
  simp only [GasLit.chkV, Bool.and_eq_true, decide_eq_true_eq] at cV
  have hm0 := moments_close (Q := g.Q) h hT h2 c1 c1' cLn cSg cLI cLEI
  have hR1 : g.R.getD 1 0 = e2 := by rw [c1']; rfl
  have hm1 : CloseL (fun i => physL l (fun s => s ^ i)) 0 g.mL g.dL := by
    unfold GasLit.mL GasLit.dL
    rw [hR1]
    exact hm0
  have hm2 := relax_close 0 _ _ _ _ hm1 cM.1 (by rw [len_dyL]; exact cM.2)
  have hmu := mu_close h2 hm2 (g.N + 1) 0 [1] [-1, 2] Pz_t0 Pz_t1 (by simp) (by simp)
    (by rw [len_dyL]; omega)
  have hmu2 := relax_close 0 _ _ _ _ hmu cV.1 (by
    have : ∀ (n : ℕ) (a b : List ℤ) (mL : List ℚ), (muV mL n a b).length = n := by
      intro n
      induction n with
      | zero => intro a b mL; rfl
      | succ n ih => intro a b mL; simp [muV, ih]
    rw [this, len_dyL]
    simp [s6])
  simp only [dyL, List.map_cons] at hmu2
  have hG : G2 l ≤ (((g.G2v : ℚ) / 2 ^ g.Q : ℚ) : ℝ) := by
    have := G2_le (Q := g.Q) h hT
    rw [cG] at this
    push_cast
    exact this
  have hS' : Sep 2 l := by
    have := sep_of (2 * 10 ^ 12) h hS
    have e : (((2 * 10 ^ 12 : ℕ) : ℝ) / 10 ^ 12) = 2 := by norm_num
    rw [e] at this
    exact this
  have hGb : (0 : ℚ) ≤ (g.G2v : ℚ) / 2 ^ g.Q := by
    have : (0 : ℚ) ≤ g.G2v := by exact_mod_cast s2
    positivity
  exact gas_main h2 hS' s5 hmu2 (by simp [s6]) hG s1 hGb s3 s4 cC s7 (by simp [dyL, s8]) acc hx0 hx1

/-- Mirror moments for the negative species. -/
def chkMir (W : ℕ) : ℕ → List ℚ → List ℚ → List ℤ → List ℚ → Bool
  | _, [], _, _, _ => true
  | _, _ :: _, [], _, _ => false
  | _, _ :: _, _ :: _, [], _ => false
  | _, _ :: _, _ :: _, _ :: _, [] => false
  | k, v :: vs, e :: es, c :: cs, f :: fs =>
    decide (|(-1 / (k : ℚ)) * v - (c : ℚ) / 2 ^ W| + 1 / (k : ℚ) * e ≤ f) && chkMir W (k + 1) vs es cs fs

/-- `Σ_{i<len} B(k+i) u^(k+i)` against `u^k Pz c u`. -/
theorem mir_close {μ : ℕ → ℝ} {u : ℝ} (W : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ (k : ℕ) (v e : List ℚ) (c : List ℤ) (f : List ℚ), 0 < k → CloseL μ k v e →
    chkMir W k v e c f = true → v.length = c.length → v.length = f.length →
    ∑ i ∈ Finset.range v.length, (-1 / ((k + i : ℕ) : ℝ)) * μ (k + i) * u ^ (k + i) ≤
      u ^ k * Pz c u / 2 ^ W + (sumQ f : ℝ)
  | _, [], _, [], [], _, _, _, _, _ => by simp [Pz, sumQ]
  | _, [], _, [], _ :: _, _, _, _, _, h => by simp at h
  | _, [], _, _ :: _, _, _, _, _, h, _ => by simp at h
  | _, _ :: _, [], _, _, _, hc, _, _, _ => by simp [CloseL] at hc
  | _, _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [chkMir] at h
  | _, _ :: _, _ :: _, _ :: _, [], _, _, h, _, _ => by simp [chkMir] at h
  | k, v :: vs, e :: es, c :: cs, f :: fs, hk, hc, h, hl, hf => by
    simp only [chkMir, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := hc
    have ih := mir_close W hu0 hu1 (k + 1) vs es cs fs (Nat.succ_pos k) g2 h2 (by simpa using hl)
      (by simpa using hf)
    have hkr : (0 : ℝ) < k := by exact_mod_cast hk
    have h1' : |(-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W| + 1 / (k : ℝ) * (e : ℝ) ≤ (f : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr h1
      push_cast at this
      exact this
    rw [List.length_cons, Finset.sum_range_succ']
    have e1 : ∑ i ∈ Finset.range vs.length, (-1 / ((k + (i + 1) : ℕ) : ℝ)) * μ (k + (i + 1)) * u ^ (k + (i + 1)) =
        ∑ i ∈ Finset.range vs.length, (-1 / ((k + 1 + i : ℕ) : ℝ)) * μ (k + 1 + i) * u ^ (k + 1 + i) :=
      Finset.sum_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]
    rw [e1]
    simp only [add_zero]
    have hp0 : 0 ≤ u ^ k := by positivity
    have hp1 : u ^ k ≤ 1 := pow_le_one₀ hu0 hu1
    have ex : (-1 / (k : ℝ)) * μ k * u ^ k - (c : ℝ) / 2 ^ W * u ^ k =
        ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * u ^ k := by ring
    have hb : (-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W) ≤ (f : ℝ) := by
      have a1 : (-1 / (k : ℝ)) * (μ k - v) ≤ 1 / (k : ℝ) * e := by
        have q := (abs_le.mp g1).1
        have : (-1 / (k : ℝ)) * (μ k - v) = 1 / (k : ℝ) * (-(μ k - v)) := by ring
        rw [this]
        have hk1 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hk1
      have a2 := le_abs_self ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)
      linarith
    have hf0 : (0 : ℝ) ≤ f := by
      have h3 := abs_nonneg ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)
      have h4 : (0 : ℝ) ≤ e := (abs_nonneg _).trans g1
      have h5 : (0 : ℝ) ≤ 1 / (k : ℝ) * e := by positivity
      linarith
    have hb2 : ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * u ^ k ≤ (f : ℝ) := by
      rcases le_or_gt 0 ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) with q | q
      · calc _ ≤ ((-1 / (k : ℝ)) * (μ k - v) + ((-1 / (k : ℝ)) * (v : ℝ) - (c : ℝ) / 2 ^ W)) * 1 :=
              mul_le_mul_of_nonneg_left hp1 q
          _ ≤ _ := by linarith
      · have := mul_nonpos_of_nonpos_of_nonneg q.le hp0
        linarith
    have eP : u ^ k * Pz (c :: cs) u / 2 ^ W = (c : ℝ) / 2 ^ W * u ^ k + u ^ (k + 1) * Pz cs u / 2 ^ W := by
      simp only [Pz]
      ring
    rw [eP]
    simp only [sumQ, Rat.cast_add]
    rw [← ex] at hb2
    linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-- The literal radial record of one species. -/
structure RadLit where
  CT : ℕ
  hq : ℚ
  Cq : List ℤ
  δc : ℚ
  s : ℤ
  W : ℕ
  sh : ℕ
  Gs : List (List (ℕ × ℕ))
  As : List (List ℤ)
  Bs : List Blk
  ns : List ℕ
  Tls : List ℤ
  etas : List ℚ

def dBlk : Blk := ⟨1, 0, 0, []⟩

def RadLit.G (R : RadLit) (i : ℕ) : List (ℕ × ℕ) := R.Gs.getD i []
def RadLit.A (R : RadLit) (i : ℕ) : List ℤ := R.As.getD i []
def RadLit.B (R : RadLit) (i : ℕ) : Blk := R.Bs.getD i dBlk
def RadLit.n (R : RadLit) (i : ℕ) : ℕ := R.ns.getD i 0
def RadLit.Tl (R : RadLit) (i : ℕ) : ℤ := R.Tls.getD i 0
def RadLit.eta (R : RadLit) (i : ℕ) : ℚ := R.etas.getD i 0

/-- The full coefficient row of class `i`, scale `2^160`. -/
def RadLit.F (R : RadLit) (i : ℕ) : List ℤ := tRow R.s (R.A i) 0 R.Cq

/-- The tolerance on `a_i(k)`, its bound, and the row tolerance. -/
def RadLit.Ab (R : RadLit) (i : ℕ) : ℚ := R.hq * (pS (R.G i) : ℚ)
def RadLit.da (R : RadLit) (i : ℕ) : ℚ := R.hq * ((pS (R.G i) : ℚ) * Ecos) + 1 / 2 ^ 80
def RadLit.e (R : RadLit) (i : ℕ) : ℚ := R.δc * R.Ab i + 2 * R.da i

/-- The error of class `i`. -/
def RadLit.err (R : RadLit) (i : ℕ) : ℚ :=
  (R.Tl i : ℚ) / 2 ^ (R.W + R.sh) + 384 * (R.e i + 1 / 2 ^ R.W) +
    ((abs1 (R.B i).D : ℤ) : ℚ) / 2 ^ R.W * (384 * R.eta i)

/-- Checks of class `i` against the `Tr` list. -/
def RadLit.chk (R : RadLit) (T : List Tr) (i : ℕ) : Bool :=
  decide (grp T i = R.G i) && decide (rowA R.CT R.hq (R.G i) = R.A i) &&
  decide ((R.B i).D = truncD R.sh (R.n i) (R.F i)) &&
  decide (abs1 ((R.F i).drop (R.n i)) ≤ R.Tl i) && decide ((R.B i).M = R.hq * (pS (R.G i) : ℚ))

/-- Radius enclosure. -/
def radA (i : ℕ) : ℚ := (sigN.getD (min i 15) 0 : ℚ) / 10 ^ 17
def radLo (i : ℕ) : ℚ := 1 / expE (radA i / 4) 24 ^ 4
def radHi (i : ℕ) : ℚ := 1 / expS (radA i / 4) 24 ^ 4

def radChk (rho sg eta : ℚ) (i : ℕ) : Bool :=
  decide (0 ≤ radA i) && decide (radA i ≤ 4) && decide (0 < expS (radA i / 4) 24) &&
  decide (0 < radLo i) && decide (radHi i ≤ rho) && decide ((rho - radLo i) / radLo i ≤ eta) &&
  decide (-radA i + eta ≤ sg)

noncomputable section

theorem rad_cap (i : ℕ) : capSource.rad i = Real.exp (-((radA i : ℚ) : ℝ)) := by
  show Real.exp (-sigmaF i) = _
  unfold sigmaF radA
  push_cast
  rfl

theorem rad_facts {rho sg eta : ℚ} {i : ℕ} (h : radChk rho sg eta i = true) :
    0 < capSource.rad i ∧ capSource.rad i ≤ rho ∧ ((rho : ℝ) - capSource.rad i) / capSource.rad i ≤ eta ∧
      Real.log rho ≤ sg ∧ 0 < rho := by
  simp only [radChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  obtain ⟨l, u⟩ := expNeg_enc h1 h2 (n := 24) (by norm_num) h3
  rw [← rad_cap] at l u
  have hr := Real.exp_pos (-((radA i : ℚ) : ℝ))
  rw [← rad_cap] at hr
  set r := capSource.rad i with hrdef
  have lo' : ((radLo i : ℚ) : ℝ) ≤ r := l
  have hi' : r ≤ ((radHi i : ℚ) : ℝ) := u
  have h5' : ((radHi i : ℚ) : ℝ) ≤ rho := by exact_mod_cast h5
  have h4' : (0 : ℝ) < radLo i := by exact_mod_cast h4
  have h6' : ((rho : ℝ) - radLo i) / radLo i ≤ eta := by exact_mod_cast h6
  have hrr : r ≤ rho := hi'.trans h5'
  have hρ : 0 < (rho : ℝ) := lt_of_lt_of_le hr hrr
  have he : ((rho : ℝ) - r) / r ≤ eta := by
    refine le_trans ?_ h6'
    rw [div_le_div_iff₀ hr h4']
    nlinarith
  refine ⟨hr, hrr, he, ?_, by exact_mod_cast hρ⟩
  have h7' : -((radA i : ℚ) : ℝ) + eta ≤ sg := by exact_mod_cast h7
  have hl : Real.log r = -((radA i : ℚ) : ℝ) := by rw [hrdef, rad_cap, Real.log_exp]
  have : Real.log ((rho : ℝ) / r) ≤ (rho : ℝ) / r - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hρ.ne' hr.ne', hl] at this
  have e : (rho : ℝ) / r - 1 = ((rho : ℝ) - r) / r := by field_simp
  rw [e] at this
  linarith

/-- The cosine moments of a class, through the literal row. -/
theorem class_facts (R : RadLit) {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : ∀ m ≤ 93, cosChk R.CT m = true) {i : ℕ} (hc : R.chk T i = true) :
    (∀ k, |aC (T.map (mkAux g M)) i k - (((R.A i).getD (fold186 k) 0 : ℤ) : ℝ) / 2 ^ 80| ≤ (R.da i : ℝ)) ∧
      (∀ k, |aC (T.map (mkAux g M)) i k| ≤ (R.Ab i : ℝ)) ∧
      aC (T.map (mkAux g M)) i 0 = ((R.B i).M : ℝ) := by
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, c5⟩ := hc
  have hq0' : (0 : ℝ) ≤ R.hq := by exact_mod_cast hq0
  have ha : ∀ k, aC (T.map (mkAux g M)) i k = (R.hq : ℝ) * cS (R.G i) k := by
    intro k
    rw [aC_map hM hg i k T hT, c1, hgq]
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  · rw [ha, ← c2]
    have := rowA_close hcos hq0 (R.G i) k
    unfold RadLit.da
    push_cast
    exact this
  · rw [ha, abs_mul, abs_of_nonneg hq0']
    unfold RadLit.Ab
    push_cast
    exact mul_le_mul_of_nonneg_left (abs_cS_le _ _) hq0'
  · rw [ha, cS_zero, c5]
    push_cast
    rfl

/-- One class, in the shape of the radial sums. -/
theorem class_le (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : ∀ m ≤ 93, cosChk R.CT m = true) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hlen : R.Cq.length = 384) (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc)
    {i : ℕ} (hc : R.chk T i = true) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ (R.B i).rho)
    (hη : ((((R.B i).rho : ℚ) : ℝ) - r) / r ≤ (R.eta i : ℝ)) {x : ℝ} (hx : 0 < x) :
    aC (T.map (mkAux g M)) i 0 * Real.log (max x r) +
      ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
        aC (T.map (mkAux g M)) i (k + 1)) * psiR r x ^ (k + 1) ≤
      blkF R.W (R.B i) x + (R.err i : ℝ) := by
  obtain ⟨f1, f2, f3⟩ := class_facts R hM hg hgq hq0 hT hcos hc
  have hclz := tRow_close (a := aC (T.map (mkAux g M)) i) hs f1 f2 R.Cq 0 hδ hCb
  have hc' := hc
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨_, _⟩, c3⟩, c4⟩, _⟩ := hc'
  have hsc : (2 : ℝ) ^ 160 = 2 ^ (R.W + R.sh) := by rw [hW]
  rw [hsc] at hclz
  have hFl : (R.F i).length = 384 := by
    unfold RadLit.F
    rw [tRow_len, hlen]
  have hAb0 : (0 : ℝ) ≤ R.Ab i := (abs_nonneg _).trans (f2 0)
  have hda0 : (0 : ℝ) ≤ R.da i := (abs_nonneg _).trans (f1 0)
  have hδ0' : (0 : ℝ) ≤ R.δc := by exact_mod_cast hδ0
  have he0 : 0 ≤ (R.δc : ℝ) * R.Ab i + 2 * R.da i := by positivity
  have ha0 : 0 ≤ aC (T.map (mkAux g M)) i 0 := by
    rw [f3]
    have : ((R.B i).M : ℝ) = (R.hq : ℝ) * ((pS (R.G i) : ℕ) : ℝ) := by
      have h5 := hc
      simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at h5
      rw [h5.2]
      push_cast
      rfl
    rw [this]
    have : (0 : ℝ) ≤ R.hq := by exact_mod_cast hq0
    positivity
  have hb := block_le (B := R.B i) (t := fun k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k)
    R.W R.sh (R.n i) 384 hr hrρ f3.symm ha0 c3 hclz hFl he0 hx
  refine hb.trans ?_
  have hTl : ((abs1 ((R.F i).drop (R.n i)) : ℤ) : ℝ) ≤ (R.Tl i : ℝ) := by exact_mod_cast c4
  have hL0 : (0 : ℝ) ≤ ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W := by
    have : (0 : ℝ) ≤ ((abs1 (R.B i).D : ℤ) : ℝ) := by exact_mod_cast abs1_nonneg _
    positivity
  have h1 : ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W * (((384 : ℕ) : ℝ) * ((((R.B i).rho : ℝ) - r) / r)) ≤
      ((abs1 (R.B i).D : ℤ) : ℝ) / 2 ^ R.W * (384 * (R.eta i : ℝ)) := by
    push_cast
    gcongr
  have h2 : ((abs1 ((R.F i).drop (R.n i)) : ℤ) : ℝ) / 2 ^ (R.W + R.sh) ≤
      (R.Tl i : ℝ) / 2 ^ (R.W + R.sh) := by gcongr
  unfold RadLit.err RadLit.e
  push_cast
  push_cast at h1
  linarith

/-- All classes together, for a positive `x`, with species sign `s`. -/
theorem classes_le (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : ∀ m ≤ 93, cosChk R.CT m = true) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hlen : R.Cq.length = 384) (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc)
    (n : ℕ) (hB : R.Bs.length = n) (hc : ∀ i < n, R.chk T i = true)
    (hrad : ∀ i < n, 0 < S.rad i ∧ S.rad i ≤ (R.B i).rho ∧
      ((((R.B i).rho : ℚ) : ℝ) - S.rad i) / S.rad i ≤ (R.eta i : ℝ)) {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max x (S.rad i)) +
      ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
        aC (T.map (mkAux g M)) i (k + 1)) * psiR (S.rad i) x ^ (k + 1)) ≤
      sumF R.W R.Bs x + ∑ i ∈ Finset.range n, (R.err i : ℝ) := by
  have e : sumF R.W R.Bs x = ∑ i ∈ Finset.range n, blkF R.W (R.B i) x := by
    subst hB
    unfold sumF
    rw [← sum_getD dBlk (fun B => blkF R.W B x)]
    rfl
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  obtain ⟨r1, r2, r3⟩ := hrad i hi'
  exact class_le R hM hg hgq hq0 hT hcos hs hδ hCb hlen hW hδ0 (hc i hi') r1 r2 r3 hx

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ)
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs (abs_pow_sub_pow_le_unit)

/-! ### Cell lists -/

def relP (P : ℕ) : List Tr → List GD → Bool
  | [], [] => true
  | t :: ts, d :: ds => decide ((d.a : ℤ) = t.1 ∧ (d.b : ℤ) = t.2.1 ∧ (d.p : ℤ) = t.2.2) && d.ok P &&
      relP P ts ds
  | _, _ => false

def relN (P : ℕ) : List Tr → List GD → Bool
  | [], [] => true
  | t :: ts, d :: ds => decide ((d.a : ℤ) = -t.2.1 ∧ (d.b : ℤ) = -t.1 ∧ (d.p : ℤ) = t.2.2) && d.ok P &&
      relN P ts ds
  | _, _ => false

noncomputable section

theorem ok_lt {P : ℕ} {d : GD} (h : d.ok P = true) : d.a < d.b := by
  simp only [GD.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.2

theorem relP_spec {P T : ℕ} {Tz : ℤ} (hT : (T : ℤ) = Tz) : ∀ (ts : List Tr) (L : List GD),
    relP P ts L = true → List.Forall₂ (Rel P T) (ts.map (mkCell 1 Tz)) L
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [relP] at h
  | _ :: _, [], h => by simp [relP] at h
  | t :: ts, d :: ds, h => by
    simp only [relP, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2, h3⟩, hok⟩, hr⟩ := h
    have hlt := ok_lt hok
    have hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2 := by omega
    obtain ⟨e1, e2, e3⟩ := mkCell_eq (m := 1) (T := Tz) hv (by omega) zero_le_one
    refine .cons ⟨?_, ?_, ?_, hok⟩ (relP_spec hT ts ds hr)
    · rw [e1, ← h1]; simp
    · rw [e2, ← h2]; simp
    · rw [e3, ← h3, ← hT]; simp

theorem relN_spec {P T : ℕ} {Tz : ℤ} (hT : (T : ℤ) = Tz) : ∀ (ts : List Tr) (L : List GD),
    relN P ts L = true →
    List.Forall₂ (Rel P T) (ts.map fun t => (mkCell 1 Tz t).reflect) L
  | [], [], _ => .nil
  | [], _ :: _, h => by simp [relN] at h
  | _ :: _, [], h => by simp [relN] at h
  | t :: ts, d :: ds, h => by
    simp only [relN, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2, h3⟩, hok⟩, hr⟩ := h
    have hlt := ok_lt hok
    have hv : t.1 < t.2.1 ∧ 0 ≤ t.2.2 := by omega
    obtain ⟨e1, e2, e3⟩ := mkCell_eq (m := 1) (T := Tz) hv (by omega) zero_le_one
    have r1 : (mkCell 1 Tz t).reflect.lo = -(mkCell 1 Tz t).hi := rfl
    have r2 : (mkCell 1 Tz t).reflect.hi = -(mkCell 1 Tz t).lo := rfl
    have r3 : (mkCell 1 Tz t).reflect.w = (mkCell 1 Tz t).w := rfl
    have c1 : (d.a : ℝ) = -(t.2.1 : ℝ) := by exact_mod_cast h1
    have c2 : (d.b : ℝ) = -(t.1 : ℝ) := by exact_mod_cast h2
    refine .cons ⟨?_, ?_, ?_, hok⟩ (relN_spec hT ts ds hr)
    · rw [r1, e2, c1]; ring
    · rw [r2, e1, c2]; ring
    · rw [r3, e3, ← h3, ← hT]; simp

/-! ### The coefficient enclosure of `capSource` -/

theorem cap_q : capSource.q = Real.exp (-(((27 / 500 : ℚ)) : ℝ)) := by
  show Real.exp (-(27 / 250 : ℝ) / 2) = _
  congr 1
  push_cast
  ring

theorem q_enc : ((1 / expE (27 / 500 / 4) 24 ^ 4 : ℚ) : ℝ) ≤ capSource.q ∧
    capSource.q ≤ ((1 / expS (27 / 500 / 4) 24 ^ 4 : ℚ) : ℝ) := by
  rw [cap_q]
  exact expNeg_enc (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)

theorem strength_eq (S : CapSource) (h1 : S.q ^ 2 < 1) (h0 : 0 ≤ S.q ^ 2) :
    S.strength = 3 * (1 - (S.q ^ 2) ^ 2) / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  unfold CapSource.strength CapSource.normalizer
  set r := S.q ^ 2
  have a : 1 - r ≠ 0 := by linarith
  have b : 1 + 4 * r + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem curvature_eq (S : CapSource) (h1 : S.q ^ 2 < 1) (h0 : 0 ≤ S.q ^ 2) :
    S.curvature = (1 - S.q ^ 2) ^ 2 / (2 * (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2)) := by
  unfold CapSource.curvature CapSource.normalizer
  set r := S.q ^ 2
  have a : 1 - r ≠ 0 := by linarith
  have b : 1 + 4 * r + r ^ 2 ≠ 0 := by positivity
  field_simp

/-- The enclosure check of a literal `CoefEnc`. -/
def CoefEnc.chk (E : CoefEnc) : Bool :=
  decide (0 ≤ E.ql) && decide (E.ql ≤ 1 / expE (27 / 500 / 4) 24 ^ 4) &&
  decide (1 / expS (27 / 500 / 4) 24 ^ 4 ≤ E.qh) && decide (E.qh < 1) &&
  decide (0 ≤ E.Al) && decide (0 ≤ E.Bl) &&
  decide (E.Al ≤ Afun (E.qh ^ 2)) && decide (Afun (E.ql ^ 2) ≤ E.Ah) &&
  decide (E.Bl ≤ Bfun (E.qh ^ 2)) && decide (Bfun (E.ql ^ 2) ≤ E.Bh)

theorem CoefEnc.valid {E : CoefEnc} (h : E.chk = true) : E.Valid capSource := by
  simp only [CoefEnc.chk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  obtain ⟨q1, q2⟩ := q_enc
  have l : (E.ql : ℝ) ≤ capSource.q := by
    refine le_trans ?_ q1
    exact_mod_cast h2
  have u : capSource.q ≤ E.qh := by
    refine q2.trans ?_
    exact_mod_cast h3
  have ql0 : (0 : ℝ) ≤ E.ql := by exact_mod_cast h1
  have qh1 : (E.qh : ℝ) < 1 := by exact_mod_cast h4
  set q := capSource.q with hq
  have q0 : 0 ≤ q := ql0.trans l
  have rl : (E.ql : ℝ) ^ 2 ≤ q ^ 2 := by gcongr
  have ru : q ^ 2 ≤ (E.qh : ℝ) ^ 2 := by gcongr
  have rl0 : (0 : ℝ) ≤ (E.ql : ℝ) ^ 2 := by positivity
  have r1 : q ^ 2 < 1 := by nlinarith
  have rh1 : (E.qh : ℝ) ^ 2 < 1 := by nlinarith [q0.trans u]
  have r0 : 0 ≤ q ^ 2 := by positivity
  have se := strength_eq capSource r1 r0
  have ce := curvature_eq capSource r1 r0
  rw [← hq] at se ce
  have A1 : ((Afun (E.qh ^ 2) : ℚ) : ℝ) ≤ capSource.strength := by
    rw [se]
    unfold Afun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have A2 : capSource.strength ≤ ((Afun (E.ql ^ 2) : ℚ) : ℝ) := by
    rw [se]
    unfold Afun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have B1 : ((Bfun (E.qh ^ 2) : ℚ) : ℝ) ≤ capSource.curvature := by
    rw [ce]
    unfold Bfun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  have B2 : capSource.curvature ≤ ((Bfun (E.ql ^ 2) : ℚ) : ℝ) := by
    rw [ce]
    unfold Bfun
    push_cast
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  exact ⟨h1, h5, h6, l, u, le_trans (by exact_mod_cast h7) A1, A2.trans (by exact_mod_cast h8),
    le_trans (by exact_mod_cast h9) B1, B2.trans (by exact_mod_cast h10)⟩

/-- Rational upper bound of `auxTail` at degree 384. -/
def CoefEnc.tail (E : CoefEnc) (m : ℚ) (c : ℚ) : ℚ :=
  E.qh ^ 385 * ((1 / 385 + E.Ah) * (1 / (1 - E.qh)) +
    E.Bh * (385 * (1 / (1 - E.qh)) + E.qh * (1 / (1 - E.qh)) ^ 2)) * m * c

theorem auxTail_le {E : CoefEnc} {S : CapSource} (h : E.Valid S) (hq1 : E.qh < 1) (σ : Sign) {m : ℚ}
    (hm : S.auxMass σ ≤ m) (hm0 : 0 ≤ S.auxMass σ) {c : ℚ} (hc : (if σ = Sign.neg then (2 : ℝ) else 1) ≤ c) :
    S.auxTail (Trunc.finite 384) σ ≤ ((E.tail m c : ℚ) : ℝ) := by
  have q0 : 0 ≤ S.q := (by exact_mod_cast h.ql0 : (0 : ℝ) ≤ E.ql).trans h.ql
  have hq1' : (E.qh : ℝ) < 1 := by exact_mod_cast hq1
  have qh0 : (0 : ℝ) ≤ E.qh := q0.trans h.qh
  have a0 : 0 ≤ S.strength := (by exact_mod_cast h.Al0 : (0 : ℝ) ≤ E.Al).trans h.Al
  have b0 : 0 ≤ S.curvature := (by exact_mod_cast h.Bl0 : (0 : ℝ) ≤ E.Bl).trans h.Bl
  have g1 : 0 < 1 - (E.qh : ℝ) := by linarith
  have g2 : 0 < 1 - S.q := by linarith [h.qh]
  have g3 : 1 / (1 - S.q) ≤ 1 / (1 - (E.qh : ℝ)) := by
    apply one_div_le_one_div_of_le g1
    linarith [h.qh]
  have g0 : 0 ≤ 1 / (1 - S.q) := by positivity
  have hAh := h.Ah
  have hBh := h.Bh
  have hqh := h.qh
  have s0 : (0 : ℝ) ≤ (if σ = Sign.neg then (2 : ℝ) else 1) := by split_ifs <;> norm_num
  unfold CapSource.auxTail CoefEnc.tail
  push_cast
  have B0 : (0 : ℝ) ≤ E.Bh := b0.trans hBh
  have A0 : (0 : ℝ) ≤ E.Ah := a0.trans hAh
  have m0 : (0 : ℝ) ≤ m := hm0.trans hm
  have e1 : ((384 : ℝ) + 1) = 385 := by norm_num
  rw [e1]
  gcongr

/-! ### Mirror block of the negative species -/

/-- `d ρ^k`, rounded down, with `ρ = rn/2^rb`. -/
def wt (rn rb : ℕ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | k, d :: t => (d * (rn : ℤ) ^ (k + 1) / 2 ^ (rb * (k + 1))) :: wt rn rb (k + 1) t

theorem wt_len (rn rb : ℕ) : ∀ (F : List ℤ) (k : ℕ), (wt rn rb k F).length = F.length
  | [], _ => rfl
  | _ :: t, k => by simp [wt, wt_len rn rb t (k + 1)]

theorem wt_close {t : ℕ → ℝ} {sc e Fb η r : ℝ} {rn rb K : ℕ} (hsc : 0 < sc) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hρ1 : (rn : ℝ) / 2 ^ rb ≤ 1) (hη : |r - (rn : ℝ) / 2 ^ rb| ≤ η) (he : 0 ≤ e) (hFb : 0 ≤ Fb) :
    ∀ (F : List ℤ) (k : ℕ), CLz t sc e k F → (∀ d ∈ F, |(d : ℝ)| / sc ≤ Fb) → k + F.length ≤ K →
    CLz (fun k => t k * r ^ k) sc (e + Fb * ((K : ℝ) * η) + 1 / sc) k (wt rn rb k F)
  | [], _, _, _, _ => trivial
  | d :: F, k, hc, hb, hk => by
    obtain ⟨h1, h2⟩ := hc
    refine ⟨?_, wt_close hsc hr0 hr1 hρ1 hη he hFb F (k + 1) h2
      (fun d hd => hb d (List.mem_cons_of_mem _ hd)) (by simp at hk; omega)⟩
    set ρ : ℝ := (rn : ℝ) / 2 ^ rb with hρd
    have hρ0 : 0 ≤ ρ := by positivity
    have hd := hb d (by simp)
    have hrp0 : 0 ≤ r ^ (k + 1) := by positivity
    have hrp1 : r ^ (k + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hη0 : 0 ≤ η := (abs_nonneg _).trans hη
    have hpw := abs_pow_sub_pow_le_unit hr0 hr1 hρ0 hρ1 (k + 1)
    have hkK : ((k + 1 : ℕ) : ℝ) ≤ K := by
      have : k + 1 ≤ K := by simp at hk; omega
      exact_mod_cast this
    have hpw2 : |r ^ (k + 1) - ρ ^ (k + 1)| ≤ (K : ℝ) * η := by
      refine hpw.trans ?_
      have := abs_nonneg (r - ρ)
      calc ((k + 1 : ℕ) : ℝ) * |r - ρ| ≤ (K : ℝ) * |r - ρ| := by gcongr
        _ ≤ _ := by gcongr
    -- floor
    set N : ℤ := d * (rn : ℤ) ^ (k + 1) with hN
    set Dn : ℤ := 2 ^ (rb * (k + 1)) with hDn
    have hD0 : 0 < Dn := by positivity
    have f1 : N / Dn * Dn ≤ N := Int.ediv_mul_le N hD0.ne'
    have f2 : N < (N / Dn + 1) * Dn := Int.lt_ediv_add_one_mul_self N hD0
    have hD0' : (0 : ℝ) < (Dn : ℝ) := by exact_mod_cast hD0
    have f1' : ((N / Dn : ℤ) : ℝ) * Dn ≤ N := by exact_mod_cast f1
    have f2' : (N : ℝ) < (((N / Dn : ℤ) : ℝ) + 1) * Dn := by exact_mod_cast f2
    have eN : (N : ℝ) / Dn = (d : ℝ) * ρ ^ (k + 1) := by
      rw [hN, hDn, hρd]
      push_cast
      rw [div_pow, pow_mul, ← pow_mul (2 : ℝ)]
      ring_nf
    have g1 : ((N / Dn : ℤ) : ℝ) ≤ (d : ℝ) * ρ ^ (k + 1) := by
      rw [← eN, le_div_iff₀ hD0']; exact f1'
    have g2 : (d : ℝ) * ρ ^ (k + 1) < ((N / Dn : ℤ) : ℝ) + 1 := by
      rw [← eN, div_lt_iff₀ hD0']; exact f2'
    have ex : t (k + 1) * r ^ (k + 1) - ((N / Dn : ℤ) : ℝ) / sc =
        (t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1) + (d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1)) +
          ((d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)) / sc := by ring
    show |t (k + 1) * r ^ (k + 1) - ((N / Dn : ℤ) : ℝ) / sc| ≤ _
    rw [ex]
    refine (abs_add_le _ _).trans ?_
    have t1 := abs_add_le ((t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1))
      ((d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1)))
    have t2 : |(t (k + 1) - (d : ℝ) / sc) * r ^ (k + 1)| ≤ e := by
      rw [abs_mul, abs_of_nonneg hrp0]
      calc _ ≤ |t (k + 1) - (d : ℝ) / sc| * 1 := by gcongr
        _ ≤ e := by linarith
    have t3 : |(d : ℝ) / sc * (r ^ (k + 1) - ρ ^ (k + 1))| ≤ Fb * ((K : ℝ) * η) := by
      rw [abs_mul, abs_div, abs_of_pos hsc]
      exact mul_le_mul hd hpw2 (abs_nonneg _) hFb
    have t4 : |((d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)) / sc| ≤ 1 / sc := by
      rw [abs_div, abs_of_pos hsc]
      have : |(d : ℝ) * ρ ^ (k + 1) - ((N / Dn : ℤ) : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      gcongr
    linarith

theorem CLz_add {t1 t2 : ℕ → ℝ} {sc e1 e2 : ℝ} : ∀ (F1 F2 : List ℤ) (k : ℕ),
    CLz t1 sc e1 k F1 → CLz t2 sc e2 k F2 → F1.length = F2.length →
    CLz (fun k => t1 k + t2 k) sc (e1 + e2) k (addZ F1 F2)
  | [], [], _, _, _, _ => by simp [addZ, CLz]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: F1, b :: F2, k, h1, h2, h => by
    refine ⟨?_, CLz_add F1 F2 (k + 1) h1.2 h2.2 (by simpa using h)⟩
    have ex : t1 (k + 1) + t2 (k + 1) - (((a + b : ℤ)) : ℝ) / sc =
        (t1 (k + 1) - (a : ℝ) / sc) + (t2 (k + 1) - (b : ℝ) / sc) := by
      push_cast
      ring
    rw [ex]
    exact (abs_add_le _ _).trans (add_le_add h1.1 h2.1)

/-! ### Change of variable to the Chebyshev list in `w` -/

/-- With `x = (A + B w)/D'` and `E = 2 D'`: `E rawSum (Rc l) 0 w = E^len Pz l x`. -/
def RcS (A B E a : ℤ) (n : ℕ) (r : List ℤ) : List ℤ :=
  addZ [a * E ^ n] (addZ (smulZ (2 * A) r) (smulZ B (xmulZ r)))

def Rc (A B E : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: t => RcS A B E a t.length (Rc A B E t)

theorem Rc_eval (A B E : ℤ) {w x : ℝ} (hx : (E : ℝ) * x = 2 * ((A : ℝ) + B * w)) : ∀ l : List ℤ,
    (E : ℝ) * rawSum (Rc A B E l) 0 w = (E : ℝ) ^ l.length * Pz l x
  | [] => by simp [Rc, Pz]
  | a :: t => by
    have ih := Rc_eval A B E hx t
    simp only [Rc, RcS, rawSum_addZ, rawSum_smulZ, rawSum_xmulZ, List.length_cons, Pz, rawSum_cons,
      rawSum_nil, basis_zero, mul_one, add_zero]
    push_cast
    have e : (E : ℝ) ^ (t.length + 1) * ((a : ℝ) + x * Pz t x) =
        (E : ℝ) * ((a : ℝ) * (E : ℝ) ^ t.length) + ((E : ℝ) * x) * ((E : ℝ) ^ t.length * Pz t x) := by
      ring
    rw [e, ← ih, hx]
    ring

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz xmulZ rawSum_xmulZ)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ addQ rawQ_addQ diffSum abs_rawQ_sub_le)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (vY vY_pos vY_le_one physX_pos reflectL)

/-- The fold of the classes of the mirror series. -/
def mirF (R : RadLit) (rns : List ℕ) (rb : ℕ) : ℕ → List ℤ
  | 0 => List.replicate 384 0
  | i + 1 => addZ (mirF R rns rb i) (wt (rns.getD i 0) rb 0 (R.F i))

/-- Its error. -/
def mirE (R : RadLit) (Fb : ℚ) : ℕ → ℚ
  | 0 => 0
  | i + 1 => mirE R Fb i + (R.e i + Fb * (384 * R.eta i) + 1 / 2 ^ 160)

noncomputable section

theorem CLz_zero {sc : ℝ} : ∀ (n k : ℕ), CLz (fun _ => 0) sc 0 k (List.replicate n 0)
  | 0, _ => trivial
  | n + 1, k => ⟨by simp, CLz_zero n (k + 1)⟩

/-- The closeness of one class row. -/
theorem class_close (R : RadLit) {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} (hM : 0 ≤ M) (hg : 0 ≤ g)
    (hgq : (R.hq : ℝ) = g / M) (hq0 : 0 ≤ R.hq) (hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2)
    (hcos : ∀ m ≤ 93, cosChk R.CT m = true) (hs : |(R.s : ℝ)| = 1)
    (hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq) (hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81)
    (hδ0 : 0 ≤ R.δc) {i : ℕ} (hc : R.chk T i = true) :
    CLz (fun k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0
      (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ) := by
  obtain ⟨f1, f2, _⟩ := class_facts R hM hg hgq hq0 hT hcos hc
  have hclz := tRow_close (a := aC (T.map (mkAux g M)) i) hs f1 f2 R.Cq 0 hδ hCb
  have hAb0 : (0 : ℝ) ≤ R.Ab i := (abs_nonneg _).trans (f2 0)
  have hda0 : (0 : ℝ) ≤ R.da i := (abs_nonneg _).trans (f1 0)
  have hδ0' : (0 : ℝ) ≤ R.δc := by exact_mod_cast hδ0
  have e : ((R.e i : ℚ) : ℝ) = (R.δc : ℝ) * R.Ab i + 2 * R.da i := by
    unfold RadLit.e
    push_cast
    ring
  rw [e]
  exact ⟨hclz, by positivity⟩

theorem mirF_close (R : RadLit) (rns : List ℕ) (rb : ℕ) {t : ℕ → ℕ → ℝ} {r : ℕ → ℝ} {Fb : ℚ}
    (hFb0 : 0 ≤ Fb) (n : ℕ)
    (hc : ∀ i < n, CLz (t i) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0 (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ))
    (hr : ∀ i < n, 0 ≤ r i ∧ r i ≤ 1 ∧ ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb ≤ 1 ∧
      |r i - ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb| ≤ (R.eta i : ℝ))
    (hl : ∀ i < n, (R.F i).length = 384)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) :
    CLz (fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k) (2 ^ 160) ((mirE R Fb n : ℚ) : ℝ) 0
      (mirF R rns rb n) ∧ (mirF R rns rb n).length = 384 ∧ (0 : ℝ) ≤ ((mirE R Fb n : ℚ) : ℝ) := by
  induction n with
  | zero =>
    refine ⟨?_, by simp only [mirF, List.length_replicate], by simp [mirE]⟩
    simp only [Finset.range_zero, Finset.sum_empty, mirF, mirE, Rat.cast_zero]
    exact CLz_zero 384 0
  | succ n ih =>
    obtain ⟨a1, a2, a3⟩ := ih (fun i hi => hc i (by omega)) (fun i hi => hr i (by omega))
      (fun i hi => hl i (by omega)) (fun i hi => hb i (by omega))
    obtain ⟨c1, c2⟩ := hc n (by omega)
    obtain ⟨r0, r1, r2, r3⟩ := hr n (by omega)
    have hFb0' : (0 : ℝ) ≤ Fb := by exact_mod_cast hFb0
    have hw := wt_close (t := t n) (sc := 2 ^ 160) (e := ((R.e n : ℚ) : ℝ)) (Fb := (Fb : ℝ))
      (η := (R.eta n : ℝ)) (r := r n) (rn := rns.getD n 0) (rb := rb) (K := 384) (by positivity) r0 r1 r2
      r3 c2 hFb0' (R.F n) 0 c1 (hb n (by omega)) (by rw [hl n (by omega)])
    have hwl : (wt (rns.getD n 0) rb 0 (R.F n)).length = 384 := by
      rw [wt_len, hl n (by omega)]
    have hadd := CLz_add _ _ 0 a1 hw (by rw [a2, hwl])
    have eE : ((mirE R Fb (n + 1) : ℚ) : ℝ) = ((mirE R Fb n : ℚ) : ℝ) +
        (((R.e n : ℚ) : ℝ) + (Fb : ℝ) * (((384 : ℕ) : ℝ) * (R.eta n : ℝ)) + 1 / 2 ^ 160) := by
      simp only [mirE]
      push_cast
      ring
    have eT : (fun k => ∑ i ∈ Finset.range (n + 1), t i k * r i ^ k) =
        fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k + t n k * r n ^ k := by
      funext k
      rw [Finset.sum_range_succ]
    have hη0 : (0 : ℝ) ≤ R.eta n := (abs_nonneg _).trans r3
    refine ⟨?_, ?_, ?_⟩
    · rw [eT, eE]
      exact hadd
    · simp only [mirF]
      rw [len_addZ, a2, hwl]
      rfl
    · rw [eE]
      positivity

theorem CLz_congr {t1 t2 : ℕ → ℝ} {sc e : ℝ} (h : ∀ k, t1 k = t2 k) :
    ∀ (F : List ℤ) (k : ℕ), CLz t1 sc e k F → CLz t2 sc e k F
  | [], _, _ => trivial
  | _ :: F, k, hc => ⟨by rw [← h]; exact hc.1, CLz_congr h F (k + 1) hc.2⟩

/-- The mirror series of all classes. -/
theorem mirror_series (R : RadLit) (rns : List ℕ) (rb nm : ℕ) {t : ℕ → ℕ → ℝ} {r : ℕ → ℝ} {Fb : ℚ}
    (hFb0 : 0 ≤ Fb) (n : ℕ) (hW : R.W + R.sh = 160)
    (hc : ∀ i < n, CLz (t i) (2 ^ 160) ((R.e i : ℚ) : ℝ) 0 (R.F i) ∧ (0 : ℝ) ≤ ((R.e i : ℚ) : ℝ))
    (hr : ∀ i < n, 0 ≤ r i ∧ r i ≤ 1 ∧ ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb ≤ 1 ∧
      |r i - ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb| ≤ (R.eta i : ℝ))
    (hl : ∀ i < n, (R.F i).length = 384)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384, t i (k + 1) * (r i * u) ^ (k + 1) ≤
      polK (truncD R.sh nm (mirF R rns rb n)) 0 u / 2 ^ R.W +
        (((abs1 ((mirF R rns rb n).drop nm) : ℤ) : ℝ) / 2 ^ 160 +
          384 * (((mirE R Fb n : ℚ) : ℝ) + 1 / 2 ^ R.W)) := by
  obtain ⟨a1, a2, a3⟩ := mirF_close R rns rb hFb0 n hc hr hl hb
  have hsc : (2 : ℝ) ^ 160 = 2 ^ (R.W + R.sh) := by rw [hW]
  rw [hsc] at a1
  have h := ser_le (t := fun k => ∑ i ∈ Finset.range n, t i k * r i ^ k) (y := u) (yh := u) (η := 0)
    R.W R.sh 384 hu0 hu1 hu0 hu1 (by simp) a3 (mirF R rns rb n) nm 0 a1 (by rw [a2])
  rw [a2, serR_eq] at h
  simp only [mul_zero, add_zero] at h
  have e : ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384, t i (k + 1) * (r i * u) ^ (k + 1) =
      ∑ k ∈ Finset.range 384, (∑ i ∈ Finset.range n, t i (k + 1) * r i ^ (k + 1)) * u ^ (k + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow]
    ring
  rw [e, hsc]
  push_cast at h
  linarith

/-! ### Reflection and field shape -/

theorem field_eq (S : CapSource) (K : ℕ) (σ : Sign) (x : ℝ) :
    S.ordField (Trunc.finite K) σ x =
      (physL (S.gas σ) (fun u => Real.log |u|) + potL (S.gas σ) (x + 1 / x) +
        massL (S.gas σ) * Real.log |x|) - kappa σ - 53 / 58 * Real.log (1 + x ^ 2) +
      (if σ = Sign.pos then S.R900 x + S.Eref900 else 0) + S.radialA (Trunc.finite K) σ x +
      S.auxTail (Trunc.finite K) σ := by
  simp only [CapSource.ordField, CapSource.rowField, CapSource.refR, CapSource.refC, Flavor.marked,
    physL, potL, List.map_nil, List.sum_nil]
  ring

theorem field_pos (S : CapSource) (K : ℕ) (h2 : ∀ c ∈ S.gas Sign.pos, 2 ≤ c.lo) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    S.ordField (Trunc.finite K) Sign.pos u ≤
      physL (S.gas Sign.pos) (fun s => Real.log |u - s|) - kappa Sign.pos -
        53 / 58 * Real.log (1 + u ^ 2) + S.Eref900 + S.radialA (Trunc.finite K) Sign.pos u +
        S.auxTail (Trunc.finite K) Sign.pos := by
  rw [field_eq]
  have a := row_list h2 hu0 hu1
  have b := physL_refl_le h2 hu0 hu1 900
  have c : S.R900 u = ∑ k ∈ Finset.range 900, u ^ (k + 1) / ((k : ℝ) + 1) *
      physL (S.gas Sign.pos) (fun s => s ^ (k + 1)) := by
    unfold CapSource.R900 CapSource.reflMoment
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [if_pos rfl]
  rw [← c] at b
  linarith

theorem field_neg (S : CapSource) (K : ℕ) (h : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2) {u : ℝ} (hu0 : 0 < u)
    (hu1 : u ≤ 1) :
    S.ordField (Trunc.finite K) Sign.neg (-u) =
      physL (reflectL (S.gas Sign.neg)) (fun s => Real.log |u - s|) +
        physL (reflectL (S.gas Sign.neg)) (fun s => Real.log |1 - s * u|) - kappa Sign.neg -
        53 / 58 * Real.log (1 + u ^ 2) + S.radialA (Trunc.finite K) Sign.neg (-u) +
        S.auxTail (Trunc.finite K) Sign.neg := by
  rw [field_eq]
  have a := row_list_neg h hu0 hu1
  have e : (if Sign.neg = Sign.pos then S.R900 (-u) + S.Eref900 else 0) = 0 := if_neg (by decide)
  rw [e, neg_sq]
  linarith

/-! ### The tail `Eref900` -/

def eInt (n P Q T : ℕ) (d : GD) : ℕ :=
  d.p * 10 ^ 12 * ((d.al + 1) ^ n / 2 ^ (n * P - Q) + 1) / (T * (d.b - d.a)) + 1

def erefTerm (c : YCell) : ℝ :=
  let prim : ℝ → ℝ := fun x => x ^ 900 / 900 + x ^ 901 / 901
  c.w / (c.hi - c.lo) * (prim (YCell.physX c.lo) - prim (YCell.physX c.hi)) / 901

theorem nat_lt_div (n d : ℕ) (hd : 0 < d) : n < (n / d + 1) * d := by
  rw [mul_comm]
  exact Nat.lt_mul_div_succ n hd

theorem xpow_le {P Q n a : ℕ} (hQ : Q ≤ n * P) {x : ℝ} (x0 : 0 ≤ x)
    (hxa : x ≤ ((a : ℝ) + 1) / 2 ^ P) :
    x ^ n ≤ (((a + 1) ^ n / 2 ^ (n * P - Q) + 1 : ℕ) : ℝ) / 2 ^ Q := by
  set X : ℕ := (a + 1) ^ n / 2 ^ (n * P - Q) + 1 with hX
  have s1 : x ^ n ≤ (((a : ℝ) + 1) / 2 ^ P) ^ n := by gcongr
  refine s1.trans ?_
  have hdv : 0 < 2 ^ (n * P - Q) := by positivity
  have s2 : (a + 1) ^ n < X * 2 ^ (n * P - Q) := nat_lt_div _ _ hdv
  have s3 : (((a : ℝ) + 1)) ^ n ≤ (X : ℝ) * 2 ^ (n * P - Q) := by
    exact_mod_cast s2.le
  have s4 : ((2 : ℝ) ^ P) ^ n = 2 ^ (n * P - Q) * 2 ^ Q := by
    rw [← pow_add, Nat.sub_add_cancel hQ, ← pow_mul, mul_comm]
  rw [div_pow, s4, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (0 : ℝ) < 2 ^ Q := by positivity
  calc ((a : ℝ) + 1) ^ n * 2 ^ Q ≤ ((X : ℝ) * 2 ^ (n * P - Q)) * 2 ^ Q := by gcongr
    _ = _ := by ring

theorem cell_erefG {P Q T n m : ℕ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hnm : n ≤ m)
    (hQ : Q ≤ n * P) {c : YCell} {d : GD} (h : Rel P T c d) (hT : 0 < T) :
    c.w / (c.hi - c.lo) * ((YCell.physX c.lo ^ n / A + YCell.physX c.lo ^ m / B) -
      (YCell.physX c.hi ^ n / A + YCell.physX c.hi ^ m / B)) / B ≤
      (1 / A + 1 / B) / B * ((eInt n P Q T d : ℝ) / 2 ^ Q) := by
  have f := h.facts
  have hdab : (0 : ℝ) < (d.b : ℝ) - d.a := by
    have : (d.a : ℝ) < d.b := by exact_mod_cast f.dab
    linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h2h : 2 ≤ c.hi := f.two.trans c.lo_lt.le
  have x0 := (vY_pos f.two).le
  have x1 := vY_le_one f.two
  have y0 := (vY_pos h2h).le
  rw [physX_pos f.two, physX_pos h2h]
  set x := vY c.lo with hx
  set y := vY c.hi with hy
  have hgc : c.w / (c.hi - c.lo) = (d.p : ℝ) * 10 ^ 12 / ((T : ℝ) * ((d.b : ℝ) - d.a)) := by
    rw [h.w, h.lo, h.hi]
    field_simp
  have hg0 : 0 ≤ c.w / (c.hi - c.lo) := by rw [hgc]; positivity
  set X : ℕ := (d.al + 1) ^ n / 2 ^ (n * P - Q) + 1 with hX
  have hp1 : x ^ n ≤ (X : ℝ) / 2 ^ Q := xpow_le hQ x0 f.lu
  have hp2 : x ^ m ≤ x ^ n := pow_le_pow_of_le_one x0 x1 hnm
  have hA' : 0 ≤ 1 / A := by positivity
  have hB' : 0 ≤ 1 / B := by positivity
  have hprim : x ^ n / A + x ^ m / B ≤ (1 / A + 1 / B) * ((X : ℝ) / 2 ^ Q) := by
    have a1 : x ^ n / A ≤ 1 / A * ((X : ℝ) / 2 ^ Q) := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hp1 (by positivity)
    have a2 : x ^ m / B ≤ 1 / B * ((X : ℝ) / 2 ^ Q) := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left (hp2.trans hp1) (by positivity)
    linarith
  have hyy : 0 ≤ y ^ n / A + y ^ m / B := by positivity
  have hE : (d.p : ℝ) * 10 ^ 12 * (X : ℝ) / ((T : ℝ) * ((d.b : ℝ) - d.a)) ≤ (eInt n P Q T d : ℝ) := by
    have hM : 0 < T * (d.b - d.a) := Nat.mul_pos hT (by have := f.dab; omega)
    have hcast : ((T * (d.b - d.a) : ℕ) : ℝ) = (T : ℝ) * ((d.b : ℝ) - d.a) := by
      rw [Nat.cast_mul, Nat.cast_sub f.dab.le]
    have n1 : d.p * 10 ^ 12 * X ≤ eInt n P Q T d * (T * (d.b - d.a)) :=
      (nat_lt_div _ _ hM).le
    have n2 : ((d.p * 10 ^ 12 * X : ℕ) : ℝ) ≤ (eInt n P Q T d : ℝ) * ((T * (d.b - d.a) : ℕ) : ℝ) := by
      exact_mod_cast n1
    rw [hcast] at n2
    push_cast at n2
    rw [div_le_iff₀ (by positivity)]
    have e10 : (10 : ℝ) ^ 12 = 1000000000000 := by norm_num
    rw [e10]
    exact n2
  have main : c.w / (c.hi - c.lo) * (x ^ n / A + x ^ m / B - (y ^ n / A + y ^ m / B)) ≤
      (1 / A + 1 / B) * ((eInt n P Q T d : ℝ) / 2 ^ Q) := by
    calc _ ≤ c.w / (c.hi - c.lo) * ((1 / A + 1 / B) * ((X : ℝ) / 2 ^ Q)) := by
          apply mul_le_mul_of_nonneg_left _ hg0
          linarith
      _ = (1 / A + 1 / B) * (((d.p : ℝ) * 10 ^ 12 * (X : ℝ) / ((T : ℝ) * ((d.b : ℝ) - d.a))) / 2 ^ Q) := by
          rw [hgc]; ring
      _ ≤ _ := by gcongr
  have e : (1 / A + 1 / B) / B * ((eInt n P Q T d : ℝ) / 2 ^ Q) =
      ((1 / A + 1 / B) * ((eInt n P Q T d : ℝ) / 2 ^ Q)) / B := by ring
  rw [e]
  gcongr

theorem eref_le {P Q T : ℕ} (hQ : Q ≤ 900 * P) (hT : 0 < T) {l : List YCell} {L : List GD}
    (h : List.Forall₂ (Rel P T) l L) :
    (l.map erefTerm).sum ≤ (1 / 900 + 1 / 901) / 901 * (((L.map (eInt 900 P Q T)).sum : ℕ) / 2 ^ Q) := by
  induction h with
  | nil => simp
  | cons hr _ ih =>
    have : erefTerm _ ≤ _ := cell_erefG (n := 900) (m := 901) (A := 900) (B := 901) (by norm_num)
      (by norm_num) (by norm_num) hQ hr hT
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.cast_add]
    have e : ∀ a b : ℝ, (1 / 900 + 1 / 901) / 901 * ((a + b) / 2 ^ Q) =
        (1 / 900 + 1 / 901) / 901 * (a / 2 ^ Q) + (1 / 900 + 1 / 901) / 901 * (b / 2 ^ Q) :=
      fun a b => by ring
    rw [e]
    linarith

/-! ### The conversion to the Chebyshev variable -/

theorem rawQ_mapD (c : ℚ) (z : ℝ) : ∀ (l : List ℤ) (k : ℕ),
    rawQ (l.map fun d : ℤ => (d : ℚ) / c) k z = rawSum l k z / (c : ℝ)
  | [], _ => by simp [rawQ]
  | d :: t, k => by
    simp only [List.map_cons, rawQ, rawSum_cons, rawQ_mapD c z t (k + 1)]
    push_cast
    ring

/-- Monomial list in the variable `x` as a Chebyshev list in `w`. -/
def Zq (A B E : ℤ) (W : ℕ) (l : List ℤ) : List ℚ :=
  (Rc A B E l).map fun d : ℤ => (d : ℚ) / (((E : ℚ) ^ (l.length - 1)) * 2 ^ W)

theorem Pz_rawQ {A B E : ℤ} (hE : 0 < E) (W : ℕ) {w x : ℝ} (hx : (E : ℝ) * x = 2 * ((A : ℝ) + B * w))
    {l : List ℤ} (hl : 0 < l.length) : Pz l x / 2 ^ W = rawQ (Zq A B E W l) 0 w := by
  unfold Zq
  rw [rawQ_mapD]
  have h := Rc_eval A B E hx l
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
  rw [hn] at h ⊢
  simp only [Nat.add_sub_cancel]
  push_cast
  have h' : rawSum (Rc A B E l) 0 w = (E : ℝ) ^ n * Pz l x := by
    have : (E : ℝ) * rawSum (Rc A B E l) 0 w = (E : ℝ) * ((E : ℝ) ^ n * Pz l x) := by
      rw [h]; ring
    exact mul_left_cancel₀ hE'.ne' this
  rw [h']
  field_simp

/-- The last step of both species. -/
theorem to_cheb (C : Cov) {Bud : ℚ} {A B E : ℤ} (hE : 0 < E) (W : ℕ) {w u : ℝ}
    (hw : w = (C.α : ℝ) * u + C.β) (hw1 : w ∈ Icc (-1 : ℝ) 1)
    (hx : (E : ℝ) * u = 2 * ((A : ℝ) + B * w)) {l : List ℤ} (hl : 0 < l.length)
    (hP : C.Phi u ≤ Bud) (p : List ℤ) (D : ℕ) :
    Pz l u / 2 ^ W + sumF C.W C.Bs u - (C.s : ℝ) * Real.log (1 + u ^ 2) ≤
      (Bud : ℝ) + (diffSum (D : ℚ) (addQ (Zq A B E W l) C.Cl) p : ℝ) + chebSum p D w := by
  have h1 := Pz_rawQ hE W hx hl
  have h2 := abs_rawQ_sub_le D (addQ (Zq A B E W l) C.Cl) p 0 w hw1
  rw [rawQ_addQ] at h2
  have h3 := (abs_le.mp h2).2
  unfold Cov.Phi at hP
  rw [← hw] at hP
  unfold chebSum
  rw [h1]
  linarith

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompactInstance
open CatalanMeasure.GenD.Signed.RouteI.CompactCap (affine)
open CatalanMeasure.Signed.ChebSquare
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (Pz)
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (rawQ addQ diffSum)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (reflectL physL_perm)

/-- Sum of the class errors. -/
def errS (R : RadLit) : ℕ → ℚ
  | 0 => 0
  | i + 1 => errS R i + R.err i

/-- Rational form of `sumE`. -/
def sumEQ (W : ℕ) : List Blk → ℚ
  | [] => 0
  | B :: t => (B.M + (S2 B.D 0 : ℚ) / 2 ^ W) + sumEQ W t

noncomputable section

theorem errS_cast (R : RadLit) (n : ℕ) : ∑ i ∈ Finset.range n, (R.err i : ℝ) = ((errS R n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [errS]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp [errS]

theorem sumEQ_cast (W : ℕ) : ∀ Bs : List Blk, sumE W Bs = ((sumEQ W Bs : ℚ) : ℝ)
  | [] => by simp [sumE, sumEQ]
  | B :: t => by
    have := sumEQ_cast W t
    unfold sumE at this ⊢
    simp only [List.map_cons, List.sum_cons, sumEQ, this]
    unfold blkE
    push_cast
    ring

theorem moments_of_lit (g : GasLit) {l : List YCell} (h : List.Forall₂ (Rel g.P g.T) l g.L)
    (hT : 0 < g.T) (h2 : ∀ c ∈ l, 2 ≤ c.lo)
    {nR : ℕ} (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) :
    CloseL (fun i => physL l (fun s => s ^ i)) 0 (dyL g.Qm g.Mi) (dyL g.Qm g.Me) := by
  simp only [GasLit.chkM, Bool.and_eq_true, beq_iff_eq] at cM
  have hm0 := moments_close (Q := g.Q) h hT h2 c1 c1' cLn cSg cLI cLEI
  have hR1 : g.R.getD 1 0 = e2 := by rw [c1']; rfl
  have hm1 : CloseL (fun i => physL l (fun s => s ^ i)) 0 g.mL g.dL := by
    unfold GasLit.mL GasLit.dL
    rw [hR1]
    exact hm0
  exact relax_close 0 _ _ _ _ hm1 cM.1 (by rw [len_dyL]; exact cM.2)

theorem CloseL_tail {m : ℕ → ℝ} {k : ℕ} {a d : ℚ} {as ds : List ℚ}
    (h : CloseL m k (a :: as) (d :: ds)) : CloseL m (k + 1) as ds := h.2

theorem mirror_le {l : List YCell} (h2 : ∀ c ∈ l, 2 ≤ c.lo) {W Qm : ℕ} {m0 e0 : ℤ} {mt et : List ℤ}
    (hc : CloseL (fun i => physL l (fun s => s ^ i)) 0 (dyL Qm (m0 :: mt)) (dyL Qm (e0 :: et)))
    {mi : List ℤ} {me : List ℚ} (ck : chkMir W 1 (dyL Qm mt) (dyL Qm et) mi me = true)
    (l1 : mt.length = mi.length) (l2 : mt.length = me.length) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    physL l (fun s => Real.log |1 - s * u|) ≤ Pz (0 :: mi) u / 2 ^ W + (sumQ me : ℝ) := by
  have a := physL_refl_le h2 hu0 hu1 mt.length
  have hc' : CloseL (fun i => physL l (fun s => s ^ i)) 1 (dyL Qm mt) (dyL Qm et) := CloseL_tail hc
  have b := mir_close (μ := fun i => physL l (fun s => s ^ i)) W hu0.le hu1 1 (dyL Qm mt) (dyL Qm et) mi me
    one_pos hc' ck (by rw [len_dyL]; exact l1) (by rw [len_dyL]; exact l2)
  rw [len_dyL] at b
  have e : ∑ i ∈ Finset.range mt.length, (-1 / ((1 + i : ℕ) : ℝ)) *
      (fun i => physL l (fun s => s ^ i)) (1 + i) * u ^ (1 + i) =
      -∑ k ∈ Finset.range mt.length, u ^ (k + 1) / ((k : ℝ) + 1) * physL l (fun s => s ^ (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm 1 i]
    push_cast
    ring
  rw [e] at b
  have ep : Pz (0 :: mi) u = u * Pz mi u := by simp [Pz]
  rw [ep]
  simp only [pow_one] at b
  linarith

/-- Everything a radial record must satisfy. -/
structure RadOK (R : RadLit) (S : CapSource) (T : List Tr) (g : ℝ) (M : ℤ) (n : ℕ) : Prop where
  hM : 0 ≤ M
  hg : 0 ≤ g
  hgq : (R.hq : ℝ) = g / M
  hq0 : 0 ≤ R.hq
  hT : ∀ t ∈ T, 0 ≤ t.2.1 ∧ 0 ≤ t.2.2
  hcos : ∀ m ≤ 93, cosChk R.CT m = true
  hδ : CLz S.coef (2 ^ 80) (R.δc : ℝ) 0 R.Cq
  hCb : ∀ d ∈ R.Cq, |(d : ℝ)| ≤ 2 ^ 81
  hlen : R.Cq.length = 384
  hW : R.W + R.sh = 160
  hδ0 : 0 ≤ R.δc
  hB : R.Bs.length = n
  hc : ∀ i < n, R.chk T i = true
  hrad : ∀ i < n, 0 < S.rad i ∧ S.rad i ≤ (R.B i).rho ∧
    ((((R.B i).rho : ℚ) : ℝ) - S.rad i) / S.rad i ≤ (R.eta i : ℝ)

theorem radial_pos {R : RadLit} {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} {n : ℕ}
    (h : RadOK R S T g M n) (hs : R.s = 1) (haux : S.aux Sign.pos = T.map (mkAux g M))
    (hl : ∀ e ∈ S.aux Sign.pos, e.rad < n) {u : ℝ} (hu : 0 < u) :
    S.radialA (Trunc.finite 384) Sign.pos u ≤ sumF R.W R.Bs u + ((errS R n : ℚ) : ℝ) := by
  have c := classes_le R h.hM h.hg h.hgq h.hq0 h.hT h.hcos (by rw [hs]; simp) h.hδ h.hCb h.hlen h.hW h.hδ0
    n h.hB h.hc h.hrad hu
  rw [errS_cast] at c
  refine le_trans (le_of_eq ?_) c
  rw [radialA_pos S 384 n hu hl, haux]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hs]
  push_cast
  ring

theorem radial_neg {R : RadLit} {S : CapSource} {T : List Tr} {g : ℝ} {M : ℤ} {n : ℕ}
    (h : RadOK R S T g M n) (hs : R.s = -1) (haux : S.aux Sign.neg = T.map (mkAux g M))
    (hl : ∀ e ∈ S.aux Sign.neg, e.rad < n) (rns : List ℕ) (rb nm : ℕ) {Fb : ℚ} (hFb0 : 0 ≤ Fb)
    (hrn : ∀ i < n, ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1)
    (hr1 : ∀ i < n, S.rad i ≤ 1)
    (hb : ∀ i < n, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ Fb) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    S.radialA (Trunc.finite 384) Sign.neg (-u) ≤ sumF R.W R.Bs u + ((errS R n : ℚ) : ℝ) +
      (polK (truncD R.sh nm (mirF R rns rb n)) 0 u / 2 ^ R.W +
        (((abs1 ((mirF R rns rb n).drop nm) : ℤ) : ℝ) / 2 ^ 160 +
          384 * (((mirE R Fb n : ℚ) : ℝ) + 1 / 2 ^ R.W))) := by
  have hs' : |(R.s : ℝ)| = 1 := by rw [hs]; simp
  have c := classes_le R h.hM h.hg h.hgq h.hq0 h.hT h.hcos hs' h.hδ h.hCb h.hlen h.hW h.hδ0
    n h.hB h.hc h.hrad hu
  rw [errS_cast] at c
  have hF : ∀ i < n, (R.F i).length = 384 := fun i _ => by
    unfold RadLit.F
    rw [tRow_len, h.hlen]
  have m := mirror_series (t := fun i k => (R.s : ℝ) ^ k * S.coef k * aC (T.map (mkAux g M)) i k)
    (r := S.rad) R rns rb nm hFb0 n h.hW
    (fun i hi => class_close R h.hM h.hg h.hgq h.hq0 h.hT h.hcos hs' h.hδ h.hCb h.hδ0 (h.hc i hi))
    (fun i hi => by
      obtain ⟨r1, r2, r3⟩ := h.hrad i hi
      obtain ⟨n1, n2⟩ := hrn i hi
      have n2' : (((R.B i).rho : ℚ) : ℝ) ≤ 1 := by exact_mod_cast n2
      refine ⟨r1.le, hr1 i hi, by rw [n1]; exact n2', ?_⟩
      rw [n1, abs_sub_comm, abs_of_nonneg (by linarith)]
      refine le_trans ?_ r3
      rw [le_div_iff₀ r1]
      have : (0 : ℝ) ≤ (((R.B i).rho : ℚ) : ℝ) - S.rad i := by linarith
      nlinarith [hr1 i hi])
    hF hb hu.le hu1
  rw [radialA_neg S 384 n hu hl, haux]
  have e : ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max u (S.rad i)) +
      ∑ k ∈ Finset.range 384, ((-1) ^ (k + 1) * S.coef (k + 1)) *
        (psiR (S.rad i) u ^ (k + 1) + (S.rad i * u) ^ (k + 1)) * aC (T.map (mkAux g M)) i (k + 1)) =
      ∑ i ∈ Finset.range n, (aC (T.map (mkAux g M)) i 0 * Real.log (max u (S.rad i)) +
        ∑ k ∈ Finset.range 384, ((R.s : ℝ) ^ (k + 1) * S.coef (k + 1) *
          aC (T.map (mkAux g M)) i (k + 1)) * psiR (S.rad i) u ^ (k + 1)) +
      ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range 384,
        (R.s : ℝ) ^ (k + 1) * S.coef (k + 1) * aC (T.map (mkAux g M)) i (k + 1) *
          (S.rad i * u) ^ (k + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs]
    push_cast
    ring
  rw [e]
  linarith

theorem sumF_snoc (W : ℕ) (Bs : List Blk) (B : Blk) (x : ℝ) :
    sumF W (Bs ++ [B]) x = sumF W Bs x + blkF W B x := by
  simp [sumF]

theorem addZ_len_pos : ∀ {a b : List ℤ}, 0 < a.length → 0 < (addZ a b).length
  | _ :: _, [], _ => by simp [addZ]
  | _ :: _, _ :: _, _ => by simp [addZ]

/-- The mirror block. -/
def mBlk (D : List ℤ) : Blk := ⟨1, 0, 0, D⟩

theorem blkF_mBlk (W : ℕ) (D : List ℤ) {u : ℝ} (hu1 : u ≤ 1) :
    blkF W (mBlk D) u = polK D 0 u / 2 ^ W := by
  unfold blkF mBlk psiR
  simp [not_lt.mpr hu1]

theorem log4 : (2 * (6931471803 / 10 ^ 10 : ℝ)) ≤ Real.log 4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  rw [h]
  norm_num at this ⊢
  linarith

theorem capAux (σ : Sign) : capSource.aux σ = (auxT σ).map (mkAux (tgt σ) (sumP (auxT σ))) := rfl

/-- Positive species. -/
theorem pos_core (g : GasLit) (R : RadLit) (C : Cov) (En : CoefEnc) {Bud : ℚ}
    (hrel : relP g.P gasPosT g.L = true) (hTg : (g.T : ℤ) = sumP row0) (hT : 0 < g.T)
    (hS : sepL (2 * 10 ^ 12) g.L = true) {nR : ℕ}
    (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true) {Ev : ℕ}
    (cE : (g.L.map (eInt 900 g.P 64 g.T)).sum = Ev) (hP : 64 ≤ 900 * g.P)
    (hR : RadOK R capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16)
    (hs : R.s = 1) (hEn : En.Valid capSource) (hq1 : En.qh < 1)
    (hCW : C.W = R.W) (hCB : C.Bs = R.Bs) (hCs : C.s = 53 / 58)
    (hCα : C.α = 2000000 / 901251) (hCβ : C.β = -(1098749 / 901251))
    (hPhi : ∀ x ∈ Icc (98749 / 1000000 : ℝ) 1, C.Phi x ≤ Bud)
    (hGl : 0 < (g.G []).length) (hmq : 0 ≤ massQ g.T g.L)
    (hfin : g.Tb + sumQ (dyL 40 g.f) - 2 * massQ g.T g.L * (6931471803 / 10 ^ 10) - 29557 / 200000 +
      (1 / 900 + 1 / 901) / 901 * ((Ev : ℚ) / 2 ^ 64) + errS R 16 +
      En.tail (1 - massQ g.T g.L) 1 + Bud +
      diffSum (D : ℚ) (addQ (Zq 1098749 901251 4000000 g.W (g.G [])) C.Cl) posP ≤ posEps) :
    PosHf capSource (Trunc.finite 384) := by
  intro u hu
  have hu0 : 0 < u := by have := hu.1; linarith
  have hu1 := hu.2
  have hF : List.Forall₂ (Rel g.P g.T) (capSource.gas Sign.pos) g.L := relP_spec hTg gasPosT g.L hrel
  have h2 : ∀ c ∈ capSource.gas Sign.pos, 2 ≤ c.lo := gas_pos_lo
  have fld := field_pos capSource 384 h2 hu0 hu1
  have gs := gas_of_lit g hF hT h2 hS c1 c1' cLn cSg cLI cLEI cM cV cG cS cC [] hu0 hu1
  have hm : massL (capSource.gas Sign.pos) = ((massQ g.T g.L : ℚ) : ℝ) := massL_rel hF
  have er : capSource.Eref900 ≤ (1 / 900 + 1 / 901) / 901 * ((Ev : ℝ) / 2 ^ 64) := by
    have := eref_le hP hT hF
    rw [cE] at this
    exact this
  have rd := radial_pos hR hs (capAux Sign.pos) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.pos).map _ from he)
    exact mkAux_rad_lt _ _ t (pa_ok t ht).2) hu0
  have tgtq : tgt Sign.pos = ((1 - massQ g.T g.L : ℚ) : ℝ) := by
    show 1 - massL (capSource.gas Sign.pos) = _
    rw [hm]
    push_cast
    ring
  have tl := auxTail_le hEn hq1 Sign.pos (m := 1 - massQ g.T g.L) (c := 1)
    (by rw [auxMass_eq, tgtq]) (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)
  set w := affine (98749 / 1000000) u with hwd
  have hw : w = (C.α : ℝ) * u + C.β := by
    rw [hwd, hCα, hCβ]
    unfold affine
    push_cast
    ring
  have hx : (((4000000 : ℤ)) : ℝ) * u = 2 * (((1098749 : ℤ) : ℝ) + ((901251 : ℤ) : ℝ) * w) := by
    rw [hwd]
    unfold affine
    push_cast
    ring
  have hw1 : w ∈ Icc (-1 : ℝ) 1 := by
    have a := hu.1
    rw [hw, hCα, hCβ]
    push_cast
    constructor <;> linarith
  have ch := to_cheb C (A := 1098749) (B := 901251) (E := 4000000) (by norm_num) g.W hw hw1 hx hGl
    (hPhi u hu) posP D
  have fq := (Rat.cast_le (K := ℝ)).mpr hfin
  have l4 := log4
  have m0 : (0 : ℝ) ≤ ((massQ g.T g.L : ℚ) : ℝ) := by exact_mod_cast hmq
  have ml := mul_le_mul_of_nonneg_left l4 m0
  rw [hCW, hCB, hCs] at ch
  have hk : kappa Sign.pos = 29557 / 200000 := rfl
  have hz : Pz ([] : List ℤ) u = 0 := by simp [Pz]
  rw [hz, hm, zero_div] at gs
  rw [hk] at fld
  push_cast at fq ch
  linarith [fld, gs, er, rd, tl, ch, fq, ml]

theorem massL_perm {a b : List YCell} (h : a.Perm b) : massL a = massL b := by
  unfold massL
  exact (h.map _).sum_eq

theorem massL_reflect (l : List YCell) : massL (reflectL l) = massL l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have e : ∀ (d : YCell) (m : List YCell), massL (d :: m) = d.w + massL m := fun d m => by
      simp [massL]
    show massL (c.reflect :: reflectL l) = _
    rw [e, e, ih]
    rfl

/-- Negative species. -/
theorem neg_core (g : GasLit) (R : RadLit) (C : Cov) (En : CoefEnc) {Bud : ℚ}
    (hrel : relN g.P gasNegT.reverse g.L = true) (hTg : (g.T : ℤ) = sumP row0) (hT : 0 < g.T)
    (hS : sepL (2 * 10 ^ 12) g.L = true) {nR : ℕ}
    (c1 : rows g.P nR (g.L.map (stAt g.P g.T 1)) = g.R) {e1 e2 : ℤ} {r : List ℤ}
    (c1' : g.R = e1 :: e2 :: r) (cLn : g.L.length = g.Ln) (cSg : SG g.P g.T g.L = g.Sg)
    (cLI : LI g.P g.T g.Q g.L = g.LIv) (cLEI : LEI g.P g.T g.Q g.L = g.LEIv)
    (cM : g.chkM = true) (cV : g.chkV = true) (cG : G2I g.P g.T g.Q g.L = g.G2v)
    (cS : g.chkS = true) (cC : g.chkC = true)
    {m0' e0' : ℤ} {mt et : List ℤ} (hMi : g.Mi = m0' :: mt) (hMe : g.Me = e0' :: et)
    {mi : List ℤ} {me : List ℚ} (ck : chkMir g.W 1 (dyL g.Qm mt) (dyL g.Qm et) mi me = true)
    (l1 : mt.length = mi.length) (l2 : mt.length = me.length)
    (hR : RadOK R capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16)
    (hs : R.s = -1) (rns : List ℕ) (rb nm : ℕ)
    (hrn : ∀ i < 16, ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1)
    (hb : ∀ i < 16, ∀ d ∈ R.F i, |(d : ℝ)| / 2 ^ 160 ≤ ((1 : ℚ) : ℝ))
    {Dm : List ℤ} (hDm : Dm = truncD R.sh nm (mirF R rns rb 16)) {Tm : ℤ}
    (hTm : abs1 ((mirF R rns rb 16).drop nm) = Tm)
    (hEn : En.Valid capSource) (hq1 : En.qh < 1)
    (hCW : C.W = R.W) (hCB : C.Bs = R.Bs ++ [mBlk Dm]) (hCs : C.s = 53 / 58)
    (hCα : C.α = 200000 / 80499) (hCβ : C.β = -(119501 / 80499))
    (hPhi : ∀ x ∈ Icc (19501 / 100000 : ℝ) 1, C.Phi x ≤ Bud)
    (hmq : 0 ≤ massQ g.T g.L)
    (hfin : g.Tb + sumQ (dyL 40 g.f) + sumQ me - 2 * massQ g.T g.L * (6931471803 / 10 ^ 10) -
      5489 / 100000 + errS R 16 + ((Tm : ℚ) / 2 ^ 160 + 384 * (mirE R 1 16 + 1 / 2 ^ R.W)) +
      En.tail (53 / 58 - massQ g.T g.L) 2 + Bud +
      diffSum (D : ℚ) (addQ (Zq 119501 80499 400000 g.W (g.G (0 :: mi))) C.Cl) negP ≤ negEps) :
    NegHf capSource (Trunc.finite 384) := by
  intro u hu
  have hu0 : 0 < u := by have := hu.1; linarith
  have hu1 := hu.2
  set l : List YCell := gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect with hl
  have hF : List.Forall₂ (Rel g.P g.T) l g.L := relN_spec hTg gasNegT.reverse g.L hrel
  have hp : l.Perm (reflectL (capSource.gas Sign.neg)) := by
    have e : l = (reflectL (capSource.gas Sign.neg)).reverse := by
      rw [hl]
      show _ = (((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect)).reverse
      rw [List.map_map, List.map_reverse]
      rfl
    rw [e]
    exact List.reverse_perm _
  have h2 : ∀ c ∈ l, 2 ≤ c.lo := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (hp.mem_iff.1 hc)
    have := gas_neg_hi d hd
    show 2 ≤ -d.hi
    linarith
  have fld := field_neg capSource 384 gas_neg_hi hu0 hu1
  rw [← physL_perm hp, ← physL_perm hp] at fld
  have gs := gas_of_lit g hF hT h2 hS c1 c1' cLn cSg cLI cLEI cM cV cG cS cC (0 :: mi) hu0 hu1
  have mo := moments_of_lit g hF hT h2 c1 c1' cLn cSg cLI cLEI cM
  rw [hMi, hMe] at mo
  have mr := mirror_le h2 mo ck l1 l2 hu0 hu1
  have hm : massL l = ((massQ g.T g.L : ℚ) : ℝ) := massL_rel hF
  have hm' : massL (capSource.gas Sign.neg) = ((massQ g.T g.L : ℚ) : ℝ) := by
    rw [← massL_reflect, ← massL_perm hp, hm]
  have rd := radial_neg hR hs (capAux Sign.neg) (fun e he => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (show e ∈ (auxT Sign.neg).map _ from he)
    exact mkAux_rad_lt _ _ t (na_ok t ht).2) rns rb nm (Fb := 1) zero_le_one hrn
    (fun i hi => (hR.hrad i hi).2.1.trans (by exact_mod_cast (hrn i hi).2)) hb hu0 hu1
  rw [← hDm, hTm] at rd
  have tgtq : tgt Sign.neg = ((53 / 58 - massQ g.T g.L : ℚ) : ℝ) := by
    show 53 / 58 - massL (capSource.gas Sign.neg) = _
    rw [hm']
    push_cast
    ring
  have tl := auxTail_le hEn hq1 Sign.neg (m := 53 / 58 - massQ g.T g.L) (c := 2)
    (by rw [auxMass_eq, tgtq]) (by rw [auxMass_eq]; exact tgt_nonneg _) (by simp)
  set w := affine (19501 / 100000) u with hwd
  have hw : w = (C.α : ℝ) * u + C.β := by
    rw [hwd, hCα, hCβ]
    unfold affine
    push_cast
    ring
  have hx : (((400000 : ℤ)) : ℝ) * u = 2 * (((119501 : ℤ) : ℝ) + ((80499 : ℤ) : ℝ) * w) := by
    rw [hwd]
    unfold affine
    push_cast
    ring
  have hw1 : w ∈ Icc (-1 : ℝ) 1 := by
    have a := hu.1
    rw [hw, hCα, hCβ]
    push_cast
    constructor <;> linarith
  have hGl : 0 < (g.G (0 :: mi)).length := by
    have : ∀ (c a b acc : List ℤ), 0 < acc.length → 0 < (comb c a b acc).length := by
      intro c
      induction c with
      | nil => intro a b acc h; exact h
      | cons d t ih =>
        intro a b acc h
        simp only [comb]
        exact ih _ _ _ (by
          exact addZ_len_pos h)
    exact this _ _ _ _ (by simp)
  have ch := to_cheb C (A := 119501) (B := 80499) (E := 400000) (by norm_num) g.W hw hw1 hx hGl
    (hPhi u hu) negP D
  have fq := (Rat.cast_le (K := ℝ)).mpr hfin
  have l4 := log4
  have m0 : (0 : ℝ) ≤ ((massQ g.T g.L : ℚ) : ℝ) := by exact_mod_cast hmq
  have ml := mul_le_mul_of_nonneg_left l4 m0
  rw [hCW, hCB, hCs, sumF_snoc, blkF_mBlk _ _ hu1] at ch
  have hk : kappa Sign.neg = 5489 / 100000 := rfl
  rw [hm] at gs
  rw [hk] at fld
  push_cast at fq ch
  linarith [fld, gs, mr, rd, tl, ch, fq, ml]

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf

open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData

/-- Decoder of the flat cell list. -/
def gdOf : List ℤ → List GD
  | a :: b :: p :: al :: ah :: lam :: t =>
    ⟨a.toNat, b.toNat, p.toNat, al.toNat, ah.toNat, lam.toNat⟩ :: gdOf t
  | _ => []

/-- Decoder of the flat node list. -/
def ndOf : List ℤ → List (ℚ × ℚ)
  | x :: d :: v :: t => ((x : ℚ) / d, (v : ℚ) / 2 ^ 80) :: ndOf t
  | _ => []

/-- Class checks and radius checks together. -/
def RadLit.allChk (R : RadLit) (T : List Tr) : Bool :=
  (List.range 16).all fun i => R.chk T i && radChk (R.B i).rho (R.B i).sg (R.eta i) i

def auxOK (T : List Tr) : Bool := T.all fun t => decide (0 ≤ t.2.1) && decide (0 ≤ t.2.2)

def cqOK (Cq : List ℤ) : Bool := Cq.all fun d => decide (|d| ≤ 2 ^ 81)

def rnOK (R : RadLit) (rns : List ℕ) (rb : ℕ) : Bool :=
  (List.range 16).all fun i => decide (((rns.getD i 0 : ℕ) : ℚ) / 2 ^ rb = (R.B i).rho) &&
    decide ((R.B i).rho ≤ 1)

def fbOK (R : RadLit) : Bool :=
  (List.range 16).all fun i => (R.F i).all fun d => decide (|d| ≤ 2 ^ 160)

noncomputable section

theorem RadLit.allChk_spec {R : RadLit} {T : List Tr} (h : R.allChk T = true) {i : ℕ} (hi : i < 16) :
    R.chk T i = true ∧ radChk (R.B i).rho (R.B i).sg (R.eta i) i = true := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simpa using this

theorem radOK_of (R : RadLit) (σ : Sign) {En : CoefEnc} (hEn : En.Valid capSource) {mq : ℚ}
    (hmq : tgt σ = mq) (h1 : R.hq = mq / (sumP (auxT σ) : ℚ)) (h2 : 0 ≤ R.hq)
    (hTa : auxOK (auxT σ) = true) (hcos : (List.range 94).all (cosChk R.CT) = true)
    (hco : coefChk En R.δc R.Cq 0 = true) (hCb : cqOK R.Cq = true) (hlen : R.Cq.length = 384)
    (hW : R.W + R.sh = 160) (hδ0 : 0 ≤ R.δc) (hB : R.Bs.length = 16)
    (hall : R.allChk (auxT σ) = true) (hM : 0 ≤ sumP (auxT σ)) :
    RadOK R capSource (auxT σ) (tgt σ) (sumP (auxT σ)) 16 where
  hM := hM
  hg := tgt_nonneg σ
  hgq := by rw [h1, hmq]; push_cast; rfl
  hq0 := h2
  hT := fun t ht => by
    have := List.all_eq_true.1 hTa t ht
    simpa using this
  hcos := fun m hm => List.all_eq_true.1 hcos m (List.mem_range.2 (by omega))
  hδ := coef_close hEn R.Cq 0 hco
  hCb := fun d hd => by
    have := List.all_eq_true.1 hCb d hd
    simp only [decide_eq_true_eq] at this
    have h : ((|d| : ℤ) : ℝ) ≤ ((2 ^ 81 : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs, Int.cast_pow, Int.cast_ofNat] at h
    exact h
  hlen := hlen
  hW := hW
  hδ0 := hδ0
  hB := hB
  hc := fun i hi => (R.allChk_spec hall hi).1
  hrad := fun i hi => by
    obtain ⟨a, b, c, _, _⟩ := rad_facts (R.allChk_spec hall hi).2
    exact ⟨a, b, c⟩

theorem blks_ok (R : RadLit) {T : List Tr} (hB : R.Bs.length = 16) (hq0 : 0 ≤ R.hq)
    (hall : R.allChk T = true) : ∀ B ∈ R.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := by
  intro B hBm
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hBm
  have hi' : i < 16 := by omega
  obtain ⟨c, r⟩ := R.allChk_spec hall hi'
  have e : R.B i = R.Bs[i] := List.getD_eq_getElem _ _ hi
  obtain ⟨_, _, _, a, b⟩ := rad_facts r
  rw [e] at a b
  refine ⟨b, ?_, a⟩
  simp only [RadLit.chk, Bool.and_eq_true, decide_eq_true_eq] at c
  rw [← e, c.2]
  positivity

theorem Phi_of (C : Cov) {E K Bud lo : ℚ} (n : ℚ × ℚ) (t : List (ℚ × ℚ)) (hs : 0 ≤ C.s) (hα : 0 ≤ C.α)
    (hB : ∀ B ∈ C.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg)
    (hE : sumEQ C.W C.Bs ≤ E) (hK : 2 * C.s + mc4 C.Cl 0 * C.α ^ 2 ≤ K) (h0 : 0 < n.1)
    (hc : C.chain E K Bud n t = true) (hn : (n :: t).all C.nodeOK = true) (hlo : bot n t = lo)
    (h1 : n.1 = 1) {x : ℝ} (hx : x ∈ Icc (lo : ℝ) 1) : C.Phi x ≤ Bud := by
  refine C.cover hs hα hB (by rw [sumEQ_cast]; exact_mod_cast hE) hK t n h0 hc
    (fun m hm => List.all_eq_true.1 hn m hm) x ?_
  rw [hlo, h1]
  simpa using hx

theorem hrn_of {R : RadLit} {rns : List ℕ} {rb : ℕ} (h : rnOK R rns rb = true) {i : ℕ} (hi : i < 16) :
    ((rns.getD i 0 : ℕ) : ℝ) / 2 ^ rb = (R.B i).rho ∧ (R.B i).rho ≤ 1 := by
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  rw [← this.1]
  push_cast
  rfl

theorem hb_of {R : RadLit} (h : fbOK R = true) {i : ℕ} (hi : i < 16) {d : ℤ} (hd : d ∈ R.F i) :
    |(d : ℝ)| / 2 ^ 160 ≤ ((1 : ℚ) : ℝ) := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h i (List.mem_range.2 hi)) d hd
  simp only [decide_eq_true_eq] at this
  have h1 : ((|d| : ℤ) : ℝ) ≤ ((2 ^ 160 : ℤ) : ℝ) := by exact_mod_cast this
  rw [Int.cast_abs, Int.cast_pow, Int.cast_ofNat] at h1
  rw [Rat.cast_one, div_le_one (by positivity)]
  exact h1

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

namespace CatalanMeasure.GenD.Signed.RouteI.OrdHf
open Real Set
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.CapFields.CapSource
open CatalanMeasure.GenD.Signed.RouteI.CapSourceData
open CatalanMeasure.GenD.Signed.RouteI.CompactInstance
open CatalanMeasure.GenD.Signed.RouteI.CompactHf (diffSum addQ)
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (reflectL)

def CTl : ℕ := 3432289493168574315307147760865130825474106292166924779170433513824196210417976913383338703551059324455566675134143829985313882632853974031432453092075303558452237396205582081627130169788205630708567009536263687035494658485063820281032815309135506764251649650001775125298312326893277362136346083476612080559403214766756854467921458681203503548857688352790435098749118491981922746054340054693791549024756659733298618902756895556207340227569415585540071448379110765362736123371139308930722709944588641739583976913362053074947174014815101781487501172563584887772329224430732407961729123729288387187482558880760144047668163479017850790306649607989655104753921029071745931422350735054141231443933206758231786587867987104494845978396329009705540237637473560124620006797501126318706269778156491694036860751134624928384798511277612612767609846013338674639143763754472045390048727260327746667174279245369949731525549451402148820335506211337341630972705470355551049728570503018640151761203991179936668563238515489984394293720441825267608612145748397032384570184865833811786929667456036674032411962373449942999713958931257749536457133914550343741466047548523659779933260111705831053156591097787450059080804340124797366766254628030527549348304758385247747664442547165486235274814885099085229989877880060538663643447963497940381244660440963784580311954965903373427664395883711314980951991513156144989793065440520027484909458895827612071340662866327119285922573537807030142266050057745552816993103996247581762607566719884023456582722503928266514996996159676078379216885259579668331081905755382116539870669710456921130925366677622036563095062623066937426309527693137110123370236450096955626269500821855960974051709254987484275258508591785547264778997013505647888889796293866476169334765200572051782696410821517222560989642325873222005276036207181275417136335113063298619303115508553519636851256610808149592432021800556878732114501044959450455160752442589963445348275564833393223582488561747444978376942617760892593836131248155719673136502837752948512849764488791988244424947691498988471162091551998897740407267779632880162951650756724567152196782079273081860670855556476931673967540977276008008279845407431573045617411793227288950954436928609047824008861621169354162762158346328158825636275981758752062483200558618543791949224942346237290831874083602575719380870432466534348040883367576842374831495408743106813200565075912367739936834156755901853186104353474372564979896426478765482707300030466235719157193869076290325478465981035048207507956671716038572991768840290014676069084130617762879380578378922530072495806415151261722724357410799216675947062991970079817655961040446680010434475735384064
def Cql : List ℤ := raw_ints% [-1208337569457489154579320, -603288975639820611874650, -401220318635059555424516, -299902041005742789206114, -238889520682016818390759, -198035453570295095276931, -168705923277331329388406, -146584430592503193941793, -129273246433301312742272, -115333961060135550427022, -103851376744274829357273, -94215459663480714335017, -86003934055423734381752, -78915197104643940277440, -72728071214716363532278, -67276652017172413564403, -62434035972752070871076, -58101474170987762084536, -54200953011896531707843, -50670002195102030565568, -47457987435786967286513, -44523415367867071153608, -41831942466697220440209, -39354882555307875468832, -37068073205771063460581, -34951004335505846719279, -32986140956599763668734, -31158391482420431687896, -29454686406530017828987, -27863641556045105750137, -26375286783071588071456, -24980845745476881284042, -23672555909897152839330, -22443520469652492948948, -21287585771564977677866, -20199239271463564624963, -19173524116953118113697, -18205967279150729551421, -17292518788118867124163, -16429500117187691152199, -15613560144039719772375, -14841637417000359489750, -14110927692541307485506, -13418855898887663171127, -12763051831648200410095, -12141329008797155524433, -11551666210432686170333, -10992191308383564187998, -10461167055701622943694, -9956978559303207518359, -9478122202814126451159, -9023195822847096767490, -8590889971938614992841, -8179980126340176020160, -7789319717713869674759, -7417833885261352273854, -7064513859512405829544, -6728411901396261519341, -6408636730707161197362, -6104349386974923007020, -5814759473323462147623, -5539121740360617593324, -5276732972668876072651, -5026929145205671142026, -4789082820995911947200, -4562600765009890920525, -4346921752151605590486, -4141514549906887739687, -3945876058477255055412, -3759529593204345463527, -3582023295813587526879, -3412928662510301653005, -3251839178277167338708, -3098369047874819791748, -2952152015059313837790, -2812840262420150395649, -2680103385026619379651, -2553627431762193362342, -2433114008838482658518, -2318279440522055665293, -2208853982588052846530, -2104581084441594062111, -2005216696228087962649, -1910528617592413003316, -1820295885049514457781, -1734308195199566845608, -1652365361263246707635, -1574276800630127700858, -1499861051308615713399, -1428945315341695345138, -1361365027411259789769, -1296963446996873969013, -1235591272584171999930, -1177106276535207565751, -1121372959339275056593, -1068262222059161274507, -1017651055875497675775, -969422247711768861137, -923464100995397970761, -879670170676886505696, -837939011689867713048, -798173940090701620759, -760282806167396817812, -724177778854635348024, -689775140834900698859, -656995093745520380574, -625761572948151955694, -596002071351149241678, -567647471806598895777, -540631887632845628077, -514892510840232531378, -490369467662756424502, -467005681021543215770, -444746739567635226876, -423540772971686652236, -403338333146907269041, -384092281109088877077, -365757679193893998784, -348291688366873010470, -331653470375986613780, -315804094509820370115, -300706448737255123324, -286325155016163659439, -272626488569796555287, -259578300939950578555, -247149946635828502232, -235312213206743055036, -224037254575529588830, -213298527477748266827, -203070730859510555985, -193329748094087245405, -184052591884374370744, -175217351724835345976, -166803143802726316480, -158790063224269444853, -151159138456986045874, -143892287884657198414, -136972278376361287301, -130382685775762203616, -124107857221303830461, -118132875212220070818, -112443523339308165637, -107026253603248638495, -101868155246899298717, -96956925031453991214, -92280838889649153738, -87828724892332043314, -83589937467682441951, -79554332815212917973, -75712245459368966652, -72054465890116776291, -68572219240349722094, -65257144952271335202, -62101277387128408139, -59097027334778712171, -56237164381588823749, -53514800097073791086, -50923372001516541094, -48456628278545491165, -46108613198308003897, -43873653218459089949, -41746343731692893968, -39721536429982558389, -37794327257065428369, -35960044922018439176, -34214239948015949531, -32552674231552128263, -30971311088544997768, -29466305764821977611, -28033996389519716095, -26670895350916484427, -25373681075155658360, -24139190189215937562, -22964410050339960992, -21846471624949777129, -20782642700857037665, -19770321417319531544, -18807030098205408882, -17890409374203728481, -17018212580666291054, -16188300418282514493, -15398635864377722159, -14647279323186941120, -13932384003992374600, -13252191516524294544, -12605027673513314139, -11989298490747912434, -11403486375435710774, -10846146494091313054, -10315903311578444076, -9811447293320534769, -9331531763062651754, -8874969908919554926, -8440631930780457029, -8027442322461485045, -7634377282302602917, -7260462246197514839, -6904769537323464368, -6566416127103483786, -6244561502187110309, -5938405632477423933, -5647187035463004306, -5370180932333555116, -5106697491567985700, -4856080155884130397, -4617704048630465541, -4390974455882570964, -4175325380681077439, -3970218166013825769, -3775140183303301855, -3589603583311453461, -3413144106518070904, -3245319950166343252, -3085710689300286855, -2933916249243773677, -2789555927090139421, -2652267459885089659, -2521706137294098147, -2397543956648945813, -2279468818366711289, -2167183759828613549, -2060406225895833788, -1958867374325006900, -1862311414427663718, -1770494977395705865, -1683186516789179410, -1600165737753347885, -1521223053599507817, -1446159068448292433, -1374784084695515831, -1306917634119058752, -1242388031501019674, -1181031949692477061, -1122694015098849994, -1067226422612119782, -1014488569062193558, -964346704303556749, -916673599095174080, -871348228971453475, -828255473340074475, -787285829078689116, -748335137937011101, -711304327083697406, -676099162168770255, -642630012302198473, -610811626377723939, -580562920198146583, -551806773884132310, -524469839073241884, -498482355439351835, -473777976085004965, -450293601380539598, -427969220844152614, -406747762676398473, -386574950581059567, -367399167521885275, -349171326081428503, -331844745104148401, -315375032321133248, -299719972668263633, -284839422023416699, -270695206101439561, -257251024258124686, -244472357966331275, -232326383738742427, -220781890282554649, -209809199681689488, -199380092411920810, -189467736003648726, -180046617175944113, -171092477273957340, -162582250849850841, -154494007235096943, -146806894959297711, -139501088877650055, -132557739875813310, -125958927027253730, -119687612084155814, -113727596188718372, -108063478697107401, -102680618013531101, -97565094336847129, -92703674226820247, -88083776901631086, -83693442182504531, -79521300005389506, -75556541423490261, -71788891028132135, -68208580718950775, -64806324757731558, -61573296043403339, -58501103548715417, -55581770862005887, -52807715780210477, -50171730901869917, -47666965171377359, -45286906328071247, -43025364216029025, -40876454912558712, -38834585635423724, -36894440390776437, -35050966325622467, -33299360750395057, -31635058798891522, -30053721694415505, -28551225592483676, -27123650971897231, -25767272547350509, -24478549678054701, -23254117248097117, -22090776995438817, -20985489267578521, -19935365182981365, -18937659178389783, -17989761923103259, -17089193582236002, -16233597411839346, -15420733669610718, -14648473825705607, -13914795058924961, -13217775024269733, -12555586878538651, -11926494551296381, -11328848249158710, -10761080181930732, -10221700499694653, -9709293430477281, -9222513608634674, -8760082584574166, -8320785506893236, -7903467968451533, -7507033008307955, -7130438261850016, -6772693251818751, -6432856813290177, -6110034646014523, -5803376987838162, -5512076403241004, -5235365681314946, -4972515837787510, -4722834215959729, -4485662681679300, -4260375907709700, -4046379743083907, -3843109663248150, -3650029297007315, -3466629026479741, -3292424656455622, -3126956149730631, -2969786425155048, -2820500215299113, -2678702980787876, -2544019878503917, -2416094780994262, -2294589344549066, -2179182123544363, -2069567728759872, -1965456027495660, -1866571383418757, -1772651934172854, -1683448904881199, -1598725955765105, -1518258562188139, -1441833425519525, -1369247913289560, -1300309527185268, -1234835397506205, -1172651802768509, -1113593713210105, -1057504357011594, -1004234808105954, -953643594505897, -905596326130686, -859965341164562, -816629370026828, -775473216079144, -736387452238842, -699268132708249, -664016519069076, -630538820028135, -598745944136000, -568553264833804, -539880397215328, -512650985921925]
def dcL : ℚ := (137056426003 / 332306998946228968225951765070086144 : ℚ)
def Enc : CoefEnc := ⟨(161197219848661288509620604195940589287 / 170141183460469231731687303715884105728 : ℚ), (322394439697322577019241208391881178575 / 340282366920938463463374607431768211456 : ℚ), (18375233944490641139105470806103934607 / 340282366920938463463374607431768211456 : ℚ), (18375233944490641139105470806103934609 / 340282366920938463463374607431768211456 : ℚ), (20652068278450630479526165946105097 / 21267647932558653966460912964485513216 : ℚ), (330433092455210087672418655137681553 / 340282366920938463463374607431768211456 : ℚ)⟩
def gdP : List ℤ := raw_ints% [2000033231527, 2000039851323, 6686, 115126506182925728565962108219083771479052611125894842417479424160288629343369, 115063421637341750954831431586478552896497309656506793059967265927116199453972, 4049562, 2000039851323, 2000046079500, 339827331, 115063421637341750954831431586478552896497309656506793059967265927116199453972, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 4570597, 2000046079500, 2000047076101, 67382266, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 115000337099550903204000753402871036297796149986674806570676279839532181277292, 4851511, 2000047076101, 2000054906859, 576255968, 115000337099550903204000753402871036297796149986674806570676279839532181277292, 114937252553494271814697321389921975114913601497877347426864829296304559872781, 5198449, 2000054906859, 2000063344594, 681756488, 114937252553494271814697321389921975114913601497877347426864829296304559872781, 114874168010579577154048090614542156544814480918177722403424196794955743302030, 5808678, 2000063344594, 2000072390306, 747606072, 114874168010579577154048090614542156544814480918177722403424196794955743302030, 114811083473813655201781925060952382457119886129382851913665900656965788972534, 6441664, 2000072390306, 2000077526822, 423820171, 114811083473813655201781925060952382457119886129382851913665900656965788972534, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 6936592, 2000077526822, 2000082045000, 371102744, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 114747998927731493596421716656176165373638983117969217813083170691053156793688, 7268996, 2000082045000, 2000092309679, 827838186, 114747998927731493596421716656176165373638983117969217813083170691053156793688, 114684914385541658656026059154822944040295957473485305826407018722641554956479, 7773120, 2000092309679, 2000095667547, 265515765, 114684914385541658656026059154822944040295957473485305826407018722641554956479, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 8220158, 2000095667547, 2000103185351, 587523009, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 114621829841840883816441546459468385985076206770933341027699542601715986248380, 8576728, 2000103185351, 2000114673025, 871028545, 114621829841840883816441546459468385985076206770933341027699542601715986248380, 114558745298863714310151891564851897661154443637270880599837209595445934409204, 9187883, 2000114673025, 2000126773712, 883302035, 114558745298863714310151891564851897661154443637270880599837209595445934409204, 114495660759545259572350261489332643266426720258549336314237020846386464754671, 9925199, 2000126773712, 2000139488427, 892417126, 114495660759545259572350261489332643266426720258549336314237020846386464754671, 114432576217694987429088217605206789839096467512528467748779856149444196669929, 10681859, 2000139488427, 2000152818186, 898714507, 114432576217694987429088217605206789839096467512528467748779856149444196669929, 114369491673959803739826918198446576334742282458619939295443180369841629920666, 11457448, 2000152818186, 2000166764007, 901668992, 114369491673959803739826918198446576334742282458619939295443180369841629920666, 114306407129951324699520023163019114049599884159940591724980692267317790406932, 12251580, 2000166764007, 2000175209840, 527733233, 114306407129951324699520023163019114049599884159940591724980692267317790406932, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 12888170, 2000175209840, 2000181326910, 376930302, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 114243322588071394194334273050030645509483403339746143923554383156073856132722, 13297780, 2000181326910, 2000196507918, 905554434, 114243322588071394194334273050030645509483403339746143923554383156073856132722, 114180238047306042588380508880014319376730932806046535317098626535067990452822, 13894066, 2000196507918, 2000198883427, 137848832, 114180238047306042588380508880014319376730932806046535317098626535067990452822, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 14372358, 2000198883427, 2000212308057, 767430198, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 114117153503905284129760909359023496880305567225401433812070000197928650839449, 14804926, 2000212308057, 2000228728354, 903974481, 114117153503905284129760909359023496880305567225401433812070000197928650839449, 114054068959455985425806640867036140032436750832262446947628546512865116326653, 15606723, 2000228728354, 2000245769838, 901563798, 114054068959455985425806640867036140032436750832262446947628546512865116326653, 113990984416315372534206872639513216542039263963325686416185979072682972069722, 16488642, 2000245769838, 2000263433541, 898941790, 113990984416315372534206872639513216542039263963325686416185979072682972069722, 113927899873989236559503926521297888226342962644653211709212254658375422194405, 17387268, 2000263433541, 2000281720497, 895910018, 113927899873989236559503926521297888226342962644653211709212254658375422194405, 113864815333022044965565770482455930871367499467403259520700841373703452848951, 18302356, 2000281720497, 2000300631744, 891626906, 113864815333022044965565770482455930871367499467403259520700841373703452848951, 113801730788286019251920830303795915057941382717919923450743405255545066490343, 19233674, 2000300631744, 2000312873558, 559274241, 113801730788286019251920830303795915057941382717919923450743405255545066490343, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 20000103, 2000312873558, 2000320168319, 329016603, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 113738646245785921307931320474290811401253572921585156632353747340058161626256, 20476299, 2000320168319, 2000340331263, 885310252, 113738646245785921307931320474290811401253572921585156632353747340058161626256, 113675561705573046378089664539418657692058753820501905361992741618029516562448, 21144129, 2000340331263, 2000361121621, 880001087, 113675561705573046378089664539418657692058753820501905361992741618029516562448, 113612477162647081381075922175107496585691787212661347009620181180202432303915, 22122859, 2000361121621, 2000382540438, 875850384, 113612477162647081381075922175107496585691787212661347009620181180202432303915, 113549392619316329669093009085194593108514295299018529638840237130752828077682, 23117002, 2000382540438, 2000404588762, 870355228, 113549392619316329669093009085194593108514295299018529638840237130752828077682, 113486308075726087474337563281120920512024001255384327574661536392612317490554, 24126377, 2000404588762, 2000414257402, 371970019, 113486308075726087474337563281120920512024001255384327574661536392612317490554, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 24851336, 2000414257402, 2000427267643, 494687752, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 113423223532915609762725323495929903215422411225970141808506848122479497794894, 25368066, 2000427267643, 2000450578133, 862571852, 113423223532915609762725323495929903215422411225970141808506848122479497794894, 113360138992715777889129711317774863419958659056791534073743502069852989759773, 26190146, 2000450578133, 2000474521289, 856525286, 113360138992715777889129711317774863419958659056791534073743502069852989759773, 113297054449861157443630930465772816859626899590367292492290779122962935726482, 27244219, 2000474521289, 2000491055474, 575368420, 113297054449861157443630930465772816859626899590367292492290779122962935726482, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 28134784, 2000491055474, 2000499098168, 276777691, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 113233969905580354480649385618445929481678508260660600768758926737720527299665, 28670971, 2000499098168, 2000524309828, 848304443, 113233969905580354480649385618445929481678508260660600768758926737720527299665, 113170885364335301661533543091946445274027220059318818946582768708663946773613, 29395990, 2000524309828, 2000550157333, 842687457, 113170885364335301661533543091946445274027220059318818946582768708663946773613, 113107800821388646718221743587517863013490057185593953163119432030403549426361, 30493406, 2000550157333, 2000576641747, 838037855, 113107800821388646718221743587517863013490057185593953163119432030403549426361, 113044716278033112818513361389318541320125783456597323538098705269599218459346, 31604997, 2000576641747, 2000603764136, 833272014, 113044716278033112818513361389318541320125783456597323538098705269599218459346, 112981631736309313442877537036646398268467753572159084890491611485586899883897, 32730636, 2000603764136, 2000631525571, 828543829, 112981631736309313442877537036646398268467753572159084890491611485586899883897, 112918547192195524478007023863643164755326782692192481621891611178299109648154, 33870200, 2000631525571, 2000659927121, 823909883, 112918547192195524478007023863643164755326782692192481621891611178299109648154, 112855462651672376385790594390495727936584729854258629880774029067459014371025, 35023572, 2000659927121, 2000688969863, 818854854, 112855462651672376385790594390495727936584729854258629880774029067459014371025, 112792378108161851077926452489299404993315490137099606715074090636781565936184, 36190638, 2000688969863, 2000710302767, 586850410, 112792378108161851077926452489299404993315490137099606715074090636781565936184, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 37202593, 2000710302767, 2000718654872, 227544099, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 112729293564908034992391187651470451538906664138081046607525591080690665836413, 37794235, 2000718654872, 2000748983226, 810636843, 112729293564908034992391187651470451538906664138081046607525591080690665836413, 112666209023670615234085762910623174458123534006486578305881639844107282285937, 38565421, 2000748983226, 2000779956008, 805432151, 112666209023670615234085762910623174458123534006486578305881639844107282285937, 112603124480858774545665788248539244571021783492859531153721513424905185025683, 39772931, 2000779956008, 2000811574301, 801122699, 112603124480858774545665788248539244571021783492859531153721513424905185025683, 112540039937960118806773704451393914699846178847183240658603263963967869990855, 40993722, 2000811574301, 2000843839191, 796246956, 112540039937960118806773704451393914699846178847183240658603263963967869990855, 112476955395243434821963932988309302497212538650197475495638644731480473594739, 42227698, 2000843839191, 2000865292450, 517925989, 112476955395243434821963932988309302497212538650197475495638644731480473594739, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 43254605, 2000865292450, 2000876751767, 274207290, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 112413870851890007523841967552160477988211825924010460705239036541501824339967, 43880024, 2000876751767, 2000910313119, 788558144, 112413870851890007523841967552160477988211825924010460705239036541501824339967, 112350786309833797421950668290638124193000411416798123046688794453718671079997, 44734844, 2000910313119, 2000944524341, 783394675, 112350786309833797421950668290638124193000411416798123046688794453718671079997, 112287701768035231377499992159953758613623397461973703474523853866892130698072, 46007841, 2000944524341, 2000971172512, 596921979, 112287701768035231377499992159953758613623397461973703474523853866892130698072, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 47140127, 2000971172512, 2000979386530, 182420482, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 112224617224561016455673616868842247233286696881558358634451002719793387854707, 47783908, 2000979386530, 2001014900783, 775854251, 112224617224561016455673616868842247233286696881558358634451002719793387854707, 112161532681958414037603093847885986645926248269989316729801757496472712015944, 48592267, 2001014900783, 2001051068201, 771229429, 112161532681958414037603093847885986645926248269989316729801757496472712015944, 112098448139952078187668360661545978681007265025721609718054529256280587234856, 49903539, 2001051068201, 2001087889888, 767275400, 112098448139952078187668360661545978681007265025721609718054529256280587234856, 112035363597402028440581868674011009104693099399195996486810854477967773724084, 51227416, 2001087889888, 2001125366950, 763288137, 112035363597402028440581868674011009104693099399195996486810854477967773724084, 111972279054059070443935845783287046029388178958261763754148789999675637415359, 52563825, 2001125366950, 2001163500494, 759364907, 111972279054059070443935845783287046029388178958261763754148789999675637415359, 111909194512140705805756091364476356109597521313115929756269449622220485479121, 53912695, 2001163500494, 2001202291632, 755525439, 111909194512140705805756091364476356109597521313115929756269449622220485479121, 111846109969684735852464486225814207645341127423672225635081560923995759438401, 55273958, 2001202291632, 2001241741478, 751521619, 111846109969684735852464486225814207645341127423672225635081560923995759438401, 111783025425663738310640806594200220012202052381253136190065124802870096181389, 56647548, 2001241741478, 2001274231906, 606595624, 111783025425663738310640806594200220012202052381253136190065124802870096181389, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 57900174, 2001274231906, 2001281851146, 141172308, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 111719940883040240180574629661151157642577345086747940659552737494936561390159, 58593571, 2001281851146, 2001322621755, 744592522, 111719940883040240180574629661151157642577345086747940659552737494936561390159, 111656856340782575627956112665453915150752371705285881589603161902975844442715, 59431452, 2001322621755, 2001364054426, 740528102, 111656856340782575627956112665453915150752371705285881589603161902975844442715, 111593771798723207363118349935374074456822704931302609616586717915727692990854, 60841642, 2001364054426, 2001406150283, 736987828, 111593771798723207363118349935374074456822704931302609616586717915727692990854, 111530687256015173259319646679929221430294844604079361792997687784858576082022, 62263911, 2001406150283, 2001448910452, 733429872, 111530687256015173259319646679929221430294844604079361792997687784858576082022, 111467602712658976029447050430727628127108286487790474505062277468344078575374, 63698203, 2001448910452, 2001492336060, 729929752, 111467602712658976029447050430727628127108286487790474505062277468344078575374, 111404518170890336293823363593429540467545921493368289616284526392948547464412, 65144461, 2001492336060, 2001536428240, 726497324, 111404518170890336293823363593429540467545921493368289616284526392948547464412, 111341433627922639899204538026701726192356378764611174457872120777870532699436, 66602632, 2001536428240, 2001581188124, 722975838, 111341433627922639899204538026701726192356378764611174457872120777870532699436, 111278349086121330356193619440564861087620976719920274079963383118465322646411, 68072662, 2001581188124, 2001620058499, 616308442, 111278349086121330356193619440564861087620976719920274079963383118465322646411, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 69446364, 2001620058499, 2001626616850, 103291982, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 111215264542988390397579414011794402802366117490443179592920562218463526677403, 70187402, 2001626616850, 2001672715556, 716686504, 111215264542988390397579414011794402802366117490443179592920562218463526677403, 111152179999674339872743526310405559956088552212013931891488748728527523738925, 71048096, 2001672715556, 2001719485382, 713118577, 111152179999674339872743526310405559956088552212013931891488748728527523738925, 111089095458050101418007938592134660953112029370127642338992125812725060566198, 72553403, 2001719485382, 2001766927474, 710063893, 111089095458050101418007938592134660953112029370127642338992125812725060566198, 111026010915384298643085814857348387926895036210243682973037409775786689720458, 74070371, 2001766927474, 2001814869793, 703666631, 111026010915384298643085814857348387926895036210243682973037409775786689720458, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 75596176, 2001814869793, 2001815042978, 3514479, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 110962926372484418020183554377212420732609873106198994710971622456158483505817, 76359512, 2001815042978, 2001863833043, 703092410, 110962926372484418020183554377212420732609873106198994710971622456158483505817, 110899841829611508171014561460802410145239953216243319490380334926252601822799, 77139113, 2001863833043, 2001913298820, 700693546, 110899841829611508171014561460802410145239953216243319490380334926252601822799, 110836757287793153874328581565194344979078007821684726017360161366356763251149, 78690798, 2001913298820, 2001963441465, 697477663, 110836757287793153874328581565194344979078007821684726017360161366356763251149, 110773672745032320206794028083502507322165359942976913556897925976919329350359, 80253969, 2001963441465, 2002009240430, 626186385, 110773672745032320206794028083502507322165359942976913556897925976919329350359, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 81750009, 2002009240430, 2002014262135, 68286827, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 110710588201449262017652004068122926680331378788633490456648460139132619262672, 82537115, 2002014262135, 2002065761988, 691747340, 110710588201449262017652004068122926680331378788633490456648460139132619262672, 110647503659152280761249537408427270304476817692927459591974397299213335362530, 83414603, 2002065761988, 2002117942187, 688662250, 110647503659152280761249537408427270304476817692927459591974397299213335362530, 110584419117313322880706572908817566078491848053170232100930005673954670091691, 85011987, 2002117942187, 2002170803898, 685812265, 110584419117313322880706572908817566078491848053170232100930005673954670091691, 110521334574736174988661704948277926618676560247836863946876774992027264790131, 86620698, 2002170803898, 2002224348289, 682972527, 110521334574736174988661704948277926618676560247836863946876774992027264790131, 110458250031059556820337365981297231323763112630118197694904681220921087730490, 88240698, 2002224348289, 2002278576528, 680174879, 110458250031059556820337365981297231323763112630118197694904681220921087730490, 110395165489025844900298425602397829590348388941858138560469895804070521129268, 89871950, 2002278576528, 2002333489790, 677416505, 110395165489025844900298425602397829590348388941858138560469895804070521129268, 110332080946305592584257567580667834459747139144429293092791985443300358535782, 91514421, 2002333489790, 2002389089250, 674678249, 110332080946305592584257567580667834459747139144429293092791985443300358535782, 110268996403710519379177614769903421102035856609349789826157032463902724031035, 93168074, 2002389089250, 2002442376672, 636246951, 110268996403710519379177614769903421102035856609349789826157032463902724031035, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 94788109, 2002442376672, 2002445376086, 35751060, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 110205911861669877267145482971565458057328846748394112166633381082233272478812, 95620013, 2002445376086, 2002502351481, 669368336, 110205911861669877267145482971565458057328846748394112166633381082233272478812, 110142827318060626897294829286871667481962053325010212872720163689176091320662, 96508796, 2002502351481, 2002560016616, 666733258, 110142827318060626897294829286871667481962053325010212872720163689176091320662, 110079742775979912364700373305936539248802317256979081127662410724455050034816, 98195800, 2002560016616, 2002618372679, 664150987, 110079742775979912364700373305936539248802317256979081127662410724455050034816, 110016658233774427867307312693236696057963061413839901994158574602410524909296, 99893857, 2002618372679, 2002677420860, 661600532, 110016658233774427867307312693236696057963061413839901994158574602410524909296, 109953573690635716473354572254589489594298176356376834769921802058558620914140, 101602937, 2002677420860, 2002737162349, 659085117, 109953573690635716473354572254589489594298176356376834769921802058558620914140, 109890489148659641061185031285847408766200245143689552845237728078057454035379, 103323011, 2002737162349, 2002797598343, 656590056, 109890489148659641061185031285847408766200245143689552845237728078057454035379, 109827404605423641520530492076502748056373997657927540282127334714463021871439, 105054049, 2002797598343, 2002858730038, 654211272, 109827404605423641520530492076502748056373997657927540282127334714463021871439, 109764320062459068567026271207096310833427598491394817102980848045118651955333, 106796023, 2002858730038, 2002920077285, 646274548, 109764320062459068567026271207096310833427598491394817102980848045118651955333, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 108542023, 2002920077285, 2002920558634, 5704814, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 109701235519964946023978611259433354308846594737750218579159323162629441927527, 109417690, 2002920558634, 2002983085334, 648959561, 109701235519964946023978611259433354308846594737750218579159323162629441927527, 109638150977892969816287289962098476545515883035618239837206840069202391710730, 110312670, 2002983085334, 2003046311345, 647035806, 109638150977892969816287289962098476545515883035618239837206840069202391710730, 109575066434976705812917004005349629220004249785431115870054444087860896105668, 112087289, 2003046311345, 2003110237874, 644629237, 109575066434976705812917004005349629220004249785431115870054444087860896105668, 109511981892731646361056364358816392135827326746712986227853241465818119262931, 113872739, 2003110237874, 2003174866134, 642335901, 109511981892731646361056364358816392135827326746712986227853241465818119262931, 109448897349487853206411866489334419585164163197410083163486154573392203669785, 115668994, 2003174866134, 2003240197337, 640060079, 109448897349487853206411866489334419585164163197410083163486154573392203669785, 109385812807291062401607696415277634628814502164675995204924122397782650210202, 117476030, 2003240197337, 2003306232701, 637807529, 109385812807291062401607696415277634628814502164675995204924122397782650210202, 109322728265061728540855281802345780626136817533203825248526045825887363720295, 119293823, 2003306232701, 2003372973446, 635627886, 109322728265061728540855281802345780626136817533203825248526045825887363720295, 109259643722527661252484273634422919562062166861412091129869313992672371128074, 121122350, 2003372973446, 2003440420795, 633198014, 109259643722527661252484273634422919562062166861412091129869313992672371128074, 109196559179259230616800526488487433654564530581388608168927985244479700415449, 122961589, 2003440420795, 2003442963668, 23903617, 109196559179259230616800526488487433654564530581388608168927985244479700415449, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 123915123, 2003442963668, 2003508575972, 607462387, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 109133474636526686520015927278482924533097953418728199851839661333016542603210, 124845950, 2003508575972, 2003577440205, 629131862, 109133474636526686520015927278482924533097953418728199851839661333016542603210, 109070390094486423392914300030741617841316670539606781590645871731674991907012, 126672112, 2003577440205, 2003647014727, 626966830, 109070390094486423392914300030741617841316670539606781590645871731674991907012, 109007305551342664688410286706514983728415331636509788619543125364061982699844, 128543355, 2003647014727, 2003717300770, 624913652, 109007305551342664688410286706514983728415331636509788619543125364061982699844, 108944221008811273406116688499520385966115354421279119941535635609269682393275, 130425225, 2003717300770, 2003788299571, 622627922, 108944221008811273406116688499520385966115354421279119941535635609269682393275, 108881136466647306845877195312445149398571267652409721248890036448066987550586, 132317702, 2003788299571, 2003829787234, 359817159, 108881136466647306845877195312445149398571267652409721248890036448066987550586, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 133816866, 2003829787234, 2003860012371, 260927166, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 108818051923624510373460217344716312319055513641780788086892543283390204756685, 134770505, 2003860012371, 2003932440411, 619013768, 108818051923624510373460217344716312319055513641780788086892543283390204756685, 108754967381057671707746159158884064742300332509471085016572734057781649954667, 136134398, 2003932440411, 2004005584937, 616554174, 108754967381057671707746159158884064742300332509471085016572734057781649954667, 108691882838394758650776093429331581864549198110156847176667519859484818301684, 138058581, 2004005584937, 2004011668828, 50995461, 108691882838394758650776093429331581864549198110156847176667519859484818301684, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 139100020, 2004011668828, 2004079447197, 563918387, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 108628798295864005512455752305364826318556968587389225647566419761594491467742, 140072817, 2004079447197, 2004154028442, 612892258, 108628798295864005512455752305364826318556968587389225647566419761594491467742, 108565713753601830738931864560991780480497127324020759493326576493681452702472, 141938525, 2004154028442, 2004229329927, 610913386, 108565713753601830738931864560991780480497127324020759493326576493681452702472, 108502629210830437610507103193680153488545984800959693934816482264560567731209, 143894252, 2004229329927, 2004305352908, 609014318, 108502629210830437610507103193680153488545984800959693934816482264560567731209, 108439544668385651936123106215111483275576339246838398118438040041282562351292, 145860460, 2004305352908, 2004382098646, 607129925, 108439544668385651936123106215111483275576339246838398118438040041282562351292, 108376460125375757851812557046925201340237773734115804533999742630940413607367, 147837133, 2004382098646, 2004459568402, 605262078, 108376460125375757851812557046925201340237773734115804533999742630940413607367, 108313375583321290972800215948363041280557923445252865363139074380489421386482, 149824255, 2004459568402, 2004537763444, 603455379, 108313375583321290972800215948363041280557923445252865363139074380489421386482, 108250291040429385491135448813565288402706660616304194084571276657990084205183, 151821810, 2004537763444, 2004616685039, 601415716, 108250291040429385491135448813565288402706660616304194084571276657990084205183, 108187206498117629843365377203810135877094960489053517174118619012673151865239, 153829784, 2004616685039, 2004626837653, 76843736, 108187206498117629843365377203810135877094960489053517174118619012673151865239, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 154962335, 2004626837653, 2004696334460, 523061490, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 108124121955356050489816494324377739304354378662470388994455254976112305334687, 155976571, 2004696334460, 2004776712981, 598076610, 108124121955356050489816494324377739304354378662470388994455254976112305334687, 108061037412690721203365091446517640619511748369353528111587926877087100253091, 157876931, 2004776712981, 2004857821880, 596249021, 108061037412690721203365091446517640619511748369353528111587926877087100253091, 107997952869857079119829152962898405959557987379414915115361147595448879005027, 159916076, 2004857821880, 2004939662437, 594513071, 107997952869857079119829152962898405959557987379414915115361147595448879005027, 107934868327357401118851186600682191248264439234753377343929035848298892320070, 161965583, 2004939662437, 2005022235936, 592787243, 107934868327357401118851186600682191248264439234753377343929035848298892320070, 107871783784912373766631492252147264612421718588914490383949470768945172156742, 164025440, 2005022235936, 2005105543664, 591075699, 107871783784912373766631492252147264612421718588914490383949470768945172156742, 107808699242255866378203853998844723633798486523047528030726380504226816276649, 166095634, 2005105543664, 2005189586910, 589422020, 107808699242255866378203853998844723633798486523047528030726380504226816276649, 107745614699888318084074567239508270766429426560235180350375370925031796634415, 168176152, 2005189586910, 2005274366968, 587533726, 107745614699888318084074567239508270766429426560235180350375370925031796634415, 107682530156827502135920802556923859152678072058544435245186007760429859928275, 170266984, 2005274366968, 2005289127186, 101573932, 107682530156827502135920802556923859152678072058544435245186007760429859928275, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 171493904, 2005289127186, 2005359885132, 484589075, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 107619445614351225155555244453560287906516522991279587739030124361700241635285, 172549150, 2005359885132, 2005446142702, 584501751, 107619445614351225155555244453560287906516522991279587739030124361700241635285, 107556361071538055135978781797658556515696073745533115532851246167809880885770, 174479538, 2005446142702, 2005533140979, 582805634, 107556361071538055135978781797658556515696073745533115532851246167809880885770, 107493276528977111932412686087609193646205344595997165767339130962636852503515, 176601239, 2005533140979, 2005620881268, 581212866, 107493276528977111932412686087609193646205344595997165767339130962636852503515, 107430191986563070495481688456031596528546201628061070364425812371479112210470, 178733207, 2005620881268, 2005709364877, 579626194, 107430191986563070495481688456031596528546201628061070364425812371479112210470, 107367107444241490370640475455025915733779230232888327146512735068743854364627, 180875434, 2005709364877, 2005798593118, 578052086, 107367107444241490370640475455025915733779230232888327146512735068743854364627, 107304022901309000966006964094165141204760018309979669744939121939495730349637, 183027907, 2005798593118, 2005888567304, 576532192, 107304022901309000966006964094165141204760018309979669744939121939495730349637, 107240938358541166712346483812387643203273655330093790969739413239193356225689, 185190619, 2005888567304, 2005979288752, 574782062, 107240938358541166712346483812387643203273655330093790969739413239193356225689, 107177853816060633774514990475443484676537401309461459214584733011280030100050, 187363559, 2005979288752, 2005999206922, 125309825, 107177853816060633774514990475443484676537401309461459214584733011280030100050, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 188688159, 2005999206922, 2006070758783, 448216729, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 107114769273369907962247553695314138014721293808686334407761199419277127866911, 189784074, 2006070758783, 2006162978720, 572016099, 107114769273369907962247553695314138014721293808686334407761199419277127866911, 107051684730745285847054381892866125165153549618625696774427114161790868651861, 191740089, 2006162978720, 2006255949889, 570436068, 107051684730745285847054381892866125165153549618625696774427114161790868651861, 106988600188536157056255433435145169608525493744369800364861806799214469607441, 193943661, 2006255949889, 2006349673621, 568969638, 106988600188536157056255433435145169608525493744369800364861806799214469607441, 106925515645827421217609971290396742304248867547982588428385895797817198387453, 196157426, 2006349673621, 2006444151248, 567505821, 106925515645827421217609971290396742304248867547982588428385895797817198387453, 106862431103156129708073858915490352752420750668549539748072153984543305619217, 198381377, 2006444151248, 2006539384106, 566053232, 106862431103156129708073858915490352752420750668549539748072153984543305619217, 106799346560480913958155269670926393640125633146597403556913283053051769753163, 200615506, 2006539384106, 2006635373534, 564650961, 106799346560480913958155269670926393640125633146597403556913283053051769753163, 106736262017865348403054775141762498511389703497634538465581077526777446076077, 202859805, 2006635373534, 2006732120874, 563027578, 106736262017865348403054775141762498511389703497634538465581077526777446076077, 106673177475479923714344491383230806536428100261171528967269185392003635840690, 205114267, 2006732120874, 2006757759095, 148164818, 106673177475479923714344491383230806536428100261171528967269185392003635840690, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 206539908, 2006757759095, 2006829627473, 413702454, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 106610092932314997733412020435324209959298350058635177349958492620185813878534, 207676225, 2006829627473, 2006927894677, 560492619, 106610092932314997733412020435324209959298350058635177349958492620185813878534, 106547008390069272829265973487024933454333751013319955582337967871214246688475, 209653654, 2006927894677, 2007026923840, 559016154, 106547008390069272829265973487024933454333751013319955582337967871214246688475, 106483923847340765283286255168738329353794510958546381280217106193037986412082, 211938565, 2007026923840, 2007126716316, 557661753, 106483923847340765283286255168738329353794510958546381280217106193037986412082, 106420839304788747040386507134133338897246983291967546007498417220445674055429, 214233613, 2007126716316, 2007227273464, 556306990, 106420839304788747040386507134133338897246983291967546007498417220445674055429, 106357754761936875071814184999709158919991313227567139013145352281282119608061, 216538792, 2007227273464, 2007328596644, 554962447, 106357754761936875071814184999709158919991313227567139013145352281282119608061, 106294670219702863522319817398435626221347443236202940435412806703112310390546, 218854097, 2007328596644, 2007430687222, 553664213, 106294670219702863522319817398435626221347443236202940435412806703112310390546, 106231585677274142892469500020463882903037352853125834490620262111481238548770, 221179521, 2007430687222, 2007533546566, 552157310, 106231585677274142892469500020463882903037352853125834490620262111481238548770, 106168501134622176683333491738573092547921281318228252631268372285793524247162, 223515060, 2007533546566, 2007565478990, 170236793, 106168501134622176683333491738573092547921281318228252631268372285793524247162, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 225045156, 2007565478990, 2007637176047, 380839641, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 106105416591872870680516749339370248127546596833066628947902345445688968298165, 226221678, 2007637176047, 2007741577039, 549823965, 106105416591872870680516749339370248127546596833066628947902345445688968298165, 106042332049306711797636087259192637562995428259487107710588302498868837530209, 228216461, 2007741577039, 2007846750920, 548440774, 106042332049306711797636087259192637562995428259487107710588302498868837530209, 105979247506761277790758026261942688410046891558850348496718933099007498177574, 230582315, 2007846750920, 2007952699071, 547186261, 105979247506761277790758026261942688410046891558850348496718933099007498177574, 105916162964246380126726870963751682512651346054008307459141862781407845795396, 232958264, 2007952699071, 2008059422877, 545928935, 105916162964246380126726870963751682512651346054008307459141862781407845795396, 105853078421354645539620477149991739484391819098003899811267440679100413613057, 235344306, 2008059422877, 2008166923725, 544681056, 105853078421354645539620477149991739484391819098003899811267440679100413613057, 105789993878451716004433473035924885258268908066323772411828067415724353058978, 237740435, 2008166923725, 2008275203005, 543475526, 105789993878451716004433473035924885258268908066323772411828067415724353058978, 105726909336073787641532037757483641836522532205442458070818424671149550258312, 240146649, 2008275203005, 2008384262112, 542075966, 105726909336073787641532037757483641836522532205442458070818424671149550258312, 105663824793774420147215949766573471817113300047439310235306102741962968159108, 242562943, 2008384262112, 2008423075252, 191610501, 105663824793774420147215949766573471817113300047439310235306102741962968159108, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 244200966, 2008423075252, 2008494102445, 349451857, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 105600740250737290300221204727345485166237830483059258009388127483585159127902, 245417553, 2008494102445, 2008604725403, 539919948, 105600740250737290300221204727345485166237830483059258009388127483585159127902, 105537655708067971098733755860895769928020081527470129488673545805108245710893, 247425762, 2008604725403, 2008716132390, 538621785, 105537655708067971098733755860895769928020081527470129488673545805108245710893, 105474571165910897450759277215755393373087556107967587810214259878832169165515, 249872281, 2008716132390, 2008828324816, 537457179, 105474571165910897450759277215755393373087556107967587810214259878832169165515, 105411486622928078674104968048639586916539628164357741380448139439262200468149, 252328868, 2008828324816, 2008941304090, 536287873, 105411486622928078674104968048639586916539628164357741380448139439262200468149, 105348402080251198882801038512946379074353973386448069558515113226431923678059, 254795523, 2008941304090, 2009055071626, 535127558, 105348402080251198882801038512946379074353973386448069558515113226431923678059, 105285317538086501826858366833547771893932111365043859371074740539292204783129, 257272241, 2009055071626, 2009169628844, 534005919, 105285317538086501826858366833547771893932111365043859371074740539292204783129, 105222232995203242651957406126797066991840815729682111064995467975204137601092, 259759022, 2009169628844, 2009284977163, 532706465, 105222232995203242651957406126797066991840815729682111064995467975204137601092, 105159148452803594521662015863311776976709511216641727275305913518129556077797, 262255863, 2009284977163, 2009331270210, 212361569, 105159148452803594521662015863311776976709511216641727275305913518129556077797, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 264005340, 2009331270210, 2009401118009, 319390304, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 105096063910114936599461506154470094028826432206946828169586489227620158526397, 265261905, 2009401118009, 2009518052809, 530710106, 105096063910114936599461506154470094028826432206946828169586489227620158526397, 105032979367688035687989083421890409293000024423628386074064258218397144453212, 267279721, 2009518052809, 2009635782996, 529492295, 105032979367688035687989083421890409293000024423628386074064258218397144453212, 104969894824687869148281453686385976400457283100655428638550704641892529300896, 269806734, 2009635782996, 2009754310003, 528411882, 104969894824687869148281453686385976400457283100655428638550704641892529300896, 104906810282128215473146484553365478495599882763286167402187326289564084589346, 272343802, 2009754310003, 2009873635269, 527326343, 104906810282128215473146484553365478495599882763286167402187326289564084589346, 104843725739654047806003907551841027469221128507102736076109729668540850565143, 274890925, 2009873635269, 2009993760236, 526250983, 104843725739654047806003907551841027469221128507102736076109729668540850565143, 104780641197162546003647944764163276277828045588313517128340170408895395242093, 277448100, 2009993760236, 2010114686350, 525212834, 104780641197162546003647944764163276277828045588313517128340170408895395242093, 104717556654280275559265245249797627926030833413034144969142740968833356685338, 280015327, 2010114686350, 2010236415058, 524017605, 104717556654280275559265245249797627926030833413034144969142740968833356685338, 104654472111927110353513281017615333885397799616451555064507573030851322643055, 282592607, 2010236415058, 2010290800207, 232576909, 104654472111927110353513281017615333885397799616451555064507573030851322643055, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 284457125, 2010290800207, 2010358947814, 290553023, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 104591387569200422392477199040224726152582162546220468190751058895910187488310, 285753631, 2010358947814, 2010482286073, 522201950, 104591387569200422392477199040224726152582162546220468190751058895910187488310, 104528303026498577536996865935668209417908801699206325016441910913550608833459, 287777322, 2010482286073, 2010606431294, 521094917, 104528303026498577536996865935668209417908801699206325016441910913550608833459, 104465218483964709474505771410097112415691930139334486544338245482625450441303, 290384757, 2010606431294, 2010731384940, 520153905, 104465218483964709474505771410097112415691930139334486544338245482625450441303, 104402133941500256929531532339823470879237059779306284801867668722721864946773, 293002244, 2010731384940, 2010857148478, 519217107, 104402133941500256929531532339823470879237059779306284801867668722721864946773, 104339049398778042616673924919004025561208091977358328694469187076413377334023, 295629784, 2010857148478, 2010983723377, 518591875, 104339049398778042616673924919004025561208091977358328694469187076413377334023, 104275964856248516946891009344722839191048470755904060932928872526658363402185, 298267377, 2010983723377, 2011111111111, 516662086, 104275964856248516946891009344722839191048470755904060932928872526658363402185, 104212880313639424765589609273198082398330793722669431932394052100552687231877, 300915024, 2011111111111, 2011302415947, 780851080, 104212880313639424765589609273198082398330793722669431932394052100552687231877, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 304230345, 2011302415947, 2012366882840, 4117912781, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 317311053, 2012366882840, 2013484981369, 4049740535, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 339463445, 2013484981369, 2014657507458, 3994784597, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 362268794, 2014657507458, 2015885272861, 3941832454, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 385728957, 2015885272861, 2017169105555, 3892112667, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 409846335, 2017169105555, 2018509850146, 3845134262, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 434623851, 2018509850146, 2019908368292, 3800708364, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 460064918, 2019908368292, 2021365539130, 3758633064, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 486173416, 2021365539130, 2022882259729, 3718733437, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 512953677, 2022882259729, 2024459445544, 3680851655, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 540410466, 2024459445544, 2026098030889, 3644845527, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 568548967, 2026098030889, 2027798969430, 3610586415, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 597374775, 2027798969430, 2029563234684, 3577957588, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 626893882, 2029563234684, 2031391820540, 3546852843, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 657112676, 2031391820540, 2033285741796, 3517175323, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 688037928, 2033285741796, 2035246034710, 3488836469, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 719676793, 2035246034710, 2037273757570, 3461755130, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 752036805, 2037273757570, 2039369991282, 3435856810, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 785125874, 2039369991282, 2041535839982, 3411072948, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 818952287, 2041535839982, 2043772431658, 3387340348, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 853524706, 2043772431658, 2046080918800, 3364600649, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 888852171, 2046080918800, 2048462479068, 3342799845, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 924944102, 2048462479068, 2050918315986, 3321887894, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 961810298, 2050918315986, 2053449659651, 3301818338, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 999460945, 2053449659651, 2056057767474, 3282547983, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 1037906619, 2056057767474, 2058743924941, 3264036608, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 1077158288, 2058743924941, 2061509446402, 3246246709, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 1117227322, 2061509446402, 2064355675884, 3229143255, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 1158125497, 2064355675884, 2067283987935, 3212693495, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 1199865001, 2067283987935, 2070295788495, 3196866761, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 1242458443, 2070295788495, 2073392515795, 3181634293, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 1285918862, 2073392515795, 2076575641295, 3166969108, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 1330259733, 2076575641295, 2079846670642, 3152845823, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 1375494981, 2079846670642, 2083207144675, 3139240576, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 1421638985, 2083207144675, 2086658640454, 3126130869, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 1468706596, 2086658640454, 2090202772336, 3113495502, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 1516713142, 2090202772336, 2093841193078, 3101314448, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 1565674445, 2093841193078, 2097575594992, 3089568777, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 1615606830, 2097575594992, 2101407711130, 3078240586, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 1666527142, 2101407711130, 2105339316520, 3067312919, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 1718452757, 2105339316520, 2109372229446, 3056769700, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 1771401599, 2109372229446, 2113508312770, 3046595673, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 1825392157, 2113508312770, 2117749475310, 3036776349, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 1880443497, 2117749475310, 2122097673263, 3027297955, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 1936575284, 2122097673263, 2126554911687, 3018147381, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 1993807798, 2126554911687, 2131123246034, 3009312141, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 2052161953, 2131123246034, 2135804783745, 3000780337, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 2111659318, 2135804783745, 2140601685900, 2992540608, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 2172322136, 2140601685900, 2145516168944, 2984582109, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 2234173347, 2145516168944, 2150550506461, 2976894478, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 2297236613, 2150550506461, 2155707031036, 2969467793, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 2361536336, 2155707031036, 2160988136175, 2962292562, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 2427097690, 2160988136175, 2166396278310, 2955359686, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 2493946643, 2166396278310, 2171933978883, 2948660445, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 2562109984, 2171933978883, 2177603826505, 2942186456, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 2631615354, 2177603826505, 2183408479212, 2935929674, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 2702491275, 2183408479212, 2189350666807, 2929882370, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 2774767180, 2189350666807, 2195433193299, 2924037096, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 2848473448, 2195433193299, 2201658939440, 2918386684, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 2923641437, 2201658939440, 2208030865372, 2912924227, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 3000303520, 2208030865372, 2214552013376, 2907643061, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 3078493122, 2214552013376, 2221225510745, 2902536751, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 3158244761, 2221225510745, 2228054572775, 2897599082, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 3239594088, 2228054572775, 2235042505876, 2892824043, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 3322577930, 2235042505876, 2242192710831, 2888205817, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 3407234335, 2242192710831, 2249508686181, 2883738765, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 3493602620, 2249508686181, 2256994031765, 2879417431, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 3581723421, 2256994031765, 2264652452415, 2875236509, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 3671638743, 2264652452415, 2272487761808, 2871190854, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 3763392018, 2272487761808, 2280503886497, 2867275457, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 3857028158, 2280503886497, 2288704870114, 2863485463, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 3952593618, 2288704870114, 2297094877771, 2859816127, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 4050136457, 2297094877771, 2305678200651, 2856262825, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 4149706406, 2305678200651, 2314459260821, 2852821064, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 4251354935, 2314459260821, 2323442616254, 2849486436, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 4355135329, 2323442616254, 2332632966095, 2846254648, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 4461102762, 2332632966095, 2342035156166, 2843121494, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 4569314377, 2342035156166, 2351654184737, 2840082864, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 4679829375, 2351654184737, 2361495208566, 2837134717, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 4792709098, 2361495208566, 2371563549232, 2834273101, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 4908017126, 2371563549232, 2381864699773, 2831494127, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 5025819378, 2381864699773, 2392404331648, 2828793984, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 5146184210, 2392404331648, 2403188302039, 2826168904, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 5269182528, 2403188302039, 2414222661519, 2823615193, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 5394887904, 2414222661519, 2425513662095, 2821129198, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 5523376696, 2425513662095, 2437067765666, 2818707319, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 5654728176, 2437067765666, 2448891652905, 2816345993, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 5789024666, 2448891652905, 2460992232592, 2814041701, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 5926351681, 2460992232592, 2473376651441, 2811790955, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 6066798080, 2473376651441, 2486052304424, 2809590292, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 6210456223, 2486052304424, 2499026845650, 2807436287, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 6357422143, 2499026845650, 2512308199817, 2805325522, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 6507795722, 2512308199817, 2525904574270, 2803254602, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 6661680882, 2525904574270, 2539824471725, 2801220143, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 6819185778, 2539824471725, 2554076703668, 2799218774, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 6980423019, 2554076703668, 2568670404505, 2797247127, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 7145509884, 2568670404505, 2583615046489, 2795301823, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 7314568564, 2583615046489, 2598920455487, 2793379487, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 7487726412, 2598920455487, 2614596827637, 2791476740, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 7665116209, 2614596827637, 2630654746951, 2789590170, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 7846876452, 2630654746951, 2647105203942, 2787716369, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 8033151652, 2647105203942, 2663959615326, 2785851890, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 8224092657, 2663959615326, 2681229844882, 2783993260, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 8419856989, 2681229844882, 2698928225555, 2782136978, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 8620609214, 2698928225555, 2717067582878, 2780279496, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 8826521322, 2717067582878, 2735661259813, 2778417220, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 9037773140, 2735661259813, 2754723143110, 2776546512, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 9254552777, 2754723143110, 2774267691295, 2774663671, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 9477057085, 2774267691295, 2794309964405, 2772764931, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 9705492163, 2794309964405, 2814865655598, 2770846455, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 9940073892, 2814865655598, 2835951124772, 2768904333, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 10181028505, 2835951124772, 2857583434359, 2766934554, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 10428593201, 2857583434359, 2879780387444, 2764933022, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 10683016794, 2879780387444, 2902560568391, 2762895539, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 10944560420, 2902560568391, 2925943386182, 2760817787, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 11213498285, 2925943386182, 2949949120659, 2758695321, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 11490118475, 2949949120659, 2974598971928, 2756523566, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 11774723818, 2974598971928, 2999915113156, 2754297797, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 12067632815, 2999915113156, 3025920747045, 2752013128, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 12369180645, 3025920747045, 3052640166290, 2749664498, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 12679720238, 3052640166290, 3080098818344, 2747246657, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 12999623436, 3080098818344, 3108323374859, 2744754152, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 13329282245, 3108323374859, 3137341806196, 2742181299, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 13669110185, 3137341806196, 3167183461447, 2739522177, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 14019543747, 3167183461447, 3197879154446, 2736770602, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 14381043969, 3197879154446, 3229461256300, 2733920101, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 14754098144, 3229461256300, 3261963795027, 2730963879, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 15139221664, 3261963795027, 3295422562941, 2727894823, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 15536960027, 3295422562941, 3329875232493, 2724705436, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 15947891007, 3329875232493, 3365361481374, 2721387827, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 16372627015, 3365361481374, 3401923127728, 2717933652, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 16811817674, 3401923127728, 3439604276464, 2714334103, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 17266152607, 3439604276464, 3478451477733, 2710579852, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 17736364492, 3478451477733, 3518513898767, 2706660985, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 18223232385, 3518513898767, 3559843510423, 2702566983, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 18727585356, 3559843510423, 3602495289904, 2698286627, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 19250306463, 3602495289904, 3646527441337, 2693807959, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 19792337106, 3646527441337, 3692001636057, 2689118194, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 20354681808, 3692001636057, 3738983274682, 2684203644, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 20938413450, 3738983274682, 3787541773333, 2679049618, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 21544679046, 3787541773333, 3837750876617, 2673640333, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 22174706087, 3837750876617, 3889689000358, 2667958793, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 22829809548, 3889689000358, 3943439607399, 2661986649, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 23511399619, 3943439607399, 3999091620303, 2655704077, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 24220990261, 3999091620303, 4056739875199, 2649089597, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 24960208685, 4056739875199, 4116485621680, 2642119876, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 25730805866, 4116485621680, 4178437074280, 2634769547, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 26534668238, 4178437074280, 4242710021848, 2627010956, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 27373830711, 4242710021848, 4309428502045, 2618813877, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 28250491190, 4309428502045, 4378725549217, 2610145204, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 29167026812, 4378725549217, 4450744025144, 2600968611, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 30126012114, 4450744025144, 4525637543577, 2591244110, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 31130239431, 4525637543577, 4603571501134, 2580927588, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 32182741822, 4603571501134, 4684724229148, 2569970253, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 33286818907, 4684724229148, 4769288283309, 2558317976, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 34446066041, 4769288283309, 4857471890760, 2545910537, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 35664407344, 4857471890760, 4949500577511, 2532680760, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 36946133169, 4949500577511, 5045619002969, 2518553427, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 38295942727, 5045619002969, 5146093032971, 2503444066, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 39718992700, 5146093032971, 5251212088326, 2487257426, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 41220952830, 5251212088326, 5361291812535, 2469885740, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 42808069669, 5361291812535, 5476677110468, 2451206386, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 44487239903, 5476677110468, 5597745619623, 2431079695, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 46266094949, 5597745619623, 5724911687529, 2409342264, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 48153098870, 5724911687529, 5858630943575, 2385823000, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 50157662093, 5858630943575, 5999405571524, 2360192908, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 52290273934, 5999405571524, 6147790411300, 2332901339, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 54562657635, 6147790411300, 6304400046307, 2298584996, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 56987952419, 6304400046307, 6410000000000, 1460169482, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 59085116079, 6410000000000, 6469917067130, 800591120, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 60420593962, 6469917067130, 6474122807018, 56009382, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 60939804547, 6474122807018, 6539645390071, 853083125, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 61511518444, 6539645390071, 6606612903226, 846740187, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 62596378178, 6606612903226, 6645101745895, 475279517, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 63461525740, 6645101745895, 6675072463768, 366333291, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 64025907442, 6675072463768, 6745073260073, 836555344, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 64855925902, 6745073260073, 6816666666667, 828881402, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 66032946220, 6816666666667, 6830803410465, 160507311, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 66745106924, 6830803410465, 6889906367041, 663108057, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 67360304431, 6889906367041, 6964848484848, 816607716, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 68487758404, 6964848484848, 7027973877427, 667400747, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 69652085879, 7027973877427, 7041551724138, 141905726, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 70299464815, 7041551724138, 7120077519380, 803070032, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 71086072098, 7120077519380, 7200490196078, 793982610, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 72442741703, 7200490196078, 7237683392161, 357748070, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 73447933363, 7237683392161, 7282857142857, 429252010, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 74157088883, 7282857142857, 7367248995984, 779385889, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 75279208848, 7367248995984, 7453739837398, 769389474, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 76762514263, 7453739837398, 7461139639404, 64532690, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 77576260176, 7461139639404, 7542407407407, 696781611, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 78355692715, 7542407407407, 7633333333333, 751073829, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 79868779165, 7633333333333, 7699710537247, 529553992, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 81255065965, 7699710537247, 7726603375527, 211554744, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 82079519288, 7726603375527, 7822307692308, 731831062, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 83175212309, 7822307692308, 7920541125541, 718811980, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 84909187301, 7920541125541, 7954951723164, 244192436, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 86095865772, 7954951723164, 8021403508772, 464235441, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 87007442613, 8021403508772, 8125000000000, 696384028, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 88551242231, 8125000000000, 8228639898899, 664704356, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 90438864082, 8228639898899, 8231441441441, 17938933, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 91406600803, 8231441441441, 8340844748858, 668977720, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 92444034547, 8340844748858, 8453333333333, 653360394, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 94492085358, 8453333333333, 8522813544898, 386153406, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 96176785072, 8522813544898, 8569037558685, 252070370, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 97254055535, 8569037558685, 8688095238095, 622728528, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 98808470700, 8688095238095, 8810652173913, 602456216, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 101084259177, 8810652173913, 8839822977139, 137648989, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 102512991695, 8839822977139, 8936862745098, 447115650, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 103717817248, 8936862745098, 9066890547264, 563528660, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 105891541173, 9066890547264, 9182392346833, 467235897, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 108250764533, 9182392346833, 9200909090909, 72880991, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 109539051802, 9200909090909, 9339102564103, 516764513, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 111070432519, 9339102564103, 9481666666667, 487152078, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 113811945810, 9481666666667, 9553697044961, 228428730, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 115912399357, 9553697044961, 9628809523810, 229818029, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 117365494225, 9628809523810, 9780752688172, 425547336, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 119627768334, 9780752688172, 9937732240437, 383831941, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 122714809917, 9937732240437, 9957461170062, 44076930, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 124478128791, 9957461170062, 10100000000000, 296594388, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 126126874296, 10100000000000, 10267824858757, 283769850, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 129282627545, 10267824858757, 10398081400337, 164285658, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 132326355070, 10398081400337, 10441494252874, 54276670, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 134105498314, 10441494252874, 10621315789474, 52023918, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 136429264952, 10621315789474, 10807619047619, 3924, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 10807261662149560027232040213498220601263609139992136342716886379089587977866, 140242264334, 10807619047619, 10880786009858, 1449, 10807261662149560027232040213498220601263609139992136342716886379089587977866, 10733325018106978829661902837225436334308070792871749259918571285640291176299, 142948580271]
def RP : List ℤ := raw_ints% [29805965679107891286107303829068541094107917564202389851142851450208743064953067645038007449872530723604732858963422679857710032023282949324704581829504126, 55379201540712338800986169987606089567650209697026479213584227991138752518850568985109105343009039606756103721681344015103392226997077177017844579577902999, 78179703045874628821822816225827705291602889073999152410163408836819207919873020334919107632046462544098630597885889567879898701328745075341904619538699752, 98897215036428374590848276619159875493175329827861622106107806290273511724499519986191462040574461856761856944385813771976596109428059123860973413487959530, 117934505562651055458751985944811100239972404734933350404355875289560557705744543769862224226879932538621445059374742863340387519673252758232485969028404848, 135558995502104858452162266654639068220936575295589033564399295672568675957891582043520935600930644950615430184132904430134753430199063529641248296669427963, 151963214283715305008050862573052917668258655275146601012108310181157754946256458295592577984414434782941379503078339862215195352785045210888411598402583187, 167293532949707612437303407592766665282745434998562760843054053495740184206464709910136367815332129653846014264625101630766601469752875219746223238927248693, 181665633748560131090290884546590737818788574710008908250126942167313637445816132217126980134351025406035000730512613577645662202432467556486624509129953223, 195173627778321530837867140875334160780144002515966975341786883333818247196082802613081629506395319493310742002346109956742369489949862588660028540886542698, 207895807184241617502467807402034427294808208378917538859506605195193766861187459024215707805656295648317393070214872991303268295501140121588921808181981650, 219898470877780461123844491736262263027503100483276762073958146399251797583224904181161631307672041890949726357109213800780320783213249018541178493811815845, 231238578262662209716983405272952549461188705418265050833089020786727860170627760712068845747755454636504447014131579503659495677431066844631671867531159791, 241965654103180762467302036076366449714306256857602733944922087400690372636427383452931175711693150725098331363049227372643151606148533897785946806271036821, 252123195202270212982464907668177524874420936760094511580445800037788917018340935492484356776041037115323056178911084482976616034781288558585652170956664591, 261749734285099906718170912155258168921461165285797467919426577952957476549365670462442662325328459043570989012986765320822321874485731714714364971479484677, 270879661175948353299180962371897152094973693834892778614878198257960553744278766419982307351886987109311073165815870920453774391994622479413758120244123075, 279543867868987020493871289738522214468489290124804257817770071031066665914786319410654273567502397342426879713335714220267106198823874388465183260044799570, 287770263073839731819216017075668188342411541240762930498628034793982032461993997108820754555308174627545553699383748415509097768188705543581067782361008627, 295584188204020931401407768298518089328713995486656375061768531886113045877414315919331483292602010502388679638686523458498880645426487517712769322651920075, 303008757716328007211254968003632883295224270355744115933390611424527113665439616620092886820375585868938202261202346340282561400114525837646422128694084875, 310065140532329523493404187301697394129962390417419448993592270408968232975051191056786722257767188934578239411968836355803011001368065038926098601637324722, 316772794970748090730573946692299962111190028649502401572709873996876001155510533716690217675826074353723185713894438905959381435723062076344201815057196030, 323149666565040801472160479416483572909029690781150024646349422743266330662292431373023452972590462209194299977407701120350212368514981499103586529166148188, 329212355934313641530440591098371414654852596486992868176524424174346979484047926805060632457326836443285687592759336590827605533434258779339185126687107969, 334976262257315259795153619640126751191577881224816113342591833936844351977468262209451447186170534183122285765297433320127136467668093747698611540004406132, 340455706695174623383433772357521184054035522492015783441868127370746408718734466873041912501017107213845501126952170750924115943345729805250945311472478013, 345664039201109393530067021106728184688605432760169412780056061397946996521199977963267681818939467591312578336303786082241802794912564764152521198334800975, 350613731463346851107173830586029523700666344139681715988852196037186481258896629454893776077107356610814608907126927097292556088823988915529966679278364599, 355316458194063712340016777271368934589815691243648917368599491840965767807908305145700158627601852492058056496083713384673841506605078437884799837828829348, 359783168561807852095620553973429270718555664527521791299463455639284091280744648040348032501243932532381282016306536325469179695608490278809206062493625503, 364024149238466284283189691677165230639258619269216937762199848761197641757965455159899833874446091718110479303067936754808108120901100980225541268824451615, 368049080273132025528104167849921678229980388778362499919062768019377445174993229616237186317381925055658603383569454929422623991413928952177812007560094177, 371867084798517272598837125936041837754134534473989429303280833804052277198365395040917142467483087427108895699437380263286861878639591666211947789615446790, 375486773409172580068961478871052736958905599319151090598496616133798417439344413117183047482366437439863822584474973731305664873217871196947309376865309200, 378916283915901595934152512319751264381840199493261971025612650581497980472195065824779551548474804384544413532159006895955497420699463657652948053633086665, 382163317070722472746006981301010453625489258038323306064907456736660678179876566439508984043013870982379780877306791406370179132045268371085208817063024509, 385235168766396563576195104750612249111146090493570305103104424500402976241168529387856160848823130214135227608667540081758418260543928910459812108865225325, 388138759139963979375707436010023678278080714996286104154463856094785611827729331014334021298343535779552178006402729808757973878052193838340089470972601884, 390880658947812508272171491767838733802741866358305687974099364019864924762295115053074724543386029245236103162574132587895404181048346892077275708289807573, 393467113528145179744031461080337545268968946644214071371983336379473605900164716194838518815310157862457698863000297909470617061308421460133249295266771696, 395904064623395178398800400486172198191439212581546018730842021522166186687011146078807988042536588779546052387566970515985384330184964398884783388777324722, 398197170298649699588002470301254767207385244286149009492866276532159164581421384479050857451952625768920177196118582303240828469500305249458822246360459100, 400351823161275668611862885605867708401404419835841975411702658265373474885852696933715874061277593331577045745632570705791892639132344287627818411883866777, 402373167060716518417334173098265369207398404235171388470736932343562227204405040904552862071559437728514374435423548517611731343270513738327237757502226077, 404266112425063600976162816644798470340706606936945286248881361028015520828865473602251604287856317915244878125717107210590792923908627417413017113903389148, 406035350371859025377841352783508907712672275377884354829656205171960409278564422088632324402979012573615280682348308637803940339260323346300033399159350903, 407685365714136824760276742211662841389473653009374932461511289250725095915209138873834616222482812292919336060881635935354959501184224162642785387613580892, 409220448968528191110966209775604590404019607969614691519949704154885606138400626132995835945573713725298595257136238420845991078289481009092669253086279637, 410644707459991271036979825666391432370821884739885737072092651823697345478210580581193321119964445807675243427521574146650030764009167428403253147603588335, 411962075607084718918597258673175432065726034118668488687513582791861768794781466470195464172582420229115659483838037429855938962145320721100339619659504472, 413176324462444246628584791817453245989009583305299282617713086060703403499755187996504924128833742374722520629557318748316890510840057588302233240151701008, 414291070575040403012294116553146234272411088490950619004488432161154843941949431593628077394987947205591353076337862990946406283588138231284308556018912625, 415309784233724291011181637764375326284059772788824873225629654445453956960558778124104188490926560060652970025342617451367506392912186544972876520837050868, 416235797145363466438408263954216027380003161587664490074827041459618123768381042514171831867419784158050164798324062408345887087624322519129995440895799834, 417072309595412759336706792113109743973494702209145333781094625924191364993125410081795454078092149485562354850559475783165589798754241482130577031063377918, 417822397133952599852755311130450337272012787156923649198179652622268351172232315042176137729060392036254821559969779683054991769702102122180361838885196894, 418489016825974363024560693277978981592843908727849667370037697299799157905816915290608076715236491603851341467878433237373823276670232391710638338279859393, 419075013100924833908701480826893507632800217473154416338966836893277467410416229447322602212314306487468868185725070315706341976448383376434682654198324602, 419583123233177425411440218083738268895583066004556838639607106785571249532146465410913194954405371619285549081823391261704132481050227414516656757217581828, 420015982482122552022192720427427672661916266086597062406415834703675922528829476723139027423732144414313810360642042946665871583238064131825590722882053117, 420376128917917455866234377566915619319765619237345149845012931843887354475063763201640016749820563232293303043358303763387064571981944471993264892902928017, 420666007956567089201409069968788516343354041229818114664473480660116532209338828914243200879782438809142243694088865601962310624923793949116251710367865661, 420887976625888102919030528581304687272342173998492027472579212276124121572838664607610275381554849016610018482046585555406189918638880880846257763770454447, 421044307582007912016025969479202810010306691511434454817972360845533830003448348345922846510988248535940285647722378651085493772003982646735031418246151008, 421137192894344476835511723137986714593865512607624023088430089071386719759332707806128865083785954445540418589203453500543915635958338570924008433827514083, 421168747615477482839675513401931142024700146381993360947667171398830221977871726706397692492574079802616760361012124715073770843268559303232278439607346629]
def MiP : List ℤ := raw_ints% [1121763465607409488174010802293126117802704769969554815152501800022757551, 683176186409461575464732725973774284614116203874193697035239327053782272, 493646939926165612032744696199800343660888315547263913012883604849950482, 390759350663220301122544106368441802662569173962174103669248515119945000, 325885681106247456854513746363922238759860897447017747597002379600611339, 280835962195223730571580429284227001525526295183629269502370868741659227, 247461031609645290648323289006548728615612801369983097091104125714070709, 221580436114695976021106480279163125829421488660551680840957288899137399, 200823625475826156165571384896430518762865405308577993292847666483940531, 183741132981572802838030160903459906285481281538060325869708582733913038, 169393562742612225322549708742863514492428654931885478546322691335682333, 157143347289248814008705764138850970300328373198826152878265639611471709, 146541281121803428325527981379102391852314575502060515609198387793172365, 137260941329916268419274108240818220352697908160677326495081516503987868, 129058895744600575187917722547881819338647630675927608376677784134902244, 121749553035851577983089517182200075382941177245789060321752896962833204, 115188706110510625499079509456907946136919398849404586086556607284514291, 109262437731295566507329677868720730066174013550739419681337860308587077, 103879444575473468369370638316340584989646405780543265108175919052913782, 98965604200580626375082520349461835338120942341234701214932238989319995, 94460051388423056848575390190096391730559636253760616967731560942609066, 90312293319360931081920892611650814685664161180033355505274279731802995, 86480054214280754448594814430772224950582525600905860273840632338847186, 82927641527237767304283641017083053774880367048618090583879560986481214, 79624691154647957283008454734120611007161611976765787288846969307659884, 76545192180585953129841765030002453264734595235040788866802030136597929, 73666720584803571954672580911683711468356155716144481356085277616073192, 70969831095833333226594207719418849019007193049953374621324789194447626, 68437570093734979990212982789638080316509742695946920257119081597552125, 66055082141326749662062883111669806456262302807377218291437907752395613, 63809289637419478664858515336389167109757650353812338737509600501640425, 61688630090900990868689350338751118147491000607505496792981328959490993, 59682839180584703109096720140964473876423033203924084073641078095409661, 57782770480401087468482307252870571280476007112105409855284493487397456, 55980244760267980374249420671959296098706680382219610209822047476711156, 54267923306657781803363834663183557721932875129614914220086569116029355, 52639200875531728815025228151903675468144364136485537169734953952295114, 51088114788296723520709380578896998804495645652178252225528600115808058, 49609267376896779772979599389923572243914307116711815402738761270622240, 48197759526763074455152251284018161132968713600912313292138946531262019, 46849133492676291949489784936667185828935183745041612228506925092126253, 45559323499782997004670838171094092922749517661416401767856622363182825, 44324612910366527395714404914043011117709698289147594946752144469231425, 43141596951822741272907012762307672771755815272718439602333818758946701, 42007150174272341066041781713874079354515770607046894368145336287100764, 40918397946260775619281351973592373113722151758458756554064110639734155, 39872691410913646604472564537426100927548507110985952260897657044996059, 38867585418046991738232158903491107429372644762124160528334898713646191, 37900819024223649770004097790436421435656639717414869671358022910751902, 36970298215850475431538378223373879558334759806008339131635519300758211, 36074080562690291034645176400041899037059038059436540135504733750123342, 35210361552649426255698586265613098774849886046689967184386439539212367, 34377462395015549578793831526989705776781803578181757176195560922477868, 33573819109757254717687022599947732330631556700963876338443990093703925, 32797972746098760168865023067988818742699000099507695370689897760146648, 32048560595191946696582173332935510793205782989087424258184477806229620, 31324308280006657445984874184994177541954990506604073836494242287765531, 30624022621104884804990921818903921499395012422089820589847259915880464, 29946585190209921141112124628661041185354680049742654667754616980543602, 29290946474800994033947929129580252907608512810165496549069001452497602, 28656120586664786313452935368659233193609757605656643387109922087827951, 28041180455671695998969336372146720970840268653914205006149495961974804, 27445253457227505670834669296812178560494650741630125043887637361808506, 26867517428055701118033351815896626299142382298383534974719704263544856, 26307197030338414031993125059027696950934374742569721284337864525101189, 25763560428907446850094177143500621034704538343533041243506336818015440, 25235916250234007333438262564338335948186287596711344087502958588429616]
def MeP : List ℤ := raw_ints% [1, 4896116775975550780284589642611307636488298976169072660, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def ViP : List ℤ := raw_ints% [10967745922124136676963595383, -17688669268547561386519296037, -688138684756238841648691341, -3470318987308317296197652421, -5242719191452692897886504718, -858104929881605307540431424, -4072876171369846790422507970, -1404418690373068221379089243, -1656566208532015283936639911, -2106058475954330825175572184, -281655983150203811026712393, -1576636231753337209287658699, -287567271395621032635564908, -348168433801639071653381508, -604659473386509320796589753, 428563351283590852678007099, -349462977349812676539296107, 390557362719613588674319280, 324871788409123252097554211, 99767052559044684450316908, 733112159882532627010354682, 151663525954084957762107978, 596398432175168303018808958, 497291189799868258282801352, 272863996655346910736155995, 676004172067168523897549800, 196994447230635528919056764, 473848998382243907139829782, 357682087126131103254311772, 144382676761679098921311436, 419631265904607222053833482, 21094515774209613534650980, 212170494216233149302178021, 105996185487800032690311159, -75966123787055620915380255, 138454566128913595352253529, -181703315700181339510115803, -24238896926497167293615637, -100286269532472792463663052, -237492552607758330016041471, -44689238145067304972180145, -289947872896283835156847012, -139286786224128725910058538, -179228554237468841494279980, -271983006322873886777400062, -86328520427570337235945384, -270186610612342595939719059, -121307882390560188635171797, -133520673829869918754506217, -194149224425702850967512455, -17817501212962793643800798, -160461470940978059137291572, -20631259459216086292536893, -21021582672260362556701009, -67465039870827234085119234, 89356706984712153613724564, -33716783701633222592885908, 86115288065100806169254203, 82138246657508276725001096, 34932637036716917158136852, 164731521577482955413894045, 46709091088169269000761067, 141010972239013442346766336, 125383763696423724791220381]
def VeP : List ℤ := raw_ints% [439098938838, 1756395755349, 3951890449534, 7025583021394, 10977473470928, 15807561798136, 21515848003018, 28102332085575, 35567014045805, 43909893883710, 53130971599289, 63230247192542, 74207720663469, 86063392012070, 98797261238346, 112409328342296, 126899593323920, 142268056183218, 158514716920190, 175639575534837, 193642632027157, 212523886397152, 232283338644821, 252920988770164, 274436836773182, 296830882653873, 320103126412239, 344253568048278, 369282207561992, 395189044953381, 421974080222443, 449637313369180, 478178744393591, 507598373295675, 537896200075435, 569072224732868, 601126447267975, 634058867680757, 667869485971213, 702558302139343, 738125316185147, 774570528108625, 811893937909778, 850095545588605, 889175351145106, 929133354579281, 969969555891130, 1011683955080653, 1054276552147851, 1097747347092723, 1142096339915269, 1187323530615489, 1233428919193383, 1280412505648952, 1328274289982195, 1377014272193112, 1426632452281703, 1477128830247973, 1528503406091940, 1580756179813713, 1633887151413928, 1687896320896299, 1742783688282460, 1798549253698505]
def cNP : List ℤ := raw_ints% [-334709043033573506987414, 269907673165093404945668, 7000108690961088477058, 26476432703463114137250, 31999018502518877550577, 4364547372851589495547, 17756330964747169670857, 5357432137958786855236, 5617154298678979776803, 6427180407575472488939, 781405315469093492062, 4009593281436506167825, 675065897769918665104, 758946955657172223017, 1230182847872943767897, -817419722144300179821, 627339041945177282965, -662159157171653897899, -521805272809678332034, -152232441038581366654, -1065371791123937155602, -210381977364397857336, -791331989023183146626, -632338447316320111952, -333085933417171521895, -793461928226375314446, -222659016057485542488, -516454422413683108891, -376399690958095264571, -146873653932372130250, -413100965836661280531, -20117297910890210662, -196209988880719872032, -95139613869880256824, 66237203357854022143, -117369389961169429654, 149868787363562786626, 19466116595215781197, 78474206803129376114, 181192438207823432935, 33263593083873696655, 210678734840235999085, 98853380938954003559, 124309577413017163013, 184450280980681618094, 57272551447044264577, 175434914844491899167, 77125474542338173316, 83157706018483636820, 118499282486390900249, 10661705593311261132, 94171066836417599685, 11879548535165512541, 11880144287256516383, 37433993181167454992, -48695540828547970153, 18051834749795062466, -45310862608337826522, -42485768803746253437, -17767657998004616881, -82413230809687857913, -22991102200499144032, -68306561298195220631, -59787637565814840694]
def fP : List ℤ := raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def gP : GasLit where
  P := 256
  T := 999997120790
  Q := 256
  Qm := 240
  Qv := 96
  W := 80
  N := 64
  Ln := 427
  Sg := 473244352085428890469631042005039278801145966237480161413251677837181121672026885
  LIv := 283904694028599334108302234421134026001164996929168315281217545808488867749014
  LEIv := 320871909030333695936730866818174657264897161702216345811401
  L := gdOf gdP
  R := RP
  Mi := MiP
  Me := MeP
  v0 := 50301613494123125310883779867
  e0 := 1
  Vi := ViP
  Ve := VeP
  G2v := 20811099275410466085108746707557842276948584876412589987479386804866956378877
  Bq := (79837491800816330374820032128692674719198011 / 730750818665451459101842416358141509827966271488 : ℚ)
  Tb := (2873152135 / 1099511627776 : ℚ)
  cN := cNP
  f := fP
def gdN : List ℤ := raw_ints% [2000000000000, 2000000000001, 329291, 115792089237316195423570985008687907853269984665640564039457584007913129639936, 115791973445284854137520208380751064855617268643195079412089068500740624389400, 6, 2000000000001, 2000000000002, 375636, 115791973445284854137520208380751064855617268643195079412089068500740624389400, 115791925482688972543614380347981446405965672015781244530264618748219112043480, 12, 2000000000002, 2000000000005, 409024, 115791925482688972543614380347981446405965672015781244530264618748219112043480, 115791830318622884124048774629459216780003948652006028859008016488999497432659, 23, 2000000000005, 2000000000011, 452954, 115791830318622884124048774629459216780003948652006028859008016488999497432659, 115791705199039359858744863812948241321826138534267888062901967395728021501795, 42, 2000000000011, 2000000000022, 512356, 115791705199039359858744863812948241321826138534267888062901967395728021501795, 115791546125549685322818259003035951062397035162850363214197953148310305624924, 72, 2000000000022, 2000000000045, 595490, 115791546125549685322818259003035951062397035162850363214197953148310305624924, 115791312482973138979779354944080359677529638708854251509688939382966837080004, 122, 2000000000045, 2000000000094, 716993, 115791312482973138979779354944080359677529638708854251509688939382966837080004, 115790966596801122642995559115354765421969838576759021677014362954309050507069, 212, 2000000000094, 2000000000195, 904326, 115790966596801122642995559115354765421969838576759021677014362954309050507069, 115790472300076605313638365668522643236508159120155505941494413832493483527834, 366, 2000000000195, 2000000000403, 1212377, 115790472300076605313638365668522643236508159120155505941494413832493483527834, 115789764750679230234440499450732541842692793345071395878741194540678085655752, 632, 2000000000403, 2000000000834, 1756879, 115789764750679230234440499450732541842692793345071395878741194540678085655752, 115788745319122013984334044963323718070864428454286428164516406515313088160159, 1090, 2000000000834, 2000000001727, 2780968, 115788745319122013984334044963323718070864428454286428164516406515313088160159, 115787277343505389990656282157648903529071733031475388412593154413262883401619, 1881, 2000000001727, 2000000003574, 4681056, 115787277343505389990656282157648903529071733031475388412593154413262883401619, 115785167052627942223993223238345148823140842478816687710163948535366176315656, 3245, 2000000003574, 2000000007398, 7219921, 115785167052627942223993223238345148823140842478816687710163948535366176315656, 115782130199618883206042657512107371701628374807731825590394346613091557491408, 5600, 2000000007398, 2000000015314, 10377967, 115782130199618883206042657512107371701628374807731825590394346613091557491408, 115777760882106131492689338715202110857992125743447598131784764900860467842730, 9664, 2000000015314, 2000000031700, 15173656, 115777760882106131492689338715202110857992125743447598131784764900860467842730, 115771474877172873196989404627109112302897679443998741234365399000075979675471, 16678, 2000000031700, 2000000065623, 21848110, 115771474877172873196989404627109112302897679443998741234365399000075979675471, 115762430592456931873321728142538432979140703427451605649004256277169584640694, 28784, 2000000065623, 2000000135851, 31522205, 115762430592456931873321728142538432979140703427451605649004256277169584640694, 115749418487567752294161822598982653334584623721067202653833218503920457929644, 49678, 2000000135851, 2000000281248, 45372795, 115749418487567752294161822598982653334584623721067202653833218503920457929644, 115730697708013546809592788872245293649154598254316349371831809541722850501901, 85743, 2000000281248, 2000000582302, 65305858, 115730697708013546809592788872245293649154598254316349371831809541722850501901, 115703763488384457662877610678722354301028560578627942522087060210706001244365, 148000, 2000000582302, 2000001205732, 93980885, 115703763488384457662877610678722354301028560578627942522087060210706001244365, 115665012562197683200060606519436843665852769808363222990090670347321748424565, 255484, 2000001205732, 2000002496994, 135193048, 115665012562197683200060606519436843665852769808363222990090670347321748424565, 115609260480600166363918176807861044326470393018416789172459753634159513954863, 441088, 2000002496994, 2000005172208, 194828728, 115609260480600166363918176807861044326470393018416789172459753634159513954863, 115529048487374376074846062460234359104418423662143311603074570344676607070798, 761679, 2000005172208, 2000010716850, 278329372, 115529048487374376074846062460234359104418423662143311603074570344676607070798, 115413645258278359346603149824482591281543847909534797857079843811065311372202, 1315651, 2000010716850, 2000019296467, 308500254, 115413645258278359346603149824482591281543847909534797857079843811065311372202, 115284556673286078219608670237913903143593913562772470587049144033852291900628, 2104908, 2000019296467, 2000022215164, 95304449, 115284556673286078219608670237913903143593913562772470587049144033852291900628, 115247611441722948123656477138943028752632944128701159024010088588971263953525, 2646941, 2000022215164, 2000046079500, 577384393, 115247611441722948123656477138943028752632944128701159024010088588971263953525, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 3930858, 2000046079500, 2000077526822, 552075950, 115008734028686139352127222438899187000086808861650697624855682582757395061057, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 6072503, 2000077526822, 2000095667547, 280633078, 114777026417937971014428971607735073176154159555973527720077552538212314736007, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 7745186, 2000095667547, 2000175209840, 956274670, 114665054492048574822219541531012136634171933205715914222258972215270201475226, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 10992149, 2000175209840, 2000198883427, 238146634, 114269496170919912096362432789765082673109058089510072180028136263009233331916, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 13796758, 2000198883427, 2000312873558, 994039847, 114170593276054393708912947917757119219440141528309136496309818764588905879557, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 17613074, 2000312873558, 2000414257402, 730130302, 113761965918400596954418294936052550722037464888177521869361525937236534166249, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 22809805, 2000414257402, 2000491055474, 509005479, 113459198284848303314083651389717967999393766355328884534849366144178958560689, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 26837805, 2000491055474, 2000710302767, 1244802039, 113254435668470541458596901977881205511720873398075302694990273524330975537136, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 33375104, 2000710302767, 2000865292450, 756580922, 112746905417847545120316069951020610505157382782941423644142749830340099726817, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 40756507, 2000865292450, 2000971172512, 490174344, 112435694697162144818640978889126107792849853485636705575729632904400340058916, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 45690063, 2000971172512, 2001274231906, 1260040360, 112239375167044973082687456083900777193093398278003360686049163365085971273497, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 53322429, 2001274231906, 2001620058499, 1255901335, 111731844916036636712362275417455485049816325674669628506398799310327144410751, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 64532944, 2001620058499, 2001814869793, 645911784, 111224314664476077953530691978762877648340561402833138840144777447402436588811, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 73285726, 2001814869793, 2002009240430, 620495292, 110963151862345428815978365573306388448810506198702852209039296025815752701910, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 79466587, 2002009240430, 2002442376672, 1275212990, 110716784413456498685168971258198458757635654221282663253859301944406972175951, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 89258669, 2002442376672, 2002920077285, 1277345235, 110209254163526918400467275577077500476415877354186299824615933069465136065437, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 102726420, 2002920077285, 2003442963668, 1281563144, 109701723912500484745642487148776035922656874971544454313159071720270423752953, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 116906567, 2003442963668, 2003829787234, 883838690, 109194193661798552142430657403347965986327165728565957960339130279825959188343, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 129264038, 2003829787234, 2004011668828, 404426934, 108844563883114627328357206513227585724017038293519532489473481965805601242920, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 136795313, 2004011668828, 2004626837653, 1297464805, 108686663411482188769017755162135810745859024175680135377220981172854922206572, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 147350692, 2004626837653, 2005289127186, 1300127234, 108179133160158920690860847044507911922456635364206870025895361149508458149584, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 163593960, 2005289127186, 2005999206922, 1306326742, 107671602909904158351717534769826516213540715636056913003433164307203044657300, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 180507422, 2005999206922, 2006757759095, 1312030739, 107164072658867370465528345084506765795905853002316149220344942758837848730026, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 198085087, 2006757759095, 2007565478990, 1317831748, 106656542408408974468973223205686075474953028250585145984816049445215638655039, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 216322278, 2007565478990, 2008423075252, 1323641180, 106149012157678007603540132309545486090063418208828408951615116460554189815166, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 235215467, 2008423075252, 2009331270210, 1329472444, 105641481906776275604493216510132466517291392356932567371277597034182613049188, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 254762143, 2009331270210, 2010290800207, 1335324079, 105133951655693115071659805547209131246348300121487697431811001197546604365733, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 274960700, 2010290800207, 2011302415947, 1341196799, 104626421405309192076133491695287957160221810718003314933143354516652722103838, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 295810351, 2011302415947, 2012366882840, 1347090903, 104118891154530808707845150921528718409420204372159439619436090796727638218026, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 317311053, 2012366882840, 2013484981369, 1353006686, 103611360903853762728092702148783436845102178938782162020106983234228760632441, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 339463445, 2013484981369, 2014657507458, 1358944358, 103103830652791224644633553023834170906713584062759008474462178132339238027498, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 362268794, 2014657507458, 2015885272861, 1364904081, 102596300402112765622285726707524040036725167004651090215623084099156950752751, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 385728957, 2015885272861, 2017169105555, 1370885977, 102088770151503761445189644652752889974572520769070123090989134380643029943111, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 409846335, 2017169105555, 2018509850146, 1376890123, 101581239900721590405546837052849105222252504840794734506386903407128883362322, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 434623851, 2018509850146, 2019908368292, 1382916576, 101073709650068361127701277556869072799946661525850806955573923875251283560304, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 460064918, 2019908368292, 2021365539130, 1388965354, 100566179399088534223053194477135827892333465136428994371033198113648309338424, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 486173416, 2021365539130, 2022882259729, 1395036472, 100058649148566538879611000728350549624379482181888662350147802572474030632539, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 512953677, 2022882259729, 2024459445544, 1401129897, 99551118897875063987180147255080340910191822413768147998542169761228225989745, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 540410466, 2024459445544, 2026098030889, 1407245609, 99043588646925407760701466927026862341657864488577286626427084174548939687980, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 568548967, 2026098030889, 2027798969430, 1413383552, 98536058396235534432442241222262106883483229817304345789243163847819692734183, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 597374775, 2027798969430, 2029563234684, 1419543666, 98028528145429276058146287785331057745311752883958497321109133082816898855157, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 626893882, 2029563234684, 2031391820540, 1425725875, 97520997894662973701130794483762686731340646242838606427083979827943205109711, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 657112676, 2031391820540, 2033285741796, 1431930094, 97013467644071505402788443522497521670149067613428124723835485286064788229079, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 688037928, 2033285741796, 2035246034710, 1438156225, 96505937393425455661077254725504330263843191173394169712605211111136731239891, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 719676793, 2035246034710, 2037273757570, 1444404161, 95998407142619212956893733771015647766137821007029345743187049239879536436992, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 752036805, 2037273757570, 2039369991282, 1450673784, 95490876891726824244903755093386203895286925392023569878036369481421559949959, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 785125874, 2039369991282, 2041535839982, 1456964968, 94983346641113745604145456371289984142327856666340779176299217153384889058530, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 818952287, 2041535839982, 2043772431658, 1463277581, 94475816390366393200967057792503167747829321374857035583159767688415615053963, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 853524706, 2043772431658, 2046080918800, 1469611473, 93968286139585080689009749778641701506612547526069326507789442116865847415587, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 888852171, 2046080918800, 2048462479068, 1475966498, 93460755888805977092172438706356244232014522063148453870942162054893527682350, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 924944102, 2048462479068, 2050918315986, 1482342490, 92953225638200409885237165124541227117947904313540833894911857835741864284819, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 961810298, 2050918315986, 2053449659651, 1488739283, 92445695387431396822335894859752718051334279270756745660129614625935517377384, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 999460945, 2053449659651, 2056057767474, 1495156698, 91938165136681090074740507924876796171272099369944824164386910113277139703565, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 1037906619, 2056057767474, 2058743924941, 1501594550, 91430634885924403849286278329927326232632208161183049023316418510689747062704, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 1077158288, 2058743924941, 2061509446402, 1508052640, 90923104635200678031902281270359152929564091489081568521561088103225324948425, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 1117227322, 2061509446402, 2064355675884, 1514530774, 90415574384419560197501607323869329390334252370301222617894122955597460874089, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 1158125497, 2064355675884, 2067283987935, 1521028734, 89908044133671944253509892878211741116661383937902848484688632137309141050524, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 1199865001, 2067283987935, 2070295788495, 1527546302, 89400513882934284366689109909568175654668502389957636941466358121391175100673, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 1242458443, 2070295788495, 2073392515795, 1534083250, 88892983632129408362262930575038545488072500074298227583135359429238492302156, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 1285918862, 2073392515795, 2076575641295, 1540639342, 88385453381504421115759885270926112305233582972723629360138013968946504068012, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 1330259733, 2076575641295, 2079846670642, 1547214333, 87877923130725949793492609161161775927010502585804951807351251138148403723074, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 1375494981, 2079846670642, 2083207144675, 1553807965, 87370392880032121197562914655469190519134532463673375906511043486291432975749, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 1421638985, 2083207144675, 2086658640454, 1560419973, 86862862629242910928564417792020477427189268700670745238688738068381431547907, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 1468706596, 2086658640454, 2090202772336, 1567050091, 86355332378551129212811178029802759264921278615693966302625767660853123323451, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 1516713142, 2090202772336, 2093841193078, 1573698043, 85847802127734235318643474849013892506231683552224736549945631964368442560878, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 1565674445, 2093841193078, 2097575594992, 1580363523, 85340271877028856414749960859298715151240418211100827130240053076889694927562, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 1615606830, 2097575594992, 2101407711130, 1587046235, 84832741626238044013391554233202256760478256670839868550382853389696421488374, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 1666527142, 2101407711130, 2105339316520, 1593745866, 84325211375473236954190419771655346933992878167491098548922721258740314192802, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 1718452757, 2105339316520, 2109372229446, 1600462096, 83817681124798235278309276349432133314231003860648267928975478617636269000334, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 1771401599, 2109372229446, 2113508312770, 1607194595, 83310150874059741901293611466333499635278273315105116669934954550831501526713, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 1825392157, 2113508312770, 2117749475310, 1613943017, 82802620623352035319069011493768483719161838505004309279921326266645114882028, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 1880443497, 2117749475310, 2122097673263, 1620707014, 82295090372593085841455006031921663369314111091197220509274122064035269491590, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 1936575284, 2122097673263, 2126554911687, 1627486222, 81787560121874219843446357722646076419728033521735462684678428582911934176625, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 1993807798, 2126554911687, 2131123246034, 1634280264, 81280029871132166205698898387884157084570454360314711051071563542650889709643, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 2052161953, 2131123246034, 2135804783745, 1641088755, 80772499620391100641856012111786720409532255852058285830691780813577831077775, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 2111659318, 2135804783745, 2140601685900, 1647911298, 80264969369567783299199408271989672817056070226803164323253026102562171367207, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 2172322136, 2140601685900, 2145516168944, 1654747484, 79757439118913802062694043332871333088869809027474702198296575883918860425344, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 2234173347, 2145516168944, 2150550506461, 1661596890, 79249908868125800447406891028047013763204922549560487470729250161224329101193, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 2297236613, 2150550506461, 2155707031036, 1668459087, 78742378617415800793501413804974780455721333987441382492380693619244943414131, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 2361536336, 2155707031036, 2160988136175, 1675333624, 78234848366628638334709617669320110898971246670067294404898797682623676824173, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 2427097690, 2160988136175, 2166396278310, 1682220040, 77727318115868800123724664057532510759255358272687201514628413931282023247855, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 2493946643, 2166396278310, 2171933978883, 1689117871, 77219787865203018719003846825067819850442385301125621459947753271949874756080, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 2562109984, 2171933978883, 2177603826505, 1696026621, 76712257614445928063477442809480003157587809252653832689651745405890837217640, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 2631615354, 2177603826505, 2183408479212, 1702945799, 76204727363699679772743397570493796920456525575969588419473474920677518773903, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 2702491275, 2183408479212, 2189350666807, 1709874886, 75697197112963415480053471023041771336739144625173921367047936408622246303269, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 2774767180, 2189350666807, 2195433193299, 1716813355, 75189666862233952965358044544181191436148475508340239193105913981819830704169, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 2848473448, 2195433193299, 2201658939440, 1723760662, 74682136611472721225902979959712055255360608554700206914325215367092243195620, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 2923641437, 2201658939440, 2208030865372, 1730716249, 74174606360747673574509672095401710931450652155382160962141332756286171534243, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 3000303520, 2208030865372, 2214552013376, 1737679545, 73667076109957764728763095142862509238035235555605707780630435751937273930554, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 3078493122, 2214552013376, 2221225510745, 1744649952, 73159545859212962167157518256011208889667634337803849419332071106539982042717, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 3158244761, 2221225510745, 2228054572775, 1751626871, 72652015608518377251110063396298983803359135933527709611212516152046091043809, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 3239594088, 2228054572775, 2235042505876, 1758609675, 72144485357728091820912002327007258892930148356886103554587376424345676040211, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 3322577930, 2235042505876, 2242192710831, 1765597725, 71636955107016483022002409205759200347605797046284801778399735830350085816004, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 3407234335, 2242192710831, 2249508686181, 1772590360, 71129424856266067663400133743847560376398961244999564886683135993021561735992, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 3493602620, 2249508686181, 2256994031765, 1779586906, 70621894605508242269439534298039612254832455951745469252352656883255494144818, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 3581723421, 2256994031765, 2264652452415, 1786586665, 70114364354788439781793100343237389307661014534211824724544511702863303518581, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 3671638743, 2264652452415, 2272487761808, 1793588922, 69606834104034857337354591289395976989627717029518359043479154125881483439315, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 3763392018, 2272487761808, 2280503886497, 1800592941, 69099303853313095563336906975690498280018599303473703131954980964075727687856, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 3857028158, 2280503886497, 2288704870114, 1807597979, 68591773602557679048506238103834413993599334818473453244899052632167152521790, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 3952593618, 2288704870114, 2297094877771, 1814603250, 68084243351835236036701552768782562978729207008169726283901513313931578064314, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 4050136457, 2297094877771, 2305678200651, 1821607952, 67576713101069556985876406849453941230875012994333414815254041056128382507730, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 4149706406, 2305678200651, 2314459260821, 1828611271, 67069182850365433002060758058466889036763207599558198716481289778998012356391, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 4251354935, 2314459260821, 2323442616254, 1835612360, 66561652599619970998310655354538339091473270161700819799038394187819752697310, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 4355135329, 2323442616254, 2332632966095, 1842610354, 66054122348888220336657016189777207252865050383721931368492460606350188491988, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 4461102762, 2332632966095, 2342035156166, 1849604359, 65546592098133030722816677125622215249408749991200710537164907172265246994599, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 4569314377, 2342035156166, 2351654184737, 1856593460, 65039061847400268052341006781466811368452812762950460219828480163870168968012, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 4679829375, 2351654184737, 2361495208566, 1863576715, 64531531596653947653489254705370631632809599725318754170432946404590289136147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 4792709098, 2361495208566, 2371563549232, 1870553147, 64024001345905573283511812788430051317106587089944123868485688958963009540766, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 4908017126, 2371563549232, 2381864699773, 1877521765, 63516471095161620999539272166134424568536448960419648292499168292625990087716, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 5025819378, 2381864699773, 2392404331648, 1884481535, 63008940844427652822806744722415772226418334267386800807368718527114231786784, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 5146184210, 2392404331648, 2403188302039, 1891431405, 62501410593684246112305854520808128169598879590888202685781988217261967854548, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 5269182528, 2403188302039, 2414222661519, 1898370283, 61993880342957083529526863666742747434370945094004150747884707707909634080354, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 5394887904, 2414222661519, 2425513662095, 1905297043, 61486350092182694096542424973888059745222828778267871540856496099642411278898, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 5523376696, 2425513662095, 2437067765666, 1912210536, 60978819841438103245558034643754978721576911170864437756622981810785903352594, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 5654728176, 2437067765666, 2448891652905, 1919109570, 60471289590717483480414032079675487125251549922405414867382942765960826804928, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 5789024666, 2448891652905, 2460992232592, 1925992917, 59963759339962519695384245032738223454126061944944904831720799338653484093429, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 5926351681, 2460992232592, 2473376651441, 1932859312, 59456229089252514638678896669314486285666888989825398117424267790016790767760, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 6066798080, 2473376651441, 2486052304424, 1939707453, 58948698838497049534013083774411225049879624692770975397327168943495483576213, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 6210456223, 2486052304424, 2499026845650, 1946535991, 58441168587750791502776320812641003296772495116022774026041758188703485670694, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 6357422143, 2499026845650, 2512308199817, 1953343541, 57933638337024401633249333376375104505436665185893180799859691130435577016692, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 6507795722, 2512308199817, 2525904574270, 1960128668, 57426108086258377885987157725533856149499693037643465061372067845335859972470, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 6661680882, 2525904574270, 2539824471725, 1966889891, 56918577835546102230065778905985889255015731030731002983827719582872148460703, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 6819185778, 2539824471725, 2554076703668, 1973625679, 56411047584794131054193616968311875430438848769473806957850594199707785450601, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 6980423019, 2554076703668, 2568670404505, 1980334473, 55903517334048639945355762429836228009878530892518370527107495218346726522566, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 7145509884, 2568670404505, 2583615046489, 1987014616, 55395987083297742487497930917346966028293113122743642295933385369285224439713, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 7314568564, 2583615046489, 2598920455487, 1993664422, 54888456832560189298861168099822237630875149790264659656258419692297813466423, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 7487726412, 2598920455487, 2614596827637, 2000282145, 54380926581831228734964376132126117968672040585668366586711147731106968974594, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 7665116209, 2614596827637, 2630654746951, 2006865970, 53873396331072305120231851667217007928996855180254859824916960557925226767739, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 7846876452, 2630654746951, 2647105203942, 2013414028, 53365866080341867495463526293723847971332353886712541730164474973397060387471, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 8033151652, 2647105203942, 2663959615326, 2019924365, 52858335829613513841144855508614349390246316191824657901851568627211315033636, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 8224092657, 2663959615326, 2681229844882, 2026394970, 52350805578862843595118768995760637098192681865071927719404684825632780181100, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 8419856989, 2681229844882, 2698928225555, 2032823752, 51843275328125527571993308910182252095439527234457026605724953502090446041137, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 8620609214, 2698928225555, 2717067582878, 2039208531, 51335745077391452415950336986372330035257321933456299167454432741636396995871, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 8826521322, 2717067582878, 2735661259813, 2045547053, 50828214826652158504463149671367264658453276846678494072610833151367035958661, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 9037773140, 2735661259813, 2754723143110, 2051836970, 50320684575900972908021555187894564420838564573862669054972982074475482469830, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 9254552777, 2754723143110, 2774267691295, 2058075841, 49813154325148427078012526178698460703082247076305335053180261543143799005731, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 9477057085, 2774267691295, 2794309964405, 2064261118, 49305624074409821343448354078609443341230933541774463521307757912346743419141, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 9705492163, 2794309964405, 2814865655598, 2070390161, 48798093823682690847548382771126718340467553427005568082756581977013335152474, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 9940073892, 2814865655598, 2835951124772, 2076460202, 48290563572928103252073001030888822551010173857428410501312219743157984295193, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 10181028505, 2835951124772, 2857583434359, 2082468359, 47783033322184034364409669126001865321309805950135397407275219088501751802251, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 10428593201, 2857583434359, 2879780387444, 2088411625, 47275503071449133113726552680585634790410964172180554341967575260859734646800, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 10683016794, 2879780387444, 2902560568391, 2094286858, 46767972820703864892583711260372678152190079848951108221120839711340407371104, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 10944560420, 2902560568391, 2925943386182, 2100090765, 46260442569979513638850712840262522151449454081788512506980775028803704297628, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 11213498285, 2925943386182, 2949949120659, 2105819903, 45752912319227129635128264356333376252594584523871113781711752488587922130294, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 11490118475, 2949949120659, 2974598971928, 2111470676, 45245382068487649749673119934054194704160461902666199468254865199333195435060, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 11774723818, 2974598971928, 2999915113156, 2117039289, 44737851817753575203231093447167658380678377409067999347273888578771356226707, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 12067632815, 2999915113156, 3025920747045, 2122521777, 44230321567008683007282446943707293714929493881942546666613778047870222316680, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 12369180645, 3025920747045, 3052640166290, 2127913969, 43722791316267711659793227854645446060393075091181611398336570571954946458378, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 12679720238, 3052640166290, 3080098818344, 2133211479, 43215261065527428522294004501444032266972198226399814391592233095024503473503, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 12999623436, 3080098818344, 3108323374859, 2138409687, 42707730814791845245460419904985052856034541491937772554081147150528101482441, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 13329282245, 3108323374859, 3137341806196, 2143503732, 42200200564050213707269307990486791607201285709815755923161854116045005991401, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 13669110185, 3137341806196, 3167183461447, 2148488472, 41692670313306820055398378961423159654311748796221135068753457252087226272171, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 14019543747, 3167183461447, 3197879154446, 2153358497, 41185140062560799534064758976145606273097429043313561196070466690228232888589, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 14381043969, 3197879154446, 3229461256300, 2158108070, 40677609811813163621849035600838405359960403492841115560192716960859305808303, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 14754098144, 3229461256300, 3261963795027, 2162731125, 40170079561077200016052571917388006045007760273684205793831153354988101521371, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 15139221664, 3261963795027, 3295422562941, 2167221234, 39662549310345933951100562961331780615445203874955610055557878170825434224957, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 15536960027, 3295422562941, 3329875232493, 2171571588, 39155019059593925053807665285355410886495719103281721740907967573135771031636, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 15947891007, 3329875232493, 3365361481374, 2175774948, 38647488808855491870214545271170196567431942468559105460064196943386713706979, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 16372627015, 3365361481374, 3401923127728, 2179823598, 38139958558112326507153889433308627610233619895161420851722252714121854065861, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 16811817674, 3401923127728, 3439604276464, 2183709341, 37632428307372653088915706789375416375104211264422148633588308689130314626324, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 17266152607, 3439604276464, 3478451477733, 2187423431, 37124898056635203887641492112989149119661684963400832250749512674103369284719, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 17736364492, 3478451477733, 3518513898767, 2190956534, 36617367805890497396979748760029627823735518971077781218351463141569995702941, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 18223232385, 3518513898767, 3559843510423, 2194298668, 36109837555153679949579697715136727183928943555622550896431101518352019862164, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 18727585356, 3559843510423, 3602495289904, 2197439146, 35602307304408842192095389219966885451602132840382123936496305128092829011917, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 19250306463, 3602495289904, 3646527441337, 2200366510, 35094777053669755076018930257610238078103525206108507803020665400642418338396, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 19792337106, 3646527441337, 3692001636057, 2203068455, 34587246802935381810555394535238615911056058298250191745962812447735301605735, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 20354681808, 3692001636057, 3738983274682, 2205531753, 34079716552190182166946806878549920018634986428193095053564175099104735183840, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 20938413450, 3738983274682, 3787541773333, 2207742150, 33572186301447813895841310052778097200646780007932443237826915818950582435738, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 21544679046, 3787541773333, 3837750876617, 2209684274, 33064656050703159919553045601403520614192787028386533312872234078511867744935, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 22174706087, 3837750876617, 3889689000358, 2211341512, 32557125799970380513998623597431276266049800636369668364968256428542764368126, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 22829809548, 3889689000358, 3943439607399, 2212695872, 32049595549220633614625365600305304251742786213251007069951947194279531582712, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 23511399619, 3943439607399, 3999091620303, 2213727873, 31542065298488482324182867500638699727176754279527871540754376644944018986262, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 24220990261, 3999091620303, 4056739875199, 2214416326, 31034535047747888650096513214444190345065525005409559876843142532974254058422, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 24960208685, 4056739875199, 4116485621680, 2214738167, 30527004797004503247968686314989062066935749746825171703615333742783794216289, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 25730805866, 4116485621680, 4178437074280, 2214668260, 30019474546263024984357341959756816009181773290432453949362747568151465087987, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 26534668238, 4178437074280, 4242710021848, 2214179135, 29511944295520843547533617342687914931428723217745094482309537407165988873946, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 27373830711, 4242710021848, 4309428502045, 2213240711, 29004414044783545597714819821124108108393408595359557873160083138159236746854, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 28250491190, 4309428502045, 4378725549217, 2211819984, 28496883794039842890800842946032480764032379793180779500119068094686092932719, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 29167026812, 4378725549217, 4450744025144, 2209880645, 27989353543295653064784092761374758062798028252925818476563360818219587614442, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 30126012114, 4450744025144, 4525637543577, 2207382672, 27481823292560292381289993677113638425483720612674289607466279132779500769056, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 31130239431, 4525637543577, 4603571501134, 2204281846, 26974293041813631821229489672048177463599083574748466689026852215089072399780, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 32182741822, 4603571501134, 4684724229148, 2200529158, 26466762791074897483651044330443252281895848531726230072109109021436477269793, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 33286818907, 4684724229148, 4769288283309, 2196070136, 25959232540331871433643992289380477561588032558049244605275010289720403270317, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 34446066041, 4769288283309, 4857471890760, 2190844113, 25451702289592981214759334876102796381869333901414473675700278958102461554473, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 35664407344, 4857471890760, 4949500577511, 2184783266, 24944172038850299166551591089910110610622937501775938159321617551889602742318, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 36946133169, 4949500577511, 5045619002969, 2177811556, 24436641788114291095584505582501420503727128292543235205689003469024338815478, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 38295942727, 5045619002969, 5146093032971, 2169843422, 23929111537372629437263940855342246757922284595533670588922370241455319961896, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 39718992700, 5146093032971, 5251212088326, 2160782239, 23421581286630258044769810408914707220858999591980467728741923649073188007528, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 41220952830, 5251212088326, 5361291812535, 2150518465, 22914051035889444818160627997760015701449816174402231214679276367261963076285, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 42808069669, 5361291812535, 5476677110468, 2138927252, 22406520785146155030294797847002483375766363747163388142020930300191513582980, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 44487239903, 5476677110468, 5597745619623, 2125866051, 21898990534408128226970578796219015569510400714787207881658546886814017485613, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 46266094949, 5597745619623, 5724911687529, 2111168249, 21391460283664901790727967914041083602908970612787642782595432069905409880306, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 48153098870, 5724911687529, 5858630943575, 2094656278, 20883930032925174615371492309322372007344414466033047196054744914703721161113, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 50157662093, 5858630943575, 5999405571524, 2076010459, 20376399782185529084889600312563905082438661697409072948778481544442678677085, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 52290273934, 5999405571524, 6147790411300, 2055579520, 19868869531444484057858747122268665885079198349899002239881089198682171933533, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 54562657635, 6147790411300, 6304400046307, 2028663952, 19361339280701796586503169259616765207598746701235794164145451259208342964800, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 56987952419, 6304400046307, 6410000000000, 1290320269, 18853809029960655290981553548900905390421098946860265050229008396145894880962, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 59085116079, 6410000000000, 6469917067130, 707905984, 18526734277970591267771357601390065256523197546502490246313213441266100742389, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 60420593962, 6469917067130, 6474122807018, 49533522, 18346278779219825533154782770845454529326805977345849816164982403051673271918, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 60939804547, 6474122807018, 6539645390071, 754653660, 18333747462573706123296661038319860998813092516874102629594785050510360736816, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 61511518444, 6539645390071, 6606612903226, 749387972, 18140760647179309983682089167826071917999612483627193442288782982677999797182, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 62596378178, 6606612903226, 6645101745895, 420777086, 17947773831783458603146185887135142408635954137994127424399554988936676130913, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 63461525740, 6645101745895, 6675072463768, 324368924, 17838748528479438313730650937234273181915184278841475914853082734478435757852, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 64025907442, 6675072463768, 6745073260073, 740931368, 17754787016388806538679890126759386043549763287206848069331640958427969506756, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 64855925902, 6745073260073, 6816666666667, 734388701, 17561800200993665330905079169789340341764315211563423591290849120007189445397, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 66032946220, 6816666666667, 6830803410465, 142237830, 17368813385596540883183443325705570835796119208083134742538922578657040505622, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 66745106924, 6830803410465, 6889906367041, 587683093, 17331218277738707196189657117800002071510038933843067431880700724358809945120, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 67360304431, 6889906367041, 6964848484848, 723879374, 17175826570202419431702550816764361339317404463347467500493673633706447003543, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 68487758404, 6964848484848, 7027973877427, 591715279, 16982839754807609546795847736110456535821787385057303209001349740685803819378, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 69652085879, 7027973877427, 7041551724138, 125821355, 16823688026999047574588478088516175555985927902263294996143467803052663434835, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 70299464815, 7041551724138, 7120077519380, 712085131, 16789852939410676832008186751813017292944024762985652943380302031610427893198, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 71086072098, 7120077519380, 7200490196078, 704063564, 16596866124014944788677135245824486049741822517229130549561151799172173364950, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 72442741703, 7200490196078, 7237683392161, 317229117, 16403879308620817341807315357583251209279057813988082282418932040238243483797, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 73447933363, 7237683392161, 7282857142857, 380625355, 16316157776257732296125933685228282499572449242874453803915162465358010467636, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 74157088883, 7282857142857, 7367248995984, 691028669, 16210892493224598058861203193029243736374708765941510744798291339494507244377, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 75279208848, 7367248995984, 7453739837398, 682019207, 16017905677828595207761592522639578600208426593989399208345612529154575191581, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 76762514263, 7453739837398, 7461139639404, 57197760, 15824918862434037598411031141574270834543636256092438833859546884236282875740, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 77576260176, 7461139639404, 7542407407407, 617463814, 15808627525515449218203504424851044578591220236128535332786480442584235490406, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 78355692715, 7542407407407, 7633333333333, 665291523, 15631932047038562098372235630100194385872059497581543667219983519304337589802, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 79868779165, 7633333333333, 7699710537247, 468837287, 15438945231642857984616326336179301720901405660772988978678736596711706361808, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 81255065965, 7699710537247, 7726603375527, 187256146, 15301097274774606022867797851390700461194620831018002816131030423547741305570, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 82079519288, 7726603375527, 7822307692308, 647430601, 15245958416247502957224747726990082229307024473975166762377286310867435689966, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 83175212309, 7822307692308, 7920541125541, 635299823, 15052971600850492935463949321299022439868690417736561252411912880723088483414, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 84909187301, 7920541125541, 7954951723164, 215654243, 14859984785455821832547389074583062229040182950404265327099363835306643793935, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 86095865772, 7954951723164, 8021403508772, 409799726, 14793567024033754094062573203394735737994058717764353486076038196930879676158, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 87007442613, 8021403508772, 8125000000000, 613991662, 14666997970059918921127789845231393357477412275624050503840610753502570515795, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 88551242231, 8125000000000, 8228639898899, 585073430, 14474011154664524427946373126085988481658748083205070504932198000989141204992, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 90438864082, 8228639898899, 8231441441441, 15789908, 14286036773293946774412432027420741588276948291654816145866117708203161628281, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 91406600803, 8231441441441, 8340844748858, 587661440, 14281024339269786967670452609886496781656957943551641761309020782532521864014, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 92444034547, 8340844748858, 8453333333333, 572506792, 14088037523874248983131009364823550984636157187247905845010921181838335254092, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 94492085358, 8453333333333, 8522813544898, 337539381, 13895050708478507373341037621319029001467081653997233325049590313713222146829, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 96176785072, 8522813544898, 8569037558685, 220083762, 13778506522552887730228791044073392229900044215911265036681779864154497344656, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 97254055535, 8569037558685, 8688095238095, 542206744, 13702063893083149893060934784177615956296996624385461993214874840650187104022, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 98808470700, 8688095238095, 8810652173913, 522097027, 13509077077687269896302309668693468125710412430266276558438430496973191350573, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 101084259177, 8810652173913, 8839822977139, 118872124, 13316090262291429946489474511746117465580925983869365095350008838247466733826, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 102512991695, 8839822977139, 8936862745098, 385256654, 13270976271811128793862717419009084622433503103386398775208984019339526398898, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 103717817248, 8936862745098, 9066890547264, 482472020, 13123103446895894565140876429068314430397120141169897896540208789843207966517, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 105891541173, 9066890547264, 9182392346833, 396677695, 12930116631499842946428393493200405168674706182018816214896810460021882972894, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 108250764533, 9182392346833, 9200909090909, 61647801, 12763446021070647113800786696107963485111899373755068465877961413049603509211, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 109539051802, 9200909090909, 9339102564103, 433701403, 12737129816104910427960518695241601011920524839777421582926159684885165246386, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 111070432519, 9339102564103, 9481666666667, 402236956, 12544143000708655107323240996115505271397726002883419072478466567404176276802, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 113811945810, 9481666666667, 9553697044961, 185534468, 12351156185313283305547074943100421116473641906545794503065596780531709739276, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 115912399357, 9553697044961, 9628809523810, 184973507, 12255915770330473304168454303651809407626001767993489956303830910901895518228, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 117365494225, 9628809523810, 9780752688172, 333530880, 12158169369917585834100200900369034306865951832215607311918652730889602669731, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 119627768334, 9780752688172, 9937732240437, 284404633, 11965182554522727279649216923190535145744834462897881971488228122562042469812, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 122714809917, 9937732240437, 9957461170062, 30947275, 11772195739127338178737045163043367871902980204873881066781741845579756268979, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 124478128791, 9957461170062, 10100000000000, 199454129, 11748385519589188602235838319967036374988487946810017877674418860480682253346, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 126126874296, 10100000000000, 10267824858757, 135301477, 11579208923731619542357098500868790785326998466564056403945758400791312963993, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 129282627545, 10267824858757, 10398081400337, 30260, 11386222108336162811846087398755975796560738865353245692907159603301262986497, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 132326355070, 10398081400337, 10441494252874, 6178, 11240855268847950941858688158878509838538294968316546568601549553789514416814, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 134105498314, 10441494252874, 10621315789474, 1847, 11193235292940088496472625549992802400544245367317170365561056948123690537651, 11000248477544705552343533450872061879022021718063390399452619754290975642837, 136429264952]
def RN : List ℤ := raw_ints% [30254651027231986546955053520018104328295516201415528357068413868021705171494498559749726719943921478684639585812139972427529484304474891777473469394972464, 58629346316250143888350428799013761894119163475130860198661295166768725612919518757543430317771234615384300612417034307325695840972565666366305488415462398, 85994455022939000437108845181126336992647891848167965702871951349425096433261415890157285633745048156911790575256486786818364403076405423535786308320439307, 112695806362060063683169155405431674144972234516506785401414316635894585044308394711262846253142081270826527719707448936415018528368289088795696880750712447, 138907694767420277701834995068254873776691092599757057001776831837246191115722711700364566533956939592209187395364259537044038581164693667522866033709509874, 164732952700984236852652070665387718741726848219795890158304754553787570971913128674751801088246467990850024490455175891714201168420694895005076646109272393, 190238913108109416245926344946568670470109311400598646549002060817569013481402351076108226685191910448389686505866421297579783331998419343265464501563417133, 215472949670441076992455722429294279871574050903065290340821523050273442293803012664569033297731611437115018935760273923083691915157066423489185696404511620, 240470168464140165247827033982005534997539263179755291285086268390523544685701452997190410162213682107106839449812820467367509487520538981546970334924761614, 265257617965972516874340835762426462675443245590297254582638527633146284356394871528733706700823741344933976413785021258888913482030473928843195160434539277, 289856776998906056106739224385655506880532372536048617069641347111885125179847730501039127854603726538841830344256984192070365739717577688934416227642362696, 314285116017465563038794044560903565788757961010712224497331244108394698665790050701218415652154372378199185635395650008453758439965432192350708750528388663, 338557125226660661011274328960302054341975915399766384378414258515507146096014159354163303310738497095511391961652066703502219400024160031793468799017022183, 362685018810786036115217236967718364490238037796189461710311414934353602896985600195660280516239739730890356270898145152998784924770430499704242360870254739, 386679233370340688043976705977067019083665713922805940310220841084729052046330052838877631250857277365444731208736314078484187174264944648401496509102040127, 410548790585799576898119351421857790284233772939124180022518692252818884633465495005647636199080130109980263690079638597017227848832577074128820534620135933, 434301567390602083979299083452122050117771849718433060079554481036777567292706814021779898528944263444592466886195821825415026072781688034854364414661638132, 457944501380972016428219413024214858548581745037891729197205722352247169252683114889360284290775817543064718800388922339887681637998526506775760725891634758, 481483749782170331385847958424732703202036835059744878279402701593775722844071125025943462331947572984937093123908380577028491185418339512144010117866406590, 504924814405174123349872087969212990591768786441171666701416061073243488941868604728424847033917424254320847108572711187971971718784722146062426738515215501, 528272641235246212312397920465382557326498709351743718817577051009592829399754285114637537428131667345521578081451058428400424059851754798988775996783335045, 551531700785396327741219599222944096513871669804045940890836470104828236915162554018702798795870698533568291761958379234475282095260463789917055767447320152, 574706053649610480166974161075263757739559699599308337478275974662446277954062897317698465940828203860862922740532523385096105354969138362602623005320195076, 597799404517041574851247377049348056965867329716059087236559210910771802220620578757551577104121608889813376228664370358460201183315379027336493159006933683, 620815147081847422790390696198491046436403350497629091098504626107477433519027978779642278203030667163837664325275150218135332788282437225029785974995494571, 643756401691421456260916958802539719618871486901764406539148038021602634911078347779476921154360685096739373093499938613532360694942823996541565235349975290, 666626047145260300733465102046318383378656827304742459403370385092906647998052478289188729171647968084225808426095348898358644148452553786768954434778600334, 689426747739207928775571032089873234240342760113373965629748627574935482545893181473539471138236302757856449661834346201963306943028829467663647059069878776, 712160976412627935940456115293317259933839116795529939731683666501709013615528972789648026207097936136254116858582525207990622804139648119069616239080056500, 734831034676766327544474367122552371952260434252624373453001721607509294754548630519040351650311923608308288948679492264783677016901368830014249601237267022, 757439069865562752427173921979572796404514614535213145843107593435510743954418833206746167015403713617235558270186671127827538633083860374749133313047377887, 779987090144417833153753059952175364530379378358542142224224650205876665349249750446895563145633774460456884152230306628941379523424350544938901291151557675, 802476977630033343731032415528302008225289542506480483919974459709695445519202822182805682304794105322427541488748649832681541117895367348226833725938602646, 824910499909691172294493833222658730911877242822899322855161850553828385883120893560588920273994064867805357604732735579324407537832648326133199860189638314, 847289320197036044274788980080656654599000519105990489759740774849474642605120466314824083673143678409085426725060679037450787321000882729129273810960495902, 869615006320473496869288306037127040993113911192144186720705145614842071336634338004237044030074855170434089686149264840113875095343847091823211406953674382, 891889038707368990408028879055446133442505085294424565907480577482882610433224668836812093392177502049068513280039328705952782770843349246020477272019911829, 914112817500585972493132716060322272766804922862342827880020710742621330605966806253040955765855447106549986669319121925709539928400272035503735886310510280, 936287668922197941436919110856859059671962682861445158918951432530620932585546792594806470861890903258964080907178192501348040640624831685747948338077790512, 958414850981429825753283646664853286384907483571052034029303735630932850654979995741739238171924554641751503516337018740057543519933970519982628466024092059, 980495558609236879438383447166620959602699263231206243741054617535008062025176846424955446559527026169277132917172384579196498734262307836770559814078229709, 1002530928289799195154619605032346777300483606650156448446478134734885376374306040138111922295080867879524735853363353155064138725320547696663371872311834919, 1024522042249114148553258147383808756629680184595733572763074588570427632927382325473852188433281432516742345228106616291139218927631207272304088197326385333, 1046469932252426643916194069854292486414242960348603370588514383225786344881950245352855065088596551342771931287878133301818206070750588158453443234769011249, 1068375583055145426779283891064088064214916952831103470588726975835102667490025783430164629371784052756085554548043156280667213961644032357596663191425111579, 1090239935545911354951607777846190117766419984734719353336121902067602973351984206757866979648532153864673942601477528990277518141822017656985736485085820498, 1112063889615416337709844439510248124683653866659568862856276457721332497668392587491406987408544366062655422544994674003483675843254146481230799930130600605, 1133848306780263009374605725491525829817714642209690081051521516392937655928184553957295343378793249893274072492260413446345170933941195677336736407824315453, 1155594012587477989230165180678313452812645928767875615948860666963626682562457032128893133926449872742798635029615637003339033411254589871318183504309304288, 1177301798822142165372405473186069086992203700943204255450371640746565744829433974637263828931522194389510804894072206026622446334386338215073808369047774852, 1198972425537894951832343369655263414873857820336022328474840100149866941508213555376457158900169987734538997472133526521279486316867011235899659808432755678, 1220606622927736089652118638233221892525032378714990649237261664370488813213585846015348647433444255556733797179510876494473100130294170194309691028186334588, 1242205093050530622484839952582131145014585925749371911902577737205525962950482728653149758857849683376924810457539099092488630506223670361577215932387303040, 1263768511426872346460022430980762769732886755609583751066709007329820288622860763474025607165520013527035033036534340403699523444088346053928313679098480050, 1285297528516438492961806442791290617435888229831312698802818289092780568039164995190749523010924161563339608490333595605892601518588100487201813859975993278, 1306792771087640378203432637729197188779421133650690337023882922322725003261757051956117187097630221302310744888819879673988345577589180724938096248400668025, 1328254843489213343155288354259579453255046150228765058481026169223419811822587591138297539063237704811773448700514884836983100884770883040376624654574246633, 1349684328832371034310465585851156357601128864858312668498682163301079671742072353509602286516620824657682367673226139321612929039062490194217339711768553114, 1371081790091254121115424973618221172509666641350088152075572120876056624151254297812760064107730520946168466275274166737545193932697588922760892605874256510, 1392447771128615126365831775732196835646276158865778467707616482454209681539462868183693893831537133245871508317531475556385828969752762382622329463996237802, 1413782797652984905632734297187186470032828855671102325240247143274586396098042340076976608804795324716139346069154488112701157155391283972892007733775075428, 1435087378112950306395846869024584533812220479020892468790470297240940539260883942786346469629456763642563778999577472970264499187673340866954319128767839466, 1456362004533626292038877996523500524055134414401116471445147082197875791950702849894683887355477774647708022453431950855218586609912862012091250522149412130, 1477607153299920442722267689847668515589887713025979729291935263435842342512287214337717222897290719782566731499238042223278385630158338592545381794303591418, 1498823285890755611094587180837334814049585581719122431078593580855345117827551643235611095203340942641435771745949859982480943843421747078007874222586585105, 1520010849568031043058538967980195890775014058341945078566333735289435111581885330223460126142578195385920350137606981916536952656133872546341442273641908822, 1541170278023757798850242606328060471556295772202047105542410261933739285127286029172760653672569728101544236415885274681238565185995657318945507818168594405, 1562301991988495918568612018787520120279444872364616485472233471088194773137396638744252415411963842407280032203209501218920020437016617044710270401896623335, 1583406399803944211800484679054275707207464916535192988679371659496147387269967621799039381365697174219193485592339185263942294992042535684687290674596686600, 1604483897962285112900392003170566626788007990382271612734042651148152581795490450912366220237405732515074298268843545499463587076025229299387844099514946368, 1625534871614663508727955149483585678371067111719899362335348357060715237344053520407395974572307415452527753461901176362833521840053430430449521988657506802, 1646559695050977000884115774040946579389663746359904028164944455095459781246671334672935697723729139618631015271466618421531058541748503465193535145807129176, 1667558732152973249037514388715133638656718751064907317482263261065785545797707368371925859603248283678284896161529487310481897422468113179441437186667824109, 1688532336822485699313455533540191147450158616150086670696716328129272262907318186084894705399047869256194597332333992607951337886816272394515551739265721221, 1709480853386490238422662518466005371843365992793096543890710540055164769231361522112293963999464797606213187817268391013789472197474458688410422622741942893, 1730404616980530464538898692323371282355802503887277153436638235092605640451903867769208522308074358937608506520350634037525786817626664829514011996408417443, 1751303953911936861949806638438984996593933521439690999508361553535246677387739782629502233426302068843753195240595003675613549156355728414497753118450786466, 1772179182004153912261604581291736969147592055425101523829569032099357782920931000944759166406045043841582206608453031741914848272941322537851776732460960298, 1793030610923387924385001804233192322002021424855718910235654244531182154090291188101517732951075256064951603382833088417488110055485369400736327289531095471, 1813858542488696103485676100624395583121596160245945371685530074923753609968864838178425663942421488206066086711996130174395213021483253674921201109007702736, 1834663270966553204836409267600997084065779922276111784064336896262855938466390865928639191065819599714887634119938652693530039254802201503649866152482435748, 1855445083350855231651024842126772541228112504215414299420522492645628590317205709326578461954665665108527423452505754527905303388617987205860920394685690344, 1876204259629249324145808983819097667292662220856366276264528683999857047487314116821439159251768463400215035143001363109233048173858334252408216623852723390, 1896941073036614615304759696541867703813819615930468611218000602421445425041956836332079438919287497972108857782242318540909927491272546175905522984882422032, 1917655790296459830336427196241167731289382829768094648510824661348636727293053948411603638767039455358073718989897766386955605651431823107878834865720843542, 1938348671850949274952634642457283593242098111855839112033460649530563063737107762179271228910149241717731490977281905007312095842576942040179467111543200774, 1959019972080219138850416663103468069386089901169274039687758490489125727379424743327465854732792845256664988489272078696074524222617281337655310235791663821, 1979669939511600328622961989908711720477208148278829986079120308978592291681838902910222512523560720828658927880946347306007796770506408870376649546756765843, 2000298817019321973902632112455779616335158657161730358895769784971485768171470575048450488285212909837727913693117684171173055587292778399688117754153693677, 2020906842015230993953397591567470406888828729126684697292703906269029743113232584980248644335663383991454241175676456299214239088172960387083668571318825181, 2041494246631027374134748429948445172015333402424343693656700888685219817224054449115942175749812764254368960562037595569788357501216938815805708149986895949, 2062061257892481816840193949884778874631788842938432362616546558303035404919327424399366515055056505835155271082131095154662969751145694535844666481569024584, 2082608097886071959905685911789867275133500307558162119969804687454035315108432408851930145664824092823087359823097909969820321054374532404760376403938369194, 2103134983918445180564197052575076883351972727061728965397465753610670464683974203786847481670948864394014025950457743428980325289600086493718404596456614116, 2123642128669089929035324814136290843636578979699240337861072098570690590059293643691413737774450126375649876220263453906738986218868754808374977766885810541, 2144129740336573385601986777778080458607016819321595851052732615505433453647192316919839442167079166385097961775968415547973532861114987159018373377742123371, 2164598022778680847996226994953618321229812201053431101727366237763536636012301116883481627658460565276450889965665936846954760036608743469972348330120633716, 2185047175646771486468279909424804769714989788538162494831207230503386881257594503694173813092843603100193304501785730285118803906505129181609865158969141161, 2205477394514645819817036434688417990788343894537688976083511542691192057346176401858248503398650660620877569153969429951073643192943297256831013049311975224, 2225888871002202346724695885716861814481673060605690678530562938520072185916213818223340885810413487061230206440132659476138036825764639624315103238079378626, 2246281792894144103605648873143084742861413950265338488069508864167088455276173146432442274895309977404200890561747330000665193700117121006182027819143378623, 2266656344253980413250405652268603217713098722902532574443984795672086423062789844543980418984846913422554692292125187162650841355664673174109987124785509481, 2287012705533554647021200522912320818165782756525853314005693022446211388532867078353840793952038829550659324647818106934617696703723614198227504322939210036, 2307351053678315364383214370683923599183439242493341524849915565043827709461983409118078670823739255010794746362528923880852093842947097937434141678888522872, 2327671562228535641460439489323597402120166078178404019846015861555524566863004111290252811783934228924155311438406280189642194796579480547419060047230081659, 2347974401416673685909362210154419461963100446287252059447153795249468941927330920507990296411946638377712990921162749508258052479979430039697092574233260933, 2368259738261056895409555804420718412268106767890955037280739416013305301287270537264049502841212493808229055554834307531573716793288561449975028351006164719, 2388527736656061293511606958417506354841018153192151419949535145400572338219199432513676116977370719918652382921965324217154960744347999817737874596730469725, 2408778557458948716329848236232666574535887249140510931368947144219719378852059840697570540337204012765227795468469949736727369885539804867402004804788218628, 2429012358573515177882758363034407524349289357889658884872742266827765603337240818493782692716256725464485247716016098382405955258883207701549095564631485433, 2449229295030695466022722222105454663173289336248187699268885498264700535409176447593927661070476405931050964607097847878122455204992590681835190411904005228, 2469429519066261173746533370416177964846515122498722111292535789445888248791368358236283139985871922158862083364883088914121243560213792228083927308945537029, 2489613180195742014433578107795312808890001889000791107820840905510797790826806703104422866753407201134022615162804620102076429470320536514617922422642990911, 2509780425286693369429570248236885248876756353906327204946774541930155935175209499354873783360692381864968804565723522695247395983751399523616385283568329796, 2529931398628426540339260604117730944984347994472351496208042775779431409099534161919075782118919320394473502019338153508058500597033158299743652962138730632, 2550066241999312096881315279798219623387942079872644285689955892367607749960022890630666406771289164230829313072827081284100740041426328323737659845554595388, 2570185094731760996955801567273549817967686454921347926814743782874204689842995966980892092830457109943660945529873017597116224208158572497752453504527513511, 2590288093774982783540094373806346697372128750147703408213082647919770015783623759768458385816205047379164827892711363485379718503279979887004077053323771149, 2610375373755615109942616558803144528961664107468926368974178155966658416463865259702699312043391377590186782954811294863908026017337557353660877916425285888, 2630447067036314089343708965263048178352532637146541486045639496722444440181222567480531458819746978314266400673544567108885943427106947190802893254142367924, 2650503303772390486588442404393653798708493536555852248621031277988502398538595685008896616117096320377358107870201175219445057380272035339495664689166774304, 2670544211966572551494669770047551779923716762105588792082250457120258887693819937833639666283985467871995870372101174037466753027191894577526170931789136907, 2690569917521972316485111715468171357777093739484303509580833490601391818162806168575709650475709950687064149873032618934928184640386010838049955822235020960, 2710580544293328431375098393775346949780268745051472692475237344119110751505951386453870506928854913316045840059887318667024633081574001926627450728285234209, 2730576214136595070023748429957412381369331690616836993703573307267217791657428083893618876594205000316428485746334065179290205104064193996722614774226398345, 2750557046956943103715772431745062391607001626550140976628505570295627318492326168680591488074792507705632326464490718816085344932590409920186973198136116048, 2770523160755236581983851543807135168506866370442120966917915950453554786818231513956845946963859971926493078333138636083417758462486625237017292253922833165, 2790474671673044581401492955786066125616167834434798858561554817757417715614922903774009187333672759283547281783916706571542219678517367001453018578578118496, 2810411694036245665791065260530496894477383968634367090499713148664605755093576554612629899919704508902966500375192770845968281707292161264512044447753973573, 2830334340397279537178933468374947905055205000360482186879257803702608798994084910016736329188471743834985010789877633191729184456337965971391325410198850079, 2850242721576097936268207143343182575355577284612779887956610034078360292472922517190480660252993454172367536232146815019360544551089673203801129359194186393]
def MiN : List ℤ := raw_ints% [645083599170974841409286698449792398024779126906064142969104401269862225, 331015814204204092456181763908176014829859886728063700161172351628636770, 209504135938623285524181936624773155038492601627266031518982323658033612, 150321407048217885620895845531773931137156161820336678591611200024841310, 116396326776926868570496428114661741005060127047490000456415024112799876, 94676774822115184683132868245451388283292801692135032068037013631747838, 79666252170833211343136793407702911647752596547437939019925841992187915, 68705270871778355351397713749770668688545198767388778511053801607569769, 60364622753928703250718537311655717929466957637725429079167070135274833, 53812242499773885436721648369345531005537706100251828102391941084963315, 48532525822834841707132136209788969356760975628730024365636410325189463, 44189660197116869027576176440816263188727596993094549303075205287220972, 40555875566861742532566084732626983005458492484969298033854146820597100, 37471394283555021832328531426266983005970811285993856050661558720507183, 34820909936552327580262429084714092487126571916630059225282599306024409, 32519170180242381701130444378100181731155088425907883065134510069237746, 30501811816175111109209290543538758964862441439784572260405089105642274, 28719348681151936476163434614028092076502086376286907769325095727722176, 27133118272453032040742936834454853249895609388544086027554472032300464, 25712482399137789413650219946286416650005521196948266498243423704068352, 24432852246072352200777036716981420917598024752370097803737944441608343, 23274268325494785260231717449796542915239080302856582596582027508613542, 22220361850433209900514405134550697311953495245852203787010406985734051, 21257583302603717095047689300565680572344501808027191678433124552290536, 20374621407530548753182742942110612371360615185705130919572303330589857, 19561959923814287094302845742025336086649562749068418514628500478575132, 18811535606184372779962352660358719873102651559478463730965547391822017, 18116471415589811970275591083341308641485815867910418547991662824137788, 17470866366736462821090142559235725056096920780301014286861446890397580, 16869628478771229585598356462253507127248026976971526761059451743474934, 16308340865650144168621791908784163987354273618078107928264232053858298, 15783153548416051898235826250279575865325848747721613800050484802854157, 15290695408798975909991652402084063760573011685591303273843818002228322, 14828002044599651303654803842300289919562495522003774528485406542172379, 14392456276654230376105600457959245784324736278403987681878706946596419, 13981738794325188615818198589595507829386102643720590145723884785781539, 13593786980835264646250114982050739395785811915760831519421491161574072, 13226760380331497766080080878710023832939891307295542136759028493501794, 12879011590259195470870446601220737071407896217553178503209735284607012, 12549061610598371299929618073668479263866535648315041701499003433846747, 12235578874062743411258872735739990606024998665200522000870690754000431, 11937361331907908608523297396464090078591372468141706881735201203218810, 11653321088474733858920954138809067509143768939514206928450250146718120, 11382471171416684841830690433663025710518218476834173007169882782173086, 11123914099295775090046416205497423421813562845135305048334064740175597, 10876831968098155673325923441004143299664081184948434875927987063330216, 10640477826431823727139045410362899339090117453233015417393760734928522, 10414168148192221795898093514473005602561402991477917772046762535917020, 10197276243221184698131907770724618061904251003726147696867478185059423, 9989226472420038360483362689424189834822095926176463389531678922583455, 9789489155064154935796276459956216583143183097667246681331979550638188, 9597576073611404710571288507858960818117775925019472896440370996200408, 9413036495817135738770926517445525085957408779530641040742459285274763, 9235453646031955638205270728023380929509974935899433932175476755157128, 9064441567618803511168739766804039853742141874988608400977596269898960, 8899642326845456216514116711570811595459544641458106228743964809598709, 8740723515679593718648344885917614672209982265287114420827269783741573, 8587376016871625403844354663507214143209101261283739785894726287755745, 8439311999746877753731686566550286365003265836440232054544088301395650, 8296263119399165292524112443372000090967405532906604724912080546147173, 8157978895609467497126541239959418070262063030035316230035980427462162, 8024225250910800328573715689055325407081880273530702913853744498654318, 7894783189869328618811147661118161736240136555027069810913542333003777, 7769447603923285574530967006732946260717178721814145372161774371165814, 7648026188074158228680692376625276493625095302299735425771402564917853, 7530338457407749916215335285374843578751508498095904388183014784692403, 7416214852876905476664631489480508399637539420932585358714245257421348, 7305495927036970864409123515907012388825484877823137653895208924086397, 7198031601518045666929658140996805449432057613643917041550183214791915, 7093680488968818394269502209205771806815827147454502231001636556133752, 6992309273035525340530049236359022079940757034857955361598536391086671, 6893792140663485931331564509844660618461965174423543375966405237012297, 6798010261642269801101155528998226547475156669443634288584532859538940, 6704851310871188240910260352280823272214935537920680268165808013960095, 6614209029309989096579419589135313345327928750233753151897399963506541, 6525982820009345012695357635987557393215836008583203726077443149619122, 6440077375994639179291034411138738019468711251857069668020504425214893, 6356402337111254800595787878454080607272931885584882479607511902492324, 6274871973235722056999219721880411294143648981777551833313274841911991, 6195404891519540846047289884621338659239146767968775388417501589626886, 6117923765565482009406882480772666229201304208815038265887101285432722, 6042355084643307331353080228777732092177929658265936308800271870324414, 5968628921236286091546285556274933172007585607330070469003566276874748, 5896678715374353840159732013981005262480553353733431172948907797980202, 5826441074356630871425767368718282469246473122512178398954614624736762, 5757855586597360499135275720710940198432387552741242804990295679279298, 5690864648446943652293887044887995417224893331591329142635070096435852, 5625413302945211889122546403508454186813769675505951751976522335880534, 5561449089558774442490521358768438108246264609316563376176747710879642, 5498921904039404984868066701765184643605175854581411377705863542996806, 5437783867617061565094975305843696955850711319713651237884243835042666, 5377989204810191674259189075406578335183443889615256665826405354448341, 5319494129198285297128347803442861826421186621425135567237559913270667, 5262256736557926705725095076277298868984250656144103330586285809809232, 5206236904814500583266108741754258892432116685410907791466070205931755, 5151396200307795764015319474487841512525966385439576617054971866463336, 5097697789911521611702602165176349583789616047069822906793960079961200, 5045106358584652250131704334282143859102311142716188808987552383082942, 4993588031966937099110513124163113727601015467942121915752896991400995, 4943110303662213262603682675975048581962091354367028334399973239220730, 4893641966881638528467879016098582335580272867169789636880946637591941, 4845153050144911366607738790208323786693239738417808119357885776378385, 4797614756761204674224971853981992943875914517782168206475220951448232, 4750999407833134943453498438351154439381040434427609546112088173532747, 4705280388546816412247914298168902383192775266635393439730912991110628, 4660432097529088237021232010048835145776501288243208469354567129195590, 4616429899069511014768335620508802199478047008733702899167410335292465, 4573250078019849951948692960349551887475004312889768670091217275479580, 4530869797197623959739312962204338362241410033127031378285499381187096, 4489267057133018345251856909787891624395577734175683821095214006206821, 4448420658010137432953333438720241377726888469865107168400936582930632, 4408310163664305973934782363680945678447470380413659608572712194146195, 4368915867506998984588300756428413560819883035968272677257356338441299, 4330218760259064894188296947167733298342802221104687746715782687627758, 4292200499381275421236875135525508008910361525784531990020625978573350, 4254843380098949710211240615903977135510763606847627356140387311095105, 4218130307924516313064204382140475085169939210557738539820596321480425, 4182044772588445668021464593307411281317666610391797709420314792285097, 4146570823295054129418230110694912347822502787684748013878527560253076, 4111693045225290376282890965992440741535164566186487679729668376134067, 4077396537213804363483107139423409202768499100760439487183841507174944, 4043666890532402598003365790499687742737058399485699104978647628892189, 4010490168716443016850610794215636350992331042033253710713429602628889, 3977852888374846881639655936797549246554944812321979795339992828137157, 3945742000928230107437931811446801446287506458434354157846558510090948, 3914144875223206223789576075810899963641732924228269811888636305071259, 3883049280974209551715641472804883723527681647378889097791491806690408, 3852443372987250110459559737404798030904504987882857130169367670592252, 3822315676122859468176191459164892929086259769942376023674063751502617, 3792655070958135894959781145621202207003401840723198089276648291586963, 3763450780110263028078091204967806418678720432241544484423872441255761]
def MeN : List ℤ := raw_ints% [1, 4249415200756889948436380134400515341135168982651205854, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127, 127]
def ViN : List ℤ := raw_ints% [759975914999918232578520615, -14663627786537734594509616899, 3017278409072490392821231498, -462364911538891693466578700, -2186515989281047044846613846, 1672003544107237266152838734, -1682360217075813290986679975, 463538688421480123120263647, 20856466663598487332864359, -779484354955663145729628420, 724979660193753486918698528, -712377965536087484834346756, 203037079220082005716724426, 65702316012080864531752936, -441658962765381616352024413, 429492711349428785373994955, -403968289315690477242471461, 108706518170948313884118996, 68689681586541199032788903, -296665893313659893150896176, 291390143479529324588324324, -262768094342166751809633649, 63602667367912054101561991, 64540661703294803491382369, -218552714458825867339782431, 213602004904143720938803954, -185106838260109433755783454, 38399803761841506958046248, 59341191026659831102474985, -170645065430900915573323379, 164588532912086561239296026, -137332011013713961906778214, 22862398502439458483191426, 54440996419006776111593041, -138657354168875727853832565, 131339765677734834151589849, -105544418151970925589880154, 12704921921996063568251314, 50277428333011557278194690, -115806123841916158726634578, 107719387466920915558357200, -82947828132726472707477112, 5906883480284682275258925, 46943571640040989695242605, -98574183362043433417779486, 90280341260520358600691166, -66119367695731331646496462, 1166460065239580601479946, 44107013154480348803480022, -85239832637747343530238630, 76698543704238847515890732, -53477274942996890697920561, -2584202662703382256404485, 41153849047502169854955355, -75096433711744226492904297, 65333817086079600153157446, -44235788911602645537680928, -5931158850107162403922104, 37984423389980487220085388, -67208057751071460365003158, 55943764717784122161211308, -36954588700836597135588110, -8256560748618400162150288, 35563695175890340554587313]
def VeN : List ℤ := raw_ints% [381100735687, 1524402942746, 3429906621178, 6097611770982, 9527518392159, 13719626484709, 18673936048632, 24390447083927, 30869159590595, 38110073568635, 46113189018048, 54878505938834, 64406024330993, 74695744194525, 85747665529428, 97561788335706, 110138112613355, 123476638362377, 137577365582772, 152440294274539, 168065424437680, 184452756072192, 201602289178078, 219514023755336, 238187959803967, 257624097323971, 277822436315347, 298782976778097, 320505718712218, 342990662117713, 366237806994580, 390247153342820, 415018701162432, 440552450453417, 466848401215775, 493906553449506, 521726907154609, 550309462331085, 579654218978934, 609761177098155, 640630336688749, 672261697750716, 704655260284056, 737811024288768, 771728989764853, 806409156712310, 841851525131140, 878056095021343, 915022866382919, 952751839215867, 991243013520188, 1030496389295882, 1070511966542948, 1111289745261388, 1152829725451202, 1195131907112405, 1238196290245064, 1282022874849589, 1326611660928361, 1371962648495257, 1418075837631158, 1464951228807478, 1512588824771820, 1560988641538372]
def cNN : List ℤ := raw_ints% [-23192624359128364031327, 223749203285793069374231, -30693343191248478117078, 3527564327536710307820, 13345434504889203154581, -8504249797094916107955, 7334508479857584450800, -1768259767232819073182, -70720983424202770090, 2378797469957468096099, -2011329401727165879458, 1811670851481342277106, -476630763643897436797, -143219682992294016226, 898557460053266634831, -819192335795266695736, 725184342894952172210, -184303314498813737461, -110328564431507631053, 452676228811126545946, -423453403261499785779, 364502083992929287733, -84391276972114966486, -82067695240395613977, 266787981517121420093, -250715995089186120768, 209222681410171433915, -41852464688809538659, -62446532178849667361, 173589137197775182671, -162027206826572109335, 130970011724199258715, -21142576740093308404, -48864922394702486026, 120899618241555984806, -111338098888596288174, 87052973692174076876, -10203248613856316471, -39342188386583813225, 88353060792477538091, -80178898112168412043, 60270638698560785717, -4192180885694411362, -32559184431624665482, 66849896485760791977, -59894290599338935255, 42931978068725151969, -741615336888364538, -27470188159229729355, 52026265037687587604, -45895172540545802406, 31384556076634856414, 1487992578299688523, -23257700063918598234, 41668386958309784764, -35604104770158822279, 23683669193523551827, 3120769027240180919, -19647332344691641711, 34183785884130584902, -27988003448878615163, 18189750770242308160, 3999527582377309726, -16958091342873735692]
def fN : List ℤ := raw_ints% [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def gN : GasLit where
  P := 256
  T := 999997120790
  Q := 256
  Qm := 240
  Qv := 96
  W := 80
  N := 64
  Ln := 277
  Sg := 119818393869546725993480329177774874481617516143557060162674100623549240835647711995
  LIv := 274859910930757621809349496791782898904955394261623556382415297275120153202432
  LEIv := 278489674596803539660726608488072173396634434447029422675630
  L := gdOf gdN
  R := RN
  Mi := MiN
  Me := MeN
  v0 := 28926549020141212282660170469
  e0 := 1
  Vi := ViN
  Ve := VeN
  G2v := 7715604399666316073048035851651784479432550975904641116756372795566377121414
  Bq := (27741145594835673561234466866838271316337243 / 730750818665451459101842416358141509827966271488 : ℚ)
  Tb := (846812735 / 549755813888 : ℚ)
  cN := cNN
  f := fN
def AP0 : List ℤ := raw_ints% [71056184761895416779408, -56217129152600110915927, 23229572177121376794605, 4171845475379828275914, -11358946407262602268441, 3188193038663855055768, 5123564915572235055894, -4590518299296164217985, -1179095075716030159144, 3895223461631588651281, -1144739835712566561132, -2386662276903160272377, 2160066491558676101640, 768346512824655270252, -2177896064604028821819, 532978570983311720844, 1547980948270507550057, -1296615473913191757268, -628583874347075325524, 1476391689606786323121, -260429533687174421842, -1167240278805124588380, 882454851673492702425, 559564671931817371459, -1114958777965732621586, 116975917412023325301, 958032373994113077908, -652040209297487032481, -517424311009735234209, 904087816420588707264, -34839607042500088672, -830027439706017529240, 513352747408480253761, 488040283875437895660, -772580354891742192216, -13190581972177154012, 746721014440350603036, -427629281486659426672, -465157158773842564616, 688618869994380031328, 39162163622031337370, -690583583118523784375, 376621043122216230278, 444913000375787705831, -636215130428517047579, -48277174522608974425, 651799216434738508993, -351327759829047730062, -423959950661565026733, 606519273143530707469, 42029098501505118180, -623734267795189496800, 347428706038631038198, 398502385376013993526, -593939581211513704464, -19463147682885461163, 600584081490793863637, -363070095620936032708, -363527485733612277711, 593873368887528991545, -22272952925129179700, -575626366026385129871, 397347664115187837858, 312008504761968731932, -600678437819027308993, 87438522551835703914, 539371151711991926712, -448448418590076429851, -234177321884890375197, 604956218607364833407, -180411555443700214368, -477330468067390436208, 510204440803996970812, 117698760554157807411, -589359917664030835003, 301728834561947023396, 368216656729925543217, -565285553531127969602, 48293234436538132578, 523484544215911984047, -437794332089579695899, -187276477776218099775, 574810782797396812733, -258212345046294095121, -365391088643752690379, 542449258324813845546, -72186122382080523307, -476887419220740584989, 459902388612719342440, 92771304606418568228, -532151554007244018279, 352916914463320936168, 232365550365955737390, -548417552420504227953]
def DP0 : List ℤ := raw_ints% [13082701365672, -2699026112163, -322367772208, 656081750336, -146683814042, -195414000701, 149153187713, 33287191583, -96979852306, 25427548392, 47735745862, -39194919503, -12726703543, 33100784083, -7465386615, -20057207518, 15590968572, 7033813885, -15411645131, 2541450422, 10668664753, -7566960245, -4508154638, 8450801823, -835097066, -6448821123, 4142346025, 3105005296, -5128678857, 186961252, 4216286617, -2469809826, -2225057855, 3339451399, 54079274, -2904917969, 1579100842, 1630999968, -2293388663, -123917178, 2076627859, -1076531855, -1209124854, 1644220156, 118668885, -1524124863, 781623455, 897531287, -1221983183, -80596862, 1138576967, -603763101, -659340219, 935696494, 29197999, -858008137, 493984414, 471075273, -732993277, 26185306, 644633570, -423888916, -317082326, 581547632, -80648380, -473958885, 375435041, 186786081, -459735321, 130628621, 329297207, -335360518, -73712550, 351685309, -171552092, -199475236, 291782955, -23751133, -245305231, 195468330, 79669249, -232986660, 99719203, 134447268, -190169819, 24111291, 151761787, -139439959, -26798173, 146450692, -92531063, -58041679, 130504853, -52677834, -76218964, 109484765]
def AP1 : List ℤ := raw_ints% [62155256464281006623320, -45768191760448193037458, 11771677783653634897992, 10947067511307199569422, -9822776752011055509821, -2458193020682826954971, 7263013894678256809691, -1277725336645726144855, -4668059391503629399113, 2847480185971105955739, 2402569290336653811882, -3196561957622296498785, -627486430126153603442, 2849551800017147887538, -624689382743428316137, -2138598312721143924325, 1386545332961636358865, 1284709635577110263818, -1720496068352292601181, -439592317110975313011, 1703316341755684490296, -291722841251109707616, -1420012014460982975951, 839668333438891963578, 960478570319341432625, -1165338331125867171790, -415749010980725562754, 1258386866977581316750, -127007975500930308495, -1135296457501782922142, 590634499103396959893, 836405101463642449028, -914364696658176380942, -421094111130509376809, 1059603905079428570207, -39180854734910209246, -1013907565752647396901, 469464537672826735621, 792495458192204397735, -800952020947353822611, -436432753062587024982, 980359057784237923389, 7542728606283067596, -978065887226422360142, 420053568585876089576, 793369582123085732758, -770600639891208084168, -456176068711830011446, 978796504508087928906, 23883713530533854152, -1001085813371328528749, 426078692702646483482, 824961135655338715278, -808220308824394067060, -473668479597505309669, 1043270613191147791950, 5791404090454632813, -1073744246556215684626, 492171665707135995397, 877018033427620544742, -918743624747320253075, -474591026707515739197, 1176148353199606772343, -66689449893184034196, -1190355971675889522545, 641166287916142920446, 931152860004441146591, -1121577765999273425997, -425382993529482400626, 1382813821472537825029, -237771575340360562625, -1332404809085289571794, 916738715595954337842, 938361289617980977495, -1440095487954765856652, -252128410786931954060, 1645923486591628575571, -587116236484147149845, -1426741420473417898385, 1367622081692301467876, 777304975978420011587, -1852034862195360153276, 178492416822421585558, 1844276614911304720746, -1190032227850007470789, -1272448711449726237481, 1938386110089128330096, 245849977678054939539, -2137164022089818347318, 938677188540239861262, 1661131773888843579493, -1884509897532820706824, -625791218369336136613, 2245061169722305273198]
def DP1 : List ℤ := raw_ints% [10651052337151, -1367742181380, -845904237503, 567354077883, 113097646081, -277013100389, 41515313643, 131784612189, -70894060534, -53367101406, 63934587946, 11385890302, -47199278426, 9494350402, 29955169094, -17965484335, -15447808511, 19252242427, 4588782801, -16622131810, 2666368913, 12176458024, -6764820729, -7279923002, 8319410030, 2798539043, -7994405502, 762160625, 6440271433, -3169546816, -4248683198, 4399132804, 1919838976, -4580100596, 160635231, 3944335633, -1733585325, -2778759916, 2667505007, 1380963408, -2948000766, -21560101, 2658056230, -1085577051, -1950161437, 1801922378, 1014886826, -2072130836, -48119652, 1919726520, -777772541, -1433621012, 1337237052, 746220575, -1565081617, -8273733, 1460910521, -637778191, -1082466996, 1080125469, 531485919, -1254710409, 67773940, 1152444725, -591375752, -818227245, 938969962, 339296828, -1050866717, 172160663, 919189560, -602577997, -587678265, 859339788, 143351086, -891651610, 303051280, 701686773, -640868683, -347054530, 787873785, -72347899, -712242455, 437877627, 446090278, -647451217, -78237821, 647976768, -271148857, -457151533, 494098457, 156313931, -534248728, 141868385, 406994919, -341760953]
def AP2 : List ℤ := raw_ints% [47435146650179874733919, -34621807623408215718073, 8273993564557326629191, 8797613254819166028368, -7186977252271326036670, -2487811379459544393846, 5643605784891935074043, -486050297666014953622, -3926079489275408438095, 1935796792851131515841, 2277312695257646924691, -2453070826974846133290, -863270189897835694332, 2368861800086696285457, -226485513998097813920, -1917830437683419422834, 961966022591706483665, 1278402550325526245820, -1354666541511956833014, -587458650402886776438, 1443777898557082496106, -52015784842812240587, -1286700863818390492878, 566481043294707874931, 952300802632326691981, -909442044442775337293, -515202207943424989318, 1059980646455936986125, 50280287237135858882, -1021404092527819625525, 373147478849787546274, 819011648726219894866, -697085521213813974568, -496593733503216730155, 880298230314538988473, 111152349299230611578, -902477096309102097014, 273804933473898888839, 766705489260455943167, -596293312026513915755, -499233603025265199060, 804063447790935383936, 146578048919280289772, -862441257201354884339, 230588297038790100974, 760127420272614251048, -565791062243534789139, -512467414505143146917, 797160482121445755008, 160571155962318004120, -877788669525697976932, 233326287459276270476, 785344051637292611815, -595152476000109447527, -528085534371039274559, 850886274360960473141, 146986463294178505864, -940884964082301889905, 288707908916878143543, 832732660637696655257, -690978643461427694808, -531992736853310917017, 969039817910209790222, 85855239778589134268, -1047321758917933625685, 419626030148902702606, 885404652537524602821, -873131670894215242125, -492255791688665188629, 1158011829870379486721, -65258448085527550226, -1180725847478538832473, 668615611001366456779, 897496890105387222354, -1165034421372420906835, -339023929750517493527, 1402944633329362855939, -382521841183560039885, -1272955952241038758788, 1082916149816735917900, 755048441116444245213, -1547509370473213250061, 54111642830636797728, 1590845927526336248246, -938056296218361690151, -1135713145460919967499, 1612458562927343953466, 267145392938079343047, -1814770578613433899650, 756247969089730647787, 1425031485852254729839, -1581977487352793977346, -539084612824176321534, 1897881998477157333309]
def DP2 : List ℤ := raw_ints% [8057095349840, -961348944025, -679811129737, 415112849927, 114460340804, -215248484791, 15792541617, 110837677828, -48195768206, -50584837669, 49063986434, 15664242621, -39237246944, 3442243281, 26862891789, -12464205172, -15371969861, 15158633109, 6132318620, -14089377261, 475428221, 11033328520, -4563876654, -7217939819, 6492553333, 3467990196, -6733950691, -301726369, 5794186669, -2002437049, -4160329755, 3353773166, 2264054471, -3805058126, -455706836, 3510845258, -1011075761, -2688331471, 1985905964, 1579678273, -2417868883, -418978020, 2343827125, -595927239, -1868449731, 1323008992, 1140122122, -1687603919, -323510334, 1683286453, -425918457, -1364774273, 984706687, 831949577, -1276472709, -209988219, 1280145386, -374120700, -1027807397, 812352447, 595769057, -1033767843, -87251401, 1013965961, -387039468, -778027154, 730974201, 392636357, -880028874, 47250970, 814550401, -439485154, -562085650, 695204201, 192756732, -760021867, 197445968, 626053426, -507455280, -337117335, 658325656, -21932941, -614369884, 345161967, 398154038, -538586329, -85014746, 550228790, -218451854, -392175587, 414777676, 134655828, -451631812, 122211787, 341657425, -293185722]
def AP3 : List ℤ := raw_ints% [54928214472818205871112, -39832958844962252768695, 9042778075566358941592, 10388909463048358120459, -7921181660506757431595, -3281155226423671139266, 6328792261064369473472, -74716524165360383628, -4556069017936732989741, 1762356372604416456523, 2849598246527754216252, -2453374280477910032536, -1372054913514126309811, 2510889569311390978361, 204972124341533429127, -2180040713711720298713, 629521181989185485371, 1636873855135175490132, -1146072918356353469918, -1009165280501297338362, 1379916735997275919898, 389494797376039281438, -1377401331593270387503, 155960490127474791172, 1191056491924094901441, -582101815015234639963, -876742645848376730045, 862047858557508628507, 491341509474969290686, -985760087890422859139, -90051536619149146423, 959006617773923000417, -276758536340184682418, -802021950846527055566, 567078635991266365463, 547182738567637617392, -750530057854227601220, -235705923239356430903, 811082918848263598037, -86803971842207698432, -748451914636850770533, 375359770454899882560, 578090695226016548644, -590987016752606259134, -329203700086308723228, 705487471774947576508, 41219372391867160584, -705365924859557497350, 241508562593856419859, 593748032905348374012, -475640608794059677335, -390469179199309572345, 625379970279085591797, 129350724875583834082, -667850333057320496097, 146306167601770837535, 597385260688308053663, -390594640458433473728, -426739502416828601606, 562092780219061903908, 186102708866509776399, -631559182914927757633, 81864006116857088410, 587108584143164791662, -328530666012601355160, -437843003596585395931, 508754271046168483686, 212405776202214907330, -588949816135280677847, 44763383580987428117, 555427287166940458489, -282813412881688172011, -417135669452599815050, 453813214454852341948, 206245760916265285030, -525252877133263051586, 29804576530196582950, 486819412978203661262, -237427029395104985390, -356074069590019976136, 373097167892345194610, 172177901362734698306, -413585746601272176670, 12659573396095349301, 366482630111991981092, -153628711464657502785, -263829487307207612321, 226202566109191994573, 152097755294156335664, -238960794711340893188, -66209702814532695712, 222066301491479397399, 16928485343648855726, -211894249466706367585]
def DP3 : List ℤ := raw_ints% [9269820656711, -1050673424649, -802774124555, 457519785922, 150960860035, -241381662128, 2427657843, 128622996899, -43877600967, -63296737871, 49070055822, 24896262267, -41589760144, -3115271726, 30535649366, -8156713427, -19682357142, 12824483629, 10534397674, -13466176135, -3560012015, 11811075769, -1256501781, -9027582520, 4155654670, 5901634065, -5476503550, -2948485328, 5591986562, 483247357, -4871461564, 1331522925, 3656553157, -2451177451, -2243361618, 2919736030, 870388062, -2843933906, 289093508, 2368256506, -1128730216, -1652411780, 1606105214, 850786681, -1734140674, -96384698, 1569276938, -511278226, -1196252359, 912109510, 712770224, -1086788004, -214016625, 1052136000, -219483891, -853438228, 531433646, 552988248, -693767814, -218792567, 707271722, -87332198, -596656029, 318067403, 403841780, -447055069, -177823286, 469762091, -34017848, -402162161, 195105222, 274185841, -284214796, -123071832, 298639770, -16146133, -251281156, 116769166, 166856562, -166582058, -73246168, 167637706, -4889010, -134848907, 53858575, 88123166, -71985346, -46115231, 69026867, 18221231, -58223424, -4228500, 50423674, -3837729, -47959343, 13621972]
def AP4 : List ℤ := raw_ints% [12839542822750700325877, -9849934607353079000232, 3323190101030927301149, 1770871657864445557608, -2535654616145224992398, 304406818949690275479, 1497505479458133415548, -1062726481778474627376, -491800484666134875565, 1098264098358287822769, -258495898618269253378, -729920226841980416167, 644977965363913071074, 223265409418136278925, -677923463760472580643, 215530625858254209995, 456367576568607842943, -463032318802179143515, -122482518557730816336, 485397955856567457641, -184656361268766195292, -325404122701844972617, 365722346672938573176, 73959666228255614483, -381106840958858113387, 165261090893623863922, 252226890676316291607, -309394541820689179323, -45425199107008435010, 319188554691573545021, -154856244826083440565, -206576093670553141081, 276006700485797290160, 25153544182433224033, -280263619585885188115, 151398849136302021069, 175273830215109268980, -256790602140574054129, -8040365746836473942, 254839586475936743512, -153570656056526156438, -151682681423431854899, 247047270591130352840, -8567287113657941887, -237700158165502263753, 160628854058272896356, 131970647064743537334, -244057674339906604898, 26357416805888254765, 225632005276167084309, -172239092080950515253, -113560462553362669753, 246116457017942053992, -46672232380331661773, -216360301291129582728, 188359213883630196452, 94371600154428219564, -252017601575211098575, 70827483976517118316, 207944086603989433850, -209159077829072715002, -72342827770054485218, 260695481003210189287, -100333802099265831757, -198288247690222465469, 234916002124988112269, 45001136549896051979, -270805473180172842603, 137063439733261691199, 184533980361509798113, -265721558609462141224, -8972120844425182231, 279951636029807569871, -183196040590963677565, -162123072320092953448, 300567299897104711294, -40402593628942959173, -283121850489388519640, 240237113137429958946, 123659024234299870443, -334922396962812556049, 108209531632463450236, 270261583313287522486, -305367566260539570661, -59422075276223670658, 356366103066623612811, -194657565619344587872, -226085654555013033980, 364115670089355490159, -34778970281582383870, -343694889399066732885, 283841485041002256528, 141630496260485783673, -389153277861466981630]
def DP4 : List ℤ := raw_ints% [2292250687323, -386118900081, -136839188935, 146456956407, -14005285340, -57115219898, 34529661378, 13884085593, -27343614841, 5741843488, 14599169218, -11703278364, -3698113585, 10303429334, -3018919591, -5913160106, 5567666340, 1370571653, -5066935215, 1802003715, 2974218383, -3136031779, -595858941, 2888589650, -1179807393, -1697819557, 1965552480, 272591528, -1810682063, 831011595, 1049343645, -1327905742, -114679245, 1211429634, -620711041, -681855859, 948247170, 28192270, -848722340, 485929287, 456119273, -706158780, 23283023, 614306973, -394837670, -308591572, 542972188, -55799154, -454591516, 330293315, 207295532, -427702239, 77221319, 340855504, -282570543, -134821424, 342889069, -91781441, -256656765, 245898900, 81015426, -278108908, 101965410, 191973032, -216673319, -39543622, 226714734, -109325458, -140236246, 192398102, 6189620, -184013933, 114732280, 96742756, -170891686, 21887431, 146138761, -118151196, -57946707, 149537618, -46033396, -109544472, 117930110, 21864615, -124933487, 65018665, 71948140, -110397936, 10046348, 94586502, -74420220, -35377326, 92605335, -32107977, -61300842, 70711724]
def AP5 : List ℤ := raw_ints% [45547106603715312893793, -33090537491025597079737, 7612915613906960997506, 8602625319738081927348, -6692104414255274688542, -2650564433566052841351, 5358745600445968699055, -194924323917913382595, -3838674279006635311323, 1638286279365890401744, 2342779731726826813590, -2214584715383274526227, -1029244383002682442799, 2218868046391559804849, -7417952198392115932, -1865265369204458463326, 729813043282668589028, 1320659677022724962438, -1143799474341866440547, -713443201737141962722, 1284051899754795644459, 138160169473806703458, -1202168259333317253075, 340052333693830120514, 958078353288004873068, -681249198282861053329, -614110777026778563406, 867038269280485009859, 230802999302079121180, -897698584308384451412, 136574238847587624671, 789609618738562705849, -441184388888721496332, -572636515855554396849, 647779748447041812995, 286790378993705481847, -735381867014426293052, 21887859070987548603, 699262808476400580344, -306479477326660461415, -551383278610991407182, 524706395737064538893, 319206815675107132119, -644597193384392235398, -42254875913549008033, 649053056962949377610, -232976666345291299986, -539046626616049800950, 459869912885097752632, 334093163219883333444, -598785328686118014973, -70329259128867065674, 624196440051612847054, -204781336501054052157, -529663430887804419068, 439588881605090360486, 330727177358215383093, -587642586244840004860, -63426947372846947152, 616379456013561548399, -220213297132612499060, -515337041836320130816, 461507117040883159764, 299917835116480261276, -605733596018810937751, -11921722552055807698, 615208682910368964521, -287227664443719383024, -478899343012419178318, 526666905503922741395, 220059946834036987930, -642943053210003366487, 105559421336483162699, 595513317196369452216, -416748372204175192763, -383441086478631059256, 626259889819115133839, 51034788293056146193, -662305603198948883749, 313256328408744031365, 496914999316502267765, -598411568512418164679, -161765988800096208898, 699987407903076117739, -245035064138634471456, -564532062673984874727, 585335800468104043340, 217965683183605413308, -723551340268661360046, 222735960046707169761, 592054463628338808472, -590610070418135603331, -227546769907664767789, 732890285110174729176]
def DP5 : List ℤ := raw_ints% [7700742221281, -884538805750, -664743978614, 386529473783, 121948356252, -204383848703, 6333399058, 108370129587, -40788612765, -52039025063, 44294014359, 18675883774, -36752787127, 112741851, 26126617237, -9456196264, -15880084678, 12799043934, 7447436559, -12530661161, -1262794437, 10308470068, -2739644910, -7261730618, 4863472917, 4133775285, -5508207128, -1385022930, 5092434236, -732904097, -4010976397, 2122598045, 2610746324, -2800005170, -1175794636, 2860806054, -80825001, -2451854384, 1020704760, 1744690622, -1577824823, -912419292, 1751799759, 109202556, -1595420685, 544777472, 1199254756, -973553362, -673113362, 1148257282, 128380431, -1084731260, 338819982, 834435406, -659457354, -472484400, 799532327, 82191492, -760771607, 258894847, 577116645, -492333967, -304795041, 586441790, 10995926, -540599216, 240463173, 381982897, -400239507, -159336399, 443548791, -69384857, -372958941, 248683827, 218010719, -339265855, -26342583, 325729017, -146792139, -221864786, 254570147, 65568215, -270328619, 90161736, 197911525, -195511294, -69364090, 219376919, -64340118, -162936265, 154851680, 56838014, -174403134, 51585403, 127553215, -121809179]
def AP6 : List ℤ := raw_ints% [26493447267419143953052, -19470496514503767050964, 4905359227000200496725, 4796188666891002077577, -4219435124547412982682, -1159422582761366568405, 3239061017082412840574, -547134163280321787158, -2144149867097779782158, 1335364659198891956121, 1099562519088698870232, -1542883994802775247487, -225887770292041035658, 1374356699297753298418, -408277707041930669633, -989164755568781569295, 781391597663014629412, 516840952214256691603, -909108966072605805919, -58700440665537585539, 833697177598972592470, -312659640995822511417, -613975011121873319913, 553278192285148083691, 316136768997530270209, -646641354983727006785, -5262579419927436355, 600844360884923002114, -262086179763787092174, -444187931253348842056, 444048985886212230083, 218984119853506882413, -517550409786438498480, 25693433615779196401, 480142924394236302136, -242040880506680978022, -348812834126466834845, 390902024868627288639, 156285125453873897100, -448034584623727461701, 55399614616414229129, 407590381686831810761, -242430743414852249118, -282929377106173416924, 367596880784837346628, 103528128311612924763, -407022227014537312007, 90542521641573146205, 355191986421471654865, -257039565135261482282, -225732493543579177634, 359815613302678032271, 49257603099854173009, -377154753559958916322, 133553152812520614191, 306185268520002918728, -280082400990284152014, -164769606515243091470, 356313112767477104414, -12916676270472755154, -344153720167647880487, 182928425825373035773, 247579282775002882272, -303260074233131311364, -91175185923727034828, 343122199914829718698, -83674893095393016830, -293310805226703592459, 230951808974511846724, 167705376415866465829, -310253166841306784083, -3025155086223681831, 301417329700288880143, -153618182650014674177, -208599120126359744193, 255243416180213424249, 64081990464495123498, -274283292810930872173, 85154942776468103881, 208606118515593567997, -188277237995560524296, -89214259496586851449, 215615772210318498027, -36408014646675098689, -165507006690872098676, 116992172119061506172, 73759068206571522813, -129432770623325143516, 11045564443949026264, 82962401099262522336, -44779078985630078005, -23599079522711167642, 23612084300696443668, -4104245966213863059]
def DP6 : List ℤ := raw_ints% [4531122367511, -569949913080, -370612158279, 243710488868, 53343233757, -123538567832, 17777252858, 60531783127, -33246736343, -24424046663, 30859296257, 4098787240, -22764507916, 6205214494, 13855148645, -10124500205, -6214680609, 10172871958, 612757689, -8135790185, 2857732852, 5264773026, -4457507369, -2396150636, 4616405752, 35424098, -3817103938, 1572749789, 2519774307, -2382918796, -1112372640, 2490005349, -117140692, -2075400896, 992328856, 1356962841, -1443478601, -547989062, 1492142433, -175295828, -1225649672, 692962919, 768907497, -950009160, -254479839, 951754282, -201436285, -751948198, 517869818, 432874633, -656814595, -85600075, 624019596, -210400555, -459329468, 400132115, 224181552, -461726565, 15942517, 404606016, -204858241, -264116600, 308191630, 88271378, -316476635, 73527215, 245555898, -184213327, -127447380, 224641616, 2086971, -198123465, 96208217, 124476137, -145122166, -34715351, 141576570, -41880117, -97752976, 84062845, 37952620, -87395018, 14060436, 60899035, -41014676, -24636681, 41189907, -3348957, -23964746, 12323420, 6187427, -5897970, 976671, -5352917, 5096659, 9212839]
def AP7 : List ℤ := raw_ints% [30167409197800602027392, -21891169344116506509430, 4974909555341647845417, 5756590721671292029470, -4420353324977311111144, -1828759770524203207768, 3596122507564467384035, -86161103865663041794, -2624270290719239160787, 1095915608739597766388, 1631745613673572454899, -1529495393323414995669, -727402627990271347107, 1562661872970884496213, -11136146573065906453, -1328537063901168220020, 541009010765795269679, 939732782598572520820, -851042220188246673719, -490927955115443469965, 955468103201537939153, 57817231384182943410, -886798193213250754951, 303625846550349792815, 689187105603813113760, -557051934114722428365, -412567344195812831037, 684812352084010599481, 107651968006456873821, -686522109681945698150, 178550495912495291491, 576902220657309744930, -406566468817353766917, -383068436583014782082, 547854293075366337817, 140866557589235795362, -587201753218999961145, 109344243893564237477, 524229243912338966821, -327735122437230933009, -373168676875943734521, 479950403612237324082, 161285630280462218756, -542068398928616292915, 74839394633820551103, 504135499865054448500, -294111929651862020682, -372560328645646807819, 457369023861885971316, 169678013741854131646, -533477652137722309428, 68478860068537494205, 505607111749545862532, -297792175812337168075, -374854624494060495508, 472666585120576889236, 162347148101995186723, -555021328146314158662, 93398114191602336847, 521635714975668105092, -341138238010096938938, -371525477022600939239, 526743154945528003576, 127934812157085407908, -602945499774415134836, 161823747522639399835, 542151212422222299739, -434759394839976769759, -344122196858765241992, 622223659350946434850, 42895369951472709461, -667698695874323494079, 297607990371204326769, 540722077950651035883, -591058666607708012742, -253649729752516755581, 750745280708078323411, -135876584985788152444, -710283570791490195777, 526591788634436609155, 453776160182939745480, -799655408190728403017, -28536901251332229306, 848120251930054084649, -448095808385069932927, -625813681366037429559, 821540822157311073951, 173357196651579617637, -944328028250922822289, 369043553804795560442, 749244327245508340783, -811134575981779426520, -284281433092273792849, 980221537997415096818]
def DP7 : List ℤ := raw_ints% [5094454935559, -578030912199, -444824559637, 255315329659, 84138399041, -137156979134, 2799510308, 74086127347, -27285144209, -36245170528, 30591510202, 13198893442, -25883548714, 169252880, 18608708405, -7009860174, -11299683349, 9523108736, 5124661349, -9324114589, -528453884, 7604203954, -2446173494, -5223676215, 3976822288, 2777122230, -4350544160, -646007395, 3894479457, -958163055, -2930487592, 1956046528, 1746473522, -2368080905, -577530332, 2284351037, -403774005, -1838126888, 1091494942, 1180782799, -1443240766, -461018103, 1473160759, -193413259, -1239202552, 687732192, 828861037, -968258932, -341858353, 1023020387, -125002677, -878646215, 492710622, 590548549, -709079480, -231932844, 755148631, -121029479, -643833336, 401060850, 416064671, -561927514, -130015264, 583742491, -149257131, -476401794, 363974772, 274481048, -472857679, -31058782, 460627030, -195619563, -338644205, 352698993, 144216053, -406703741, 70135299, 349325098, -246761288, -202603968, 340181249, 11566792, -327536144, 164878836, 219395404, -274407458, -55168153, 286315237, -106602929, -206195679, 212670861, 71009543, -233259618, 64447289, 175179579, -154149394]
def AP8 : List ℤ := raw_ints% [10500946989401061787128, -7880800440399371600552, 2303190282281625059585, 1726766496155357006686, -1905143709465002832277, -145402359521568762103, 1337158319811979777591, -562461944015758395317, -714216924530854081951, 803798530095594511509, 151426544219425226290, -735387722764246769049, 262556938985958611765, 481834872262784861431, -481943471970153304740, -159509112207726385381, 507875513144461298476, -132669053121952472276, -381277405408130150184, 325792613413977701433, 168330933053796573990, -388564342620416070294, 57513190361321388486, 327035154207623776273, -232438247520212315036, -177398619497889355139, 315376308506375363310, -6811394372856112266, -294451827404851106023, 169433703086263951758, 186786604749285269001, -266049840326980370926, -31190424576422679719, 273936252762307956155, -123158868716893558009, -196847203863517694391, 230704819075714634653, 62183382652669468312, -261182344021688999262, 86875764140448455742, 208068501639730163674, -204411412836969250094, -89366979447993610083, 254179333270993157875, -56893585472745909936, -221041066333112765947, 184598090722644955577, 114765294948109020408, -252118578660560346620, 31085354909622331626, 236480073421544948114, -170027822503000075958, -139787976720019823798, 254979999027275661326, -8278033802011202545, -255269926939852516734, 160415080943880442821, 165461243200024648434, -263418868867537579613, -11932775678896856787, 278501655911889917299, -156389083410111133264, -192434116535845310609, 278811181832722664825, 29051880479340290556, -307435629306208098960, 159720538710908008216, 220696571827695478471, -303351943013726854875, -41177507795580950341, 343196636187225632571, -173769038112388929108, -248759145198693353336, 339939538473020020091, 43984026288635503898, -385690813819372622705, 203862667883838446882, 271841175387415279533, -390989546374863269567, -29399570431553720744, 430714489046673661582, -256231615425149342336, -279047936458414900797, 454161388763221286982, -13831026557858079663, -464776432683705350577, 331765023623754979944, 253168624204603006239, -513885043011201680759, 91162309011382365700, 463915031987401042475, -412976623798983250861, -183915008488598126615, 539873869280786453903]
def DP8 : List ℤ := raw_ints% [1833999000630, -267605906203, -133431085062, 110039256699, 6689736915, -50999540584, 18275276656, 20163154005, -20012269771, -3363564071, 14708524864, -4764158015, -7980994868, 7324824662, 2234230897, -6580549052, 1595260182, 4266470104, -3400859122, -1642688965, 3551507587, -493169735, -2634771495, 1761759811, 1266457830, -2122898407, 43272105, 1766972413, -961157794, -1002360833, 1351452166, 150061370, -1248921516, 532349876, 807042018, -897495265, -229623733, 915794558, -289332607, -658371732, 614677853, 255446162, -690774486, 147034510, 543335379, -431652160, -255326384, 533739831, -62629141, -453484669, 310372176, 242924147, -421875940, 13041271, 382947880, -229172649, -225122577, 341350023, 14728130, -327421845, 175137309, 205287953, -283345155, -28126617, 283561346, -140350422, -184764230, 241961605, 31292768, -248494635, 119878496, 163510916, -212897826, -26246332, 219289833, -110439202, -140316025, 192292863, 13776659, -192307292, 109003440, 113105822, -175392900, 5089187, 162939572, -110814697, -80566863, 155807212, -26333394, -127671671, 108278079, 45939407, -128471746, 41693977, 89189973, -95445796]
def AP9 : List ℤ := raw_ints% [11377067889563009526014, -8542512382660134930095, 2506715941119983776305, 1859564843789757817300, -2063245649032316490093, -146773434551962355001, 1437649307187159630954, -610560054054549912788, -761186770092861132128, 861305798135997677229, 158826600281313223742, -782553647447784718799, 278672822701340514632, 511831759169675979929, -508446562914443977233, -172513126537318523867, 535958225895148911820, -133765178053351025833, -405554998283678984665, 337522924097064555746, 185383109075254516849, -407303134886466175568, 49975903695489002609, 348693699161674027623, -235534404344051074500, -197265385557728475870, 328444261508278977187, 6445695019110141189, -314548122109536334312, 166596925472715263909, 208783961060245120329, -275076574658427727425, -48801242566752308778, 292978956321098985495, -115671075172640923949, -220723709933694717020, 236539118210743646149, 83564699773784158424, -279566770581389867704, 75358178268414420195, 233892776398811072286, -207588941736798741018, -114388107382397468219, 272344798117175932141, -41627408167303753207, -249150428961723958105, 185552787295711638786, 143603617977121527004, -270640490709896351507, 12170433284466072308, 267480613376620857235, -169226684903425077063, -172865072398288699567, 274663749898216074783, 14258147075181240026, -290073767521020069915, 158492549575648312584, 203404854665397750465, -285425282269288000373, -38011287223571838161, 318387372768394290315, -154331703008915923738, -236018396410589654451, 304832262613846497472, 58339035609904874325, -354103765924152150009, 159154972107534745708, 270683644144728311634, -335837226324232309363, -72706214703647997308, 398738324684004720657, -177405992709073855810, -305486202502661572162, 382299835151472545080, 75459626692876568746, -452239900506393937529, 216069745569549182117, 334264604862472692315, -447459257785713785746, -56106496950651780990, 509255276450443071182, -283311503374515516714, -342947590396590280626, 528415778398762933632, 27190513760742326, -552438175216039782247, 380437376620067147710, 309253751625412087478, -605163385724107267392, 99931018379841814015, 550897245299990099530, -485059377507002180079, -219746922001522191001, 638607483750891770794]
def DP9 : List ℤ := raw_ints% [1987990850822, -291253395856, -143692708541, 119171071704, 6752817950, -54832291062, 19838060196, 21489166029, -21444035219, -3527937911, 15651892770, -5056584553, -8477855960, 7727632264, 2416377047, -6944417094, 1608440381, 4538134836, -3523308595, -1809095821, 3722781571, -428538272, -2809264409, 1785227053, 1408287690, -2210862962, -40948854, 1887568025, -945065418, -1120406174, 1397305227, 234789409, -1335740408, 499984152, 904931870, -920192042, -308578233, 980256640, -250974232, -740085073, 624232881, 326966439, -740142149, 107580942, 612430283, -433884561, -319485020, 572951071, -24520350, -512932678, 308909764, 300405666, -454443596, -22462383, 435159502, -226426077, -276747739, 369866923, 46915755, -374313684, 172833286, 251783491, -309789386, -56481016, 326605413, -139853444, -226612741, 267872734, 55252948, -288710098, 122387532, 200797959, -239427294, -45028584, 257127234, -117052183, -172537073, 220065274, 26291544, -227374527, 120523490, 139006114, -204069254, -10005, 193671695, -127072022, -98415057, 183482320, -28866347, -151609598, 127177411, 54889720, -151967011, 49817159, 104757583, -113341501]
def AP10 : List ℤ := raw_ints% [32364631542096924157784, -23323650424424628172499, 5015753901107549269723, 6254635765148739766885, -4453884509127845738266, -2175322085807517984007, 3644742229878369032631, 227130862370631153433, -2726573245551623928891, 797638651001238768548, 1821957947896513802484, -1274258223174420664904, -1016058964024247539955, 1397777018103994313624, 354599488305965873179, -1297284663456225145265, 147226663196259211128, 1064324491567801877089, -493422864173644995299, -764236300903527029702, 698103929288368595021, 443534676311066914011, -779808320024878931082, -135565674470145326023, 758765249258300938199, -135526076963720333772, -655914102707142099623, 352302225434375475837, 492845375887079000098, -502906688371006974591, -291766736655527826724, 580694593669896352292, 75332156292144724977, -584456936858950385412, 134113981127652940950, 518558411144812997963, -315528704615216931277, -393075642514775118026, 450696039126436624760, 223287606044232191599, -525621388768858328455, -28939122096356160527, 532171026586552788548, -167392648572611623447, -469042252507873821408, 342022218694670745792, 342687294515783883003, -472760717738330376033, -167015030718905477691, 541126862305752188375, -37076715336608202741, -535212253994474907310, 243823552051533087651, 451353112248310328644, -424654569343743734467, -296133537363954195500, 552074940980890658259, 86198896104793339162, -602711887896204369695, 151774041882565197396, 561997475579693631897, -384241166555020808315, -426604490720133153191, 573433602630019242815, 208077824449949015040, -683696088892754798119, 67709755744893927812, 685942518509064232660, -360200901618021373496, -565716059611971043429, 620021791939865807679, 326639068997477843923, -793334819905350860031, 3307492517769964179, 833862107345625437638, -374283207555670990094, -710682804978316106761, 715240616528908520802, 423328107057713157550, -948192986509717882332, -6082790480869669240, 999784493213796759456, -464230637314819846390, -828249561893823618198, 882472688978974895973, 438561290671897459270, -1130516881753046777097, 96820438675962129854, 1120212166048902292587, -651946820427447760877, -823092072714370734306, 1070287659784623284365, 303174780426672053621, -1227142557176504065707]
def DP10 : List ℤ := raw_ints% [5427818137632, -582776585297, -483309607099, 257252058401, 100083193346, -139011347061, -7379840346, 76974255817, -19858906512, -40470264460, 25486499406, 18436631215, -23152436343, -5389385329, 18170958625, -1907617623, -12797818654, 5521370711, 7977651695, -6812578055, -4053940611, 6686776716, 1092190151, -5751041993, 967527604, 4415166788, -2238140689, -2957509862, 2852872091, 1565720140, -2949751692, -362433241, 2664637614, -579702965, -2126006459, 1227479856, 1451505088, -1580294341, -743641057, 1663174680, 87021743, -1521155211, 454917279, 1212182309, -840716050, -801317665, 1051783855, 353573999, -1090233987, 71099952, 976987118, -423717618, -746784137, 669003724, 444250177, -788706871, -117280139, 781021183, -187328408, -660715102, 430304742, 455099982, -582758668, -201450824, 630602849, -59498252, -574261938, 287305852, 429914836, -448932398, -225339342, 521463856, -2071422, -497585677, 212803881, 385000561, -369185132, -208197316, 444323909, 2715870, -425318125, 188165477, 319862268, -324709733, -153749167, 377610284, -30811555, -339642373, 188323139, 226518936, -280618045, -75728839, 292018479, -68730458, -231148502, 169342815]
def AP11 : List ℤ := raw_ints% [15208416258496312610423, -11605276230968001167596, 3802031767104892848883, 2154878664962169314440, -2896993834052355941374, 226734704571755060083, 1740624493815528021869, -1085928237351257320140, -660521671047815276829, 1161556115656374027686, -126693341015751957341, -834592252969414279036, 550909669639359162807, 375939040916808806884, -652861639775134154941, 38241225585644431520, 528455365764549182466, -315682390692541879925, -285698823503933077773, 427970683670701150383, 20915768888035447710, -390756524792582076989, 192509526732980227935, 247776158269994160214, -309556637300036589454, -57396013303926018691, 316054421408028832761, -120761808478205975052, -227060292147581780674, 238519091167010511520, 80417015631937868344, -269487852287637331813, 74733117689371757073, 213747004051163110888, -191437949035364629873, -96084244537974595641, 237781679937551340403, -42700391392847853000, -204694842816719641353, 158034574768023116577, 107716891022051872987, -215126526956550239711, 19021709285199482481, 198585814406554489320, -133307119126480050103, -117009074215077331821, 198575180507169532875, -791219507545619437, -194672849302527242317, 114556375266171683880, 124821740903807628211, -186431842731205486717, -13595489484972488652, 192442141408242917881, -100195329377022017642, -131588740151952771570, 177623902061393464675, 25068253921933451335, -191491607447153915028, 89226673383536212684, 137502285412283112290, -171408631317574376030, -34176940651274087101, 191460325183593732168, -80975181734987902225, -142599983814916226523, 167204263840307027178, 41255378601324119428, -191978204055017390232, 74917987429574927129, 146822351562899861278, -164475916630934794250, -46543778338687022145, 192639804013541404861, -70550945112996347070, -150083517314208149374, 162658678759251060231, 50318071171107182153, -193032087512615936864, 67281642745756745952, 152389316616586690731, -161143530515898187248, -53041494248435008223, 192877251191548117450, -64412230376060157026, -154006132160386216412, 159415564905501289176, 55442993717865885057, -192312525793235925873, 61377546492001358559, 155517942461844240237, -157393667898681465527, -58218166628116568455, 191978808245024590313]
def DP11 : List ℤ := raw_ints% [2700749139710, -441755144712, -166512263866, 167327559899, -10431711895, -66387837699, 35283523050, 18647276086, -28919403894, 2814177474, 16692719398, -9996386797, -6226962242, 9922526848, -535641674, -6847202446, 3795878061, 3196951805, -4467467780, -204110452, 3571544299, -1650749535, -1996218298, 2346276693, 409753078, -2127463001, 767187652, 1362563363, -1353063052, -431545222, 1368916219, -359551185, -974508593, 827483798, 393930018, -925025895, 157679155, 717730074, -526321189, -340838501, 646898869, -54371567, -539689880, 344515937, 287617006, -464335277, 1760281, 412126128, -230802170, -239363702, 340316402, 23626300, -318404227, 157848409, 197405270, -253757564, -34107262, 248143441, -110128784, -161655240, 191957430, 36459825, -194573816, 78396230, 131526211, -146926558, -34538454, 153126939, -56933782, -106308055, 113467427, 30593511, -120646735, 42099454, 85332054, -88117628, -25972636, 94935256, -31528226, -68039450, 68552037, 21499180, -74487399, 23700765, 53990890, -53247287, -17643846, 58308135, -17729686, -42799294, 41266946, 14542087, -45684472, 13198199, 33992086, -31996234]
def AP12 : List ℤ := raw_ints% [6216371463688147405217, -5169493621707549728271, 2661417632293134874055, -132984905292470367392, -1176373757384204385412, 1009644008244754168694, -84598286890400660770, -606494611720311215321, 566769774444346079869, -35345315428521286916, -395367368620466053965, 362494737083171985263, 2884000090119955780, -293758848294162486318, 249493742855199418840, 29581227029583665248, -236213778648280743518, 179804476372217746939, 47765788672836739531, -199299633035923222035, 133096433791787307831, 60287447417900942953, -173230188182872197280, 99544133150244513130, 69238194067145933370, -153561432879907348156, 74136591884454244994, 75838268136487779578, -137904306600753037203, 53955917972874986943, 80990045310471027978, -125067947666441307534, 37436338616147171586, 85078051062481336731, -114130365382131930080, 23374029923801421420, 88592499080743788811, -104752915513782370638, 11251296158772853840, 91561385462622400595, -96373671809986970972, 344266002021401987, 94406381137447863431, -89029623025819614535, -9399638132442696835, 96931204470717863747, -82199125186657097245, -18626352052219824492, 99657832619252800842, -76213011423652555501, -27053479202580852216, 102157235342791933852, -70422230543236210723, -35461989700393591527, 105195910801624067496, -65508831964537959834, -43197328910007711708, 108022444588080110738, -60536753937806156854, -51370446388671066418, 111836808628904159938, -56709963193289846966, -58786503434431577387, 115378695298913591088, -52588566127351034370, -67139381387888887851, 120575143284777083931, -50229554821481642644, -74344339641614227231, 125314482937124015579, -47358594373914478538, -83032681365323104713, 132688086685330562989, -47437242682079168956, -89601778887541987476, 139122290878877689976, -46839422501031382937, -98067499647254907718, 149384700048309267109, -51164328900622488342, -102317917533012763860, 157348000207174495215, -54517137074640378081, -108311556172862852146, 169748824973631242141, -65029263791433737715, -106534554639938654386, 176428758343585046336, -72872141080473334775, -106029962560107995500, 186145567930531932359, -87697052058718195223, -95249225731617276293, 185440095976702794789]
def DP12 : List ℤ := raw_ints% [1203030860593, -309228066284, 10276039203, 67946209632, -46452153982, 3226599050, 19705967555, -16000553691, 879996617, 8782102784, -7250274500, -52330867, 4865749648, -3791934173, -414341793, 3060624733, -2162033384, -534496161, 2080433831, -1298846499, -551031846, 1485431174, -801981198, -524789139, 1096282934, -499037019, -481792908, 827548287, -306079311, -434620295, 635307086, -180111313, -387885165, 493324488, -95829781, -344645373, 386819668, -39450890, -304937684, 304946210, -1035230, -269850765, 241952763, 24292214, -238264110, 192209084, 41439348, -210977530, 153549973, 51878950, -186479855, 122380055, 58673465, -165726361, 98274280, 61712690, -146972733, 78446249, 63404412, -131481496, 63508463, 62713209, -117254962, 50913690, 61925592, -105952387, 42051514, 59299029, -95232502, 34290419, 57281971, -87216696, 29709064, 53467547, -79099898, 25374476, 50619416, -73469002, 23975640, 45683351, -66937382, 22097298, 41828914, -62459832, 22797714, 35584204, -56145629, 22094445, 30628104, -51228165, 22993234, 23791930, -44128480, 21593230, 18939807, -38297556]
def AP13 : List ℤ := raw_ints% [2467779796423076254060, -2197725340331291011172, 1495291849009523805270, -631992150398866527479, -84717858827462158380, 449003623291587469776, -434904386253403615593, 180760862939340924175, 103477447216680155630, -250472745433002574219, 209784046668627954357, -48802151357521551234, -109443917948600109602, 168009906533647038948, -108500530843292942682, -11338339915801591937, 105286504352469352453, -116554539300181464795, 49309017798772797650, 42165446075549325983, -94625239245619716516, 77810291722936673474, -10411573578443298674, -57380102665643023970, 80070515083172004634, -46484875649521867018, -15910403702262154760, 62599792392997609520, -63140590433424869645, 20483737978173829914, 33431175371246332107, -61171321809462570144, 45417244650811884000, 579908756602660356, -43759131599129968572, 54751167638722515295, -27600526204946557740, -17369610618398736546, 48617892713810249752, -45330922093592736231, 11110777904510377586, 29478916913928066027, -48442203344410414671, 33522867633190785520, 4018674487140399321, -37861807423887580901, 45010137724891113172, -21318551065661854738, -16251549383180873067, 41752336728942448912, -38104172532666541685, 8440778516153934984, 26534670210570142834, -43002850806930439073, 30210239768521320572, 2580933328014209857, -32812712348095636926, 40138482985547662096, -20059590855054092490, -13420290897968983465, 37618558122827243153, -36565919204445052739, 11519333970200579696, 20299451008646747788, -37575161172161597233, 29170492984928049957, -1232249803395596413, -27372429374989110924, 37895646646909143242, -24049967877928512127, -4288467802844053161, 28141330936291000905, -32184381546258093575, 14576075169431667462, 12463499512668375926, -31266865899004268567, 30426269367011966538, -11775921312578977036, -11634270162497804331, 24689130361950736313, -20036302033611314878, 2130983740524044788, 16694283741329215371, -24895331617740842750, 19002974074365256064, -4857477840703190179, -7406423073489288533, 10583080592595811613, -4679001867592416337, -4340181684164682670, 9782894076845829758, -9199217772384635028, 5439584683281724636, -3406353367827328116]
def DP13 : List ℤ := raw_ints% [511448818976, -173736809056, 48835438124, 4893221528, -20657959912, 16587358107, -5873205849, -2921285723, 6236050408, -4659830848, 976094153, 1985885883, -2782874962, 1649046849, 158815186, -1364198487, 1401493500, -551764798, -440153448, 923418134, -711191973, 89278180, 462285038, -606892442, 331857908, 107097996, -397690200, 378899606, -116199458, -179403126, 310731685, -218508536, -2643902, 189147306, -224471022, 107372449, 64140525, -170470948, 150970917, -35156798, -88644940, 138466970, -91103952, -10385773, 93067138, -105248777, 47428872, 34404839, -84120416, 73070249, -15407966, -46112065, 71150161, -47593420, -3871835, 46876990, -54611452, 25994120, 16564108, -44226444, 40949512, -12288780, -20629557, 36378442, -26905224, 1082808, 22915833, -30226580, 18276727, 3105103, -19413933, 21154991, -9128726, -7437272, 17777207, -16482925, 6078367, 5721859, -11569345, 8945895, -906542, -6766654, 9614345, -6992229, 1702916, 2473860, -3367896, 1418648, 1253716, -2692300, 2411937, -1358733, 810597, -1233168, 1986741, -2012731]
def AP14 : List ℤ := raw_ints% [7606039608613005870977, -6464507236674791988898, 3672201276458574953673, -702289450421010475190, -1089775678795549818124, 1266482259518315660560, -410508184231908509815, -462366958822845029273, 672620793607048499496, -252422466879783545448, -274737915852817418318, 431688645920947507407, -166527449718346724878, -196341491947668596173, 310995278774418292147, -117101390651050826884, -155812007031481504573, 241877226390797713130, -86736612153250116491, -131747356139243689707, 198554491441241460970, -67007420820874583127, -116133928054798128641, 169671680354704291275, -53591129452644912635, -105481517732930607674, 149686529673893324963, -44240037388663066198, -97947141929290449633, 135512965679032923944, -37581652949079451272, -92607420164298704031, 125479131431972693642, -32932234328167563612, -88762821015567076805, 118408274092478480701, -29704847738836076558, -86154700413389786981, 113764581077485017653, -27766518721813149908, -84355043368668459580, 110935734809758849006, -26759288472728670768, -83386377868596099185, 109879214505219618545, -26863026421641451676, -82821407660414985329, 110125336045423371937, -27746212145233236980, -82882937926176320867, 111966412904073607223, -29885645607998151973, -82980666748386123154, 114863704809805941351, -32856608550671407933, -83548797666577054988, 119445848497138125367, -37524357627907606252, -83649892198915204245, 124914517833923733767, -43253924289293546682, -83982971384526306019, 132315431604342912093, -51489179964554848409, -82975019687215190613, 140304952965330342083, -61200021729583940108, -81679842616502171289, 150465379645439943289, -74702904025033575384, -77391858829769566186, 160349876300918876053, -90169530715066992021, -71670312439511125788, 172124628313162198151, -111056147780823959244, -59950743995348357751, 181150890357501161377, -133727246949835380499, -44746968539303579920, 189979101023669672484, -162430077924935647937, -19318983155044968331, 190297223323384841783, -189427564182659235853, 10917601077587559781, 185407630626669730396, -218235499209031414801, 52576702993704291521, 164393564192311845987, -235302760260870248896, 93092472535761326672, 135797485064364875115, -245018516367959899142]
def DP14 : List ℤ := raw_ints% [1504402998311, -426670239930, 54267466739, 62944388430, -58268883343, 15656881082, 15023032543, -18988848042, 6284592860, 6102619505, -8634225166, 3021680125, 3252152406, -4726666135, 1640229461, 2018858024, -2908418349, 970577216, 1375274267, -1937631224, 612452912, 995836574, -1366966521, 406192608, 753037957, -1007587719, 281052518, 587769820, -768733379, 201676008, 470417491, -603697153, 150143603, 383674170, -485454966, 115558748, 318142292, -398897501, 92474113, 266916787, -333590667, 76488626, 226616308, -283969386, 66031316, 193664188, -245003543, 58739259, 166988191, -214711756, 54553853, 144204159, -190047195, 51762526, 125337266, -170643068, 51054735, 108397294, -154176811, 50851689, 94051012, -141153579, 52326486, 80332376, -129409404, 53777985, 68381276, -120015203, 56770328, 56036276, -110620985, 59268987, 44885786, -102710927, 63142505, 32477316, -93504499, 65768498, 20968461, -84822702, 69099347, 7830516, -73491016, 69700710, -3827452, -61929043, 69449954, -15940977, -47487174, 64756462, -24407857, -33920321, 58306130, -30785619, -20105049, 48411147]
def AP15 : List ℤ := raw_ints% [5020548015259021364663, -4174504595687876813543, 2175688631971467644877, -221804146766199736820, -729287942134808176461, 580965515963001534629, 25159747109861271601, -371195165058962099513, 232263951533748232217, 99545149222530163784, -236888249161362720236, 90302908416268543867, 119754701372689593308, -156960744043863436523, 15688788823960837776, 118271964583989446636, -99521123625753095186, -27524091363505963047, 106189493793109325396, -55071295662479108463, -52317946453981565819, 88350899932749912557, -19894884107857529942, -64773125108595326615, 67591956299155078682, 7540476902864268593, -68153033229197695618, 45671604728349242233, 28177272388965928311, -64816195790845825321, 24140435296037470425, 42412352814542109639, -56321689522209979547, 3948084676078529738, 50914440063885967143, -44318364369890333226, -13795725145156934582, 53948838535747829988, -29820676809276641092, -28688024730345246886, 52394691905627218164, -14319226653075331879, -39874956530816593600, 46519129447887191242, 1561012925399594376, -47516054792033176394, 37548629568394059598, 16362000205702674661, -50919959419131897432, 25638100091286257334, 29967923784106697365, -50872182484099384103, 12388982538802725501, 40865368956255854157, -46654026877309983967, -2388209504484828774, 49638087955374042029, -39794003474553860392, -16627170194259802287, 54553264050921997503, -29245054273814378073, -31230968145964789554, 57191681646786116496, -17471711344275685142, -43455589465648887259, 55243737711422964013, -2612740819093946250, -55418764238272513088, 51722940504049157427, 11544144613235052726, -63264980364478102665, 43167406549008075426, 28386912203514878390, -71062512632508768665, 34692829106900585333, 42150991281967703763, -73083147974259555692, 20773138006277715274, 58750518959360061347, -76363810028334455388, 9657233175598133600, 69361006442314493867, -72133638539177527513, -7485920160302542613, 83656861488960340593, -71561374694450652154, -18140982785541146334, 88552336771205994508, -61580196267962290965, -35550146241116392429, 98200567764766694458, -57727188450268129848, -43078422113027991248, 95598475053581898442]
def DP15 : List ℤ := raw_ints% [971479650388, -252791587588, 17139299401, 42122965671, -26729321806, -959598819, 12060717008, -6557074839, -2478387689, 5261883295, -1806152772, -2172977499, 2599859339, -238446279, -1656625594, 1289496379, 330959526, -1188253735, 574874047, 510554487, -807533933, 170596599, 521847212, -512311522, -53831851, 458759779, -290147123, -169088654, 367687128, -129545836, -215441837, 270971301, -17999984, -220075876, 181698198, 53668571, -199216144, 104561484, 95543113, -165787632, 43058806, 113978392, -126423449, -4034247, 116797996, -87801272, -36401687, 107798523, -51654298, -57467819, 92863096, -21529628, -67613602, 73499074, 3582716, -70914107, 54142761, 21546235, -67332832, 34382092, 34974997, -61011860, 17755832, 42071587, -50953720, 2295880, 46395851, -41255598, -8772951, 45807582, -29780011, -18658892, 44505133, -20702050, -23965528, 39591577, -10722453, -28894138, 35784135, -4311804, -29506853, 29237752, 2890992, -30781913, 25087717, 6059371, -28180364, 18670788, 10269112, -27025274, 15135455, 10760389, -22749209, 9765982, 12467258, -20203768]
def BsP : List Blk := [⟨(1 : ℚ), (0 : ℚ), (2682440649296263659772 / 45638135109346677424085 : ℚ), DP0⟩,
  ⟨(3276730368397 / 4398046511104 : ℚ), (-2846434036817249496802584327549855809799 / 9671406556917033397649408000000000000000 : ℚ), (469284375641376006464 / 9127627021869335484817 : ℚ), DP1⟩,
  ⟨(1305092809445 / 2199023255552 : ℚ), (-50459512470861903514431699337636266627633 / 96714065569170333976494080000000000000000 : ℚ), (14325786390716182021873 / 365105080874773419392680 : ℚ), DP2⟩,
  ⟨(8542441030865 / 17592186044416 : ℚ), (-8733377158418276106796407556106148303303 / 12089258196146291747061760000000000000000 : ℚ), (1276057819392731753977 / 28085006221136416876360 : ℚ), DP3⟩,
  ⟨(6896403054357 / 17592186044416 : ℚ), (-181136711433848873382792786417759206259407 / 193428131138340667952988160000000000000000 : ℚ), (3877642651548166445691 / 365105080874773419392680 : ℚ), DP4⟩,
  ⟨(2976343721197 / 8796093022208 : ℚ), (-3275016434406850332866121948892436228973 / 3022314549036572936765440000000000000000 : ℚ), (2751116697211811781621 / 73021016174954683878536 : ℚ), DP5⟩,
  ⟨(4805667573359 / 17592186044416 : ℚ), (-251003728701191018592854999347220598140897 / 193428131138340667952988160000000000000000 : ℚ), (8001228901129807608149 / 365105080874773419392680 : ℚ), DP6⟩,
  ⟨(511616124031 / 2199023255552 : ℚ), (-282055736375561776914842081200209473889673 / 193428131138340667952988160000000000000000 : ℚ), (1822158844858885818939 / 73021016174954683878536 : ℚ), DP7⟩,
  ⟨(3532845575111 / 17592186044416 : ℚ), (-15526003837186727201177233263846439039421 / 9671406556917033397649408000000000000000 : ℚ), (3171368364892012948109 / 365105080874773419392680 : ℚ), DP8⟩,
  ⟨(3132095659693 / 17592186044416 : ℚ), (-8345227062488155416624620250623650617991 / 4835703278458516698824704000000000000000 : ℚ), (3435963749422450522437 / 365105080874773419392680 : ℚ), DP9⟩,
  ⟨(2597141326789 / 17592186044416 : ℚ), (-370036424786292096417260675745534622838311 / 193428131138340667952988160000000000000000 : ℚ), (488718630413001614219 / 18255254043738670969634 : ℚ), DP10⟩,
  ⟨(2124937635887 / 17592186044416 : ℚ), (-408851434379226432243644719811994253074577 / 193428131138340667952988160000000000000000 : ℚ), (918612202327773411607 / 73021016174954683878536 : ℚ), DP11⟩,
  ⟨(108661779151 / 1099511627776 : ℚ), (-17906657758888708979164490742088108331339 / 7737125245533626718119526400000000000000 : ℚ), (375478589202600891417 / 73021016174954683878536 : ℚ), DP12⟩,
  ⟨(1295321823375 / 17592186044416 : ℚ), (-100919024941704288683653862844431468802141 / 38685626227668133590597632000000000000000 : ℚ), (745288856880723849763 / 365105080874773419392680 : ℚ), DP13⟩,
  ⟨(422113244307 / 8796093022208 : ℚ), (-587400478506638731396024528063810947569941 / 193428131138340667952988160000000000000000 : ℚ), (574270906738638952867 / 91276270218693354848170 : ℚ), DP14⟩,
  ⟨(349141633395 / 17592186044416 : ℚ), (-151637304143068635474707076414507938439379 / 38685626227668133590597632000000000000000 : ℚ), (1516244884017072869617 / 365105080874773419392680 : ℚ), DP15⟩]
def RPd : RadLit where
  CT := CTl
  hq := (365103327107 / 365105080874773419392680 : ℚ)
  Cq := Cql
  δc := dcL
  s := 1
  W := 48
  sh := 112
  Gs := (List.range 16).map (grp paT)
  As := [AP0, AP1, AP2, AP3, AP4, AP5, AP6, AP7, AP8, AP9, AP10, AP11, AP12, AP13, AP14, AP15]
  Bs := BsP
  ns := List.replicate 16 96
  Tls := [12136612605718089222387078469703275775138751, 24967422942625284341006484582797485455611758, 20899252474068709484365082565420061025533654, 10317047611981725485598512386957232487127876, 4933511864959644812927486571890929182365335, 11761572813188027757331495787281030906075048, 5356475335327404467022377888541959034191275, 11688810027134130841790846702897900814857938, 5767326481238594717174189600892432463514665, 6619386373499516263756333159020467830584811, 13483719099059077639734713371945715228664359, 3601058712153784159180050622176751074673809, 2382278170527396113877178993212632015803032, 619663739928225932603709386076352130530163, 2882340284688722915718467944333029421697902, 1275037952532855330774667571042191558309606]
  etas := [(0 : ℚ), (37404884055593501 / 316912650057057350374175801344 : ℚ), (62745745870815631 / 633825300114114700748351602688 : ℚ), (11711144910478457 / 79228162514264337593543950336 : ℚ), (319361129837801841 / 1267650600228229401496703205376 : ℚ), (4412697932863827 / 19807040628566084398385987584 : ℚ), (439808553525426143 / 1267650600228229401496703205376 : ℚ), (516309778300344375 / 1267650600228229401496703205376 : ℚ), (147397393848122127 / 316912650057057350374175801344 : ℚ), (69714487683429021 / 158456325028528675187087900672 : ℚ), (647189962250053657 / 1267650600228229401496703205376 : ℚ), (933573703881399087 / 1267650600228229401496703205376 : ℚ), (846941453063133933 / 1267650600228229401496703205376 : ℚ), (1267034594534226415 / 1267650600228229401496703205376 : ℚ), (2812784006849544619 / 1267650600228229401496703205376 : ℚ), (5428270652266624033 / 1267650600228229401496703205376 : ℚ)]
def AN0 : List ℤ := raw_ints% [128062015286317533651322, 56487193454092010637277, -24594258385096990187215, -3935104058344594455189, 14261593543174458789303, -7763633569621899955782, -3141142067184376103105, 7530402711933797747253, -3770834140719142567849, -2338213323417992131777, 4730115656326806734400, -2248056723853923549998, -1721233168238514106660, 3296514301028360664354, -1557736979841088814720, -1296277846338948557758, 2485675330536450281044, -1199881000768444429808, -1013078877534231016244, 1991015727112301693863, -990289792154754744389, -823832235928046606594, 1669517729296815901448, -854408419586783006068, -695293511476456846886, 1449748176059419781337, -759346933943912313374, -606557537453301255604, 1293849061847009656965, -689116816627600646314, -544862621375846530605, 1180524101757212232869, -635092253453438095991, -502396107664884467222, 1097071750454434468444, -592135572523973322923, -474290765764513397640, 1035499490526669593532, -556915592569721278299, -457452818349435470007, 990540639217882055048, -527113721189339603306, -449890486823283354997, 958588944436562425016, -501011333138579192118, -450327555945256962226, 937094415739838170648, -477253225889060813120, -457977627780882180393, 924201785394389757871, -454698204994616126685, -472410761232653529947, 918522333289056839312, -432314235428446752409, -493475996011198770324, 918980855769091578199, -409094010047314508651, -521259780898640112846, 924703139203002995850, -383974430395168798193, -556068641758784217360, 934918782801864479438, -355745913243269029530, -598426373111622633741, 948855541143670464098, -322937738540757146897, -649072231538738795395, 965595150236364840784, -283667338261717506020, -708932881058092095480, 983848888347128505876, -235451245953265300134, -779012188952621589371, 1001597283866306163481, -175007249510805719253, -860090402135834898054, 1015539974575566771976, -98160968295325857445, -952052904340479987086, 1020370368511135609124, -140987080036744329, -1052635134614917290167, 1008134243263082657389, 123209850869352968944, -1155575207872968613961, 968464820182838661295, 272733133383072737258, -1248973223410091018926, 891067389444764613926, 442094138117733376293, -1316053499226181896055, 771194981169229795144, 615487022816175420489, -1340697380005643367020]
def DN0 : List ℤ := raw_ints% [13145550014459, 2857587952310, -304074236734, -823735839480, -357192732375, 119803915483, 244674674191, 106454925524, -58214781514, -105067755135, -44963489595, 31232184628, 54602655873, 23675287478, -18156856223, -32206924758, -14427798643, 11336288706, 20783663340, 9663928567, -7529889174, -14315944052, -6883574809, 5269959563, 10349826480, 5111406127, -3853399175, -7764243203, -3909198624, 2923919258, 5996702920, 3055515131, -2290508473, -4742054039, -2427661040, 1845101103, 3823774910, 1952736396, -1523509089, -3134275253, -1585063800, 1285964894, 2605124408, 1294802486, -1106938624, -2191240587, -1061778653, 969547357, 1862033226, 871949428, -862348022, -1596212064, -715283454, 777425472, 1378626048, 584441046, -709213485, -1198271936, -473923720, 653744838, 1046998659, 379508332, -608157866, -918635761, -297859622, 570355960, 808383394, 226260639, -538752186, -712364704, -162431362, 512049503, 627281794, 104431056, -489016265, -550151852, -50667663, 468229856, 478146281, 62948, -447801306, -408624607, 47582497, 425199013, 339520750, -91097124, -397465736, -270166895, 127704520, 362184315, 202199124, -153740087, -319040692, -139532400, 166553881, 270764610]
def AN1 : List ℤ := raw_ints% [89395206150142350203013, 45164731058328650569065, -13705398636756911540090, -9240355476536286486957, 10897648683222293516011, 31316374217062973693, -7015713017331012941975, 3719064721042381557700, 2997648655124549252634, -4457022964331192435453, 270596800796692607929, 3334638667475581953144, -2205627346363880783284, -1377623451105449854724, 2666986286001302361277, -500739042930013636388, -1947821908066301727650, 1661302120143861122399, 628953723327002481967, -1857300222970652548962, 644736944428478954525, 1233958162727596272868, -1383647875838468102844, -207077980488401779980, 1393947476958342871812, -731134578768214515548, -797894804937782033575, 1205965864135400517309, -61068919863217554202, -1085450485871106041354, 782436936610036454579, 498948741176864793643, -1074215786255158876091, 246846830931627902295, 857600785347235540573, -812121415107462814133, -276315396106674576018, 966922463011111556539, -384162942252483371983, -676532126285653637624, 828001994203801545856, 100062739596116060094, -874102979139168275401, 490898212328450121245, 524867345184596975682, -834695371598685913107, 46118390565131079158, 790602748109754725962, -577252594092773357136, -392795646734335519143, 835153165434335220263, -171783383336897706509, -713493473032049730551, 649577534787682324796, 274476334332718740135, -831339458461541614587, 283021095587637930163, 641197592987118574607, -712024446894805543855, -166149527500681186268, 824915155452704168087, -383786741499308717846, -572839393363779217912, 767771840875772516367, 65612608711905774991, -817295176402302321461, 477012756023728380419, 508531463860350793275, -819194675304317369452, 28475601617441266900, 810454733209501254662, -564379659338981575708, -449037073397960594008, 868726217206727593939, -115689246728307258538, -806494329000965900277, 646792914013420264546, 397134222157178403730, -917564547928381557333, 193998546714332300201, 808573988443298893490, -721809483032674884581, -356557040171812651935, 965283984719088868882, -257111074092800842568, -817066539673440197586, 783164565192732950044, 331800277285508477227, -1003859287722287099175, 298507119330148653315, 826366394608339604386, -818959673241834510880, -317762682879918024293, 1019970577561965589408]
def DN1 : List ℤ := raw_ints% [10510616561246, 1592419718975, -714022805246, -629437640279, 1440817778, 267580985324, 120838284979, -84627022145, -110967042857, -6010634935, 66696266796, 40021632034, -22818617593, -40534228718, -7013810221, 25237951579, 19976091343, -7037952472, -19387844120, -6291786329, 11278471277, 11864639248, -1668331839, -10565389603, -5219607205, 5370884128, 7661380130, 366467743, -6157506889, -4198824324, 2534507655, 5168198118, 1125416278, -3706949219, -3329567772, 1074930989, 3570541451, 1347006565, -2253134754, -2619969396, 300894892, 2498531928, 1334097292, -1356455431, -2051743301, -107840243, 1758909265, 1222054732, -791384043, -1601526721, -313576813, 1239912027, 1074755408, -432411902, -1247149193, -404330402, 872397978, 922673316, -205071473, -969815568, -429795841, 611102797, 780257196, -63522935, -753827140, -419163008, 425735766, 653411536, 21639978, -586817094, -389350059, 295154830, 544067110, 69034570, -458543478, -350389279, 204988428, 451268111, 90907857, -361015656, -307064830, 144522399, 372783686, 94605158, -286444112, -261589189, 105590127, 304364798, 86227581, -227420046, -214722519, 79372692, 242718546, 72037570, -176869555, -170016474]
def AN2 : List ℤ := raw_ints% [65768366494850206803684, 34368888541816608449482, -9160722213901172445947, -8076770174854697599620, 7744393556618438392632, 1429306739104599927227, -5684491333467430942772, 1645542647878859181703, 3359506974453578353319, -2883126945697309853446, -1173079700697678503421, 2884239966204401665530, -533653048858774003039, -2095511726934511151927, 1551161126391627700218, 945120874729430127021, -1836124345033765608539, 179753984570218585725, 1504904308679628736362, -987289910054876074580, -789818103294345108988, 1323745086915982130477, -28529994465730837638, -1185587198568885611084, 694397369385033863993, 696832417587748952966, -1036631081072432005367, -58437522288041504244, 1000979875459842820400, -515607288569561193831, -648863569208740831940, 858300607160268232218, 125997026345525501093, -890401626481157442626, 388337581983476790355, 633134920937541035914, -735861260546468848376, -191759194015310975845, 822826704228557082430, -282657028025933006102, -641268432770318967737, 641134752320487644118, 264321631133526079372, -779892733386423400061, 181342049100142000983, 667428954617801959926, -555990484364745299877, -348738760430394093603, 748419404187296180597, -72229139041875797715, -706278282258441506197, 466073741439263078988, 448184021827745576275, -716106888130555236958, -54621202019766705857, 751195089482689525495, -357363887710337013992, -563407153282818253741, 668854449744136851969, 207984827788610100388, -791549779656747366758, 214794137212548875120, 691157445767826722845, -587842570002313899412, -393943241003775651544, 809677906383929751469, -21635034523814195800, -819504307571921402611, 447956593721423839542, 612259226007208802208, -775429900917986193738, -236699288333015546516, 920903744066032329854, -217113185532339779066, -845234622978457969229, 642442179127563470706, 562577673318423277070, -939353847886793736877, -132975117431017698400, 1039281737885162310828, -350361670299797741660, -916171673392965155511, 785433508078984000898, 593502220488158981309, -1079904865144848219506, -133912472577361334244, 1173551334353557089533, -370706895183244341811, -1044771571679245841932, 822996608051297661145, 718621215159107576704, -1133902162074855363467, -255418220364182182099, 1245164804731547565734]
def DN2 : List ℤ := raw_ints% [7998236691207, 1064377263303, -624109982805, -447308676153, 65760184965, 216807869467, 53466278848, -94842693001, -71781562246, 26057048009, 57687820922, 9683261313, -34709543250, -23575344278, 13238229661, 23790684929, 2161426252, -16839784243, -10306046724, 7707588013, 12099130580, 244641789, -9551729578, -5263167278, 4974722318, 6977894060, -371247716, -6006768041, -2924919628, 3482023929, 4359905698, -606188815, -4059490985, -1678575534, 2595751803, 2862671006, -708106573, -2885111631, -941366047, 2029105823, 1927932144, -755535733, -2119487824, -468656337, 1640590007, 1300091959, -775863528, -1584418129, -145523477, 1354390533, 850780299, -778856122, -1184831233, 86050616, 1126919142, 510538212, -766558183, -866731692, 256707049, 930589398, 240544074, -737324028, -597401951, 381396675, 746801397, 19011244, -686078088, -357302135, 465285226, 561457046, -163292352, -605315696, -135973960, 504371931, 365269364, -304767076, -484865465, 65398592, 487008163, 156431012, -389748411, -318357858, 229205030, 397355776, -46946531, -391984464, -117971536, 316769185, 237733047, -197768049, -297297091, 63799914, 296307165, 57903929, -244887236, -147849000]
def AN3 : List ℤ := raw_ints% [75034584808517162235642, 39541555005716793473170, -10132092825281877949537, -9550343390938724677514, 8653012414487663508998, 2023250480793552049694, -6485091121236859393242, 1507666078913608315660, 4006535159034657269250, -3028347459557304390788, -1628003788940593861268, 3194234137324485948117, -292142717231055396154, -2466328155564867317679, 1517614834944316927923, 1283216048343002543253, -1973615254379296003116, -51517099018469471053, 1748214656370528347432, -905342174051887132883, -1057245284251070361091, 1393607938690293572164, 182962887140652586612, -1369851366802421258667, 597567672343753210970, 928594867274640296663, -1076615751934084809699, -260248143856073346531, 1157635953715157143508, -409153974784514485981, -866116251224146761306, 880892780017642798821, 329103697276647751409, -1033472767574447155865, 269347072023867841430, 848163523877680184059, -743625402684744458309, -405286152161102902858, 958117549849478959902, -145545080413824108818, -861500928472850389713, 631986435306992281894, 496120010895161411247, -908736736761520772090, 18910167923559076783, 897439162649045686936, -524620072588670030944, -606139281347455226059, 868717923924962539348, 124456838187368562006, -948331271656966664931, 403829422533431452501, 738211856759267277448, -821987308313899206130, -296578256460536374355, 1004641076827253947436, -251510828917963273670, -892321297147785063149, 749308615741355713324, 508353291174288532605, -1051144707586073239044, 47422249356689815287, 1062818745328876654741, -624538886079144177915, -767286494211552958813, 1062318446634345215529, 231143824831090736476, -1231893969665055987889, 412155256415366192459, 1071715154013942032546, -994938303946648385317, -604176389940653105564, 1359034218877299704388, -66919171604736636837, -1395223951202745090972, 782097115023166158937, 1073613243188129660197, -1363199347144057472037, -451304133109172104654, 1659065925903267591614, -337428679172853444329, -1580936111396903450632, 1114537480708434535113, 1128041090656174847960, -1697255893953626434637, -386490863429857920860, 1944899975208985559024, -486010249030103959895, -1788982954277107607932, 1300153872749645277282, 1254469388761577909114, -1874337921143373421653, -450286420677428628499, 2081652144744640157204]
def DN3 : List ℤ := raw_ints% [9202005927230, 1177240067005, -737976260369, -499789621945, 93086614795, 247342938323, 48986451423, -113109032657, -75397135043, 36162055197, 63888029102, 5300998987, -40851655795, -23065490494, 17973900701, 25572156273, -619460039, -19562411679, -9450616938, 10317326288, 12737682348, -1568888075, -11036261047, -4529249041, 6629286317, 7247043618, -1653330346, -6946843608, -2321034862, 4647876157, 4474667056, -1583362609, -4711776414, -1164243242, 3477334646, 2892875320, -1496594672, -3359487572, -484725952, 2725966945, 1900422584, -1418107154, -2469642768, -48871016, 2205972204, 1226737430, -1348520481, -1839092385, 250749102, 1818562073, 737158278, -1282867742, -1360015176, 467231421, 1507130805, 359314114, -1214070833, -970987821, 627439390, 1235783455, 53107320, -1133810832, -634695016, 742849445, 979822834, -203111845, -1031325219, -328746033, 814447879, 720394095, -416804733, -893301552, -41910236, 832563858, 444672105, -581612077, -703641430, 221956225, 777439475, 150656634, -672545720, -451752773, 435638964, 624512820, -135494512, -649626949, -154664983, 542410119, 375565998, -345236069, -491431474, 112475277, 495362898, 102081022, -404798093, -258094307]
def AN4 : List ℤ := raw_ints% [17917354285551642731534, 10366788083262305911299, -1438631067814624199951, -3166253694741935457006, 1375779432285517268113, 1567826263413653925256, -1274520695277542169019, -790527368375951351988, 1139938065136038329064, 309404331479083772849, -978771594762017503698, 15200375456880178796, 799064424711545006160, -235584868406717707729, -609638953466931803698, 376423076353489981573, 419618995910220623843, -452244383182890390074, -237825976469313256545, 473863730638697670313, 72353583017707862508, -450843396057641341802, 69976176733234918400, 392606405658738498974, -183850587822883473011, -308591194085310345485, 265861114469860231929, 208332921373221173359, -314463988945335632084, -101015435949096018849, 330194597470882656651, -4648018926807111648, -315315668730352211406, 101035672929816294998, 273886433472799557740, -181631677531237870438, -211116903061958060632, 241653718037413222777, 133389330829545268345, -277797083548523791071, -47373992507700175348, 288815835303996028876, -39855146879903562728, -274902985680132466185, 121881096576850062928, 238260273658911927061, -192571261385207452891, -182069443301277083771, 247281931101758655777, 111165528276235916645, -282065246087215679111, -30576647180216907357, 295047088399990505659, -53516506232757472448, -285058398186933065735, 135706738973725666013, 253301045531768968850, -209879498284304935806, -201251308534765310545, 271688263939540194821, 132823503800787090418, -316277028238979237215, -51375639888208075710, 341473270041799240885, -37321290408976386424, -344397585710053428408, 129200383928078086194, 325662412257283250451, -217710403357930306873, -284487792355556794559, 299389357307686774956, 224353155917550701647, -367914419529269733612, -146123928329466512106, 421638704040149427574, 55803403184064721197, -455173376644925891215, 44993193667531952356, 469610172764280303338, -148329852756146042779, -460761406522241310258, 252960596641817608471, 432962196754885569588, -349690939341155536297, -383037316379559053218, 438731743896105398481, 318524895040972050365, -510348607675615964009, -236735683809818896524, 567048883175670958590, 147727709529223953482, -599478586178560499800, -48764733594664357048, 612881932108254083018]
def DN4 : List ℤ := raw_ints% [2412531458986, 167153436498, -244663460295, -79463688414, 72133253314, 48610526487, -25685482397, -32181744755, 7703277274, 21740976695, 304023433, -14499213764, -3902170088, 9265606240, 5272526793, -5437008310, -5437948342, 2661257667, 4946532622, -706076003, -4120742864, -600038571, 3163048843, 1393490874, -2203048340, -1789595861, 1323518145, 1887063151, -573036957, -1771937191, -23610521, 1517026529, 460638650, -1183864472, -744660797, 821293727, 892351403, -467708581, -925180401, 149901100, 868487210, 113921768, -747094448, -314986781, 585661472, 450296103, -405062633, -523500557, 223970468, 540900815, -55815222, -512734100, -88545480, 449082957, 203582962, -361871660, -285556983, 260790501, 335333559, -156154607, -354192932, 54807329, 347026241, 36132657, -317652979, -113531601, 272640232, 173651628, -216195954, -216775578, 154775093, 241832410, -91514705, -251602007, 31727794, 246582588, 23224097, -230959334, -69507475, 205722770, 107611917, -175491517, -135047385, 140940276, 153808923, -106392287, -162410276, 71777000, 163799289, -40655384, -157176912, 12180751, 145845198, 11055083, -129468537, -30393473]
def AN5 : List ℤ := raw_ints% [62061542435968808974389, 32939915802852854159686, -8182429215519538132076, -8165979825730244938237, 7080954358411509258634, 1986911952201323577466, -5449424144544472295685, 965510760938009384732, 3551229861715337499021, -2337263431977708634967, -1678802151254663109616, 2642265562316681410938, 97544302092951873545, -2215180743788495150430, 1002528419692695389106, 1368399120487036130438, -1537500692919374111517, -399274062075524921399, 1536825930736959651586, -440558017176632242080, -1126698381728712222011, 978649125958707126608, 494422824209699902378, -1141989264503072691515, 157388032896419525814, 957183630989660427846, -655986563452194090628, -530325340295809455143, 893078361715149981502, 11888048102295466836, -841634826511371465261, 444768524639743963412, 552484025546655559962, -721271518299500769760, -132803785297160160202, 760145645304164804360, -286868596374780032736, -573326806942395031377, 588564160286384881104, 232765801693644955150, -696505670498984859887, 153568512501205291009, 593846557181993135684, -472960070287011866711, -322804194217356876507, 638531008770338652218, -30372195835321196387, -610892713201283455007, 361392916726848346957, 406354170197410360345, -576947886000435891460, -89564333707164676583, 619792855071431464851, -245948755645141656143, -482621857481404498498, 504683142514861220819, 208590547622285867669, -614971958444983096064, 122421949364208604522, 548291600085223867755, -416182569877987678789, -325490974268877047192, 590724440291120587420, 10642158815436901189, -597845522228908125244, 307922832104567989961, 436484153509688893169, -541203020626708283709, -151458961899501164544, 624769316871862324312, -178107367496052170208, -534834259010980512752, 461860381384224108227, 295833398690591019981, -621197774691621007294, 28145178429409240562, 612302717208795426663, -348799014061799108339, -435657668257950759816, 579824895041226381137, 138407467691530433324, -657299509140107482705, 201364136167785106963, 560064688197659683418, -492017797380998579648, -311590995184304278415, 656893556195538475538, -21926000296861158099, -650126285518040840762, 354068076533435110703, 474034280513303383739, -595729463798051391980, -172865035101667412176, 684650868707467122693]
def DN5 : List ℤ := raw_ints% [7665689941037, 950710152783, -631003410805, -408989070197, 91414735488, 207842350228, 31370969109, -100255247604, -58191131951, 37290414476, 52848079346, -1769964529, -36691711549, -15236942340, 19167052924, 19921414724, -4801014240, -17196985179, -4598863478, 10995097358, 8944927300, -4239625232, -9200481119, -1192918610, 6833382965, 4415654545, -3369103676, -5359263151, 67438118, 4516500455, 2259288655, -2658075722, -3288398335, 574039688, 3116475437, 1115985386, -2117116117, -2063707091, 775207409, 2203887856, 461790084, -1697448263, -1285347417, 834247941, 1569556707, 71020365, -1359095774, -765075686, 818701043, 1106380834, -163492521, -1077078691, -406933340, 760325788, 757109706, -297997221, -836716013, -158639871, 676733588, 489287089, -364511464, -630182496, 10815219, 578804941, 284010715, -383549514, -453087959, 120807710, 474792246, 128960253, -368967497, -303583670, 185274968, 370683728, 16002329, -331704790, -180039286, 214261126, 271706359, -61796773, -279621655, -81618437, 216291767, 181040126, -109236399, -219412701, -6977599, 197114833, 102277071, -130456537, -156193932, 43179278, 162923781, 39188922, -128658845, -97527728]
def AN6 : List ℤ := raw_ints% [36330417821871980620389, 19585004548309488182759, -4504295667711839024025, -5095646158733430893111, 3989773049613543568515, 1536315467773916317582, -3211383368807779993872, 211070769819913096789, 2274296243231967359359, -1119773976714579586426, -1301074255853132555383, 1467002436805562457723, 412235685087826664231, -1404776894604570962579, 292349314611759672042, 1065242189504192786444, -748010198708900706792, -579282976567904351974, 933451703472380564351, 70828500399753354169, -871241523194861278217, 355850183580188945673, 620897155344259285757, -628270098909963433205, -265913094685601634476, 713441100367062277673, -102571189297560483669, -618949850759741274306, 402612632860535999909, 387338360920783800861, -575510906216603192819, -84617940397618922446, 594906843176551795079, -214514517995353861837, -469125421277702090054, 442308068000989913411, 237022374992089856059, -551061780725432346186, 42089967988258644586, 521863140870472547941, -301705857917544502315, -366847406723571437767, 482572471400326453853, 125520307556704416650, -544659005589386738780, 144806785918168080144, 475323405249752657216, -381364064063712356010, -291029188181949273742, 529758215764813243005, 33766253455242116237, -555026841600246553909, 238606308639678218448, 449482994741795443007, -464161988270786061206, -233739735673627856905, 590709090499519838402, -46773436619970085225, -586120437505358926099, 331991214582755153017, 446294845378398834947, -558573568090119632188, -195389981999605179216, 674258095612090159206, -117284067817823227335, -647489211821496453991, 428383872318111697019, 476119547764808633043, -671246171692029158817, -186632641384550502043, 791481727668211825253, -167973407025603314116, -755626368844600447402, 520803047927515283419, 561476605962860560203, -800508710626754389693, -235808273336241469597, 949039082964483604253, -165733063003782755681, -928626982326399609556, 573540265708555398071, 734947615252026441128, -911162373163197466212, -392542388214641374619, 1116262747150070609893, -42000011155604724639, -1144959483091027035663, 498075518004318796210, 988896453549852027266, -894824899195927518456, -667748807470895892155, 1165864347756993647418, 236315227466311509493, -1260803156288257534976]
def DN6 : List ℤ := raw_ints% [4557770373783, 523350646811, -393751904246, -230445429707, 70683490507, 122482935655, 6858022580, -64205962968, -27879148898, 28900128719, 29341585602, -7480114412, -23268380584, -4443275186, 14920758949, 9691977021, -6965505861, -10445265654, 739359155, 8502173719, 3252497690, -5324129707, -5061682594, 2015481567, 5093292555, 690439352, -3932126298, -2416033284, 2197279983, 3088388441, -429833368, -2862177662, -978007818, 2027778126, 1813392260, -922072023, -2034898357, -147581813, 1738022384, 954659674, -1103133008, -1379382929, 341122249, 1407604555, 355945849, -1111465313, -848447324, 616114332, 1067329034, -64751665, -1013157063, -414651070, 743689942, 731243983, -350648968, -843900499, -63638810, 759521235, 409762991, -524688735, -625536451, 208441259, 685222748, 113548727, -597207661, -376431595, 398600941, 535403861, -141831119, -573079518, -115880250, 496677860, 326169285, -335046664, -455140272, 127745200, 489864683, 81509302, -435155266, -256076770, 312653920, 369319233, -151596215, -410733820, -14724206, 382434338, 158504560, -299828147, -258481565, 183767715, 305677235, -59028253, -300028566, -53573235, 251790063, 137382519]
def AN7 : List ℤ := raw_ints% [41390845343580658862267, 21674876650323161705047, -5753695017458595688908, -5154582013990112476786, 4910675842414879790687, 975299114553076054184, -3672086701461049272061, 994224309707863184834, 2250771683845606235417, -1839016711944280667506, -879704443802790624470, 1916022952756487710925, -235032374490858395203, -1478955286340005736023, 953803699657648552753, 773552379391205858081, -1227008742720529352615, -32252603426045342342, 1098056617967316140372, -555214124876341634354, -685905370823173876257, 869782462308609338044, 152123111273516457420, -877440227159223287435, 339292381214150821600, 625331509372546626417, -659556731373806331584, -220412493639924775754, 741673405289887585128, -203622910773238558190, -590116390703124249249, 522986051974156266408, 272496305689852120653, -654821138236573904608, 103949148859221656022, 575671005046676723283, -424040687642523516957, -323193661313000822925, 596477446868109736654, -17975216119364724667, -577239636167661331928, 342269930305963180096, 379473998744397903859, -553267548898166135102, -67226938376309176161, 590441447320869596243, -263954648228398772955, -444805605032807242536, 514911190425422056328, 160620305605146390253, -610489679185327283393, 178169406996196990006, 520828252436990075483, -471402765561688411749, -269119559494970555313, 631368801484428597764, -74196359102691102346, -606858600719151370626, 411408618555221047684, 398618131750174591409, -643601819945201319752, -59134929652594636559, 699019618953328900626, -319756868508397541155, -552360135878577712281, 632350060516692241726, 234289043998004182498, -786050763559314154639, 176802153791547542248, 728565420594159502307, -572488400732100307243, -461204988746659984335, 844460786440445015757, 42810669265261602490, -910498948700327126013, 426591941076097836300, 740009979148509417102, -826997919768781531860, -360022364687154166852, 1052647671422373781308, -145528828039081123277, -1034776611426493806974, 660356581920134052270, 765478491641804271547, -1058303513644125515676, -295115336348757405807, 1241108489340821159381, -271722002704354519046, -1155774711597345713470, 808722689657212161401, 816646514900906360536, -1189639380491981581300, -293794039203162618909, 1328259612468914301899]
def DN7 : List ℤ := raw_ints% [5044119872863, 668517395634, -398306008773, -283635883692, 44871998721, 140054271796, 32303917646, -63541837969, -45786222760, 19540446324, 38322466326, 4264718255, -24497053305, -14496398995, 10835083984, 15898366841, -387816849, -12287184259, -5795726923, 6693536134, 7949877730, -1304440146, -7069131466, -2571658012, 4464273672, 4439686482, -1400258457, -4450698977, -1155105178, 3166766468, 2656609874, -1311016756, -2985439860, -449316539, 2360158948, 1649616642, -1193452846, -2091453778, -59864983, 1826505480, 1029227004, -1084686730, -1503596307, 173739796, 1451348988, 617214368, -989590160, -1090076794, 323609357, 1170702063, 325233987, -905097579, -779957195, 423972802, 947159530, 105998613, -825677174, -533121800, 491997832, 756653650, -66224140, -745711364, -324956693, 534768204, 583244158, -205875628, -658071227, -141022117, 553671896, 414515414, -318172682, -555069270, 26811527, 543316732, 242544733, -400888070, -426870802, 177062870, 493271449, 64976348, -440204115, -267660731, 295620665, 389407463, -103460424, -414549608, -86471178, 350424747, 233609844, -224745088, -311910797, 73385659, 316080923, 66603820, -256924724, -168016708]
def AN8 : List ℤ := raw_ints% [14706378963776832265619, 8054350044167967851084, -1705549228091661499974, -2199914955790181961444, 1550877149718460679590, 790489040460475957199, -1311460210716604386670, -84309724398746799191, 1012463458542460546133, -319748487156465673448, -684636903564968401461, 528946333839490892457, 360598172316663990314, -591394935624742740965, -70881329086872379153, 542080031959643207809, -159571869078105100750, -414446267480861009728, 314245426229215130131, 242458926583109873629, -386579633085174961366, -59044990372289178806, 380376635114900099569, -106427526456512832284, -308623141287085598377, 231015916722000628570, 191462965457820741667, -300119548313935067027, -52959902266216786126, 308790170606037476414, -82092509853603037615, -261338174149492653276, 191835674649171899718, 170335847650769202640, -259844416729106132118, -53914251008971701270, 277501160292027291780, -66774153710611724844, -244332136454005109131, 171324906787054833113, 168204854064278640582, -242484723117294424591, -63141226986679927900, 269312038700769617346, -52258982659704513016, -247787353841766168191, 158672338620205821450, 182214520033128680733, -237935786926422976282, -83234818612239628357, 277044255610354934313, -32514365690455558261, -268572253947407328046, 146597027961307816871, 213518162706743891244, -239660931715581508615, -119060192063476611498, 296602923971749703450, -56798399228413118, -306186880629843077324, 126556763841219461925, 265875240808714348512, -239763147201219797859, -178610828140927224598, 322591340143354004340, 56807355309959305607, -359368986341343082144, 84413714196512376085, 343669854965555302003, -223310320015983474274, -272845695125475931351, 341591477800131131023, 156189988118004607312, -418667374011055549408, -4765098062228132690, 444344360212717707172, -159382303924623474128, -408809022142877876641, 318625061202906877265, 317598337353971122318, -447500573402232660080, -175218882854237864714, 533150421616864801651, 2981608018513266787, -557417280782780297746, 184799632936724075741, 521841682277540577029, -358634392108551726746, -422057387957559875910, 504643686752802673976, 276806780184534007988, -596633822425607014319, -94532794921013615796, 631690851163160196592]
def DN8 : List ℤ := raw_ints% [1874387004651, 198166452102, -169992318156, -89577163098, 36369174013, 50019408509, -2739356067, -28582992000, -7960816977, 15207506066, 10579480813, -6543139479, -9795720937, 1077290880, 7592870023, 2067574601, -4983450269, -3516386489, 2530961777, 3772509814, -539675695, -3261690806, -857437525, 2339201284, 1649234461, -1288798218, -1906629377, 317806437, 1751694459, 440536496, -1327518337, -922947499, 776589818, 1123168348, -221039797, -1079543888, -246576011, 856711972, 570583549, -532234914, -729166670, 180482592, 731900122, 135056946, -609079744, -371029069, 405385395, 503714591, -167697142, -531272343, -59352372, 466726018, 242551412, -336377980, -359531759, 170092109, 403550783, 73601, -377913772, -148787084, 297748880, 255778376, -181515363, -312317238, 52395912, 315786492, 70670036, -274120249, -169704251, 197556398, 235654598, -102664640, -262203608, 2843449, 252638116, 86342706, -211014600, -156703232, 148826807, 199802015, -74539831, -216100567, 1151469, 205104156, 64786359, -174303268, -114129655, 127965555, 145772753, -76178571, -156431045, 23612975, 150321086, 21430813, -128854158, -56950178]
def AN9 : List ℤ := raw_ints% [16044590121307007262143, 8713713768177999827241, -1931242288615831996390, -2322259086161745872518, 1732955559759547539853, 766836107318949195940, -1429894821122475160057, 5215205407121843747, 1058922846902707980936, -427309031562475447104, -663814114550755482171, 618936866325006176837, 288980906715985098532, -639673414784656531381, 26764253926854001009, 537572694496156683862, -255317430071593350038, -359637241121081584398, 382668860828189541323, 151751199890360837425, -409873909574874116042, 44967486131242260239, 351841728497398661345, -198190152066463553369, -233868237182176685431, 287714403450876625709, 87029292221456793052, -306767362535270738954, 57319963453522965824, 261624350721125529784, -172323349702524865667, -168878424386952461916, 239752427756249624516, 51795293354926341991, -251873101486889394619, 64669387898373994670, 212039614170831379448, -158025189366792250374, -132632051806067862320, 212423403663685112091, 32485051964548694085, -220390294986969045981, 67618795532187546578, 184057690430356283470, -148230639431356489612, -113282834153534491023, 195439440907890715212, 24070915059242197328, -202085897475556095910, 65804839025641398331, 169632519828984353527, -139038425136971405613, -106007275850364758808, 183294574354848520807, 25160515534590016681, -191504440789798199900, 57669234810444505873, 164669666643979615975, -126782916798701799838, -108859536974574268613, 171334789943568978498, 36341343754008195217, -184096570026204791676, 40212083829568536820, 165816436118156880085, -106444018375607057172, -120497584296172574479, 153306728680664664301, 58975963003257812724, -173236488008579434470, 9096673383265067131, 167227681979494108678, -70563594290009278018, -136880796824937724877, 118996583484846226385, 92074788329447339943, -146384289670495582402, -38675033522022854547, 155014680868523622447, -11068900731116293441, -143746458210146946943, 54592122221996192849, 122439712069829777358, -83314237816266543110, -92389657391761458789, 102233819289615738111, 65369835924190080915, -107419165364653030919, -38941836168005394113, 109666466745402184710, 21812905466869093825, -105776199827810928938, -5334193964040802201, 106781646719172030499]
def DN9 : List ℤ := raw_ints% [2027832383713, 224389555095, -179446121031, -100093835832, 35280939266, 54536533093, 169450258, -29894593238, -10638764934, 14744979596, 12379385739, -5243627186, -10595393847, -406776892, 7529736121, 3308150971, -4324406917, -4282040404, 1584088868, 3999831377, 411006236, -3017006895, -1596726702, 1772598381, 2054007862, -585821893, -1948862274, -343970677, 1484133788, 924746057, -857850966, -1153481509, 236143466, 1088712618, 265134136, -824883288, -583537472, 465053301, 707458721, -102789417, -662727348, -193281254, 500207293, 383083950, -278457632, -457002868, 53552249, 427819692, 132580134, -325294838, -253803514, 184219900, 303269162, -39638049, -287288913, -82387587, 224045576, 164291008, -134360813, -201430591, 40698014, 196393492, 40866004, -160535405, -98177981, 105884232, 128346350, -47040803, -131650738, -6586529, 115365794, 46381884, -85725904, -71008138, 52350391, 79301248, -19962859, -76237888, -5186895, 64180548, 23224023, -49628192, -32175183, 33995183, 35840747, -21834546, -34184430, 11806957, 31678555, -6003018, -27733395, 1332407, 25410425, 1209274, -22844336, -4487784]
def AN10 : List ℤ := raw_ints% [45623693067445048977968, 22549802248038901704533, -7407312847925455410992, -4177857702786475682627, 5690761855242023417101, -549674530975148437986, -3380863575610974513836, 2300808346323350229316, 1101677961000704187110, -2376843879519655649768, 597959719302699432950, 1495259663766091326693, -1415627088001141655328, -313262422835546799326, 1366976823199328088319, -629613587393032116430, -738169963133050414982, 1027491554614854866039, -53543190203184359943, -856820325426543746089, 630166149346582696109, 325923644115522048163, -785968100987435831059, 251341167224885170363, 535748244088333738530, -602294515904805830927, -69035169936074597911, 602890915431479710613, -359870651876266622947, -307422872044610342941, 553131375562541892808, -101843318375953152232, -449483269167302938626, 414110799567737352850, 134152690801978859650, -489558460543910806401, 217878169654713678858, 315560183057638121269, -432518607409928494830, 1061027140216382877, 417498496492306674448, -295320672255558974576, -197616802599649309244, 426544745485381064976, -106817494230937390491, -341977441366112505929, 344135183315414262923, 94876099733101198701, -404302610164210462694, 188281329682866400101, 267601441376166218460, -371338643239311477794, -7462367681426370798, 372566741188822099097, -248955808982841951546, -198494468716891239166, 382946676041738978627, -63876893167872482230, -337262224212966304040, 292001547889461685973, 138994140497970998196, -384224659650958030397, 118473017881048497667, 304568645478418170800, -319846966239883121954, -93239145444334080146, 380738592734733144021, -154631899207963780971, -280279497332108468732, 334930153179292954093, 66720086955811640072, -376899072701176989537, 170217055137434346850, 271191889090301931787, -337091144640435470492, -65036884934091251485, 376563031027870045257, -159411708677690406990, -281813773402191954338, 323727288347920658861, 95980073959170843281, -377008783666525186982, 115015903483302072741, 313573929869973505599, -283644054509986090943, -161206487516370121969, 367968049717811612603, -28283154802533798666, -351901533377511979717, 205437632670265971086, 250115977031135161093, -327085474405469504706, -89567063911351645516, 371181791398178916353]
def DN10 : List ℤ := raw_ints% [5247730240106, 860649978616, -322832350383, -328692896760, -25289672146, 128946951589, 74756896018, -31101618612, -59176571168, -13282187992, 29906759744, 25686889721, -5188802084, -20776016546, -8818945271, 9564476972, 12354926235, 599144919, -8944110760, -6149594494, 2978966848, 6739596209, 2024939931, -4060690250, -4299811397, 464697722, 3830105492, 2159543446, -1743938095, -2968292223, -517333043, 2162525086, 1888000883, -579870286, -2007111305, -847596623, 1165264803, 1516558052, 3533663, -1321051509, -888047661, 564866958, 1159206074, 276056743, -840605984, -804703313, 211077499, 855916323, 379339336, -513164384, -677848963, 12968134, 616428522, 392206691, -297775132, -547086368, -86909361, 437039565, 360405403, -163409147, -430286257, -126386547, 309521481, 309660267, -85998548, -334564499, -129455766, 223558407, 254529528, -48309284, -260012341, -111884718, 169842448, 201150434, -36977619, -203996745, -82283404, 138599044, 151698838, -42853604, -160383233, -46619118, 121099331, 104368085, -56515164, -122907073, -9000662, 106694673, 59343275, -68833132, -85758334, 22372605, 88328728, 20305070, -70640185, -51458817]
def AN11 : List ℤ := raw_ints% [22906649695065272119120, 11795809391799801545692, -3342114063965949853434, -2623720422528391033096, 2759157186656254749270, 283715687389343832346, -1927422710620472603706, 753409405647994194465, 1018661562552863578093, -1094907073397890061113, -208272396711857193791, 977779343475513362800, -367332180922424502068, -596826719872412282025, 641057726580863401855, 137497424528005026805, -625345189945414474323, 244968270978983573102, 400600536205267707509, -451878821234825984719, -86194234925334236077, 455413000861089703229, -196506133319438716479, -294234869432833491736, 358225273070560144600, 52021492405197711625, -363080892301457854634, 174415882442569280892, 232204238294470511174, -307045709456825977198, -29589137177265544328, 309568636486362030583, -163589268033406348495, -194610318811506448144, 277944324320944225690, 14858688229242778342, -278036335850028630077, 158609051633412868043, 171992803758789994830, -261958411430873521562, -5283308671047926485, 260658071725911614947, -157107096783753783900, -159542396897564205262, 254970741298991807256, -307009596200681415, -253462252967963452552, 158059949269372070571, 155169582740067663897, -254722886660476909811, 2496653591117316179, 254850735746002483987, -160482543098347711647, -157922352181973049386, 260361836570553550055, -730908832449377538, -263997897946215983156, 163826882358641624495, 168470608467184459095, -270926942060975612059, -5734533155928613508, 281558954563848126188, -166369901989584631955, -187710801811340547373, 286307409135364374625, 19702877006556784955, -307660033735796511245, 166437399884869754042, 218818467745577999970, -304324395764407968643, -44226245611417345389, 343850186127819345110, -158536687223163000058, -264046319993270796313, 322506078953582429746, 86755210153911656828, -387539332920395045966, 135930919057862525726, 327825932945037306883, -330287303923606910458, -153149274300743527160, 433670578563794011152, -83463317149477440239, -404791868616840666171, 313094523112203933752, 249817794926671528883, -459767713154612957000, -7677077257557813888, 479310582689728585785, -246100028370852512279, -357555385231642546178, 439876849196190888350, 133159383873669022906, -509895627886608168179]
def DN11 : List ℤ := raw_ints% [2745089512138, 388317660768, -202740708519, -159366248557, 13053318486, 73512366707, 24479461180, -28757971507, -27260034582, 4626253303, 19556611214, 6665329663, -9885691681, -9743124908, 1925915015, 8102605047, 2945586174, -4482694719, -4717038225, 841142598, 4162509398, 1685020027, -2370514720, -2715159386, 371384098, 2444013157, 1108046600, -1393431608, -1741798540, 158785434, 1572514397, 787050197, -887261222, -1201404562, 60918242, 1081625844, 585693491, -603065550, -872431003, 16717480, 783815061, 449074201, -433582919, -658940683, -754653, 592679634, 351647031, -328496962, -513202297, -4787694, 465209613, 278887253, -261289674, -410175826, -1096487, 377153426, 222898904, -218311795, -334393892, 6741832, 315312787, 177482753, -190763319, -277188901, 18172826, 270348545, 139339173, -174535450, -231270743, 32022413, 237212819, 104207139, -165367311, -192447174, 49325871, 209942972, 70163345, -161228320, -154772867, 68378758, 184487715, 33829983, -156326851, -115204516, 87580182, 153569592, -2443107, -145324421, -71089127, 98400978, 115331032, -33261360, -121337937, -30187555, 94999576, 73563380]
def AN12 : List ℤ := raw_ints% [10501621370504027922608, 5992606997322241689615, -924412533526733917473, -1760952801267246656675, 863561979856088429307, 793059451990345231129, -767113233557532914855, -317888515579600177736, 642559461471821515482, 33562726419453868512, -499811096176797967314, 140400239203211335884, 350169883206611875582, -236041713302006980281, -205037955243569709708, 271500850633415579280, 74830038816676609932, -260692664992533818200, 32118151090834337431, 216507219626195586323, -110116180723035012951, -151367944691696624417, 156684105777558880084, 77195776915776760080, -172382371276617549993, -4573902261049884923, 160786714576092735402, -57633772893045217634, -127612729437528995962, 103169150607636482657, 80304622351357087408, -128316152148839929175, -26718144813693621617, 132424580625936083081, -25272430976546938071, -117142812043788328372, 69172384209635309838, 86589580480462381498, -99803677401539229513, -45946412601173799513, 114517757554796893159, 1581913361713226311, -112373004928801156623, 40758468156142256732, 95134335086727118931, -75433118268013123113, -65600568682196847533, 98889160754242131286, 28635150576254118226, -108335611334105156579, 11274175629570958795, 103850270196166835813, -48510494053603136249, -85972832934235241935, 79417139701969993831, 58147994337336105338, -99803776852296958309, -23107637792039806053, 108703850017692884172, -13871872878825058360, -104409519435438646458, 49899675466207487360, 89195385620602725780, -79729582403192930446, -63449369228650640039, 102252615376158541146, 31999412021902730670, -113493981822849005778, 4131533566992850949, 115231040308523840339, -38849324784349282484, -104873176518839346447, 72269637899048779450, 87163092560562457014, -98109605524576186478, -59968168167971666353, 118993647867213824079, 30403541317484396964, -128760225405696309585, 4638176854683078179, 133167296168153078736, -36332909762919983505, -125657368616665377208, 70048157099715071308, 115077502957797675589, -95563724595895906486, -93574518708817415675, 121141225085020083614, 72607744019356519485, -135223500822415136237, -42490206965900441974, 148704199587654569061, 16482567279855265044, -149052937895926795421]
def DN12 : List ℤ := raw_ints% [1394583624770, 107406780778, -136072736840, -49878504129, 36487434659, 29257883608, -10328699800, -18140182534, 835615281, 11102060431, 2808151870, -6353915696, -3909737155, 3116272257, 3802889884, -969573702, -3134661917, -359400084, 2260059075, 1074589390, -1383514505, -1343550208, 621930792, 1306567817, -32653323, -1082306600, -366141577, 765789686, 585254476, -430942081, -651806976, 128544625, 603745967, 109239193, -480266774, -269096621, 319748168, 349945801, -153020759, -362357848, 4756912, 321206479, 110767895, -245863049, -185420215, 153396099, 220005636, -60621159, -218268901, -21619859, 189570353, 84301745, -142245941, -125114308, 87231784, 142581955, -31439695, -140863341, -17121478, 122749566, 55881745, -95153285, -81026130, 61428591, 94312065, -28118682, -95015650, -3295422, 87569608, 28129205, -72349131, -47503278, 54588627, 58544373, -34095730, -64462825, 15693369, 63325663, 2173452, -59457118, -15456376, 50932396, 27051945, -42343277, -33502371, 31255349, 38551255, -22014282, -39061030, 11693511, 38988659, -4117116, -35469565, -3736638, 32115434, 8741927]
def AN13 : List ℤ := raw_ints% [4825448121208936173335, 3039520787666950967116, -33912026168255934960, -979626558262652473884, 45052878297675062796, 555362547962904287980, -57306455639656962507, -369946950655818214068, 67623654685322572870, 266005798367661410801, -75165769638617435858, -199412501563526316088, 80181574874641096465, 152913804475787849003, -83059125898047448798, -118307380352795897984, 84314168017354533856, 91408959352668789149, -84198865627568226009, -69673228002796084757, 83107768564848417275, 51761073882392922304, -81102697406028312892, -36574288055997319900, 78522289859217288757, 23683157905545391039, -75286739175805640049, -12432668582148665930, 71747414629051873882, 2786135407538879348, -67700524007897389006, 5794450222863826303, 63560134230303358215, -13108769815899110655, -58990556059963965930, 19719625853176778923, 54515103783292419447, -25226882250036863007, -49638116472050809565, 30308697806116995093, 45045019735073455144, -34348372621564070359, -40029188291041087958, 38222955579975986451, 35506000209003336825, -41043203339800447715, -30480389354961044445, 43981138250059289697, 26191512824552552839, -45781066635591703217, -21247484075190473340, 48033954969820459546, 17341589076107614699, -48982587177662604784, -12536119671617145761, 50803665086530719339, 9156274575097132159, -51050606184371696143, -4512211995182627854, 52713347861681560419, 1806691683501257034, -52390632996172200188, 2691782275436582589, 54203747065259502001, -4552820846058031232, -53416194195549387626, 8961284067559920929, 55734552850478771403, -9756309852951227128, -54543519074652552969, 14158485440370487720, 57771719628800434029, -13576434666705718200, -56174777948137488425, 18054759053026663513, 60742644130852448562, -15661786404599186066, -58636391096906092276, 20248451494151669554, 64905011147455420738, -15491680921653918983, -62016863965744462649, 20117607718934361881, 70069732647848507447, -12462998481763613755, -65900307476723043935, 16967374709742887681, 75242215096846382725, -6326090521283211797, -69195960220571438113, 10596005182193750526, 78628056628106944451, 2071864517954059990, -70517420880450715958]
def DN13 : List ℤ := raw_ints% [707349225391, 3940212219, -75697921471, -2602210645, 25551368980, 2185682029, -12020160553, -1909092486, 6622778716, 1669620629, -3988458941, -1454913720, 2532826823, 1262375297, -1657121659, -1092459676, 1099134046, 942179992, -727299587, -811022739, 473100144, 695447348, -294662181, -595157708, 169075277, 506779026, -78983497, -430548194, 15805094, 363304176, 29434042, -305796443, -59765090, 254984602, 80847308, -212076400, -93154966, 174048200, 100940631, -142531750, -103287697, 114419247, 103877219, -91760914, -100887247, 71273358, 97847916, -55447932, -92237290, 40745117, 87682139, -30136289, -81043906, 19749489, 76214053, -13080863, -69458224, 5847127, 65061899, -2124046, -58671324, -2871583, 55085197, 4407819, -49268096, -7874504, 46660225, 7781893, -41450243, -10251580, 39855126, 8923874, -35181222, -10773712, 34536068, 8484511, -30266296, -9958407, 30414534, 6916793, -26382582, -8154222, 27060278, 4585815, -23103082, -5667368, 23944630, 1918037, -19988135, -2916073, 20615440, -517523, -16780765, -469697, 16981189, -2180021]
def AN14 : List ℤ := raw_ints% [15390206556022527497535, 7700979457687243089294, -2262471531789714317383, -1383059635506070197154, 1628894419009698965080, -156038372598466496422, -824648602617725031391, 607064489609814889878, 127039392840566037816, -498438680567549102629, 270887534338188083428, 165046427008833135638, -332472037295566890847, 128384059185529160635, 166602299636374612158, -237479064828573027530, 50513904187485252030, 160739884073070354316, -173175166607387859918, 868607685314971683, 151250330650875913294, -124326177098114226539, -33170927248439246942, 139139792779445968368, -84489624416934283240, -57190269342149600589, 124812156824588335999, -50488387273510539698, -73922849951996974088, 108394148478387343838, -20712746893036566335, -84698526459306880183, 89959646545302109271, 5545508920562131596, -90125181751154970403, 69662340174384897377, 28427250740483220445, -90449978795327521182, 47809658001526528090, 47694061030540073269, -85774591457453358761, 24912593285813267258, 62850710510871871513, -76207345202085434010, 1721840715509550106, 73245951334218842041, -61989044194497481269, -20751793947284943921, 78176055819246717315, -43607162819326999522, -41240107323127889536, 77005760186619958507, -21900442407272121831, -58254171934420725960, 69314421134718734966, 1852675256978613106, -70168513673187273666, 55069092659888688793, 25877064833061017821, -75367041869032557874, 34818382250914652994, 47898394964468810501, -72464146879886785101, 9890811281978816916, 65226332776623855669, -60610653864949359601, -17432406928943807452, 74964452668597160542, -39885823328640304583, -43821952169742593947, 74398615177685551235, -11757496390431880281, -64970069605343100823, 61624006591427517285, 20453271491327098456, -75970475191503654547, 36456648518806393028, 51268471586453900728, -72225125297079157951, 1581158853239440245, 73268865055535555397, -51112029023135657474, -36402790724232072386, 78444607652058014463, -14391191005582631196, -66964682139955046189, 61311986174549848212, 29586381542031675322, -78190288693145276698, 23397814279758308842, 66309424643943133778, -62674988459523337493, -23898790957077809803, 80738851091044655143]
def DN14 : List ℤ := raw_ints% [1792151537916, 262874825922, -106872092018, -94083365061, -7179083372, 31452296450, 19724483787, -3586466177, -12409688456, -6017092857, 3301101446, 6032784078, 2126522127, -2532107403, -3326349554, -654509257, 1932793901, 1937819185, 9067155, -1476004704, -1136350697, 284437314, 1120985175, 640386968, -408284262, -840150391, -320747659, 443602737, 614894667, 111151686, -430242721, -432808084, 25282909, 389562926, 285604440, -110588600, -334003409, -167637001, 158841158, 271408530, 74913720, -179652182, -207106098, -4449887, 180043995, 144951146, -46167969, -165500199, -87857422, 79083857, 140567849, 38058683, -96384162, -109198416, 2779324, 100244341, 74925679, -33532665, -93022415, -40934403, 53640547, 77304465, 10051653, -63148962, -55903861, 15318290, 62759241, 31813997, -33302409, -53868992, -8111175, 42705226, 38593971, -12204962, -43194062, -19749782, 26463202, 35521093, 740932, -32713404, -21743559, 14755054, 30294577, 5295302, -23476227, -20479161, 9415392, 23706879, 6758756, -18248676, -16432716, 5969585, 19213119, 5417913, -13535829, -13642490]
def AN15 : List ℤ := raw_ints% [17365046217871703229544, 1857423972032770461718, -982730737966866002280, 349418296526816129024, -76652767088107908870, 3947927650416260652, 3792495710345361426, -1145048008950895962, -119159668630151457, 173869710879773180, -31824494772584565, -13180009121648948, 18356560970603996, -5451801815408987, 11750284292823161, -4574887610729656, 15170300228449695, -6046660295904655, 18380688392048109, -7160215064293296, 21989736239163727, -8510504372748480, 26194335525789886, -10105020513097506, 31066832110520211, -11955332509779688, 36711178226473562, -14095463377076104, 43271599547011448, -16574486211028997, 50892973600095042, -19416623963310119, 59759798494820568, -22661419806607396, 70088678513455048, -26372127118973756, 82129347629741812, -30631447738173318, 96204657740242990, -35549360667630875, 112692313749603013, -41288509699040633, 132036164685520578, -48033029180186136, 154771852263885019, -56040169701077268, 181536655522351263, -65572538709488169, 213066340499495173, -76956757957738041, 250237955441807222, -90522073356984594, 294084434417031896, -106626708364368680, 345818798358018448, -125654320056232448, 406891579440817662, -148032204140986580, 479025660487134277, -174293592677594347, 564284970609416308, -205140915064274570, 665136334716253104, -241522628539459174, 784484138648406492, -284674845006320255, 925694926797183811, -336190422548182362, 1092581383233222410, -397916348869685450, 1289246394066854613, -471862814386614900, 1519850824658458585, -559890606421721950, 1788167226007240934, -663371061386349236, 2096838046497325843, -782689730268364629, 2446249155405365062, -916807549882022860, 2832938923909747783, -1062720928178188387, 3247639692496767662, -1215035124776431528, 3673108841542829003, -1365584544258024224, 4082852107193534917, -1503427671870949109, 4441913458925627068, -1615707024072259681, 4711335187601545436, -1689618503542216400, 4856406606546494155, -1715463139752774774]
def DN15 : List ℤ := raw_ints% [432254786073, 114182728066, 27000328388, 4427389635, 181638024, -144646701, -37204418, 3364012, 4328855, 706902, -263614, -333085, -90303, -178587, -64081, -196562, -72708, -205679, -74744, -214591, -77787, -224614, -81412, -235471, -85350, -247115, -89548, -259669, -94024, -273110, -98631, -287513, -103318, -302956, -108122, -319503, -113113, -337327, -118395, -356582, -124158, -377412, -130538, -399989, -137751, -424494, -145884, -451066, -155049, -479868, -165241, -511062, -176419, -544806, -188503, -581295, -201410, -620744, -215124, -663405, -229734, -709565, -245451, -759500, -262569, -813432, -281455, -871473, -302396, -933491, -325526, -999008, -350650, -1067043, -377169, -1135928, -404001, -1203092, -429617, -1264863, -452092, -1316358, -469236, -1351537, -478742, -1363737, -478442, -1346765, -466718, -1296583, -443001, -1213063, -408223, -1100960, -364905, -969310]
def BsN : List Blk := [⟨(1 : ℚ), (0 : ℚ), (5544576681669439738489 / 52341686910962986249880 : ℚ), DN0⟩,
  ⟨(3276730368397 / 4398046511104 : ℚ), (-2846434036817249496802584327549855809799 / 9671406556917033397649408000000000000000 : ℚ), (73538690711166046764981 / 994492051308296738747720 : ℚ), DN1⟩,
  ⟨(1305092809445 / 2199023255552 : ℚ), (-50459512470861903514431699337636266627633 / 96714065569170333976494080000000000000000 : ℚ), (54102672509309981947951 / 994492051308296738747720 : ℚ), DN2⟩,
  ⟨(8542441030865 / 17592186044416 : ℚ), (-8733377158418276106796407556106148303303 / 12089258196146291747061760000000000000000 : ℚ), (15431322781466384577851 / 248623012827074184686930 : ℚ), DN3⟩,
  ⟨(6896403054357 / 17592186044416 : ℚ), (-181136711433848873382792786417759206259407 / 193428131138340667952988160000000000000000 : ℚ), (14739255402069114346683 / 994492051308296738747720 : ℚ), DN4⟩,
  ⟨(2976343721197 / 8796093022208 : ℚ), (-3275016434406850332866121948892436228973 / 3022314549036572936765440000000000000000 : ℚ), (51053348057516050917473 / 994492051308296738747720 : ℚ), DN5⟩,
  ⟨(4805667573359 / 17592186044416 : ℚ), (-251003728701191018592854999347220598140897 / 193428131138340667952988160000000000000000 : ℚ), (14943146700298895738363 / 497246025654148369373860 : ℚ), DN6⟩,
  ⟨(511616124031 / 2199023255552 : ℚ), (-282055736375561776914842081200209473889673 / 193428131138340667952988160000000000000000 : ℚ), (239782572422541609571 / 7003465150058427737660 : ℚ), DN7⟩,
  ⟨(3532845575111 / 17592186044416 : ℚ), (-15526003837186727201177233263846439039421 / 9671406556917033397649408000000000000000 : ℚ), (2419565658323974811365 / 198898410261659347749544 : ℚ), DN8⟩,
  ⟨(3132095659693 / 17592186044416 : ℚ), (-8345227062488155416624620250623650617991 / 4835703278458516698824704000000000000000 : ℚ), (3299668408775036133583 / 248623012827074184686930 : ℚ), DN9⟩,
  ⟨(2597141326789 / 17592186044416 : ℚ), (-370036424786292096417260675745534622838311 / 193428131138340667952988160000000000000000 : ℚ), (3753116971342953177799 / 99449205130829673874772 : ℚ), DN10⟩,
  ⟨(2124937635887 / 17592186044416 : ℚ), (-408851434379226432243644719811994253074577 / 193428131138340667952988160000000000000000 : ℚ), (9421786132050598207979 / 497246025654148369373860 : ℚ), DN11⟩,
  ⟨(108661779151 / 1099511627776 : ℚ), (-17906657758888708979164490742088108331339 / 7737125245533626718119526400000000000000 : ℚ), (8638891493065119576081 / 994492051308296738747720 : ℚ), DN12⟩,
  ⟨(1295321823375 / 17592186044416 : ℚ), (-100919024941704288683653862844431468802141 / 38685626227668133590597632000000000000000 : ℚ), (496191507646906666672 / 124311506413537092343465 : ℚ), DN13⟩,
  ⟨(422113244307 / 8796093022208 : ℚ), (-587400478506638731396024528063810947569941 / 193428131138340667952988160000000000000000 : ℚ), (1582545206623613833667 / 124311506413537092343465 : ℚ), DN14⟩,
  ⟨(349141633395 / 17592186044416 : ℚ), (-151637304143068635474707076414507938439379 / 38685626227668133590597632000000000000000 : ℚ), (2856982645929358828211 / 198898410261659347749544 : ℚ), DN15⟩]
def RNd : RadLit where
  CT := CTl
  hq := (994495450927 / 994492051308296738747720 : ℚ)
  Cq := Cql
  δc := dcL
  s := -1
  W := 48
  sh := 112
  Gs := (List.range 16).map (grp naT)
  As := [AN0, AN1, AN2, AN3, AN4, AN5, AN6, AN7, AN8, AN9, AN10, AN11, AN12, AN13, AN14, AN15]
  Bs := BsN
  ns := List.replicate 16 96
  Tls := [19968421719879877470087429193167617847909508, 16347072166041377821211510539575221993697786, 16411372343178323905084972452859250859795581, 23699601601248675408729555419649812686721057, 7095260698655561622649806311135141000642754, 11686680984269382118224129639056725515396648, 13883301843759568622932990378271913705174774, 14814197452065671765148627806910965292193033, 6817357156355906447857040442734153643883773, 3016609106516498848816174364421700226172619, 7311039789402973093082948284013009081825707, 6114380622668960961825543029244760533439933, 2271614297669874729017408550824048955875231, 1029864344326972204940708833487533239638021, 1677191918772829387342679483874510907493886, 331589278870427995407001958072198765383456]
  etas := [(0 : ℚ), (37404884055593501 / 316912650057057350374175801344 : ℚ), (62745745870815631 / 633825300114114700748351602688 : ℚ), (11711144910478457 / 79228162514264337593543950336 : ℚ), (319361129837801841 / 1267650600228229401496703205376 : ℚ), (4412697932863827 / 19807040628566084398385987584 : ℚ), (439808553525426143 / 1267650600228229401496703205376 : ℚ), (516309778300344375 / 1267650600228229401496703205376 : ℚ), (147397393848122127 / 316912650057057350374175801344 : ℚ), (69714487683429021 / 158456325028528675187087900672 : ℚ), (647189962250053657 / 1267650600228229401496703205376 : ℚ), (933573703881399087 / 1267650600228229401496703205376 : ℚ), (846941453063133933 / 1267650600228229401496703205376 : ℚ), (1267034594534226415 / 1267650600228229401496703205376 : ℚ), (2812784006849544619 / 1267650600228229401496703205376 : ℚ), (5428270652266624033 / 1267650600228229401496703205376 : ℚ)]
def miN : List ℤ := raw_ints% [-226490210991982502099905, -71674273427854132827554, -34284693498016513052152, -19910399653998682311783, -12956095621626612715798, -9084976955200374620518, -6715721998022014170198, -5162893869911328233709, -4091092273047298231250, -3320730171159325815048, -2748708406128167692968, -2312454677375965568914, -1972228337802560888211, -1701816672031373467715, -1483367943837598770583, -1304386659458335654430, -1155916222521460508161, -1031401827461264846819, -925957599195381179296, -835881795202547477361, -758328600790540696860, -691081297446595517119, -632392553439102027625, -580870070181724056960, -535393445320792500986, -495052883799162003691, -459103435576722517880, -426930423586284557822, -398023041504450497302, -371953987804707110945, -348363609337169242431, -326947448651253294716, -307446385151851607755, -289638770656273661195, -273334111343172519049, -258367958178753633025, -244597748745656424131, -231899403313267511261, -220164522782063968083, -209298069901724812900, -199216440816656407976, -189845853626809550337, -181120995784062751165, -172983883884769512499, -165382898585232457108, -158271964566291419310, -151609851160262055075, -145359573770363219508, -139487879818987258858, -133964805854646985607, -128763294780103677447, -123858864053316647374, -119229317249480506824, -114854492627552326183, -110716043374011714439, -106797245044029286448, -103082826420487022755, -99558820592026710579, -96212433534565899872, -93031927884210725562, -90006519927460012518, -87126288118552095715, -84382091673098258175, -81765497989382190771, -79268717820099097507, -76884547262956519379, -74606315762652410303, -72427839422741993642, -70343379016664704188, -68347602165100862822, -66435549213841302729, -64602602404131812683, -62844457977378750720, -61157100899331098925, -59536781926362202190, -57979996769083351048, -56483467136925981242, -55044123472118213912, -53659089203154621264, -52325666366840894219, -51041322464650346206, -49803678433767013891, -48610497626076084394, -47459675699724377744, -46349231337907571463, -45277297718415539333, -44242114665328228090, -43242021421227820198, -42275449984487564228, -41340918961708185436, -40437027890281409392, -39562451990438376996, -38715937310050960598, -37896296228950654994, -37102403292660423295, -36333191348241318741, -35587647957474443671, -34864812064861958375, -34163770899966656949, -33483657095442956004, -32823646003764927374, -32182953197148614131, -31560832136513421933, -30956571996546031890, -30369495635033470261, -29798957695631615069, -29244342834142110808, -28705064059193819695, -28180561178972949340, -27670299346326339886, -27173767695181741660, -26690478061793228767, -26219963784834506587, -25761778578832554620, -25315495475863078129, -24880705830821459409, -24457018385941747430, -24044058390564799720, -23641466772457778155, -23248899357263309303, -22866026132910010726, -22492530556048796589, -22128108897793250267, -21772469626239052196, -21425332823418482860, -21086429634512745544, -20755501747298505335, -20432300899946738549, -20116588415422745386, -19808134760856920038]
def meN : List ℤ := raw_ints% [3196905158976488924, 300037106874, 529653368846, 381704217037, 414273777996, 92935155635, 479284793212, 166257639592, 238879268449, 421043556154, 439944519375, 306783421300, 466641308536, 460794964929, 95226732882, 37607500320, 345310374105, 430498285256, 97478225028, 246691333376, 55768701387, 247356240879, 41790671812, 264808891750, 18426784126, 93757350072, 221209124622, 283870529852, 445189823234, 245428472492, 325423491416, 159921029061, 180362915060, 168097813899, 266808436260, 486606110088, 378787441102, 406807036951, 500191899676, 207981689195, 469096100660, 248302620559, 102756145799, 24988669917, 18490444095, 148189611288, 492532533716, 432266771834, 149612890820, 215779439946, 208231092009, 545232232637, 152873560694, 412250700562, 452040537646, 526894949773, 153346490617, 493461975887, 167850914140, 467580523103, 223675799124, 473801694849, 461473013592, 294204957132, 360615720698, 364433566913, 306051810752, 98148106781, 512013649191, 123842458268, 533544429992, 509172865812, 177698294705, 75135412159, 329863264876, 341903090477, 16027823576, 91058650558, 381679002050, 175770874452, 271579841579, 156951807795, 548747569633, 189628787033, 340329699059, 354045700346, 99780023154, 109840910307, 531039875448, 40631847122, 487420275781, 370930895981, 214134120370, 56224678046, 94839861550, 421873703813, 396704247254, 84746960393, 497764894315, 225529500168, 469588491298, 87724067888, 291396530764, 305818961524, 466372252176, 341192515810, 493794317874, 377509678036, 439804710427, 389435243270, 478340360393, 529287750621, 374517868455, 348771211244, 218770470903, 198310600921, 289662351984, 77529775039, 69414040306, 234618966345, 12785368879, 378415298635, 61600994087, 541285286367, 289042406771, 26920467361, 303957853665, 343177062914, 270292211383, 306682089692]
def rnsN : List ℕ := [17592186044416, 13106921473588, 10440742475560, 8542441030865, 6896403054357, 5952687442394, 4805667573359, 4092928992248, 3532845575111, 3132095659693, 2597141326789, 2124937635887, 1738588466416, 1295321823375, 844226488614, 349141633395]
def DmN : List ℤ := raw_ints% [38278005097012, 4645031464585, -870515092447, -1110755429539, -348278428796, 178854444187, 261752806290, 96573218021, -66834839209, -105214216425, -42136146604, 32422143897, 54062535072, 23000315992, -18236065189, -31973562585, -14293349888, 11299626540, 20710871299, 9646686613, -7506337636, -14297650859, -6885550375, 5260899021, 10346509519, 5113966366, -3850688080, -7764149304, -3910409036, 2923305268, 5996979710, 3055934979, -2290440487, -4742221246, -2427772881, 1845128031, 3823841500, 1952755106, -1523532417, -3134295460, -1585062070, 1285975591, 2605128663, 1294799262, -1106942257, -2191240729, -1061776925, 969548252, 1862032794, 871948777, -862348117, -1596211784, -715283274, 777425418, 1378625931, 584441018, -709213440, -1198271901, -473923726, 653744817, 1046998652, 379508339, -608157859, -918635762, -297859625, 570355958, 808383396, 226260641, -538752186, -712364704, -162431362, 512049503, 627281794, 104431056, -489016265, -550151852, -50667663, 468229856, 478146281, 62948, -447801306, -408624607, 47582497, 425199013, 339520750, -91097124, -397465736, -270166895, 127704520, 362184315, 202199124, -153740087, -319040692, -139532400, 166553881, 270764610]
def ClP : List ℤ := raw_ints% [-1559967793860780510, -157273581225108147, -73370811030474029, 14854778902084386, -1501075823086774, 108740876454019, -52516859504918, 38414366460235, -25583176309219, 19232817769418, -15873874130543, 13281643476098, -10721652308148, 7976083109685, -4976594651338, 1713238545129, 1787473283029]
def ndP : List ℤ := raw_ints% [1, 1, 1242697445389625304888128, 8177989, 8388608, 1242697872654140315796896, 3983507, 4194304, 1242698925091305404161403, 7758247, 8388608, 1242701122466435669643885, 7554485, 8388608, 1242699145112045524988445, 14673819, 16777216, 1242697097651961973991741, 1783869, 2097152, 1242698080098982135733445, 6932875, 8388608, 1242700369712247750595758, 13479943, 16777216, 1242701338532483916755580, 13057993, 16777216, 1242700101647969800245748, 6325511, 8388608, 1242697865565115679343504, 3276730368397, 4398046511104, 1242697083661047865998868, 12118089, 16777216, 1242696813069620785167920, 11717643, 16777216, 1242698148114186235205479, 11314877, 16777216, 1242700314305960974326319, 10931387, 16777216, 1242701651523665230042504, 10553913, 16777216, 1242701360164316802269255, 10201481, 16777216, 1242699740550574705017135, 1305092809445, 2199023255552, 1242698128066342544714669, 9584327, 16777216, 1242696583482779202325385, 2304725, 4194304, 1242696299456389431534430, 8882431, 16777216, 1242697518498063769433572, 4265267, 8388608, 1242699747561240842648836, 8185089, 16777216, 1242701747359562603887832, 8542441030865, 17592186044416, 1242701890429538754809521, 3911749, 8388608, 1242702546850805985482456, 7506633, 16777216, 1242701576265150761948152, 7182461, 16777216, 1242699297680613844761770, 3430325, 8388608, 1242696727105546662268896, 6896403054357, 17592186044416, 1242695315255708497194771, 6294491, 16777216, 1242695181722373226161767, 1499777, 4194304, 1242696926114424233361073, 5709143, 16777216, 1242699839923803429373320, 2976343721197, 8796093022208, 1242700152018250958674433, 2699435, 8388608, 1242703100428519828760049, 1285713, 4194304, 1242704458347940532639501, 4901869, 16777216, 1242703884386880795623798, 4669443, 16777216, 1242701484224242528154078, 4805667573359, 17592186044416, 1242700242855755133920190, 4346035, 16777216, 1242696210568790675212833, 1033571, 4194304, 1242693030873304322234671, 3926417, 16777216, 1242691482062602722021101, 511616124031, 2199023255552, 1242691416088350795276836, 1848191, 8388608, 1242693018093322439236849, 875793, 4194304, 1242697084480155318682239, 3532845575111, 17592186044416, 1242700970825576221197685, 199149, 1048576, 1242706942836649959194694, 3024881, 16777216, 1242710830656216339916881, 3132095659693, 17592186044416, 1242711269154184050329884, 1413449, 8388608, 1242711161150156778731537, 1338101, 8388608, 1242706194796003205688805, 316357, 2097152, 1242696631710537277180348, 2597141326789, 17592186044416, 1242692118380797779335963, 1174819, 8388608, 1242680521263989764178608, 2224445, 16777216, 1242671263610484065956744, 1053779, 8388608, 1242670345963577040231886, 2124937635887, 17592186044416, 1242678552224384795089737, 1910871, 16777216, 1242711903117418414351556, 1812919, 16777216, 1242770682803320783678715, 1721467, 16777216, 1242862939257396941356002, 108661779151, 1099511627776, 1242955272260855998760154, 98749, 1000000, 1242957484367979535299446]
def ClN : List ℤ := raw_ints% [-975396137404471176, -18039847499279627, -57144266227350972, 10222735143864220, -987093121083358, 49857397058215, -2171723658801, 6183998173011, 1384150907879, 1296591874904, 3167716353948, -983073430486, 4043533649476, -2752150795221, 4693179549314, -3835562797762, 4696478466951]
def ndN : List ℤ := raw_ints% [1, 1, 678206261282382131965272, 4109003, 4194304, 678243083110532865320073, 2015253, 2097152, 678244671213510608537483, 15800979, 16777216, 678247885435467156952681, 7737939, 8388608, 678247731187177964458118, 15150227, 16777216, 678245078970231233047281, 7413993, 8388608, 678243952712084802527556, 14513471, 16777216, 678245419222430412296978, 888201, 1048576, 678247633106189907071909, 13894071, 16777216, 678248681783589181311207, 13575087, 16777216, 678247642756843399335504, 3317843, 4194304, 678245555337164668714194, 12972421, 16777216, 678243899760901380236498, 6331145, 8388608, 678243555456031637516795, 3276730368397, 4398046511104, 678243663501829891832833, 12190601, 16777216, 678246269644002219308960, 11888879, 16777216, 678248252703728664718587, 11598921, 16777216, 678249070661268799751079, 11325103, 16777216, 678248497016771680464023, 1380429, 2097152, 678246805059319977433105, 10767289, 16777216, 678244812683040000460202, 10484779, 16777216, 678243367500474453092157, 5102165, 8388608, 678243146941311880788603, 1305092809445, 2199023255552, 678243425723106986746403, 9685339, 16777216, 678246209193799052887979, 9428735, 16777216, 678248246116749023486962, 9164773, 16777216, 678249551324857126666280, 1113249, 2097152, 678249532002387965895393, 8667717, 16777216, 678248295764997202813108, 2104629, 4194304, 678246095375982584789183, 8173887, 16777216, 678242915200987237141370, 8542441030865, 17592186044416, 678242312030696782503676, 3955543, 8388608, 678242324111487733191333, 1922145, 4194304, 678242376511771809267383, 7459697, 16777216, 678243722170891443495307, 7235303, 16777216, 678246049214178584128815, 7005737, 16777216, 678248690751132058910415, 3400317, 8388608, 678250437726305576338009, 6599293, 16777216, 678250717232712101164473, 6896403054357, 17592186044416, 678250585931704408020726, 6371029, 16777216, 678249672594671944581878, 6174991, 16777216, 678247193675894298426665, 1495507, 4194304, 678244138045355935138972, 5781849, 16777216, 678241323465002130119546, 2976343721197, 8796093022208, 678240072289348721739861, 1373623, 4194304, 678240515951594236466943, 1326707, 4194304, 678242754542102921564368, 160089, 524288, 678246732497038378116026, 4953449, 16777216, 678250865335430219965416, 2396999, 8388608, 678253744752216326243769, 4623123, 16777216, 678254439016372660344368, 4805667573359, 17592186044416, 678254443176819589274114, 4427539, 16777216, 678249677793549958695333, 4279481, 16777216, 678243326106011497507076, 2066873, 8388608, 678236658562714454482249, 3982563, 16777216, 678232824012374234155928, 511616124031, 2199023255552, 678232952572263814657618, 3767547, 16777216, 678241883311399234200065, 1814321, 8388608, 678258380913240971956568, 3504541, 16777216, 678273834759925120726770, 3382719, 16777216, 678272843321166777803090, 3532845575111, 17592186044416, 678270420174319607697623, 19501, 100000, 678230697793987129637398]
def CovP : Cov := ⟨48, BsP, 53 / 58, dyL 60 ClP, 2000000 / 901251, -(1098749 / 901251)⟩
def CovN : Cov := ⟨48, BsN ++ [mBlk DmN], 53 / 58, dyL 60 ClN, 200000 / 80499, -(119501 / 80499)⟩
def BudP : ℚ := (1245533632274955841239409 / 1208925819614629174706176 : ℚ)
def BudN : ℚ := (679737719396984153615469 / 1208925819614629174706176 : ℚ)
def EP : ℚ := (2629838063963 / 549755813888 : ℚ)
def EN : ℚ := (3200188786997 / 549755813888 : ℚ)
def KP : ℚ := (23501918744161 / 1099511627776 : ℚ)
def KN : ℚ := (9737388142267 / 549755813888 : ℚ)
def EvP : ℕ := 14641620594118061632
def TmN : ℤ := 19968421719879748231774235233666320145938651

/-! ### The instances -/

theorem enc_valid : Enc.Valid capSource := CoefEnc.valid (by decide +kernel)
theorem enc_q1 : Enc.qh < 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem tot_T : ((999997120790 : ℕ) : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cos_ok : (List.range 94).all (cosChk CTl) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem co_ok : coefChk Enc dcL Cql 0 = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cq_ok : cqOK Cql = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem cq_len : Cql.length = 384 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! positive gas -/
theorem pRel : relP gP.P gasPosT gP.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pSep : sepL (2 * 10 ^ 12) gP.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pRows : rows gP.P 67 (gP.L.map (stAt gP.P gP.T 1)) = gP.R := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pR' : gP.R = gP.R.headD 0 :: (gP.R.drop 1).headD 0 :: gP.R.drop 2 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLn : gP.L.length = gP.Ln := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pSg : SG gP.P gP.T gP.L = gP.Sg := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLI : LI gP.P gP.T gP.Q gP.L = gP.LIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pLEI : LEI gP.P gP.T gP.Q gP.L = gP.LEIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pM : gP.chkM = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pV : gP.chkV = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pG : G2I gP.P gP.T gP.Q gP.L = gP.G2v := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pS' : gP.chkS = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pC : gP.chkC = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pE : (gP.L.map (eInt 900 gP.P 64 gP.T)).sum = EvP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pmq : 0 ≤ massQ gP.T gP.L := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pGl : 0 < (gP.G []).length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! negative gas -/
theorem nRel : relN gN.P gasNegT.reverse gN.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nSep : sepL (2 * 10 ^ 12) gN.L = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nRows : rows gN.P 131 (gN.L.map (stAt gN.P gN.T 1)) = gN.R := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nR' : gN.R = gN.R.headD 0 :: (gN.R.drop 1).headD 0 :: gN.R.drop 2 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLn : gN.L.length = gN.Ln := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nSg : SG gN.P gN.T gN.L = gN.Sg := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLI : LI gN.P gN.T gN.Q gN.L = gN.LIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nLEI : LEI gN.P gN.T gN.Q gN.L = gN.LEIv := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nM : gN.chkM = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nV : gN.chkV = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nG : G2I gN.P gN.T gN.Q gN.L = gN.G2v := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nS' : gN.chkS = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nC : gN.chkC = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nmq : 0 ≤ massQ gN.T gN.L := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMi : gN.Mi = gN.Mi.headD 0 :: gN.Mi.tail := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMe : gN.Me = gN.Me.headD 0 :: gN.Me.tail := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nMir : chkMir gN.W 1 (dyL gN.Qm gN.Mi.tail) (dyL gN.Qm gN.Me.tail) miN (dyL 120 meN) = true := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nl1 : gN.Mi.tail.length = miN.length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nl2 : gN.Mi.tail.length = (dyL 120 meN).length := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! radial records -/
theorem pAll : RPd.allChk (auxT Sign.pos) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nAll : RNd.allChk (auxT Sign.neg) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pAux : auxOK (auxT Sign.pos) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nAux : auxOK (auxT Sign.neg) = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHq : RPd.hq = (1 - massQ gP.T gP.L) / (sumP (auxT Sign.pos) : ℚ) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHq : RNd.hq = (53 / 58 - massQ gN.T gN.L) / (sumP (auxT Sign.neg) : ℚ) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHq0 : 0 ≤ RPd.hq := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHq0 : 0 ≤ RNd.hq := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTot : 0 ≤ sumP (auxT Sign.pos) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTot : 0 ≤ sumP (auxT Sign.neg) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nRn : rnOK RNd rnsN 44 = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nFb : fbOK RNd = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nDm : DmN = truncD RNd.sh 96 (mirF RNd rnsN 44 16) := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTm : abs1 ((mirF RNd rnsN 44 16).drop 96) = TmN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! covers -/
theorem pNodes : (ndOf ndP).all CovP.nodeOK = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nNodes : (ndOf ndN).all CovN.nodeOK = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pChain : CovP.chain EP KP BudP ((ndOf ndP).headD (0, 0)) (ndOf ndP).tail = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nChain : CovN.chain EN KN BudN ((ndOf ndN).headD (0, 0)) (ndOf ndN).tail = true := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pEs : sumEQ CovP.W CovP.Bs ≤ EP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nEs : sumEQ CovN.W CovN.Bs ≤ EN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pK : 2 * CovP.s + mc4 CovP.Cl 0 * CovP.α ^ 2 ≤ KP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nK : 2 * CovN.s + mc4 CovN.Cl 0 * CovN.α ^ 2 ≤ KN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pBot : bot ((ndOf ndP).headD (0, 0)) (ndOf ndP).tail = 98749 / 1000000 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nBot : bot ((ndOf ndN).headD (0, 0)) (ndOf ndN).tail = 19501 / 100000 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTop : ((ndOf ndP).headD (0, 0)).1 = 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTop : ((ndOf ndN).headD (0, 0)).1 = 1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pHd : (ndOf ndP).headD (0, 0) :: (ndOf ndP).tail = ndOf ndP := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nHd : (ndOf ndN).headD (0, 0) :: (ndOf ndN).tail = ndOf ndN := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

/-! final constants -/
theorem pFin : gP.Tb + sumQ (dyL 40 gP.f) - 2 * massQ gP.T gP.L * (6931471803 / 10 ^ 10) - 29557 / 200000 +
    (1 / 900 + 1 / 901) / 901 * ((EvP : ℚ) / 2 ^ 64) + errS RPd 16 +
    Enc.tail (1 - massQ gP.T gP.L) 1 + BudP +
    diffSum (D : ℚ) (addQ (Zq 1098749 901251 4000000 gP.W (gP.G [])) CovP.Cl) posP ≤ posEps := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

theorem nFin : gN.Tb + sumQ (dyL 40 gN.f) + sumQ (dyL 120 meN) -
    2 * massQ gN.T gN.L * (6931471803 / 10 ^ 10) -
    5489 / 100000 + errS RNd 16 + ((TmN : ℚ) / 2 ^ 160 + 384 * (mirE RNd 1 16 + 1 / 2 ^ RNd.W)) +
    Enc.tail (53 / 58 - massQ gN.T gN.L) 2 + BudN +
    diffSum (D : ℚ) (addQ (Zq 119501 80499 400000 gN.W (gN.G (0 :: miN))) CovN.Cl) negP ≤ negEps := by
  decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

theorem pT0 : 0 < gP.T := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nT0 : 0 < gN.T := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pTg : (gP.T : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nTg : (gN.T : ℤ) = sumP row0 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pP64 : 64 ≤ 900 * gP.P := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pW : RPd.W + RPd.sh = 160 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nW : RNd.W + RNd.sh = 160 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pB : RPd.Bs.length = 16 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nB : RNd.Bs.length = 16 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem dc0 : 0 ≤ dcL := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pS0 : 0 ≤ CovP.s := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nS0 : 0 ≤ CovN.s := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pA0 : 0 ≤ CovP.α := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nA0 : 0 ≤ CovN.α := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem pH0 : 0 < ((ndOf ndP).headD (0, 0)).1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)
theorem nH0 : 0 < ((ndOf ndN).headD (0, 0)).1 := by decide +kernel -- kcost: at most 60 s measured 6 Nov (whole file 293 s)

noncomputable section

theorem tgtP : tgt Sign.pos = ((1 - massQ gP.T gP.L : ℚ) : ℝ) := by
  have hF : List.Forall₂ (Rel gP.P gP.T) (capSource.gas Sign.pos) gP.L := relP_spec pTg gasPosT gP.L pRel
  show 1 - massL (capSource.gas Sign.pos) = _
  rw [massL_rel hF]
  push_cast
  ring

theorem tgtN : tgt Sign.neg = ((53 / 58 - massQ gN.T gN.L : ℚ) : ℝ) := by
  have hF := relN_spec nTg gasNegT.reverse gN.L nRel
  have hp : (gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect).Perm
      (reflectL (capSource.gas Sign.neg)) := by
    have e : (gasNegT.reverse.map fun t => (mkCell 1 (sumP row0) t).reflect) =
        (reflectL (capSource.gas Sign.neg)).reverse := by
      show _ = (((gasNegT.map (mkCell 1 (sumP row0))).map YCell.reflect)).reverse
      rw [List.map_map, List.map_reverse]
      rfl
    rw [e]
    exact List.reverse_perm _
  show 53 / 58 - massL (capSource.gas Sign.neg) = _
  rw [← massL_reflect, ← massL_perm hp, massL_rel hF]
  push_cast
  ring

theorem radP : RadOK RPd capSource (auxT Sign.pos) (tgt Sign.pos) (sumP (auxT Sign.pos)) 16 :=
  radOK_of RPd Sign.pos enc_valid tgtP pHq pHq0 pAux cos_ok co_ok cq_ok cq_len pW dc0 pB pAll pTot

theorem radN : RadOK RNd capSource (auxT Sign.neg) (tgt Sign.neg) (sumP (auxT Sign.neg)) 16 :=
  radOK_of RNd Sign.neg enc_valid tgtN nHq nHq0 nAux cos_ok co_ok cq_ok cq_len nW dc0 nB nAll nTot

theorem phiP : ∀ x ∈ Icc (98749 / 1000000 : ℝ) 1, CovP.Phi x ≤ BudP := fun x hx =>
  Phi_of CovP (lo := 98749 / 1000000) _ _ pS0 pA0 (blks_ok RPd pB pHq0 pAll) pEs pK pH0 pChain
    (by rw [pHd]; exact pNodes) pBot pTop ⟨by push_cast; exact hx.1, by simpa using hx.2⟩

theorem blkN : ∀ B ∈ CovN.Bs, 0 < B.rho ∧ 0 ≤ B.M ∧ Real.log B.rho ≤ B.sg := by
  intro B hB
  rcases List.mem_append.1 hB with h | h
  · exact blks_ok RNd nB nHq0 nAll B h
  · obtain rfl := List.mem_singleton.1 h
    simp [mBlk]

theorem phiN : ∀ x ∈ Icc (19501 / 100000 : ℝ) 1, CovN.Phi x ≤ BudN := fun x hx =>
  Phi_of CovN (lo := 19501 / 100000) _ _ nS0 nA0 blkN nEs nK nH0 nChain
    (by rw [nHd]; exact nNodes) nBot nTop ⟨by push_cast; exact hx.1, by simpa using hx.2⟩

/-- The source-to-polynomial bound of the positive ordinary compact field. -/
theorem posHf : PosHf capSource (Trunc.finite 384) :=
  pos_core gP RPd CovP Enc (Bud := BudP) pRel pTg pT0 pSep pRows pR' pLn pSg pLI pLEI pM pV pG pS' pC pE
    pP64 radP rfl enc_valid enc_q1 rfl rfl rfl rfl rfl phiP pGl pmq pFin

/-- The source-to-polynomial bound of the negative ordinary compact field. -/
theorem negHf : NegHf capSource (Trunc.finite 384) :=
  neg_core gN RNd CovN Enc (Bud := BudN) nRel nTg nT0 nSep nRows nR' nLn nSg nLI nLEI nM nV nG nS' nC
    nMi nMe nMir nl1 nl2 radN rfl rnsN 44 96 (fun i hi => hrn_of nRn hi)
    (fun i hi d hd => hb_of nFb hi hd) nDm nTm enc_valid enc_q1 rfl rfl rfl rfl rfl phiN nmq nFin

end

end CatalanMeasure.GenD.Signed.RouteI.OrdHf

module

public import CatalanMeasure.GenD.Signed.EnergyFixed

/-!
# The signed second-sheet energy bound with fixed first-kind and near-type nodes

Extension of `Signed.EnergyFixed` by a third fixed population: the **near-type** positive nodes
`zp` (the set `S` of the marked positives of Lemma 17.43.1, `MarkedExpansion`).  In the
`S`-term of the determinant expansion the pairs (near, other) carry `log (1 - x y)` instead of
`log |x - y|` (the `groupedPairProduct` of the 532 route):

* the Vandermonde (D7.1), the pin and the free copy are applied to the NON-NEAR rows only
  (free rows, first-kind fixed rows), with a reference `μ` of mass `1 - s/ν`;
* the near-near pairs are bounded by `0` (`|z - z'| ≤ 1`);
* the cross Cauchy pairs are cancelled against the decay convexity: the positive pairs by the
  series `-ip (P, Q)` (the decay convexity `½ L(ρ⁺)` of the tilted square), the negative pairs by
  `-ip (B, Q)` plus the dilation error `log (1/τ²)`; the tangent point of the negative
  quadratic is shifted by the near power sum `Q` (`quad_master_near`), which leaves the linear
  near field `fld (R - t)` and the diagonal `ip (Q, Q) ≤ (s/ν²) Σ -log (1 - z²)`;
* the fixed rows carry their own row fields `Rm` (first kind, `groupedMarkedField`) and `Rn`
  (near, `groupedNearField`), the exact fields of the 532 identity `log_groupedProduct`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### Power sums of appended lists -/

theorem powSum_append {a b : ℕ} (τ ν : ℝ) (y : Fin a → ℝ) (z : Fin b → ℝ) (n : ℕ) :
    powSum τ ν (Fin.append y z) n = powSum τ ν y n + powSum τ ν z n := by
  unfold powSum
  rw [row_sum_split (fun u => (τ * u) ^ (n + 1)) y z]
  ring

theorem powSum_split3 {a b c : ℕ} (τ ν : ℝ) (gp : Fin a → ℝ) (yp : Fin b → ℝ) (zp : Fin c → ℝ)
    (n : ℕ) :
    powSum τ ν (Fin.append gp (Fin.append yp zp)) n =
      powSum τ ν (Fin.append gp yp) n + powSum τ ν zp n := by
  rw [powSum_append, powSum_append, powSum_append]; ring

/-! ### The cross Cauchy pairs -/

theorem cross_pp_le {a b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (u : Fin a → ℝ) (z : Fin b → ℝ) (hu : ∀ i, u i ∈ Ioo (0 : ℝ) 1)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    (∑ i, ∑ j, Real.log (1 - u i * z j)) / ν ^ 2 ≤ -ip (powSum τ ν u) (powSum τ ν z) := by
  have hu' : ∀ i, |τ * u i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hu i).1]
    nlinarith [hτ.1, hτ.2, (hu i).1, (hu i).2]
  have hz' : ∀ j, |τ * z j| < 1 := fun j => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz j).1]
    nlinarith [hτ.1, hτ.2, (hz j).1, (hz j).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hu' hz').tsum_eq
  have hip : ip (powSum τ ν u) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * u i) * (τ * z j))) / ν ^ 2 := h
  rw [hip, neg_div, neg_neg]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ν)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have huz : 0 ≤ u i * z j := mul_nonneg (hu i).1.le (hz j).1.le
  have hlt : u i * z j < 1 := by nlinarith [(hu i).1, (hu i).2, (hz j).1, (hz j).2]
  have e : (τ * u i) * (τ * z j) = τ ^ 2 * (u i * z j) := by ring
  refine Real.log_le_log (by linarith) ?_
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.1.le hτ.2.le : τ ^ 2 ≤ 1) huz]

theorem cross_np_le {a b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (xn : Fin a → ℝ) (z : Fin b → ℝ) (hx : ∀ i, xn i ∈ Ioo (-1 : ℝ) 0)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    (∑ i, ∑ j, Real.log (1 - xn i * z j)) / ν ^ 2 ≤ -ip (powSum τ ν xn) (powSum τ ν z) +
      ((a : ℝ) * b / ν ^ 2) * Real.log (1 / τ ^ 2) := by
  have hx' : ∀ i, |τ * xn i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_neg (hx i).2]
    nlinarith [hτ.1, hτ.2, (hx i).1, (hx i).2]
  have hz' : ∀ j, |τ * z j| < 1 := fun j => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz j).1]
    nlinarith [hτ.1, hτ.2, (hz j).1, (hz j).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hx' hz').tsum_eq
  have hip : ip (powSum τ ν xn) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) / ν ^ 2 := h
  rw [hip, neg_div, neg_neg]
  have hτ2 : 0 < τ ^ 2 := pow_pos hτ.1 2
  have hL : ∀ i j, Real.log (1 - xn i * z j) ≤
      Real.log (1 - (τ * xn i) * (τ * z j)) + Real.log (1 / τ ^ 2) := by
    intro i j
    have hxz : xn i * z j < 0 := mul_neg_of_neg_of_pos (hx i).2 (hz j).1
    have e : (τ * xn i) * (τ * z j) = τ ^ 2 * (xn i * z j) := by ring
    have hp1 : 0 < 1 - (τ * xn i) * (τ * z j) := by rw [e]; nlinarith
    have hp2 : 0 < 1 - xn i * z j := by linarith
    rw [← Real.log_mul hp1.ne' (by positivity)]
    refine Real.log_le_log hp2 ?_
    rw [e, mul_one_div, le_div_iff₀ hτ2]
    nlinarith [mul_le_mul_of_nonneg_right (pow_le_one₀ hτ.1.le hτ.2.le : τ ^ 2 ≤ 1)
      (neg_nonneg.mpr hxz.le)]
  have hs : ∑ i, ∑ j, Real.log (1 - xn i * z j) ≤
      (∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) +
        (a : ℝ) * b * Real.log (1 / τ ^ 2) := by
    calc ∑ i, ∑ j, Real.log (1 - xn i * z j)
        ≤ ∑ i : Fin a, ∑ j : Fin b,
            (Real.log (1 - (τ * xn i) * (τ * z j)) + Real.log (1 / τ ^ 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hL i j
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  calc (∑ i, ∑ j, Real.log (1 - xn i * z j)) / ν ^ 2
      ≤ ((∑ i, ∑ j, Real.log (1 - (τ * xn i) * (τ * z j))) +
          (a : ℝ) * b * Real.log (1 / τ ^ 2)) / ν ^ 2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg ν)
    _ = _ := by ring

theorem near_near_nonpos {b : ℕ} (z : Fin b → ℝ) (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| ≤ 0 := by
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
  refine Real.log_nonpos (abs_nonneg _) ?_
  rw [abs_le]
  constructor <;> nlinarith [(hz i).1, (hz i).2, (hz j).1, (hz j).2]

/-! ### The quadratic tangent plane with a near species -/

/-- **The tangent-plane inequality with a near species** `Q`: the cross-Cauchy bounds
`-ip (P, Q)` (positives) and `-ip (B, Q)` (negatives) are carried on the left; the tangent point
of the negative quadratic is shifted by `Q`.  Pointwise the difference of the two sides is
`-½ (B + Q - t)² ≤ 0`. -/
theorem quad_master_near {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {B P Q R mp mn t : ℕ → ℝ}
    (hB : IsGeom τ B) (hP : IsGeom τ P) (hQ : IsGeom τ Q) (hR : IsGeom τ R)
    (hmp : IsGeom τ mp) (hmn : IsGeom τ mn) (ht : IsGeom τ t) :
    -(1 / 2) * ip B B + ip B (fun n => P n + Q n) +
        (1 / 2) * ip (fun n => B n - (P n + Q n) - R n) (fun n => B n - (P n + Q n) - R n)
        - (1 / 2) * ip (fun n => P n - mp n) (fun n => P n - mp n)
        - (1 / 2) * ip (fun n => B n - mn n) (fun n => B n - mn n)
        - ip P Q - ip B Q ≤
      ip P (fun n => mp n + R n) + ip B (fun n => mn n - R n - t n) + (1 / 2) * ip R R
        - (1 / 2) * ip mp mp + (1 / 2) * ip t t - (1 / 2) * ip mn mn
        + ip Q (fun n => R n - t n) + ip Q Q := by
  have hPQ : IsGeom τ (fun n => P n + Q n) := hP.add hQ
  have hBPR : IsGeom τ (fun n => B n - (P n + Q n) - R n) := (hB.sub hPQ).sub hR
  have hPm : IsGeom τ (fun n => P n - mp n) := hP.sub hmp
  have hBm : IsGeom τ (fun n => B n - mn n) := hB.sub hmn
  have hL : HasSum (fun n : ℕ => (-(1 / 2) * (B n * B n) + B n * (P n + Q n) +
      (1 / 2) * ((B n - (P n + Q n) - R n) * (B n - (P n + Q n) - R n)) -
      (1 / 2) * ((P n - mp n) * (P n - mp n)) - (1 / 2) * ((B n - mn n) * (B n - mn n)) -
      P n * Q n - B n * Q n) / ((n : ℝ) + 1))
      (-(1 / 2) * ip B B + ip B (fun n => P n + Q n) +
        (1 / 2) * ip (fun n => B n - (P n + Q n) - R n) (fun n => B n - (P n + Q n) - R n)
        - (1 / 2) * ip (fun n => P n - mp n) (fun n => P n - mp n)
        - (1 / 2) * ip (fun n => B n - mn n) (fun n => B n - mn n)
        - ip P Q - ip B Q) := by
    have h := ((((((((hasSum_ip hτ hB hB).mul_left (-(1 / 2))).add (hasSum_ip hτ hB hPQ)).add
      ((hasSum_ip hτ hBPR hBPR).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hPm hPm).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hBm hBm).mul_left (1 / 2))).sub (hasSum_ip hτ hP hQ)).sub
      (hasSum_ip hτ hB hQ))
    convert h using 1
    funext n; ring
  have hMR : IsGeom τ (fun n => mp n + R n) := hmp.add hR
  have hBmt : IsGeom τ (fun n => mn n - R n - t n) := (hmn.sub hR).sub ht
  have hRt : IsGeom τ (fun n => R n - t n) := hR.sub ht
  have hR' : HasSum (fun n : ℕ => (P n * (mp n + R n) + B n * (mn n - R n - t n) +
      (1 / 2) * (R n * R n) - (1 / 2) * (mp n * mp n) + (1 / 2) * (t n * t n) -
      (1 / 2) * (mn n * mn n) + Q n * (R n - t n) + Q n * Q n) / ((n : ℝ) + 1))
      (ip P (fun n => mp n + R n) + ip B (fun n => mn n - R n - t n) + (1 / 2) * ip R R
        - (1 / 2) * ip mp mp + (1 / 2) * ip t t - (1 / 2) * ip mn mn
        + ip Q (fun n => R n - t n) + ip Q Q) := by
    have h := ((((((((hasSum_ip hτ hP hMR).add (hasSum_ip hτ hB hBmt)).add
      ((hasSum_ip hτ hR hR).mul_left (1 / 2))).sub ((hasSum_ip hτ hmp hmp).mul_left (1 / 2))).add
      ((hasSum_ip hτ ht ht).mul_left (1 / 2))).sub ((hasSum_ip hτ hmn hmn).mul_left (1 / 2))).add
      (hasSum_ip hτ hQ hRt)).add (hasSum_ip hτ hQ hQ))
    convert h using 1
    funext n; ring
  refine hasSum_le (fun n => ?_) hL hR'
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hn]
  nlinarith [sq_nonneg (B n + Q n - t n)]

theorem eD7_mono (D : SignedData) (hν : 0 < D.ν) (hC : 0 ≤ D.Cb) (hτ : D.τ ∈ Ioo (0 : ℝ) 1)
    {p n : ℕ} (h : p ≤ n) : D.eD7 p ≤ D.eD7 n := by
  unfold SignedData.eD7
  have hK : 0 ≤ 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hK0 : 0 < 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hL : 0 ≤ 1 + Real.log (1 / (1 - D.τ ^ 2)) := by
    have : 0 ≤ Real.log (1 / (1 - D.τ ^ 2)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hK0]; nlinarith [hτ.1])
    linarith
  have hab : (p : ℝ) / D.ν ≤ (n : ℝ) / D.ν :=
    div_le_div_of_nonneg_right (by exact_mod_cast h) hν.le
  have ha : 0 ≤ (p : ℝ) / D.ν := by positivity
  have hc : 0 ≤ D.Cb * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2))) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hab hc, mul_le_mul_of_nonneg_left
    (mul_le_mul hab hab ha (ha.trans hab)) hK]


/-! ### Fields of the fixed rows (first kind with `Rm`, near with `Rn`) -/

namespace SignedData

variable (D : SignedData)

/-- Row field of a first-kind fixed row: its own field `Rm` (the exact `groupedMarkedField` of the
532 identity), the D7.1 diagonal cost and the reference potential. -/
def rowBaseM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  Rm x + (1 / (2 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) - rowRef D.μ x

/-- Field of a first-kind fixed negative node. -/
def fNegM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  D.rowBaseM Rm x - (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) -
    2 * barrierTrialS D.a (-D.τ * x) +
    fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) x

/-- Field of a first-kind fixed positive node. -/
def fPosM (Rm : ℝ → ℝ) (x : ℝ) : ℝ :=
  D.rowBaseM Rm x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x

/-- With the spike cost attached. -/
def fPosMS (Rm : ℝ → ℝ) (x : ℝ) : ℝ := D.fPosM Rm x + D.cs * (if 1 - D.θ < x then 1 else 0)

/-- With the spike cost and the Lemma R′ remainder `rc · α · (-log (1 - x²))`. -/
def fPosMR (Rm : ℝ → ℝ) (rc α x : ℝ) : ℝ :=
  D.fPosMS Rm x + rc * α * (-Real.log (1 - x ^ 2))

/-- Field of a near-type node (second-sheet row of Lemma 17.43.1): its own field `Rn` (the exact
`groupedNearField`), the decay terms of a positive node WITHOUT the D7.1 terms (the near rows are
not in the D7.1 list), the linear field of the shifted tangent point `fld (R - t)`, the diagonal
`β (-log (1 - x²))` of `ip (Q, Q)` (`β = s/ν`) and the dilation error `log (1/τ²)` of the
negative cross pairs. -/
def fNearM (Rn : ℝ → ℝ) (β x : ℝ) : ℝ :=
  Rn x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => D.R n - D.t n) x + β * (-Real.log (1 - x ^ 2)) + Real.log (1 / D.τ ^ 2)

/-- With the spike cost attached. -/
def fNearMS (Rn : ℝ → ℝ) (β x : ℝ) : ℝ :=
  D.fNearM Rn β x + D.cs * (if 1 - D.θ < x then 1 else 0)

end SignedData

theorem sum_fNegM_eq (D : SignedData) (Rm : ℝ → ℝ) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNegM Rm (xn b) = (∑ b, D.rowBaseM Rm (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) (xn b) := by
  unfold SignedData.fNegM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fPosM_eq (D : SignedData) (Rm : ℝ → ℝ) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPosM Rm (gp p) = (∑ p, D.rowBaseM Rm (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) := by
  unfold SignedData.fPosM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fNearM_eq (D : SignedData) (Rn : ℝ → ℝ) (β : ℝ) {s : ℕ} (zp : Fin s → ℝ) :
    ∑ j, D.fNearM Rn β (zp j) = (∑ j, Rn (zp j)) +
      2 * (∑ j, barrierTrialS D.a (-D.τ * zp j)) -
      ((D.sp : ℝ) / D.ν) * (∑ j, denPoly D.b D.K (zp j)) +
      (∑ j, fld D.τ (fun n => D.R n - D.t n) (zp j)) +
      β * (∑ j, -Real.log (1 - zp j ^ 2)) + (s : ℝ) * Real.log (1 / D.τ ^ 2) := by
  unfold SignedData.fNearM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The D7.1 row terms of the free and the first-kind fixed rows. -/
theorem rowBase_split4 (D : SignedData) (hν : 0 < D.ν) (Rm : ℝ → ℝ) {k m1 q m2 : ℕ}
    (xn : Fin k → ℝ) (yn : Fin m1 → ℝ) (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) :
    ((∑ b, D.Rf (xn b)) + (∑ p, D.Rf (gp p))) / D.ν +
      ((∑ j, Rm (yn j)) + ∑ j, Rm (yp j)) / D.ν +
      (1 / 2) * ((((∑ b, (1 / D.ν) ^ 2 * (-Real.log |xn b| + Real.log (1 / (1 - D.τ ^ 2)))) +
        ∑ j, (1 / D.ν) ^ 2 * (-Real.log |yn j| + Real.log (1 / (1 - D.τ ^ 2)))) +
        ((∑ p, (1 / D.ν) ^ 2 * (-Real.log |gp p| + Real.log (1 / (1 - D.τ ^ 2)))) +
          ∑ j, (1 / D.ν) ^ 2 * (-Real.log |yp j| + Real.log (1 / (1 - D.τ ^ 2)))))) -
      ((((∑ b, rowRef D.μ (xn b)) + ∑ j, rowRef D.μ (yn j)) +
        ((∑ p, rowRef D.μ (gp p)) + ∑ j, rowRef D.μ (yp j)))) / D.ν =
    (1 / D.ν) * (((∑ b, D.rowBaseFix (xn b)) + ∑ p, D.rowBaseFix (gp p)) +
      ((∑ j, D.rowBaseM Rm (yn j)) + ∑ j, D.rowBaseM Rm (yp j))) := by
  unfold SignedData.rowBaseFix SignedData.rowBaseM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]
  field_simp
  ring


/-! ### The master inequality with a near species -/

set_option maxHeartbeats 3200000 in
/-- **The master inequality with first-kind fixed and near-type nodes.**  Free rows `xn`
(negative), `gp` (positive) with columns `sc`; first-kind fixed rows `yn`, `yp`; near-type
positive rows `zp`.  Pin and free copy on the free rows; D7.1 on the non-near rows
(reference mass `(ν - s)/ν`); the route II ratio, the prefactor and the tilted square on the
positive list `gp ++ (yp ++ zp)` (all positives); the near species through `quad_master_near`. -/
theorem signed_master_near (D : SignedData) {k q m1 m2 s : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hkm : ((k + m1 : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : ∀ τ, BD (D.μ τ) D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : (((k + m1) + (q + m2) : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    (hμf : ∀ τ, BD (D.μf τ) D.Cbf) (hCf : 0 ≤ D.Cbf)
    (hmassf : ((k + q : ℕ) : ℝ) / D.ν = ∑ τ, (D.μf τ).real univ)
    (Rm Rn : ℝ → ℝ)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ p, zp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (LR spike : ℝ)
    (hA7 : LR / D.ν ^ 2 ≤ logPref (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) / D.ν ^ 2 +
      D.numB (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) -
      D.denB (Fin.append gp (Fin.append yp zp)) + spike) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / D.ν ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          D.ν ^ 2 +
        ((∑ b, D.Rf (xn b)) + ∑ p, D.Rf (gp p)) / D.ν +
        ((∑ j, Rm (yn j)) + ∑ j, Rm (yp j)) / D.ν + (∑ j, Rn (zp j)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR / D.ν ^ 2 ≤
      D.constFix (k + q) ((k + m1) + (q + m2) + s) + spike +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegM Rm (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, D.fPosM Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearM Rn ((s : ℝ) / D.ν) (zp j) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  have hτb := realEnergyTau_bounds he
  have hτ : D.τ ∈ Ioo (0 : ℝ) 1 := hτb
  have hτ1 : D.τ ∈ Ioc (0 : ℝ) 1 := ⟨hτb.1, hτb.2.le⟩
  have hτ0 := hτ.1
  have hXN : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hxn i
    · simp only [Fin.append_right]; exact hyn i
  have hGP : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hgp i
    · simp only [Fin.append_right]; exact hyp i
  have hGPall : ∀ p, Fin.append gp (Fin.append yp zp) p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hgp i
    · simp only [Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]; exact hyp j
      · simp only [Fin.append_right]; exact hzp j
  have hZ : ∀ i, Fin.append (Fin.append xn yn) (Fin.append gp yp) i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hGP p).1], (hGP p).2⟩
  have hZ0 : ∀ i, Fin.append (Fin.append xn yn) (Fin.append gp yp) i ≠ 0 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact (hXN b).2.ne
    · simp only [Fin.append_right]; exact (hGP p).1.ne'
  have hxF : ∀ i, Fin.append xn gp i ∈ Ioo (-1 : ℝ) 1 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact ⟨(hxn b).1, by linarith [(hxn b).2]⟩
    · simp only [Fin.append_right]; exact ⟨by linarith [(hgp p).1], (hgp p).2⟩
  have hx0F : ∀ i, Fin.append xn gp i ≠ 0 := by
    intro i
    refine Fin.addCases (fun b => ?_) (fun p => ?_) i
    · simp only [Fin.append_left]; exact (hxn b).2.ne
    · simp only [Fin.append_right]; exact (hgp p).1.ne'
  have h1 := pin_zero_canonical hν he hp hxF hs hinjF hsi D.v hv
  have h2 := rows_vandermonde_le hν (Fin.append (Fin.append xn yn) (Fin.append gp yp)) hZ0 hZ hinj
    D.μ hμ hC hmass (ρ := D.τ ^ 2) (pow_pos hτ.1 2) (by nlinarith [hτ.1, hτ.2])
  have h2f := rows_vandermonde_le hν (Fin.append xn gp) hx0F hxF hinjF D.μf hμf hCf hmassf
    (ρ := D.τ ^ 2) (pow_pos hτ.1 2) (by nlinarith [hτ.1, hτ.2])
  have hn' : ∀ b, Fin.append xn yn b < 0 := fun b => (hXN b).2
  have hg' : ∀ p, 0 < Fin.append gp yp p := fun p => (hGP p).1
  rw [Fintype.sum_bool, Lpart_true_eq hτ0 hν (Fin.append xn yn) (Fin.append gp yp) hn' hg' D.μ,
    Lpart_false_eq hτ0 hν (Fin.append xn yn) (Fin.append gp yp) hn' hg' D.μ] at h2
  rw [Fintype.sum_bool, Lpart_true_eq hτ0 hν xn gp (fun b => (hxn b).2) (fun p => (hgp p).1) D.μf,
    Lpart_false_eq hτ0 hν xn gp (fun b => (hxn b).2) (fun p => (hgp p).1) D.μf] at h2f
  have nn1 := ip_self_nonneg (fun n => powSum D.τ D.ν gp n - mpos D.μf D.τ n)
  have nn2 := ip_self_nonneg (fun n => powSum D.τ D.ν xn n - mneg D.μf D.τ n)
  have hsplitF : pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc =
      pinOffDiagonalInteraction D.ν 0 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |Fin.append xn gp j - Fin.append xn gp i|) /
          D.ν ^ 2 := by
    unfold pinOffDiagonalInteraction; ring
  have h3 := logPref_le_prefTau hτ1 hν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp))
    hXN hGPall
  have hnorm1 : ∀ b, |D.τ * Fin.append xn yn b| < 1 := fun b => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append xn yn b| < 1 := abs_lt.mpr ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    nlinarith [hτ.2, abs_nonneg (Fin.append xn yn b)]
  have hnorm2 : ∀ p, |D.τ * Fin.append gp (Fin.append yp zp) p| < 1 := fun p => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append gp (Fin.append yp zp) p| < 1 :=
      abs_lt.mpr ⟨by linarith [(hGPall p).1], (hGPall p).2⟩
    nlinarith [hτ.2, abs_nonneg (Fin.append gp (Fin.append yp zp) p)]
  have h4 := prefTau_eq hν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) hnorm1 hnorm2
  have hxn1 : ∀ b, |Fin.append xn yn b| ≤ 1 :=
    fun b => (abs_lt.mpr ⟨(hXN b).1, by linarith [(hXN b).2]⟩).le
  have hgp1 : ∀ p, |Fin.append gp yp p| ≤ 1 :=
    fun p => (abs_lt.mpr ⟨by linarith [(hGP p).1], (hGP p).2⟩).le
  have hzp1 : ∀ p, |zp p| ≤ 1 :=
    fun p => (abs_lt.mpr ⟨by linarith [(hzp p).1], (hzp p).2⟩).le
  have hB := isGeom_powSum hτ0 hν (Fin.append xn yn) hxn1
  have hP := isGeom_powSum hτ0 hν (Fin.append gp yp) hgp1
  have hQ := isGeom_powSum hτ0 hν zp hzp1
  have hmp : IsGeom D.τ (mpos D.μ D.τ) := isGeom_refMoment (hμ true) hτ0
  have hmn : IsGeom D.τ (mneg D.μ D.τ) := isGeom_mneg (hμ false) hτ0
  have h5 := quad_master_near hτ hB hP hQ hR hmp hmn ht
  have hl1 := ip_powSum_left hτ hν (Fin.append gp yp) hgp1 (hmp.add hR)
  have hl1q := ip_powSum_left hτ hν zp hzp1 (hR.sub ht)
  have hl2 := ip_powSum_left hτ hν (Fin.append xn yn) hxn1 ((hmn.sub hR).sub ht)
  have hQQ := lemmaR'_linearisation hτ hν zp hzp
  have hcpp := cross_pp_le hτ hν (Fin.append gp yp) zp hGP hzp
  have hcnp := cross_np_le hτ hν (Fin.append xn yn) zp hXN hzp
  have hnn0 := div_nonpos_of_nonpos_of_nonneg (near_near_nonpos zp hzp) (sq_nonneg D.ν)
  have hmono := eD7_mono D hν hC hτ (p := (k + m1) + (q + m2)) (n := (k + m1) + (q + m2) + s)
    (by omega)
  have hpA : powSum D.τ D.ν (Fin.append gp (Fin.append yp zp)) =
      fun n => powSum D.τ D.ν (Fin.append gp yp) n + powSum D.τ D.ν zp n :=
    funext fun n => powSum_split3 D.τ D.ν gp yp zp n
  have hcross : (∑ i, ∑ j, Real.log (1 -
        Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) =
      (∑ b, ∑ j, Real.log (1 - Fin.append xn yn b * zp j)) +
        ∑ p, ∑ j, Real.log (1 - Fin.append gp yp p * zp j) :=
    row_sum_split (fun u => ∑ j, Real.log (1 - u * zp j)) (Fin.append xn yn) (Fin.append gp yp)
  have hL0 : 0 ≤ Real.log (1 / D.τ ^ 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (pow_pos hτ0 2)]; nlinarith [hτ.1, hτ.2])
  have herr : (((k + m1 : ℕ) : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2) ≤
      (1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2)) := by
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    calc (((k + m1 : ℕ) : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2)
        = (((k + m1 : ℕ) : ℝ) / D.ν) * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) := by
          field_simp
      _ ≤ 1 * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) :=
          mul_le_mul_of_nonneg_right ((div_le_one hν).mpr hkm) (by positivity)
      _ = _ := one_mul _
  -- row terms
  have hbaseZ := rowBase_split4 D hν Rm xn yn gp yp
  have hlogZ := sum_split4 (fun x => (1 / D.ν) ^ 2 * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))))
    xn yn gp yp
  have hrefZ := sum_split4 (fun x => rowRef D.μ x) xn yn gp yp
  beta_reduce at hlogZ hrefZ
  have hpin := pinPart_sum D hν (Fin.append xn gp)
  rw [row_sum_split D.pinPart xn gp] at hpin
  have e1 := row_sum_split (fun x => -barrierTrialS D.a (-D.τ * x)) xn yn
  have e2 := row_sum_split (fun x => barrierTrialS D.a (-D.τ * x)) gp (Fin.append yp zp)
  have e2' := row_sum_split (fun x => barrierTrialS D.a (-D.τ * x)) yp zp
  have e3 := row_sum_split (fun x => denPoly D.b D.K x) gp (Fin.append yp zp)
  have e3' := row_sum_split (fun x => denPoly D.b D.K x) yp zp
  have e4 := row_sum_split (fun x => Real.log (1 - (D.τ * x) * (D.τ * x))) xn yn
  have e5 := row_sum_split (fun x => fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x) gp yp
  have e6 := row_sum_split
    (fun x => fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) x) xn yn
  beta_reduce at e1 e2 e2' e3 e3' e4 e5 e6
  have hsN := congrArg (fun z => (1 / D.ν) * z) (sum_fNeg_eq D xn)
  have hsNF := congrArg (fun z => (1 / D.ν) * z) (sum_fNegM_eq D Rm yn)
  have hsP := congrArg (fun z => (1 / D.ν) * z) (sum_fPos_eq D gp)
  have hsPF := congrArg (fun z => (1 / D.ν) * z) (sum_fPosM_eq D Rm yp)
  have hsZ := congrArg (fun z => (1 / D.ν) * z) (sum_fNearM_eq D Rn ((s : ℝ) / D.ν) zp)
  beta_reduce at hsN hsNF hsP hsPF hsZ
  have hsC : ∑ j, D.fCol (sc j) = (∑ j, D.Cf (sc j)) + (∑ j, 2 * barrierTrialT D.v (sc j)) -
      (∑ j, Real.log (1 - sc j)) / D.ν := by
    unfold SignedData.fCol
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have h4' : prefTau D.τ D.ν (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) =
      -(1 / 2) * ip (powSum D.τ D.ν (Fin.append xn yn)) (powSum D.τ D.ν (Fin.append xn yn)) +
        ip (powSum D.τ D.ν (Fin.append xn yn))
          (powSum D.τ D.ν (Fin.append gp (Fin.append yp zp))) -
        (1 / (2 * D.ν ^ 2)) *
          ∑ b, Real.log (1 - (D.τ * Fin.append xn yn b) * (D.τ * Fin.append xn yn b)) := h4
  unfold SignedData.numB SignedData.denB at hA7
  rw [e1, e2, e3, e2', e3'] at hA7
  rw [e4] at h4'
  rw [e5] at hl1
  rw [e6] at hl2
  rw [hpA] at hA7 h4'
  beta_reduce at hA7 h4'
  unfold SignedData.constFix SignedData.constTotal SignedData.eD7 SignedData.eD7f SignedData.Kq
  unfold SignedData.eD7 at hmono
  have hsC' : (1 / D.ν) * ∑ j, D.fCol (sc j) = (1 / D.ν) * ((∑ j, D.Cf (sc j)) +
      (∑ j, 2 * barrierTrialT D.v (sc j)) - (∑ j, Real.log (1 - sc j)) / D.ν) := by rw [hsC]
  rw [hlogZ, hrefZ] at h2
  rw [hcross]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h1 h2 h2f hbaseZ hpin hsC' hA7 hsN hsNF hsP hsPF hsZ hQQ
  push_cast at h1 h2 h2f hbaseZ hpin hsC' hA7 hsN hsNF hsP hsPF hsZ hQQ hcnp hmono herr ⊢
  ring_nf at hA7 h1 h2 h2f h3 h4' h5 hl1 hl1q hl2 hbaseZ hpin hsN hsNF hsP hsPF hsZ hsC' nn1 nn2 hsplitF hQQ hcpp hcnp hnn0 hmono herr ⊢
  linarith only [hA7, h1, h2, h2f, h3, h4', h5, hl1, hl1q, hl2, hbaseZ, hpin, hsN, hsNF, hsP,
    hsPF, hsZ, hsC', nn1, nn2, hsplitF, hQQ, hcpp, hcnp, hnn0, hmono, herr]


theorem fPosMS_le_fPosMR (D : SignedData) (Rm : ℝ → ℝ) {rc α x : ℝ} (hrc : 0 ≤ rc) (hα : 0 ≤ α)
    (hx : x ∈ Ioo (0 : ℝ) 1) : D.fPosMS Rm x ≤ D.fPosMR Rm rc α x := by
  unfold SignedData.fPosMR
  have h1 : Real.log (1 - x ^ 2) ≤ 0 := by
    apply Real.log_nonpos
    · nlinarith [hx.1, hx.2]
    · nlinarith [hx.1, hx.2]
  have : 0 ≤ rc * α * (-Real.log (1 - x ^ 2)) :=
    mul_nonneg (mul_nonneg hrc hα) (by linarith)
  linarith

/-! ### The deterministic theorem with near nodes -/

/-- **The deterministic theorem with first-kind fixed and near-type nodes (fixed `N`).**  The A7
hypothesis is `SpikeCompareFixed` with the marked positives `yp ++ zp` (the near rows are
marked positives of the determinant, in the positive list of the route II ratio). -/
theorem signed_second_energy_near_det (D : SignedData) {k q m1 m2 s : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hkm : ((k + m1 : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : ∀ τ, BD (D.μ τ) D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : (((k + m1) + (q + m2) : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    (hμf : ∀ τ, BD (D.μf τ) D.Cbf) (hCf : 0 ≤ D.Cbf)
    (hmassf : ((k + q : ℕ) : ℝ) / D.ν = ∑ τ, (D.μf τ).real univ)
    (Rm Rn : ℝ → ℝ)
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin (m2 + s) → ℝ) → Prop}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin (m2 + s) → ℝ) → ℝ}
    {c' : ℝ} (hA7 : SpikeCompareFixed D c' Cls LR)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ p, zp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (hcls : Cls xn gp yn (Fin.append yp zp)) :
    D.constant + pinOffDiagonalInteraction D.ν 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / D.ν ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          D.ν ^ 2 +
        ((∑ b, D.Rf (xn b)) + ∑ p, D.Rf (gp p)) / D.ν +
        ((∑ j, Rm (yn j)) + ∑ j, Rm (yp j)) / D.ν + (∑ j, Rn (zp j)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR xn gp yn (Fin.append yp zp) / D.ν ^ 2 ≤
      D.constFix (k + q) ((k + m1) + (q + m2) + s) + D.errJ3 c' ((k + m1) + (q + m2) + s) +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegM Rm (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosMS Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearMS Rn ((s : ℝ) / D.ν) (zp j) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  have hyp' : ∀ p, Fin.append yp zp p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hyp i
    · simp only [Fin.append_right]; exact hzp i
  have hA := hA7 xn gp yn (Fin.append yp zp) hxn hgp hyn hyp' hcls
  have hN : (k + m1) + (q + (m2 + s)) = (k + m1) + (q + m2) + s := by omega
  rw [hN] at hA
  have h := signed_master_near D hν he hp hkm hv hR ht hμ hC hmass hμf hCf hmassf Rm Rn xn gp yn
    yp zp sc hxn hgp hyn hyp hzp hinjF hinj hs hsi (LR xn gp yn (Fin.append yp zp))
    (D.spikeTerm (Fin.append gp (Fin.append yp zp)) + D.errJ3 c' ((k + m1) + (q + m2) + s))
    (by linarith only [hA])
  have e := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) gp (Fin.append yp zp)
  have e' := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) yp zp
  beta_reduce at e e'
  have hsp : D.spikeTerm (Fin.append gp (Fin.append yp zp)) +
      ((1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, D.fPosM Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearM Rn ((s : ℝ) / D.ν) (zp j)) =
      (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosMS Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearMS Rn ((s : ℝ) / D.ν) (zp j) := by
    unfold SignedData.spikeTerm SignedData.fPosS SignedData.fPosMS SignedData.fNearMS
    rw [e, e']
    simp only [Finset.sum_add_distrib]
    ring
  linarith only [h, hsp]


/-! ### The contract (α-dependent caps) and the theorem -/

/-- **The contract with fixed first-kind and near-type nodes, indexed by α-intervals, with caps
that are FUNCTIONS of the fixed fraction `α = (m₁ + m₂ + s)/n` and of the near fraction
`β = s/n`.**  On interval `i` the trial data `D i N α β` (a `SignedData`: references `μ` of mass
`1 - β` (the non-near rows) and `μf` of mass `1 - α` (the free rows), trial sequences, tilt data)
may depend on `N`, `α`, `β`; the caps `MXn MXp MY cInf` are functions of `(α, β)` and the
fixed-node sup `ZB` of the three fractions `(m₁/n, m₂/n, s/n)`.  The problem's own data are
`ν = n N`, the free-row field `Rf`, the column field `Cf`, the EXACT fixed-row fields `Rm`
(`groupedMarkedField`) and `Rn` (`groupedNearField`) and the constant `constant N α` (the exact
grouped constant at `α n` fixed rows).  The per-fixed-row cost of the second sheet is the field
`cost` of the budget: `budgetFix` has right side `B + cost · α`. -/
structure SignedNearBounds (I : ℕ) where
  ncount : ℕ → ℕ
  ncount_pos : ∀ N, 0 < ncount N
  B : ℝ
  cost : ℝ
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  lo : Fin I → ℝ
  hi : Fin I → ℝ
  cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i
  D : Fin I → ℕ → ℝ → ℝ → SignedData
  Rf : ℕ → ℝ → ℝ
  Cf : ℕ → ℝ → ℝ
  Rm : ℕ → ℝ → ℝ
  Rn : ℕ → ℝ → ℝ
  constant : ℕ → ℝ → ℝ
  same : ∀ i N α β, (D i N α β).ν = (ncount N : ℝ) ∧ (D i N α β).Rf = Rf N ∧
    (D i N α β).Cf = Cf N ∧ (D i N α β).constant = constant N α
  MXn : Fin I → ℝ → ℝ → ℝ
  MXp : Fin I → ℝ → ℝ → ℝ
  MY : Fin I → ℝ → ℝ → ℝ
  cInf : Fin I → ℝ → ℝ → ℝ
  κlo : Fin I → ℝ
  κhi : Fin I → ℝ
  epsSplit : Fin I → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  ZB : Fin I → ℝ → ℝ → ℝ → ℝ
  Clsf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop
  e_mem : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc (0 : ℝ) α,
    (D i N α β).e ∈ Ioo (0 : ℝ) (1 / 8)
  v_summable : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc (0 : ℝ) α,
    Summable (fun j => |(D i N α β).v j|)
  R_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc (0 : ℝ) α,
    IsGeom (D i N α β).τ (D i N α β).R
  t_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc (0 : ℝ) α,
    IsGeom (D i N α β).τ (D i N α β).t
  reference : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc (0 : ℝ) α,
    (∀ τ, BD ((D i N α β).μ τ) (D i N α β).Cb) ∧ 0 ≤ (D i N α β).Cb ∧
      1 - β = ∑ τ, ((D i N α β).μ τ).real univ ∧
    (∀ τ, BD ((D i N α β).μf τ) (D i N α β).Cbf) ∧ 0 ≤ (D i N α β).Cbf ∧
      1 - α = ∑ τ, ((D i N α β).μf τ).real univ
  cp : Fin I → ℕ → ℝ → ℝ → ℝ
  cp_pos : ∀ i N α β, 0 < cp i N α β
  cp_le : ∀ i N α β, cp i N α β ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, (D i N α β).errJ3 (cp i N α β) (ncount N) ≤ ε
  spikeFix : ∀ i N α β k q m1 m2,
    SpikeCompareFixed (D i N α β) (cp i N α β) (Clsf N k q m1 m2) (LRf N k q m1 m2)
  rowNeg : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, ∀ x ∈ Ioo (-1 : ℝ) 0, (D i N α β).fNeg x ≤ MXn i α β + ε
  rowPos : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, ∀ x ∈ Ioo (0 : ℝ) 1, (D i N α β).fPosS x ≤ MXp i α β + ε
  column : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, ∀ s ∈ Ioo (0 : ℝ) 1, (D i N α β).fCol s ≤ MY i α β + ε
  fixedSum : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) → (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
      FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (ncount N : ℝ) = α →
      (s : ℝ) / (ncount N : ℝ) = β →
      (1 / (D i N α β).ν) * ((∑ j, (D i N α β).fNegM (Rm N) (yn j)) +
          (∑ j, (D i N α β).fPosMR (Rm N) (remC (epsSplit i)) α (yp j)) +
          ∑ j, (D i N α β).fNearMS (Rn N) β (zp j)) ≤
        ZB i ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ))
          ((s : ℝ) / (ncount N : ℝ)) + ε
  const_le : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc (0 : ℝ) α, (D i N α β).constTotal (ncount N) ≤ cInf i α β + ε
  budgetFix : ∀ i (κ c d e : ℝ), κlo i ≤ κ → κ ≤ κhi i → 0 ≤ c → 0 ≤ d → 0 ≤ e →
    lo i ≤ c + d + e → c + d + e ≤ hi i → κ + (c + d + e) ≤ 1 →
    cInf i (c + d + e) e + (2 * (c + d + e) - (c + d + e) ^ 2) * Real.log 2 +
      κ * MXn i (c + d + e) e + (1 - κ - (c + d + e)) * MXp i (c + d + e) e +
      (1 - (c + d + e)) * MY i (c + d + e) e + ZB i c d e ≤ B + cost * (c + d + e)

set_option maxHeartbeats 3200000 in
/-- **Theorem `signed_second_energy_near_nodes`.**  For every `δ > 0` and all large `N`, every
configuration of `k` free negatives, `q` free positives (with `k + q` columns), `m₁` first-kind
fixed negatives, `m₂` first-kind fixed positives and `s` near-type positives,
`(k + m₁) + (q + (m₂ + s)) = n N`, `m₁ + m₂ + s ≤ α₁ n N`, with the free negative fraction in the
range of every interval containing `α = (m₁ + m₂ + s)/n`, admissible fixed nodes and in the class,
has `constant + E_disc + V_nonnear/ν² + V_near/ν² + Cauchy_cross/ν² + fields + LR/ν² ≤ B + cost·α + δ`.
Factor-free statement. -/
theorem signed_second_energy_near_nodes {I : ℕ} (T : SignedNearBounds I) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (k q m1 m2 s : ℕ),
      (k + m1) + (q + (m2 + s)) = T.ncount N →
      ((m1 + m2 + s : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) →
      (∀ i, T.lo i ≤ ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) →
        ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
        T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i) →
      ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
        (sc : Fin (k + q) → ℝ),
      (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
      (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) →
      (∀ p, zp p ∈ Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append xn gp) →
      Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)) →
      (∀ j, sc j ∈ Ioo (0 : ℝ) 1) → Function.Injective sc →
      T.Clsf N k q m1 (m2 + s) xn gp yn (Fin.append yp zp) → T.FixAdm N m1 m2 s yn yp zp →
      T.constant N (((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ)) +
        pinOffDiagonalInteraction (T.ncount N : ℝ) 1 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / (T.ncount N : ℝ) ^ 2 +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / (T.ncount N : ℝ) ^ 2 +
        (∑ i, ∑ j, Real.log (1 - Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) /
          (T.ncount N : ℝ) ^ 2 +
        ((∑ b, T.Rf N (xn b)) + ∑ p, T.Rf N (gp p)) / (T.ncount N : ℝ) +
        ((∑ j, T.Rm N (yn j)) + ∑ j, T.Rm N (yp j)) / (T.ncount N : ℝ) +
        (∑ j, T.Rn N (zp j)) / (T.ncount N : ℝ) +
        (∑ j, T.Cf N (sc j)) / (T.ncount N : ℝ) +
        T.LRf N k q m1 (m2 + s) xn gp yn (Fin.append yp zp) / (T.ncount N : ℝ) ^ 2 ≤
      T.B + T.cost * (((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ)) + δ := by
  have hε : 0 < δ / 8 := by linarith
  have hall : ∀ᶠ N : ℕ in Filter.atTop, ∀ i : Fin I,
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        (T.D i N α β).e ∈ Ioo (0 : ℝ) (1 / 8)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        Summable (fun j => |(T.D i N α β).v j|)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        IsGeom (T.D i N α β).τ (T.D i N α β).R) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        IsGeom (T.D i N α β).τ (T.D i N α β).t) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        (∀ τ, BD ((T.D i N α β).μ τ) (T.D i N α β).Cb) ∧ 0 ≤ (T.D i N α β).Cb ∧
          1 - β = ∑ τ, ((T.D i N α β).μ τ).real univ ∧
        (∀ τ, BD ((T.D i N α β).μf τ) (T.D i N α β).Cbf) ∧ 0 ≤ (T.D i N α β).Cbf ∧
          1 - α = ∑ τ, ((T.D i N α β).μf τ).real univ) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α, ∀ x ∈ Ioo (-1 : ℝ) 0,
        (T.D i N α β).fNeg x ≤ T.MXn i α β + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α, ∀ x ∈ Ioo (0 : ℝ) 1,
        (T.D i N α β).fPosS x ≤ T.MXp i α β + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α, ∀ s ∈ Ioo (0 : ℝ) 1,
        (T.D i N α β).fCol s ≤ T.MY i α β + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
          (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) →
          (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
          T.FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) = α →
          (s : ℝ) / (T.ncount N : ℝ) = β →
          (1 / (T.D i N α β).ν) * ((∑ j, (T.D i N α β).fNegM (T.Rm N) (yn j)) +
              (∑ j, (T.D i N α β).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
              ∑ j, (T.D i N α β).fNearMS (T.Rn N) β (zp j)) ≤
            T.ZB i ((m1 : ℝ) / (T.ncount N : ℝ)) ((m2 : ℝ) / (T.ncount N : ℝ))
              ((s : ℝ) / (T.ncount N : ℝ)) + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        (T.D i N α β).constTotal (T.ncount N) ≤ T.cInf i α β + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ β ∈ Icc (0 : ℝ) α,
        (T.D i N α β).errJ3 (T.cp i N α β) (T.ncount N) ≤ δ / 8) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [T.e_mem i, T.v_summable i, T.R_geom i, T.t_geom i, T.reference i,
      T.rowNeg i hε, T.rowPos i hε, T.column i hε, T.fixedSum i hε, T.const_le i hε,
      T.err_small i hε]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  filter_upwards [hall] with N hN k q m1 m2 s hkq hα hκ xn gp yn yp zp sc hxn hgp hyn hyp hzp
    hinjF hinj hs hsi hcls hadm
  have hνp : (0 : ℝ) < (T.ncount N : ℝ) := by exact_mod_cast T.ncount_pos N
  have hkqR : (((k + m1) + (q + (m2 + s)) : ℕ) : ℝ) = (T.ncount N : ℝ) := by exact_mod_cast hkq
  set n : ℝ := (T.ncount N : ℝ) with hn
  set α : ℝ := ((m1 + m2 + s : ℕ) : ℝ) / n with hαdef
  set β : ℝ := (s : ℝ) / n with hβdef
  have hm10 : (0 : ℝ) ≤ m1 := Nat.cast_nonneg m1
  have hm20 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg m2
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hα1 : α ≤ T.α1 := by rw [hαdef, div_le_iff₀ hνp]; exact hα
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hβα : β ≤ α := by
    rw [hβdef, hαdef]
    refine div_le_div_of_nonneg_right ?_ hνp.le
    push_cast; linarith
  obtain ⟨i, hlo, hhi⟩ := T.cover α hα0 hα1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hN i
  have hαI : α ∈ Icc (T.lo i) (T.hi i) := ⟨hlo, hhi⟩
  have hβI : β ∈ Icc (0 : ℝ) α := ⟨hβ0, hβα⟩
  obtain ⟨hνD, hRfD, hCfD, hcD⟩ := T.same i N α β
  rw [← hn] at hνD
  have he := h1 α hαI β hβI
  have hv := h2 α hαI β hβI
  have hR := h3 α hαI β hβI
  have ht := h4 α hαI β hβI
  obtain ⟨hμ, hC, hmu1, hμf, hCf, hmuf⟩ := h5 α hαI β hβI
  have hν : 0 < (T.D i N α β).ν := by rw [hνD]; exact hνp
  have hsum : (k : ℝ) + m1 + (q + (m2 + s)) = n := by
    have := hkqR; push_cast at this; linarith
  have hpfN : ((k + q : ℕ) : ℝ) ≤ (T.D i N α β).ν := by
    rw [hνD, ← hkqR]; push_cast; linarith
  have hkmN : ((k + m1 : ℕ) : ℝ) ≤ (T.D i N α β).ν := by
    rw [hνD, ← hkqR]; push_cast; linarith
  have hmass' : (((k + m1) + (q + m2) : ℕ) : ℝ) / (T.D i N α β).ν =
      ∑ τ, ((T.D i N α β).μ τ).real univ := by
    rw [← hmu1, hνD, hβdef]
    push_cast
    field_simp
    linarith
  have hfree : ((k + q : ℕ) : ℝ) / (T.D i N α β).ν = 1 - α := by
    rw [hνD, hαdef]; push_cast
    field_simp; linarith
  have hmassf' : ((k + q : ℕ) : ℝ) / (T.D i N α β).ν =
      ∑ τ, ((T.D i N α β).μf τ).real univ := by
    rw [hfree]; exact hmuf
  have h := signed_second_energy_near_det (T.D i N α β) hν he hpfN hkmN hv hR ht hμ hC hmass'
    hμf hCf hmassf' (T.Rm N) (T.Rn N) (T.spikeFix i N α β k q m1 (m2 + s)) xn gp yn yp zp sc
    hxn hgp hyn hyp hzp hinjF hinj hs hsi hcls
  set κ : ℝ := (k : ℝ) / n with hκdef
  set c : ℝ := (m1 : ℝ) / n with hc
  set d : ℝ := (m2 : ℝ) / n with hd
  have hcde : c + d + β = α := by
    rw [hc, hd, hβdef, hαdef]; push_cast; ring
  have hq : (q : ℝ) / n = 1 - κ - α := by
    rw [hκdef, ← hcde, hc, hd, hβdef]; field_simp; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hκα : κ + α ≤ 1 := by
    have : 0 ≤ (q : ℝ) / n := by positivity
    linarith
  obtain ⟨hκlo, hκhi⟩ := hκ i hlo hhi
  -- free negatives
  have g1 : (1 / (T.D i N α β).ν) * (∑ b, (T.D i N α β).fNeg (xn b)) ≤
      κ * (T.MXn i α β + δ / 8) := by
    have hs1 : ∑ b, (T.D i N α β).fNeg (xn b) ≤ (k : ℝ) * (T.MXn i α β + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun b => (T.D i N α β).fNeg (xn b))
        (T.MXn i α β + δ / 8) (fun b _ => h6 α hαI β hβI _ (hxn b))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α β).ν) * ((k : ℝ) * (T.MXn i α β + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = κ * (T.MXn i α β + δ / 8) := by rw [hνD, hκdef]; field_simp
  -- free positives
  have g2 : (1 / (T.D i N α β).ν) * (∑ p, (T.D i N α β).fPosS (gp p)) ≤
      (1 - κ - α) * (T.MXp i α β + δ / 8) := by
    have hs1 : ∑ p, (T.D i N α β).fPosS (gp p) ≤ (q : ℝ) * (T.MXp i α β + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun p => (T.D i N α β).fPosS (gp p))
        (T.MXp i α β + δ / 8) (fun p _ => h7 α hαI β hβI _ (hgp p))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α β).ν) * ((q : ℝ) * (T.MXp i α β + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - κ - α) * (T.MXp i α β + δ / 8) := by rw [hνD, ← hq]; field_simp
  -- columns
  have hcol : ((k + q : ℕ) : ℝ) / n = 1 - α := by rw [← hfree, hνD]
  have g3 : (1 / (T.D i N α β).ν) * ∑ j, (T.D i N α β).fCol (sc j) ≤
      (1 - α) * (T.MY i α β + δ / 8) := by
    have hs1 : ∑ j, (T.D i N α β).fCol (sc j) ≤
        ((k + q : ℕ) : ℝ) * (T.MY i α β + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun j => (T.D i N α β).fCol (sc j))
        (T.MY i α β + δ / 8) (fun j _ => h8 α hαI β hβI _ (hs j))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α β).ν) * (((k + q : ℕ) : ℝ) * (T.MY i α β + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - α) * (T.MY i α β + δ / 8) := by rw [hνD, ← hcol]; field_simp
  -- fixed nodes
  have g4 : (1 / (T.D i N α β).ν) * ((∑ j, (T.D i N α β).fNegM (T.Rm N) (yn j)) +
      (∑ j, (T.D i N α β).fPosMS (T.Rm N) (yp j)) +
      ∑ j, (T.D i N α β).fNearMS (T.Rn N) β (zp j)) ≤ T.ZB i c d β + δ / 8 := by
    have hrc : 0 ≤ remC (T.epsSplit i) := by
      unfold remC
      have := T.epsSplit_pos i
      positivity
    have hle : ∑ j, (T.D i N α β).fPosMS (T.Rm N) (yp j) ≤
        ∑ j, (T.D i N α β).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j) :=
      Finset.sum_le_sum fun j _ => fPosMS_le_fPosMR _ _ hrc hα0 (hyp j)
    have := h9 α hαI β hβI m1 m2 s yn yp zp hyn hyp hzp hadm (by rw [← hαdef]) (by rw [← hβdef])
    calc _ ≤ (1 / (T.D i N α β).ν) * ((∑ j, (T.D i N α β).fNegM (T.Rm N) (yn j)) +
          (∑ j, (T.D i N α β).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
          ∑ j, (T.D i N α β).fNearMS (T.Rn N) β (zp j)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ T.ZB i c d β + δ / 8 := by rw [hc, hd, hβdef]; exact this
  have hb := T.budgetFix i κ c d β hκlo hκhi hc0 hd0 hβ0 (by rw [hcde]; exact hlo)
    (by rw [hcde]; exact hhi) (by rw [hcde]; exact hκα)
  rw [hcde] at hb
  -- the constant
  have hτ : (T.D i N α β).τ ∈ Ioo (0 : ℝ) 1 := realEnergyTau_bounds he
  have hmono : (T.D i N α β).eD7f (k + q) ≤ (T.D i N α β).eD7f ((k + m1) + (q + m2) + s) :=
    eD7f_mono (T.D i N α β) hν hCf hτ (by omega)
  have hnR : ((((k + m1) + (q + m2) + s : ℕ)) : ℝ) = n := by
    rw [← hkqR]; push_cast; ring
  have hct : (T.D i N α β).constFix (k + q) ((k + m1) + (q + m2) + s) ≤
      (T.D i N α β).constTotal (T.ncount N) + (2 * α - α ^ 2) * Real.log 2 := by
    unfold SignedData.constFix
    have hN' : (k + m1) + (q + m2) + s = T.ncount N := by omega
    have hmono' : (T.D i N α β).eD7f (k + q) ≤ (T.D i N α β).eD7f (T.ncount N) := by
      rw [← hN']; exact hmono
    rw [hN', hνD, ← hn]
    have h1' : n / n = 1 := by field_simp
    rw [h1', hcol]
    nlinarith [hmono']
  have hconst := h10 α hαI β hβI
  have herr := h11 α hαI β hβI
  have hej : (T.D i N α β).errJ3 (T.cp i N α β) ((k + m1) + (q + m2) + s) =
      (T.D i N α β).errJ3 (T.cp i N α β) (T.ncount N) := by
    congr 1; omega
  rw [hej] at h
  have hβD : (s : ℝ) / (T.D i N α β).ν = β := by rw [hνD]
  rw [hβD, hνD, hRfD, hCfD, hcD] at h
  simp only [mul_add] at g1 g2 g3 g4 hb h
  have hκ0 : 0 ≤ κ := by rw [hκdef]; positivity
  have hm1 := mul_nonneg hκ0 hδ.le
  have hm2 := mul_nonneg (show 0 ≤ 1 - κ - α by linarith) hδ.le
  have hm3 := mul_nonneg (show 0 ≤ 1 - α by linarith) hδ.le
  have hm4 := mul_nonneg hα0 hδ.le
  rw [hνD] at g1 g2 g3 g4
  nlinarith only [h, hct, g1, g2, g3, g4, hb, hconst, hδ, hm1, hm2, hm3, hm4, herr]

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.quad_master_near
#print axioms CatalanMeasure.Signed.cross_pp_le
#print axioms CatalanMeasure.Signed.cross_np_le
#print axioms CatalanMeasure.Signed.signed_master_near
#print axioms CatalanMeasure.Signed.signed_second_energy_near_det
#print axioms CatalanMeasure.Signed.signed_second_energy_near_nodes

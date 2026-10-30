module

public import CatalanMeasure.GenD.Signed.EnergyFixed
public import CatalanMeasure.GenD.Signed.ArcsinePhantom

/-!
# The signed second-sheet energy bound with fixed first-kind and near-type nodes

Extension of `Signed.EnergyFixed` by a third fixed population: the **near-type** positive nodes
`zp` (the set `S` of the marked positives of Lemma 17.43.1, `MarkedExpansion`).  In the
`S`-term of the determinant expansion the pairs (near, other) carry `log (1 - x y)` instead of
`log |x - y|` (the `groupedPairProduct` of the 532 route).  The near step follows PROOF-A §17.43
and joint-cert NOTES §17.2 (the near field of `scripts/nearcert.py`):

* **mass defect, arcsine compensation** (17.2 step 2): D7.1 is applied to the non-near rows with
  the reference `μ` of the full mass `n/ν` (the first-kind reference, independent of the near
  count), the defect `s/ν` filled by the arcsine law (`rows_vandermonde_phantom`);
* **positive cross-Cauchy pairs** (step 1): `Σ log (1 - u z)/ν² ≤ -ip (P, Q)` cancels the cross
  term of the decay convexity `½ L(ρ⁺)` exactly;
* **negative cross pairs** (step 4): the free rows and half of the first-kind rows go against the
  negative `L`-terms of D7.1 (both copies, Cauchy–Schwarz, cost `¼ ip (Q, Q)`), the other half of
  the first-kind negatives is bounded pointwise by `log (1 + z)` (the `(α/2) log (1 + x)` field);
  the reference part is the linear field `fld (R - (mnf + t)/2)`;
* **near self-energy** (step 5): the near-near Vandermonde plus `½ ip (Q, Q)` is at most the
  diagonal `(1/(2ν²)) Σ -log (1 - z²)`;
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

theorem powSum_nonneg {m : ℕ} {τ ν : ℝ} (hτ : 0 < τ) (hν : 0 < ν) (y : Fin m → ℝ)
    (hy : ∀ j, y j ∈ Ioo (0 : ℝ) 1) (n : ℕ) : 0 ≤ powSum τ ν y n := by
  unfold powSum
  exact div_nonneg (Finset.sum_nonneg fun j _ => pow_nonneg
    (mul_nonneg hτ.le (hy j).1.le) _) hν.le

theorem ip_const_mul_left (β : ℝ) (u v : ℕ → ℝ) :
    ip (fun n => β * u n) v = β * ip u v := by
  unfold ip
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

theorem ip_const_mul_right (β : ℝ) (u v : ℕ → ℝ) :
    ip u (fun n => β * v n) = β * ip u v := by
  unfold ip
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

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

/-- The negative cross pairs, pointwise: `log (1 - y z) ≤ log (1 + z)` for `y ∈ (-1, 0)`. -/
theorem cross_neg_le_log {a b : ℕ} (y : Fin a → ℝ) (z : Fin b → ℝ)
    (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 0) (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) :
    ∑ i, ∑ j, Real.log (1 - y i * z j) ≤ (a : ℝ) * ∑ j, Real.log (1 + z j) := by
  calc ∑ i, ∑ j, Real.log (1 - y i * z j) ≤ ∑ _i : Fin a, ∑ j, Real.log (1 + z j) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have h1 : 0 < 1 - y i * z j := by nlinarith [(hy i).1, (hy i).2, (hz j).1, (hz j).2]
        exact Real.log_le_log h1 (by nlinarith [(hy i).1, (hy i).2, (hz j).1, (hz j).2])
    _ = (a : ℝ) * ∑ j, Real.log (1 + z j) := by simp

/-- **The near self-energy** (NOTES §17.2 step 5): the near-near Vandermonde and the convexity
`½ L(π) = ½ ip (Q, Q)` together are at most the diagonal `(1/(2ν²)) Σ -log (1 - z²)`
(`|z - z'| ≤ 1 - z z'`). -/
theorem near_near_le {b : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν) (z : Fin b → ℝ)
    (hz : ∀ j, z j ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective z) :
    (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) / ν ^ 2 +
        (1 / 2) * ip (powSum τ ν z) (powSum τ ν z) ≤
      (1 / (2 * ν ^ 2)) * ∑ j, -Real.log (1 - z j ^ 2) := by
  have hy : ∀ i, |τ * z i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1, abs_of_pos (hz i).1]
    nlinarith [hτ.1, hτ.2, (hz i).1, (hz i).2]
  have h := (hasSum_pair_powSum (τ := τ) hν hy hy).tsum_eq
  have hip : ip (powSum τ ν z) (powSum τ ν z) =
      -(∑ i, ∑ j, Real.log (1 - (τ * z i) * (τ * z j))) / ν ^ 2 := h
  set g : Fin b → Fin b → ℝ := fun i j => Real.log (1 - (τ * z i) * (τ * z j)) with hg
  have hgs : ∀ i j, g i j = g j i := fun i j => by simp only [hg]; ring_nf
  have hsplit : ∑ i, ∑ j, g i j = (∑ i, g i i) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
    rw [← sum_offdiag_eq_two_mul g hgs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hgi : ∀ j, g i j = (if i = j then g i j else 0) + (if i = j then 0 else g i j) := by
      intro j; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun j _ => hgi j), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  have hpair : ∀ i, ∀ j ∈ Finset.Ioi i, Real.log |z j - z i| ≤ g i j := by
    intro i j hj
    have hne : z j ≠ z i := fun h => (ne_of_lt (Finset.mem_Ioi.mp hj)).symm (hzi h)
    have hpos : 0 < |z j - z i| := abs_pos.mpr (sub_ne_zero.mpr hne)
    refine Real.log_le_log hpos ?_
    have h1 : |z j - z i| ≤ 1 - z i * z j := by
      rw [abs_le]
      constructor <;> nlinarith [(hz i).1, (hz i).2, (hz j).1, (hz j).2]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
    have h2 : 1 - z i * z j ≤ 1 - (τ * z i) * (τ * z j) := by
      have e : (τ * z i) * (τ * z j) = τ ^ 2 * (z i * z j) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hτ2 (mul_nonneg (hz i).1.le (hz j).1.le)]
    linarith
  have hdiag : ∀ i, -g i i ≤ -Real.log (1 - z i ^ 2) := by
    intro i
    simp only [hg]
    have h0 : 0 < 1 - z i ^ 2 := by nlinarith [(hz i).1, (hz i).2]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
    have hle : 1 - z i ^ 2 ≤ 1 - (τ * z i) * (τ * z i) := by
      have e : (τ * z i) * (τ * z i) = τ ^ 2 * z i ^ 2 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hτ2 (sq_nonneg (z i))]
    have := Real.log_le_log h0 hle
    linarith
  have hS1 : ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i| ≤
      ∑ i, ∑ j ∈ Finset.Ioi i, g i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hpair i j hj
  have hS2 : ∑ i, -g i i ≤ ∑ i, -Real.log (1 - z i ^ 2) :=
    Finset.sum_le_sum fun i _ => hdiag i
  rw [hip]
  have hν2 : 0 < ν ^ 2 := by positivity
  have e1 : -(∑ i, ∑ j, Real.log (1 - (τ * z i) * (τ * z j))) = -(∑ i, ∑ j, g i j) := rfl
  rw [e1, hsplit]
  rw [Finset.sum_neg_distrib] at hS2
  have key : (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) / ν ^ 2 +
      (1 / 2) * (-(∑ i, g i i + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2) =
      ((∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) - ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2 +
        (1 / (2 * ν ^ 2)) * (-(∑ i, g i i)) := by
    field_simp; ring
  rw [key]
  have h3 : ((∑ i, ∑ j ∈ Finset.Ioi i, Real.log |z j - z i|) -
      ∑ i, ∑ j ∈ Finset.Ioi i, g i j) / ν ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hν2.le
  have h4 : (1 / (2 * ν ^ 2)) * (-(∑ i, g i i)) ≤
      (1 / (2 * ν ^ 2)) * ∑ j, -Real.log (1 - z j ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-! ### The quadratic tangent plane with a near species -/

/-- **The tangent-plane inequality with a near species** (NOTES §17.2).  `B = Bf + Bm`
(free + first-kind negatives), `P = Pf + Pm` (free + first-kind positives), `Q` (near), `Φp`, `Φn`
the arcsine moments of the mass defect.  Left: the route II prefactor, the decay convexity, the
D7.1 `L`-terms of both copies (all rows with the arcsine compensation; free rows), the positive
cross pairs `-ip (P, Q)` and the negative cross pairs `-ip (Bf, Q) - ½ ip (Bm, Q)`.  Pointwise the
difference of the two sides is `Pm Φp + ½ (Pf - mpf + Φp)² + ½ (B - t + Q/2 + Φn)² +
½ (Bf - mnf + Q/2)²`. -/
theorem quad_master_near {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    {B Bf Bm P Pf Pm Q R mp mn mpf mnf t Φp Φn : ℕ → ℝ}
    (hB : IsGeom τ B) (hBf : IsGeom τ Bf) (hBm : IsGeom τ Bm) (hP : IsGeom τ P)
    (hPf : IsGeom τ Pf) (hQ : IsGeom τ Q) (hR : IsGeom τ R)
    (hmp : IsGeom τ mp) (hmn : IsGeom τ mn) (hmpf : IsGeom τ mpf) (hmnf : IsGeom τ mnf)
    (ht : IsGeom τ t) (hΦp : IsGeom τ Φp) (hΦn : IsGeom τ Φn)
    (hBs : ∀ n, B n = Bf n + Bm n) (hPs : ∀ n, P n = Pf n + Pm n)
    (hPΦ : ∀ n, 0 ≤ Pm n * Φp n) :
    -(1 / 2) * ip B B + ip B (fun n => P n + Q n) +
        (1 / 2) * ip (fun n => B n - (P n + Q n) - R n) (fun n => B n - (P n + Q n) - R n)
        - (1 / 2) * ip (fun n => P n + Φp n - mp n) (fun n => P n + Φp n - mp n)
        - (1 / 2) * ip (fun n => B n + Φn n - mn n) (fun n => B n + Φn n - mn n)
        - (1 / 2) * ip (fun n => Pf n - mpf n) (fun n => Pf n - mpf n)
        - (1 / 2) * ip (fun n => Bf n - mnf n) (fun n => Bf n - mnf n)
        - ip P Q - ip Bf Q - (1 / 2) * ip Bm Q ≤
      ip P (fun n => mp n + R n) + ip B (fun n => mn n - R n - t n) + (1 / 2) * ip R R
        - (1 / 2) * ip mp mp + (1 / 2) * ip t t - (1 / 2) * ip mn mn
        + ip Q (fun n => R n - (mnf n + t n) / 2) + (3 / 4) * ip Q Q
        + (1 / 2) * ip Q Φn + ip Φn (fun n => mn n - t n)
        + ip (fun n => mp n - mpf n) Φp := by
  have hPQ : IsGeom τ (fun n => P n + Q n) := hP.add hQ
  have hBPR : IsGeom τ (fun n => B n - (P n + Q n) - R n) := (hB.sub hPQ).sub hR
  have hA1 : IsGeom τ (fun n => P n + Φp n - mp n) := (hP.add hΦp).sub hmp
  have hA2 : IsGeom τ (fun n => B n + Φn n - mn n) := (hB.add hΦn).sub hmn
  have hA3 : IsGeom τ (fun n => Pf n - mpf n) := hPf.sub hmpf
  have hA4 : IsGeom τ (fun n => Bf n - mnf n) := hBf.sub hmnf
  have hL : HasSum (fun n : ℕ => (-(1 / 2) * (B n * B n) + B n * (P n + Q n) +
      (1 / 2) * ((B n - (P n + Q n) - R n) * (B n - (P n + Q n) - R n)) -
      (1 / 2) * ((P n + Φp n - mp n) * (P n + Φp n - mp n)) -
      (1 / 2) * ((B n + Φn n - mn n) * (B n + Φn n - mn n)) -
      (1 / 2) * ((Pf n - mpf n) * (Pf n - mpf n)) -
      (1 / 2) * ((Bf n - mnf n) * (Bf n - mnf n)) -
      P n * Q n - Bf n * Q n - (1 / 2) * (Bm n * Q n)) / ((n : ℝ) + 1))
      (-(1 / 2) * ip B B + ip B (fun n => P n + Q n) +
        (1 / 2) * ip (fun n => B n - (P n + Q n) - R n) (fun n => B n - (P n + Q n) - R n)
        - (1 / 2) * ip (fun n => P n + Φp n - mp n) (fun n => P n + Φp n - mp n)
        - (1 / 2) * ip (fun n => B n + Φn n - mn n) (fun n => B n + Φn n - mn n)
        - (1 / 2) * ip (fun n => Pf n - mpf n) (fun n => Pf n - mpf n)
        - (1 / 2) * ip (fun n => Bf n - mnf n) (fun n => Bf n - mnf n)
        - ip P Q - ip Bf Q - (1 / 2) * ip Bm Q) := by
    have h := ((((((((((hasSum_ip hτ hB hB).mul_left (-(1 / 2))).add (hasSum_ip hτ hB hPQ)).add
      ((hasSum_ip hτ hBPR hBPR).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hA1 hA1).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hA2 hA2).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hA3 hA3).mul_left (1 / 2))).sub
      ((hasSum_ip hτ hA4 hA4).mul_left (1 / 2))).sub (hasSum_ip hτ hP hQ)).sub
      (hasSum_ip hτ hBf hQ)).sub ((hasSum_ip hτ hBm hQ).mul_left (1 / 2))
    convert h using 1
    funext n; ring
  have hMR : IsGeom τ (fun n => mp n + R n) := hmp.add hR
  have hBmt : IsGeom τ (fun n => mn n - R n - t n) := (hmn.sub hR).sub ht
  have hRq : IsGeom τ (fun n => R n - (mnf n + t n) / 2) := by
    have := (hmnf.add ht).const_mul (1 / 2)
    refine hR.sub ?_
    simpa [div_eq_inv_mul, mul_comm] using this
  have hmt : IsGeom τ (fun n => mn n - t n) := hmn.sub ht
  have hσ : IsGeom τ (fun n => mp n - mpf n) := hmp.sub hmpf
  have hR' : HasSum (fun n : ℕ => (P n * (mp n + R n) + B n * (mn n - R n - t n) +
      (1 / 2) * (R n * R n) - (1 / 2) * (mp n * mp n) + (1 / 2) * (t n * t n) -
      (1 / 2) * (mn n * mn n) + Q n * (R n - (mnf n + t n) / 2) + (3 / 4) * (Q n * Q n) +
      (1 / 2) * (Q n * Φn n) + Φn n * (mn n - t n) + (mp n - mpf n) * Φp n) / ((n : ℝ) + 1))
      (ip P (fun n => mp n + R n) + ip B (fun n => mn n - R n - t n) + (1 / 2) * ip R R
        - (1 / 2) * ip mp mp + (1 / 2) * ip t t - (1 / 2) * ip mn mn
        + ip Q (fun n => R n - (mnf n + t n) / 2) + (3 / 4) * ip Q Q
        + (1 / 2) * ip Q Φn + ip Φn (fun n => mn n - t n)
        + ip (fun n => mp n - mpf n) Φp) := by
    have h := ((((((((((hasSum_ip hτ hP hMR).add (hasSum_ip hτ hB hBmt)).add
      ((hasSum_ip hτ hR hR).mul_left (1 / 2))).sub ((hasSum_ip hτ hmp hmp).mul_left (1 / 2))).add
      ((hasSum_ip hτ ht ht).mul_left (1 / 2))).sub ((hasSum_ip hτ hmn hmn).mul_left (1 / 2))).add
      (hasSum_ip hτ hQ hRq)).add ((hasSum_ip hτ hQ hQ).mul_left (3 / 4))).add
      ((hasSum_ip hτ hQ hΦn).mul_left (1 / 2))).add (hasSum_ip hτ hΦn hmt)).add
      (hasSum_ip hτ hσ hΦp)
    convert h using 1
    funext n; ring
  refine hasSum_le (fun n => ?_) hL hR'
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_div_iff_of_pos_right hn, hBs n, hPs n]
  nlinarith [hPΦ n, sq_nonneg (Pf n - mpf n + Φp n), sq_nonneg (Bf n + Bm n - t n + Q n / 2 + Φn n),
    sq_nonneg (Bf n - mnf n + Q n / 2)]


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

/-- The arcsine-compensation constant per unit near mass: the cross of the arcsine moments with
the negative tangent difference `mn - t` and with the fixed part `mp - mpf` of the positive
reference. -/
def phConst : ℝ :=
  ip (arcNeg D.τ) (fun n => mneg D.μ D.τ n - D.t n) +
    ip (fun n => mpos D.μ D.τ n - mpos D.μf D.τ n) (arcPos D.τ)

/-- **Field of a near-type node** (second-sheet row of Lemma 17.43.1; NOTES §17.2 `f_near`):
its own field `Rn` (the exact `groupedNearField`), the decay node terms of a positive node
(`2 S_a`, the denominator `-(sp/ν) denPoly`, the tilt `R`), the cross with the negative reference
`-(mnf + t)/2` (`t W_mn + ½ W_sn`), the arcsine cross `½ β fld arcNeg ≤ 0`, the first-kind
negatives `(α/2) log (1 + x)`, the remainder `(β/4) (-log (1 - x²))`, and the vanishing
diagonal/dilation costs `(1/(2ν)) (-log (1 - x²) + log (1/(1-τ²)))`, `log (1/τ²)`; `β = s/ν`. -/
def fNearM (Rn : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  Rn x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => D.R n - (mneg D.μf D.τ n + D.t n) / 2) x +
    (1 / 2) * fld D.τ (fun n => β * arcNeg D.τ n) x +
    (α / 2) * Real.log (1 + x) +
    (β / 4 + 1 / (2 * D.ν)) * (-Real.log (1 - x ^ 2)) +
    (1 / (2 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2)) + Real.log (1 / D.τ ^ 2) + D.phConst

/-- With the spike cost attached. -/
def fNearMS (Rn : ℝ → ℝ) (α β x : ℝ) : ℝ :=
  D.fNearM Rn α β x + D.cs * (if 1 - D.θ < x then 1 else 0)

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

theorem sum_fNearM_eq (D : SignedData) (Rn : ℝ → ℝ) (α β : ℝ) {s : ℕ} (zp : Fin s → ℝ) :
    ∑ j, D.fNearM Rn α β (zp j) = (∑ j, Rn (zp j)) +
      2 * (∑ j, barrierTrialS D.a (-D.τ * zp j)) -
      ((D.sp : ℝ) / D.ν) * (∑ j, denPoly D.b D.K (zp j)) +
      (∑ j, fld D.τ (fun n => D.R n - (mneg D.μf D.τ n + D.t n) / 2) (zp j)) +
      (1 / 2) * (∑ j, fld D.τ (fun n => β * arcNeg D.τ n) (zp j)) +
      (α / 2) * (∑ j, Real.log (1 + zp j)) +
      (β / 4 + 1 / (2 * D.ν)) * (∑ j, -Real.log (1 - zp j ^ 2)) +
      (s : ℝ) * ((1 / (2 * D.ν)) * Real.log (1 / (1 - D.τ ^ 2))) +
      (s : ℝ) * Real.log (1 / D.τ ^ 2) + (s : ℝ) * D.phConst := by
  unfold SignedData.fNearM
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

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

set_option maxHeartbeats 6400000 in
/-- **The master inequality with first-kind fixed and near-type nodes.**  Free rows `xn`
(negative), `gp` (positive) with columns `sc`; first-kind fixed rows `yn`, `yp`; near-type
positive rows `zp`.  Pin and free copy on the free rows; D7.1 on the non-near rows with the
reference of the full mass `n/ν` and the arcsine compensation of the near mass
(`rows_vandermonde_phantom`); the route II ratio, the prefactor and the tilted square on the
positive list `gp ++ (yp ++ zp)` (all positives); the near species through `quad_master_near`,
`near_near_le` and the cross bounds. -/
theorem signed_master_near (D : SignedData) {k q m1 m2 s : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hkm : ((k + m1 : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : ∀ τ, BD (D.μ τ) D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    (hμf : ∀ τ, BD (D.μf τ) D.Cbf) (hCf : 0 ≤ D.Cbf)
    (hmassf : ((k + q : ℕ) : ℝ) / D.ν = ∑ τ, (D.μf τ).real univ)
    (Rm Rn : ℝ → ℝ) (α : ℝ) (hα : (m1 : ℝ) / D.ν ≤ α)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hzp : ∀ p, zp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hzinj : Function.Injective zp)
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
        (1 / D.ν) * ∑ j, D.fNearM Rn α ((s : ℝ) / D.ν) (zp j) +
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
  have h2 := rows_vandermonde_phantom hν hτ (Fin.append xn yn) (Fin.append gp yp) hXN hGP hinj
    D.μ hμ hC hmass
  have h2f := rows_vandermonde_le hν (Fin.append xn gp) hx0F hxF hinjF D.μf hμf hCf hmassf
    (ρ := D.τ ^ 2) (pow_pos hτ.1 2) (by nlinarith [hτ.1, hτ.2])
  rw [Fintype.sum_bool, Lpart_true_eq hτ0 hν xn gp (fun b => (hxn b).2) (fun p => (hgp p).1) D.μf,
    Lpart_false_eq hτ0 hν xn gp (fun b => (hxn b).2) (fun p => (hgp p).1) D.μf] at h2f
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
  have hab1 : ∀ {m : ℕ} (y : Fin m → ℝ), (∀ b, y b ∈ Ioo (-1 : ℝ) 0) → ∀ b, |y b| ≤ 1 :=
    fun y hy b => (abs_lt.mpr ⟨(hy b).1, by linarith [(hy b).2]⟩).le
  have hab2 : ∀ {m : ℕ} (y : Fin m → ℝ), (∀ b, y b ∈ Ioo (0 : ℝ) 1) → ∀ b, |y b| ≤ 1 :=
    fun y hy b => (abs_lt.mpr ⟨by linarith [(hy b).1], (hy b).2⟩).le
  have hB := isGeom_powSum hτ0 hν (Fin.append xn yn) (hab1 _ hXN)
  have hBf := isGeom_powSum hτ0 hν xn (hab1 _ hxn)
  have hBm := isGeom_powSum hτ0 hν yn (hab1 _ hyn)
  have hP := isGeom_powSum hτ0 hν (Fin.append gp yp) (hab2 _ hGP)
  have hPf := isGeom_powSum hτ0 hν gp (hab2 _ hgp)
  have hQ := isGeom_powSum hτ0 hν zp (hab2 _ hzp)
  have hmp : IsGeom D.τ (mpos D.μ D.τ) := isGeom_refMoment (hμ true) hτ0
  have hmn : IsGeom D.τ (mneg D.μ D.τ) := isGeom_mneg (hμ false) hτ0
  have hmpf : IsGeom D.τ (mpos D.μf D.τ) := isGeom_refMoment (hμf true) hτ0
  have hmnf : IsGeom D.τ (mneg D.μf D.τ) := isGeom_mneg (hμf false) hτ0
  have hΦp : IsGeom D.τ (fun n => ((s : ℝ) / D.ν) * arcPos D.τ n) :=
    (isGeom_arcPos hτ).const_mul _
  have hΦn : IsGeom D.τ (fun n => ((s : ℝ) / D.ν) * arcNeg D.τ n) :=
    (isGeom_arcNeg hτ).const_mul _
  have hBs : ∀ n, powSum D.τ D.ν (Fin.append xn yn) n =
      powSum D.τ D.ν xn n + powSum D.τ D.ν yn n := fun n => powSum_append _ _ xn yn n
  have hPs : ∀ n, powSum D.τ D.ν (Fin.append gp yp) n =
      powSum D.τ D.ν gp n + powSum D.τ D.ν yp n := fun n => powSum_append _ _ gp yp n
  have hPΦ : ∀ n, 0 ≤ powSum D.τ D.ν yp n * (((s : ℝ) / D.ν) * arcPos D.τ n) := fun n =>
    mul_nonneg (powSum_nonneg hτ0 hν yp hyp n)
      (mul_nonneg (by positivity) (arcPos_nonneg hτ0 n))
  have h5 := quad_master_near hτ hB hBf hBm hP hPf hQ hR hmp hmn hmpf hmnf ht hΦp hΦn hBs hPs hPΦ
  beta_reduce at h5
  have hl1 := ip_powSum_left hτ hν (Fin.append gp yp) (hab2 _ hGP) (hmp.add hR)
  have hRq : IsGeom D.τ (fun n => D.R n - (mneg D.μf D.τ n + D.t n) / 2) := by
    have := (hmnf.add ht).const_mul (1 / 2)
    refine hR.sub ?_
    simpa [div_eq_inv_mul, mul_comm] using this
  have hl1q := ip_powSum_left hτ hν zp (hab2 _ hzp) hRq
  have hlΦ := ip_powSum_left hτ hν zp (hab2 _ hzp) hΦn
  have hl2 := ip_powSum_left hτ hν (Fin.append xn yn) (hab1 _ hXN) ((hmn.sub hR).sub ht)
  have hQQ := lemmaR'_linearisation hτ hν zp hzp
  have hnn := near_near_le hτ hν zp hzp hzinj
  have hcpp := cross_pp_le hτ hν (Fin.append gp yp) zp hGP hzp
  have hcnf := cross_np_le hτ hν xn zp hxn hzp
  have hcnm := cross_np_le hτ hν yn zp hyn hzp
  have hcnm2 := cross_neg_le_log yn zp hyn hzp
  have hph1 : ip (fun n => ((s : ℝ) / D.ν) * arcNeg D.τ n)
      (fun n => mneg D.μ D.τ n - D.t n) =
      ((s : ℝ) / D.ν) * ip (arcNeg D.τ) (fun n => mneg D.μ D.τ n - D.t n) :=
    ip_const_mul_left _ _ _
  have hph2 : ip (fun n => mpos D.μ D.τ n - mpos D.μf D.τ n)
      (fun n => ((s : ℝ) / D.ν) * arcPos D.τ n) =
      ((s : ℝ) / D.ν) * ip (fun n => mpos D.μ D.τ n - mpos D.μf D.τ n) (arcPos D.τ) :=
    ip_const_mul_right _ _ _
  have hphC : ((s : ℝ) / D.ν) * D.phConst =
      ((s : ℝ) / D.ν) * ip (arcNeg D.τ) (fun n => mneg D.μ D.τ n - D.t n) +
        ((s : ℝ) / D.ν) * ip (fun n => mpos D.μ D.τ n - mpos D.μf D.τ n) (arcPos D.τ) := by
    unfold SignedData.phConst; ring
  have hpA : powSum D.τ D.ν (Fin.append gp (Fin.append yp zp)) =
      fun n => powSum D.τ D.ν (Fin.append gp yp) n + powSum D.τ D.ν zp n :=
    funext fun n => powSum_split3 D.τ D.ν gp yp zp n
  have hcross : (∑ i, ∑ j, Real.log (1 -
        Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) =
      ((∑ b, ∑ j, Real.log (1 - xn b * zp j)) + ∑ b, ∑ j, Real.log (1 - yn b * zp j)) +
        ∑ p, ∑ j, Real.log (1 - Fin.append gp yp p * zp j) := by
    rw [row_sum_split (fun u => ∑ j, Real.log (1 - u * zp j)) (Fin.append xn yn)
      (Fin.append gp yp), row_sum_split (fun u => ∑ j, Real.log (1 - u * zp j)) xn yn]
  have hL0 : 0 ≤ Real.log (1 / D.τ ^ 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (pow_pos hτ0 2)]; nlinarith [hτ.1, hτ.2])
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hm10 : (0 : ℝ) ≤ m1 := Nat.cast_nonneg m1
  have herr : ((k : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2) +
      (1 / 2) * (((m1 : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2)) ≤
      (1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2)) := by
    have hkm' : (k : ℝ) + m1 ≤ D.ν := by exact_mod_cast hkm
    have e : ((k : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2) +
        (1 / 2) * (((m1 : ℝ) * (s : ℝ) / D.ν ^ 2) * Real.log (1 / D.τ ^ 2)) =
        (((k : ℝ) + m1 / 2) / D.ν) * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) := by
      field_simp
    rw [e]
    have hfr : ((k : ℝ) + m1 / 2) / D.ν ≤ 1 := by
      rw [div_le_one hν]; linarith
    calc (((k : ℝ) + m1 / 2) / D.ν) * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2)))
        ≤ 1 * ((1 / D.ν) * ((s : ℝ) * Real.log (1 / D.τ ^ 2))) :=
          mul_le_mul_of_nonneg_right hfr (by positivity)
      _ = _ := one_mul _
  have hlog1 : 0 ≤ ∑ j, Real.log (1 + zp j) :=
    Finset.sum_nonneg fun j _ => Real.log_nonneg (by linarith [(hzp j).1])
  have hαt : (1 / 2) * (((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2) ≤
      (1 / D.ν) * ((α / 2) * ∑ j, Real.log (1 + zp j)) := by
    have e : (1 / 2) * (((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2) =
        (1 / D.ν) * ((((m1 : ℝ) / D.ν) / 2) * ∑ j, Real.log (1 + zp j)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hlog1)
      (by positivity)
  have hcnm2' : (∑ b, ∑ j, Real.log (1 - yn b * zp j)) / D.ν ^ 2 ≤
      ((m1 : ℝ) * ∑ j, Real.log (1 + zp j)) / D.ν ^ 2 :=
    div_le_div_of_nonneg_right hcnm2 (sq_nonneg _)
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
  have hsZ := congrArg (fun z => (1 / D.ν) * z) (sum_fNearM_eq D Rn α ((s : ℝ) / D.ν) zp)
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
  rw [hph1, hph2] at h5
  unfold SignedData.constFix SignedData.constTotal SignedData.eD7 SignedData.eD7f SignedData.Kq
  have hsC' : (1 / D.ν) * ∑ j, D.fCol (sc j) = (1 / D.ν) * ((∑ j, D.Cf (sc j)) +
      (∑ j, 2 * barrierTrialT D.v (sc j)) - (∑ j, Real.log (1 - sc j)) / D.ν) := by rw [hsC]
  rw [hlogZ, hrefZ] at h2
  rw [hcross]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h1 h2 h2f hbaseZ hpin hsC' hA7 hsN hsNF hsP hsPF hsZ hQQ hnn
  push_cast at h1 h2 h2f hbaseZ hpin hsC' hA7 hsN hsNF hsP hsPF hsZ hQQ hnn hcnf hcnm herr hαt hcnm2' hphC ⊢
  ring_nf at hA7 h1 h2 h2f h3 h4' h5 hl1 hl1q hlΦ hl2 hbaseZ hpin hsN hsNF hsP hsPF hsZ hsC' hsplitF hQQ hnn hcpp hcnf hcnm hcnm2' herr hαt hphC ⊢
  linarith only [hA7, h1, h2, h2f, h3, h4', h5, hl1, hl1q, hlΦ, hl2, hbaseZ, hpin, hsN, hsNF, hsP,
    hsPF, hsZ, hsC', hsplitF, hQQ, hnn, hcpp, hcnf, hcnm, hcnm2', herr, hαt, hphC]


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
    (hmass : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    (hμf : ∀ τ, BD (D.μf τ) D.Cbf) (hCf : 0 ≤ D.Cbf)
    (hmassf : ((k + q : ℕ) : ℝ) / D.ν = ∑ τ, (D.μf τ).real univ)
    (Rm Rn : ℝ → ℝ) (α : ℝ) (hα : (m1 : ℝ) / D.ν ≤ α)
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
    (hzinj : Function.Injective zp)
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
        (1 / D.ν) * ∑ j, D.fNearMS Rn α ((s : ℝ) / D.ν) (zp j) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  have hyp' : ∀ p, Fin.append yp zp p ∈ Ioo (0 : ℝ) 1 := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · simp only [Fin.append_left]; exact hyp i
    · simp only [Fin.append_right]; exact hzp i
  have hA := hA7 xn gp yn (Fin.append yp zp) hxn hgp hyn hyp' hcls
  have hN : (k + m1) + (q + (m2 + s)) = (k + m1) + (q + m2) + s := by omega
  rw [hN] at hA
  have h := signed_master_near D hν he hp hkm hv hR ht hμ hC hmass hμf hCf hmassf Rm Rn α hα xn gp
    yn yp zp sc hxn hgp hyn hyp hzp hinjF hinj hzinj hs hsi (LR xn gp yn (Fin.append yp zp))
    (D.spikeTerm (Fin.append gp (Fin.append yp zp)) + D.errJ3 c' ((k + m1) + (q + m2) + s))
    (by linarith only [hA])
  have e := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) gp (Fin.append yp zp)
  have e' := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) yp zp
  beta_reduce at e e'
  have hsp : D.spikeTerm (Fin.append gp (Fin.append yp zp)) +
      ((1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, D.fPosM Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearM Rn α ((s : ℝ) / D.ν) (zp j)) =
      (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosMS Rm (yp j)) +
        (1 / D.ν) * ∑ j, D.fNearMS Rn α ((s : ℝ) / D.ν) (zp j) := by
    unfold SignedData.spikeTerm SignedData.fPosS SignedData.fPosMS SignedData.fNearMS
    rw [e, e']
    simp only [Finset.sum_add_distrib]
    ring
  linarith only [h, hsp]


/-! ### The contract (α-dependent caps) and the theorem -/

/-- **The contract with fixed first-kind and near-type nodes, indexed by α-intervals, with caps
that are FUNCTIONS of the fixed fraction `α = (m₁ + m₂ + s)/n`.**  On interval `i` the trial data
`D i N α` (a `SignedData`: references `μ` of the FULL mass `1` (all rows; the near mass is
compensated by the arcsine law, not by the reference) and `μf` of mass `1 - α` (the free rows),
trial sequences, tilt data) may depend on `N` and `α` only; the caps `MXn MXp MY cInf` are functions
of `α` and the fixed-node sup `ZB` of the three fractions `(m₁/n, m₂/n, s/n)`.  The problem's own
data are `ν = n N`, the free-row field `Rf`, the column field `Cf`, the EXACT fixed-row fields `Rm`
(`groupedMarkedField`) and `Rn` (`groupedNearField`) and the constant `constant N α` (the exact
grouped constant at `α n` fixed rows).  The near field is `fNearMS (Rn N) α β` with `β = s/n`
(NOTES §17.2 `f_near`).  The per-fixed-row cost of the second sheet is the field `cost` of the
budget: `budgetFix` has right side `B + cost · α`. -/
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
  D : Fin I → ℕ → ℝ → SignedData
  Rf : ℕ → ℝ → ℝ
  Cf : ℕ → ℝ → ℝ
  Rm : ℕ → ℝ → ℝ
  Rn : ℕ → ℝ → ℝ
  constant : ℕ → ℝ → ℝ
  same : ∀ i N α, (D i N α).ν = (ncount N : ℝ) ∧ (D i N α).Rf = Rf N ∧
    (D i N α).Cf = Cf N ∧ (D i N α).constant = constant N α
  MXn : Fin I → ℝ → ℝ
  MXp : Fin I → ℝ → ℝ
  MY : Fin I → ℝ → ℝ
  cInf : Fin I → ℝ → ℝ
  κlo : Fin I → ℝ
  κhi : Fin I → ℝ
  epsSplit : Fin I → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  ZB : Fin I → ℝ → ℝ → ℝ → ℝ
  Clsf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop
  e_mem : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).e ∈ Ioo (0 : ℝ) (1 / 8)
  v_summable : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    Summable (fun j => |(D i N α).v j|)
  R_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    IsGeom (D i N α).τ (D i N α).R
  t_geom : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    IsGeom (D i N α).τ (D i N α).t
  reference : ∀ i, ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (∀ τ, BD ((D i N α).μ τ) (D i N α).Cb) ∧ 0 ≤ (D i N α).Cb ∧
      1 = ∑ τ, ((D i N α).μ τ).real univ ∧
    (∀ τ, BD ((D i N α).μf τ) (D i N α).Cbf) ∧ 0 ≤ (D i N α).Cbf ∧
      1 - α = ∑ τ, ((D i N α).μf τ).real univ
  cp : Fin I → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).errJ3 (cp i N α) (ncount N) ≤ ε
  spikeFix : ∀ i N α k q m1 m2,
    SpikeCompareFixed (D i N α) (cp i N α) (Clsf N k q m1 m2) (LRf N k q m1 m2)
  rowNeg : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, (D i N α).fNeg x ≤ MXn i α + ε
  rowPos : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (D i N α).fPosS x ≤ MXp i α + ε
  column : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ s ∈ Ioo (0 : ℝ) 1, (D i N α).fCol s ≤ MY i α + ε
  fixedSum : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) → (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
      FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (ncount N : ℝ) = α →
      (1 / (D i N α).ν) * ((∑ j, (D i N α).fNegM (Rm N) (yn j)) +
          (∑ j, (D i N α).fPosMR (Rm N) (remC (epsSplit i)) α (yp j)) +
          ∑ j, (D i N α).fNearMS (Rn N) α ((s : ℝ) / (ncount N : ℝ)) (zp j)) ≤
        ZB i ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ))
          ((s : ℝ) / (ncount N : ℝ)) + ε
  const_le : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop, ∀ α ∈ Icc (lo i) (hi i),
    (D i N α).constTotal (ncount N) ≤ cInf i α + ε
  budgetFix : ∀ i (κ c d e : ℝ), κlo i ≤ κ → κ ≤ κhi i → 0 ≤ c → 0 ≤ d → 0 ≤ e →
    lo i ≤ c + d + e → c + d + e ≤ hi i → κ + (c + d + e) ≤ 1 →
    cInf i (c + d + e) + (2 * (c + d + e) - (c + d + e) ^ 2) * Real.log 2 +
      κ * MXn i (c + d + e) + (1 - κ - (c + d + e)) * MXp i (c + d + e) +
      (1 - (c + d + e)) * MY i (c + d + e) + ZB i c d e ≤ B + cost * (c + d + e)

set_option maxHeartbeats 3200000 in
/-- **Theorem `signed_second_energy_near_nodes`.**  For every `δ > 0` and all large `N`, every
configuration of `k` free negatives, `q` free positives (with `k + q` columns), `m₁` first-kind
fixed negatives, `m₂` first-kind fixed positives and `s` near-type positives (distinct),
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
      Function.Injective zp →
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
      (∀ α ∈ Icc (T.lo i) (T.hi i), (T.D i N α).e ∈ Ioo (0 : ℝ) (1 / 8)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), Summable (fun j => |(T.D i N α).v j|)) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), IsGeom (T.D i N α).τ (T.D i N α).R) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), IsGeom (T.D i N α).τ (T.D i N α).t) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        (∀ τ, BD ((T.D i N α).μ τ) (T.D i N α).Cb) ∧ 0 ≤ (T.D i N α).Cb ∧
          1 = ∑ τ, ((T.D i N α).μ τ).real univ ∧
        (∀ τ, BD ((T.D i N α).μf τ) (T.D i N α).Cbf) ∧ 0 ≤ (T.D i N α).Cbf ∧
          1 - α = ∑ τ, ((T.D i N α).μf τ).real univ) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ x ∈ Ioo (-1 : ℝ) 0,
        (T.D i N α).fNeg x ≤ T.MXn i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
        (T.D i N α).fPosS x ≤ T.MXp i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), ∀ s ∈ Ioo (0 : ℝ) 1,
        (T.D i N α).fCol s ≤ T.MY i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        ∀ (m1 m2 s : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
          (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) →
          (∀ j, zp j ∈ Ioo (0 : ℝ) 1) →
          T.FixAdm N m1 m2 s yn yp zp → ((m1 + m2 + s : ℕ) : ℝ) / (T.ncount N : ℝ) = α →
          (1 / (T.D i N α).ν) * ((∑ j, (T.D i N α).fNegM (T.Rm N) (yn j)) +
              (∑ j, (T.D i N α).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
              ∑ j, (T.D i N α).fNearMS (T.Rn N) α ((s : ℝ) / (T.ncount N : ℝ)) (zp j)) ≤
            T.ZB i ((m1 : ℝ) / (T.ncount N : ℝ)) ((m2 : ℝ) / (T.ncount N : ℝ))
              ((s : ℝ) / (T.ncount N : ℝ)) + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i), (T.D i N α).constTotal (T.ncount N) ≤ T.cInf i α + δ / 8) ∧
      (∀ α ∈ Icc (T.lo i) (T.hi i),
        (T.D i N α).errJ3 (T.cp i N α) (T.ncount N) ≤ δ / 8) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [T.e_mem i, T.v_summable i, T.R_geom i, T.t_geom i, T.reference i,
      T.rowNeg i hε, T.rowPos i hε, T.column i hε, T.fixedSum i hε, T.const_le i hε,
      T.err_small i hε]
      with N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  filter_upwards [hall] with N hN k q m1 m2 s hkq hα hκ xn gp yn yp zp sc hxn hgp hyn hyp hzp
    hinjF hinj hzinj hs hsi hcls hadm
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
  obtain ⟨i, hlo, hhi⟩ := T.cover α hα0 hα1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hN i
  have hαI : α ∈ Icc (T.lo i) (T.hi i) := ⟨hlo, hhi⟩
  obtain ⟨hνD, hRfD, hCfD, hcD⟩ := T.same i N α
  rw [← hn] at hνD
  have he := h1 α hαI
  have hv := h2 α hαI
  have hR := h3 α hαI
  have ht := h4 α hαI
  obtain ⟨hμ, hC, hmu1, hμf, hCf, hmuf⟩ := h5 α hαI
  have hν : 0 < (T.D i N α).ν := by rw [hνD]; exact hνp
  have hsum : (k : ℝ) + m1 + (q + (m2 + s)) = n := by
    have := hkqR; push_cast at this; linarith
  have hpfN : ((k + q : ℕ) : ℝ) ≤ (T.D i N α).ν := by
    rw [hνD, ← hkqR]; push_cast; linarith
  have hkmN : ((k + m1 : ℕ) : ℝ) ≤ (T.D i N α).ν := by
    rw [hνD, ← hkqR]; push_cast; linarith
  have hmass' : ((((k + m1) + (q + m2)) + s : ℕ) : ℝ) / (T.D i N α).ν =
      ∑ τ, ((T.D i N α).μ τ).real univ := by
    rw [← hmu1, hνD]
    push_cast
    field_simp
    linarith
  have hfree : ((k + q : ℕ) : ℝ) / (T.D i N α).ν = 1 - α := by
    rw [hνD, hαdef]; push_cast
    field_simp; linarith
  have hmassf' : ((k + q : ℕ) : ℝ) / (T.D i N α).ν =
      ∑ τ, ((T.D i N α).μf τ).real univ := by
    rw [hfree]; exact hmuf
  have hm1α : (m1 : ℝ) / (T.D i N α).ν ≤ α := by
    rw [hνD, hαdef]
    refine div_le_div_of_nonneg_right ?_ hνp.le
    push_cast; linarith
  have h := signed_second_energy_near_det (T.D i N α) hν he hpfN hkmN hv hR ht hμ hC hmass'
    hμf hCf hmassf' (T.Rm N) (T.Rn N) α hm1α (T.spikeFix i N α k q m1 (m2 + s)) xn gp yn yp zp sc
    hxn hgp hyn hyp hzp hinjF hinj hzinj hs hsi hcls
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
  have g1 : (1 / (T.D i N α).ν) * (∑ b, (T.D i N α).fNeg (xn b)) ≤
      κ * (T.MXn i α + δ / 8) := by
    have hs1 : ∑ b, (T.D i N α).fNeg (xn b) ≤ (k : ℝ) * (T.MXn i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun b => (T.D i N α).fNeg (xn b))
        (T.MXn i α + δ / 8) (fun b _ => h6 α hαI _ (hxn b))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * ((k : ℝ) * (T.MXn i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = κ * (T.MXn i α + δ / 8) := by rw [hνD, hκdef]; field_simp
  -- free positives
  have g2 : (1 / (T.D i N α).ν) * (∑ p, (T.D i N α).fPosS (gp p)) ≤
      (1 - κ - α) * (T.MXp i α + δ / 8) := by
    have hs1 : ∑ p, (T.D i N α).fPosS (gp p) ≤ (q : ℝ) * (T.MXp i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun p => (T.D i N α).fPosS (gp p))
        (T.MXp i α + δ / 8) (fun p _ => h7 α hαI _ (hgp p))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * ((q : ℝ) * (T.MXp i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - κ - α) * (T.MXp i α + δ / 8) := by rw [hνD, ← hq]; field_simp
  -- columns
  have hcol : ((k + q : ℕ) : ℝ) / n = 1 - α := by rw [← hfree, hνD]
  have g3 : (1 / (T.D i N α).ν) * ∑ j, (T.D i N α).fCol (sc j) ≤
      (1 - α) * (T.MY i α + δ / 8) := by
    have hs1 : ∑ j, (T.D i N α).fCol (sc j) ≤
        ((k + q : ℕ) : ℝ) * (T.MY i α + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun j => (T.D i N α).fCol (sc j))
        (T.MY i α + δ / 8) (fun j _ => h8 α hαI _ (hs j))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D i N α).ν) * (((k + q : ℕ) : ℝ) * (T.MY i α + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - α) * (T.MY i α + δ / 8) := by rw [hνD, ← hcol]; field_simp
  -- fixed nodes
  have hβD : (s : ℝ) / (T.D i N α).ν = β := by rw [hνD]
  have g4 : (1 / (T.D i N α).ν) * ((∑ j, (T.D i N α).fNegM (T.Rm N) (yn j)) +
      (∑ j, (T.D i N α).fPosMS (T.Rm N) (yp j)) +
      ∑ j, (T.D i N α).fNearMS (T.Rn N) α β (zp j)) ≤ T.ZB i c d β + δ / 8 := by
    have hrc : 0 ≤ remC (T.epsSplit i) := by
      unfold remC
      have := T.epsSplit_pos i
      positivity
    have hle : ∑ j, (T.D i N α).fPosMS (T.Rm N) (yp j) ≤
        ∑ j, (T.D i N α).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j) :=
      Finset.sum_le_sum fun j _ => fPosMS_le_fPosMR _ _ hrc hα0 (hyp j)
    have := h9 α hαI m1 m2 s yn yp zp hyn hyp hzp hadm (by rw [← hαdef])
    calc _ ≤ (1 / (T.D i N α).ν) * ((∑ j, (T.D i N α).fNegM (T.Rm N) (yn j)) +
          (∑ j, (T.D i N α).fPosMR (T.Rm N) (remC (T.epsSplit i)) α (yp j)) +
          ∑ j, (T.D i N α).fNearMS (T.Rn N) α β (zp j)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ T.ZB i c d β + δ / 8 := by rw [hc, hd, hβdef]; exact this
  have hb := T.budgetFix i κ c d β hκlo hκhi hc0 hd0 hβ0 (by rw [hcde]; exact hlo)
    (by rw [hcde]; exact hhi) (by rw [hcde]; exact hκα)
  rw [hcde] at hb
  -- the constant
  have hτ : (T.D i N α).τ ∈ Ioo (0 : ℝ) 1 := realEnergyTau_bounds he
  have hmono : (T.D i N α).eD7f (k + q) ≤ (T.D i N α).eD7f ((k + m1) + (q + m2) + s) :=
    eD7f_mono (T.D i N α) hν hCf hτ (by omega)
  have hct : (T.D i N α).constFix (k + q) ((k + m1) + (q + m2) + s) ≤
      (T.D i N α).constTotal (T.ncount N) + (2 * α - α ^ 2) * Real.log 2 := by
    unfold SignedData.constFix
    have hN' : (k + m1) + (q + m2) + s = T.ncount N := by omega
    have hmono' : (T.D i N α).eD7f (k + q) ≤ (T.D i N α).eD7f (T.ncount N) := by
      rw [← hN']; exact hmono
    rw [hN', hνD, ← hn]
    have h1' : n / n = 1 := by field_simp
    rw [h1', hcol]
    nlinarith [hmono']
  have hconst := h10 α hαI
  have herr := h11 α hαI
  have hej : (T.D i N α).errJ3 (T.cp i N α) ((k + m1) + (q + m2) + s) =
      (T.D i N α).errJ3 (T.cp i N α) (T.ncount N) := by
    congr 1; omega
  rw [hej] at h
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

#print axioms CatalanMeasure.Signed.near_near_le
#print axioms CatalanMeasure.Signed.quad_master_near
#print axioms CatalanMeasure.Signed.cross_pp_le
#print axioms CatalanMeasure.Signed.cross_np_le
#print axioms CatalanMeasure.Signed.cross_neg_le_log
#print axioms CatalanMeasure.Signed.signed_master_near
#print axioms CatalanMeasure.Signed.signed_second_energy_near_det
#print axioms CatalanMeasure.Signed.signed_second_energy_near_nodes

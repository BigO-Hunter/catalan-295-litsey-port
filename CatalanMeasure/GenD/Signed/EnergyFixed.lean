module

public import CatalanMeasure.GenD.Signed.Energy

/-!
# Fixed (marked) nodes in the signed second-sheet energy bound: fields and the A7 interface

The fields of the free rows, the pin parts, the constant `constFix`, the A7 interface for fixed
nodes `SpikeCompareFixed` (the marked positives sit in the positive list of the route II ratio), the
η-split and the linearisation of Lemma R′.  The master inequality, the contract and the energy
theorem with first-kind fixed and near-type nodes are `EnergyNear`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open OAI.InternalCatalan Set Finset MeasureTheory
open scoped BigOperators
open CatalanMeasure.Signed.ReflectionEnergy

noncomputable section

/-! ### Sums over the four populations -/

theorem sum_split4 (F : ℝ → ℝ) {k q m1 m2 : ℕ} (xn : Fin k → ℝ) (yn : Fin m1 → ℝ)
    (gp : Fin q → ℝ) (yp : Fin m2 → ℝ) :
    ∑ i, F (Fin.append (Fin.append xn yn) (Fin.append gp yp) i) =
      ((∑ b, F (xn b)) + ∑ j, F (yn j)) + ((∑ p, F (gp p)) + ∑ j, F (yp j)) := by
  rw [row_sum_split, row_sum_split, row_sum_split]

/-! ### Fields of the fixed nodes -/

namespace SignedData

variable (D : SignedData)

/-- Row field of a fixed node: the problem's field, the D7.1 diagonal cost and the reference
potential (no pin terms: the fixed rows carry no column). -/
def rowBaseFix (x : ℝ) : ℝ :=
  D.Rf x + (1 / (2 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) - rowRef D.μ x

/-- The free-row copy of the Vandermonde (pin principal): D7.1 diagonal cost and the potential of
the free reference `μf`. -/
def freeCopy (x : ℝ) : ℝ :=
  (1 / (2 * D.ν)) * (-Real.log |x| + Real.log (1 / (1 - D.τ ^ 2))) - rowRef D.μf x

/-- The pin terms of a free row (`-S_v`, `-log(1-x)/(2ν)`, and the free-row Vandermonde copy). -/
def pinPart (x : ℝ) : ℝ :=
  -barrierTrialS D.v x - Real.log (1 - x) / (2 * D.ν) + D.freeCopy x

theorem rowBase_eq (x : ℝ) : D.rowBase x = D.rowBaseFix x + D.pinPart x := by
  unfold rowBase rowBaseFix pinPart freeCopy; ring

/-- The constant with `pf` free rows (pin, free-row D7.1 copy) and `n` rows in all (D7.1). -/
def constFix (pf n : ℕ) : ℝ :=
  D.constTotal n + (((n : ℝ) / D.ν) ^ 2 - ((pf : ℝ) / D.ν) ^ 2) * Real.log 2 +
    (D.eD7f pf - D.eD7f n)

end SignedData

/-- The remainder constant `REMC = (1 + 1/ε)/8` of NOTES §12.1, `ε = 1 - 2η`. -/
def remC (ε : ℝ) : ℝ := (1 + 1 / ε) / 8

theorem sum_fNeg_eq (D : SignedData) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNeg (xn b) = (∑ b, D.rowBaseFix (xn b)) + (∑ b, D.pinPart (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) (xn b) := by
  unfold SignedData.fNeg
  simp only [SignedData.rowBase_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

theorem sum_fPos_eq (D : SignedData) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPos (gp p) = (∑ p, D.rowBaseFix (gp p)) + (∑ p, D.pinPart (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) := by
  unfold SignedData.fPos
  simp only [SignedData.rowBase_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

/-- The pin terms of the free rows as a sum of `pinPart`. -/
theorem pinPart_sum (D : SignedData) (hν : 0 < D.ν) {p : ℕ} (x : Fin p → ℝ) :
    (∑ i, -barrierTrialS D.v (x i)) / D.ν - (∑ i, Real.log (1 - x i)) / (2 * D.ν ^ 2) +
      ((1 / 2) * (∑ i : Fin p, (1 / D.ν) ^ 2 * (-Real.log |x i| + Real.log (1 / (1 - D.τ ^ 2)))) -
        (∑ i, rowRef D.μf (x i)) / D.ν) = (1 / D.ν) * ∑ i, D.pinPart (x i) := by
  unfold SignedData.pinPart SignedData.freeCopy
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]
  field_simp

theorem eD7f_mono (D : SignedData) (hν : 0 < D.ν) (hCf : 0 ≤ D.Cbf) (hτ : D.τ ∈ Ioo (0 : ℝ) 1)
    {pf n : ℕ} (h : pf ≤ n) : D.eD7f pf ≤ D.eD7f n := by
  unfold SignedData.eD7f
  have hK : 0 ≤ 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hK1 : 1 - D.τ ^ 2 ≤ 1 := by nlinarith [hτ.1]
  have hK0 : 0 < 1 - D.τ ^ 2 := by nlinarith [hτ.1, hτ.2]
  have hL : 0 ≤ 1 + Real.log (1 / (1 - D.τ ^ 2)) := by
    have : 0 ≤ Real.log (1 / (1 - D.τ ^ 2)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hK0]; linarith)
    linarith
  have hab : (pf : ℝ) / D.ν ≤ (n : ℝ) / D.ν :=
    div_le_div_of_nonneg_right (by exact_mod_cast h) hν.le
  have ha : 0 ≤ (pf : ℝ) / D.ν := by positivity
  have hc : 0 ≤ D.Cbf * (1 - D.τ ^ 2) * (1 + Real.log (1 / (1 - D.τ ^ 2))) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hab hc, mul_le_mul_of_nonneg_left
    (mul_le_mul hab hab ha (ha.trans hab)) hK]

/-! ### The A7 interface and the deterministic theorem -/

/-- **The A7 interface with fixed nodes (bound form).**  `LR` is the logarithm of the route II
ratio of the whole configuration; for configurations of the class `Cls` it is bounded by the
consumer's expression at the TRUE positions of the combined sign-split node lists, plus the
spike cost of the positive nodes (free and fixed). -/
def SpikeCompareFixed (D : SignedData) (c' : ℝ) {k q m1 m2 : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ) : Prop :=
  ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ),
    (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
    (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) → Cls xn gp yn yp →
    LR xn gp yn yp / D.ν ^ 2 ≤
      logPref (Fin.append xn yn) (Fin.append gp yp) / D.ν ^ 2 +
        D.numB (Fin.append xn yn) (Fin.append gp yp) - D.denB (Fin.append gp yp) +
        D.spikeTerm (Fin.append gp yp) + D.errJ3 c' ((k + m1) + (q + m2))

/-! ### The η-split and the linearisation of Lemma R′ (PROOF-A 17.33, NOTES §§11-12.1)

Sequence-level statements, with `L(u) = ip u u`.  They are the paper's route when the fixed nodes
enter the Vandermonde only through `I(c)`, `c = a + b/2`; in `signed_master_fixed` the Vandermonde
is applied at weight one to every row, which needs no remainder, and these lemmas supply the
optional remainder field `fPosFixR`. -/

/-- Young: `L(c + d) ≤ (1 + ε) L(c) + (1 + 1/ε) L(d)`. -/
theorem ip_add_le {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {c d : ℕ → ℝ} (hc : IsGeom τ c)
    (hd : IsGeom τ d) {ε : ℝ} (hε : 0 < ε) :
    ip (fun n => c n + d n) (fun n => c n + d n) ≤ (1 + ε) * ip c c + (1 + 1 / ε) * ip d d := by
  have hcd : IsGeom τ (fun n => c n + d n) := hc.add hd
  have hL := hasSum_ip hτ hcd hcd
  have hR := ((hasSum_ip hτ hc hc).mul_left (1 + ε)).add
    ((hasSum_ip hτ hd hd).mul_left (1 + 1 / ε))
  refine hasSum_le (fun n => ?_) hL hR
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : 2 * (c n * d n) ≤ ε * (c n * c n) + (1 / ε) * (d n * d n) := by
    have h0 : 0 ≤ (ε * c n - d n) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e : (ε * c n - d n) ^ 2 / ε =
        ε * (c n * c n) - 2 * (c n * d n) + (1 / ε) * (d n * d n) := by
      field_simp
      ring
    linarith
  show (c n + d n) * (c n + d n) / ((n : ℝ) + 1) ≤
    (1 + ε) * (c n * c n / ((n : ℝ) + 1)) + (1 + 1 / ε) * (d n * d n / ((n : ℝ) + 1))
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_le_div_iff_of_pos_right hn]
  nlinarith [h2]

/-- **The η-split** (NOTES §12.1).  With `I(c) ≥ L(c⁺)` (Theorem 7.1 / D7.1), `ρ⁺ = c⁺ + b⁺/2`,
`ε = 1 - 2η ∈ (0, 1]` and `REMC = (1 + 1/ε)/8`:
`(1 - η) I - (1/2) L(ρ⁺) ≥ - REMC · L(b⁺)`. -/
theorem eta_split {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {cp bp : ℕ → ℝ} (hc : IsGeom τ cp)
    (hb : IsGeom τ bp) {I ε : ℝ} (hε : 0 < ε) (hI : ip cp cp ≤ I) :
    -(remC ε * ip bp bp) ≤ (1 - (1 - ε) / 2) * I -
      (1 / 2) * ip (fun n => cp n + bp n / 2) (fun n => cp n + bp n / 2) := by
  have hb2 : IsGeom τ (fun n => bp n / 2) := by
    simpa [div_eq_inv_mul] using hb.const_mul ((2 : ℝ)⁻¹)
  have hy := ip_add_le hτ hc hb2 hε
  have hq : ip (fun n => bp n / 2) (fun n => bp n / 2) = ip bp bp / 4 := by
    unfold ip
    rw [← tsum_div_const]
    refine tsum_congr fun n => ?_
    ring
  rw [hq] at hy
  unfold remC
  have h1 : (1 + ε) / 2 * ip cp cp ≤ (1 + ε) / 2 * I :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have h3 : 1 - (1 - ε) / 2 = (1 + ε) / 2 := by ring
  rw [h3]
  have e : (1 + 1 / ε) / 8 * ip bp bp = (1 / 2) * ((1 + 1 / ε) * (ip bp bp / 4)) := by ring
  rw [e]
  nlinarith [h1, hy]

/-- `-log (1 - ab) ≤ (-log (1 - a²) - log (1 - b²))/2` (from `(1 - ab)² ≥ (1 - a²)(1 - b²)`). -/
theorem neg_log_pair_le {a b : ℝ} (ha : |a| < 1) (hb : |b| < 1) :
    -Real.log (1 - a * b) ≤ (-Real.log (1 - a ^ 2) - Real.log (1 - b ^ 2)) / 2 := by
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith [ha'.1, ha'.2]
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith [hb'.1, hb'.2]
  have hab : 0 < 1 - a * b := by nlinarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have key : (1 - a ^ 2) * (1 - b ^ 2) ≤ (1 - a * b) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h := Real.log_le_log (mul_pos ha2 hb2) key
  rw [Real.log_mul ha2.ne' hb2.ne', Real.log_pow] at h
  push_cast at h
  linarith

/-- **Lemma R′, linearisation** (NOTES §11): for the positive fixed nodes `yp`,
`L(b⁺) = ip (powSum yp) (powSum yp) ≤ (m/ν²) Σ_j -log (1 - y_j²)`, i.e. `α² ∫ -log(1-x²) dσ⁺`
with `α = m/ν`, `σ⁺` the empirical measure of the fixed nodes. -/
theorem lemmaR'_linearisation {m : ℕ} {τ ν : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) (hν : 0 < ν)
    (yp : Fin m → ℝ) (hyp : ∀ j, yp j ∈ Ioo (0 : ℝ) 1) :
    ip (powSum τ ν yp) (powSum τ ν yp) ≤ ((m : ℝ) / ν ^ 2) * ∑ j, -Real.log (1 - yp j ^ 2) := by
  have hy : ∀ i, |τ * yp i| < 1 := fun i => by
    rw [abs_mul, abs_of_pos hτ.1]
    have : |yp i| < 1 := by rw [abs_of_pos (hyp i).1]; exact (hyp i).2
    nlinarith [hτ.2, abs_nonneg (yp i), hτ.1]
  have h := (hasSum_pair_powSum (τ := τ) hν hy hy).tsum_eq
  have hip : ip (powSum τ ν yp) (powSum τ ν yp) =
      -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) / ν ^ 2 := h
  rw [hip]
  have hpair : ∀ i j, -Real.log (1 - (τ * yp i) * (τ * yp j)) ≤
      (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 := by
    intro i j
    have h1 := neg_log_pair_le (hy i) (hy j)
    have hmono : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → -Real.log (1 - (τ * t) ^ 2) ≤ -Real.log (1 - t ^ 2) := by
      intro t ht
      have h0 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
      have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
      have hle : 1 - t ^ 2 ≤ 1 - (τ * t) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hτ2 (sq_nonneg t)]
      have := Real.log_le_log h0 hle
      linarith
    have := hmono _ (hyp i)
    have := hmono _ (hyp j)
    linarith
  have hs : -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) ≤
      (m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2) := by
    have h1 : -(∑ i, ∑ j, Real.log (1 - (τ * yp i) * (τ * yp j))) =
        ∑ i, ∑ j, -Real.log (1 - (τ * yp i) * (τ * yp j)) := by
      simp only [Finset.sum_neg_distrib]
    have h2 : ∑ i : Fin m, ∑ j : Fin m, (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 =
        (m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2) := by
      have e : ∀ i : Fin m, ∑ j : Fin m,
          (-Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2)) / 2 =
          ((m : ℝ) * (-Real.log (1 - yp i ^ 2)) + ∑ j, -Real.log (1 - yp j ^ 2)) / 2 := by
        intro i
        rw [← Finset.sum_div]
        congr 1
        have : ∀ j : Fin m, -Real.log (1 - yp i ^ 2) - Real.log (1 - yp j ^ 2) =
            -Real.log (1 - yp i ^ 2) + -Real.log (1 - yp j ^ 2) := fun j => by ring
        simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      simp only [e]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h1, ← h2]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  rw [div_eq_mul_inv, mul_comm ((m : ℝ) / ν ^ 2), div_eq_mul_inv]
  calc -(∑ i, ∑ j, Real.log (1 - τ * yp i * (τ * yp j))) * (ν ^ 2)⁻¹
      ≤ ((m : ℝ) * ∑ j, -Real.log (1 - yp j ^ 2)) * (ν ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring

/-- The remainder field of `fPosFixR` summed over the positive fixed nodes bounds `REMC · L(b⁺)`
by the linearisation. -/
theorem remainder_sum_eq {m : ℕ} {ν rc : ℝ} (hν : 0 < ν) (yp : Fin m → ℝ) :
    (1 / ν) * ∑ j, rc * ((m : ℝ) / ν) * (-Real.log (1 - yp j ^ 2)) =
      rc * (((m : ℝ) / ν ^ 2) * ∑ j, -Real.log (1 - yp j ^ 2)) := by
  rw [← Finset.mul_sum]
  field_simp

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.eta_split
#print axioms CatalanMeasure.Signed.ip_add_le
#print axioms CatalanMeasure.Signed.lemmaR'_linearisation
#print axioms CatalanMeasure.Signed.neg_log_pair_le
#print axioms CatalanMeasure.Signed.remainder_sum_eq
#print axioms CatalanMeasure.Signed.eD7f_mono

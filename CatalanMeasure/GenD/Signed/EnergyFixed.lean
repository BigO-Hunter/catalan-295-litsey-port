module

public import CatalanMeasure.GenD.Signed.Energy

/-!
# The signed second-sheet energy bound with fixed (marked) nodes (A9, theorem layer)

Extension of `Signed.Energy` (`signed_second_energy`) by a third population `σ` of `m ≤ α₁ n`
FIXED nodes `y_j` (negative `yn`, positive `yp`), each of weight one in the row Vandermonde.

* The pin part (`pin_zero_canonical`) involves only the FREE rows and the `k + q` columns.
* The row Vandermonde (D7.1, `rows_vandermonde_le`), the prefactor, the tilted square and the
  quadratic tangent plane (`quad_master`) are applied ONCE to the whole node list
  (free and fixed, split by sign), exactly as in Lemma R′ of PROOF-A 17.33 (Lemma 7.3 applied to
  `ρ = tμ + ασ`).  With the Vandermonde at weight one on every pair the quadratic part is
  concave and the fixed nodes carry plain tangent fields; the η-split of NOTES §12.1 and
  Lemma R′ are proved below (`eta_split`, `lemmaR'_linearisation`) and a remainder field
  `REMC · α · (-log (1 - x²))` can be added on positive fixed nodes (`SignedData.fPosFixR`);
  the master inequality holds with or without it.
* The statement is factor-free (no `(∏ (1 + s_i))^m`), as in `SignedSecondSheetCore`.
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

/-- The pin terms of a free row (`-S_v`, `-log(1-x)/(2ν)`). -/
def pinPart (x : ℝ) : ℝ := -barrierTrialS D.v x - Real.log (1 - x) / (2 * D.ν)

theorem rowBase_eq (x : ℝ) : D.rowBase x = D.rowBaseFix x + D.pinPart x := by
  unfold rowBase rowBaseFix pinPart; ring

/-- Field of a fixed negative node. -/
def fNegFix (x : ℝ) : ℝ :=
  D.rowBaseFix x - (1 / (2 * D.ν)) * Real.log (1 - (D.τ * x) * (D.τ * x)) -
    2 * barrierTrialS D.a (-D.τ * x) +
    fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) x

/-- Field of a fixed positive node. -/
def fPosFix (x : ℝ) : ℝ :=
  D.rowBaseFix x + 2 * barrierTrialS D.a (-D.τ * x) - ((D.sp : ℝ) / D.ν) * denPoly D.b D.K x +
    fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x

/-- Field of a fixed positive node with the spike cost attached. -/
def fPosFixS (x : ℝ) : ℝ := D.fPosFix x + D.cs * (if 1 - D.θ < x then 1 else 0)

/-- Field of a fixed positive node with the spike cost and the Lemma R′ remainder
`rc · α · (-log (1 - x²))` (`rc = REMC`, `α = m/ν`). -/
def fPosFixR (rc α x : ℝ) : ℝ := D.fPosFixS x + rc * α * (-Real.log (1 - x ^ 2))

/-- The constant with `pf` free rows (pin) and `n` rows in all (D7.1). -/
def constFix (pf n : ℕ) : ℝ :=
  D.constTotal n + (((n : ℝ) / D.ν) ^ 2 - ((pf : ℝ) / D.ν) ^ 2) * Real.log 2

end SignedData

/-- The remainder constant `REMC = (1 + 1/ε)/8` of NOTES §12.1, `ε = 1 - 2η`. -/
def remC (ε : ℝ) : ℝ := (1 + 1 / ε) / 8

theorem fPosFixS_le_fPosFixR (D : SignedData) {rc α x : ℝ} (hrc : 0 ≤ rc) (hα : 0 ≤ α)
    (hx : x ∈ Ioo (0 : ℝ) 1) : D.fPosFixS x ≤ D.fPosFixR rc α x := by
  unfold SignedData.fPosFixR
  have h1 : Real.log (1 - x ^ 2) ≤ 0 := by
    apply Real.log_nonpos
    · nlinarith [hx.1, hx.2]
    · nlinarith [hx.1, hx.2]
  have : 0 ≤ rc * α * (-Real.log (1 - x ^ 2)) :=
    mul_nonneg (mul_nonneg hrc hα) (by linarith)
  linarith

theorem sum_fNeg_eq (D : SignedData) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNeg (xn b) = (∑ b, D.rowBaseFix (xn b)) + (∑ b, D.pinPart (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) (xn b) := by
  unfold SignedData.fNeg
  simp only [SignedData.rowBase_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

theorem sum_fNegFix_eq (D : SignedData) {k : ℕ} (xn : Fin k → ℝ) :
    ∑ b, D.fNegFix (xn b) = (∑ b, D.rowBaseFix (xn b)) -
      (1 / (2 * D.ν)) * (∑ b, Real.log (1 - (D.τ * xn b) * (D.τ * xn b))) -
      2 * (∑ b, barrierTrialS D.a (-D.τ * xn b)) +
      ∑ b, fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) (xn b) := by
  unfold SignedData.fNegFix
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem sum_fPos_eq (D : SignedData) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPos (gp p) = (∑ p, D.rowBaseFix (gp p)) + (∑ p, D.pinPart (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) := by
  unfold SignedData.fPos
  simp only [SignedData.rowBase_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

theorem sum_fPosFix_eq (D : SignedData) {q : ℕ} (gp : Fin q → ℝ) :
    ∑ p, D.fPosFix (gp p) = (∑ p, D.rowBaseFix (gp p)) +
      2 * (∑ p, barrierTrialS D.a (-D.τ * gp p)) -
      ((D.sp : ℝ) / D.ν) * (∑ p, denPoly D.b D.K (gp p)) +
      ∑ p, fld D.τ (fun n => mpos D.μ D.τ n + D.R n) (gp p) := by
  unfold SignedData.fPosFix
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The common row terms (free rows and fixed rows) as a sum of `rowBaseFix`. -/
theorem rowBaseFix_sum (D : SignedData) (hν : 0 < D.ν) {p : ℕ} (x : Fin p → ℝ) :
    (∑ i, D.Rf (x i)) / D.ν +
      (1 / 2) * (∑ i : Fin p, (1 / D.ν) ^ 2 * (-Real.log |x i| + Real.log (1 / (1 - D.τ ^ 2)))) -
      (∑ i, rowRef D.μ (x i)) / D.ν = (1 / D.ν) * ∑ i, D.rowBaseFix (x i) := by
  unfold SignedData.rowBaseFix
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_div]
  field_simp

/-- The pin terms of the free rows as a sum of `pinPart`. -/
theorem pinPart_sum (D : SignedData) (hν : 0 < D.ν) {p : ℕ} (x : Fin p → ℝ) :
    (∑ i, -barrierTrialS D.v (x i)) / D.ν - (∑ i, Real.log (1 - x i)) / (2 * D.ν ^ 2) =
      (1 / D.ν) * ∑ i, D.pinPart (x i) := by
  unfold SignedData.pinPart
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_div]
  field_simp

/-! ### The master inequality with fixed nodes -/

/-- **The master inequality with fixed nodes.**  Free rows `xn` (negative), `gp` (positive) with
columns `sc`; fixed rows `yn` (negative), `yp` (positive).  The pin bound is applied to the free
rows only; D7.1, the prefactor, the tilted square and the quadratic tangent plane to the whole
node list (negatives `Fin.append xn yn`, positives `Fin.append gp yp`). -/
theorem signed_master_fixed (D : SignedData) {k q m1 m2 : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : ∀ τ, BD (D.μ τ) D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : (((k + m1) + (q + m2) : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (LR spike : ℝ)
    (hA7 : LR / D.ν ^ 2 ≤ logPref (Fin.append xn yn) (Fin.append gp yp) / D.ν ^ 2 +
      D.numB (Fin.append xn yn) (Fin.append gp yp) - D.denB (Fin.append gp yp) + spike) :
    D.constant + pinOffDiagonalInteraction D.ν 0 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, D.Rf (Fin.append (Fin.append xn yn) (Fin.append gp yp) i)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR / D.ν ^ 2 ≤
      D.constFix (k + q) ((k + m1) + (q + m2)) + spike +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegFix (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPos (gp p)) + ∑ j, D.fPosFix (yp j)) +
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
  have h1 := pin_zero_canonical hν he hp hxF hs hinjF hsi D.v hv
  have h2 := rows_vandermonde_le hν (Fin.append (Fin.append xn yn) (Fin.append gp yp)) hZ0 hZ hinj
    D.μ hμ hC hmass (ρ := D.τ ^ 2) (pow_pos hτ.1 2) (by nlinarith [hτ.1, hτ.2])
  have hn' : ∀ b, Fin.append xn yn b < 0 := fun b => (hXN b).2
  have hg' : ∀ p, 0 < Fin.append gp yp p := fun p => (hGP p).1
  rw [Fintype.sum_bool, Lpart_true_eq hτ0 hν (Fin.append xn yn) (Fin.append gp yp) hn' hg' D.μ,
    Lpart_false_eq hτ0 hν (Fin.append xn yn) (Fin.append gp yp) hn' hg' D.μ] at h2
  have h3 := logPref_le_prefTau hτ1 hν (Fin.append xn yn) (Fin.append gp yp) hXN hGP
  have hnorm1 : ∀ b, |D.τ * Fin.append xn yn b| < 1 := fun b => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append xn yn b| < 1 := abs_lt.mpr ⟨(hXN b).1, by linarith [(hXN b).2]⟩
    nlinarith [hτ.2, abs_nonneg (Fin.append xn yn b)]
  have hnorm2 : ∀ p, |D.τ * Fin.append gp yp p| < 1 := fun p => by
    rw [abs_mul, abs_of_pos hτ0]
    have : |Fin.append gp yp p| < 1 := abs_lt.mpr ⟨by linarith [(hGP p).1], (hGP p).2⟩
    nlinarith [hτ.2, abs_nonneg (Fin.append gp yp p)]
  have h4 := prefTau_eq hν (Fin.append xn yn) (Fin.append gp yp) hnorm1 hnorm2
  have hxn1 : ∀ b, |Fin.append xn yn b| ≤ 1 :=
    fun b => (abs_lt.mpr ⟨(hXN b).1, by linarith [(hXN b).2]⟩).le
  have hgp1 : ∀ p, |Fin.append gp yp p| ≤ 1 :=
    fun p => (abs_lt.mpr ⟨by linarith [(hGP p).1], (hGP p).2⟩).le
  have hB := isGeom_powSum hτ0 hν (Fin.append xn yn) hxn1
  have hP := isGeom_powSum hτ0 hν (Fin.append gp yp) hgp1
  have hmp : IsGeom D.τ (mpos D.μ D.τ) := isGeom_refMoment (hμ true) hτ0
  have hmn : IsGeom D.τ (mneg D.μ D.τ) := isGeom_mneg (hμ false) hτ0
  have h5 := quad_master hτ hB hP hR hmp hmn ht
  have hl1 := ip_powSum_left hτ hν (Fin.append gp yp) hgp1 (hmp.add hR)
  have hl2 := ip_powSum_left hτ hν (Fin.append xn yn) hxn1 ((hmn.sub hR).sub ht)
  -- row terms: free + fixed rows (rowBaseFix) and the pin terms of the free rows
  have hbaseZ := rowBaseFix_sum D hν (Fin.append (Fin.append xn yn) (Fin.append gp yp))
  rw [sum_split4 D.rowBaseFix xn yn gp yp] at hbaseZ
  have hpin := pinPart_sum D hν (Fin.append xn gp)
  rw [row_sum_split D.pinPart xn gp] at hpin
  -- splitting of the sums over the combined lists
  have e1 := row_sum_split (fun x => -barrierTrialS D.a (-D.τ * x)) xn yn
  have e2 := row_sum_split (fun x => barrierTrialS D.a (-D.τ * x)) gp yp
  have e3 := row_sum_split (fun x => denPoly D.b D.K x) gp yp
  have e4 := row_sum_split (fun x => Real.log (1 - (D.τ * x) * (D.τ * x))) xn yn
  have e5 := row_sum_split (fun x => fld D.τ (fun n => mpos D.μ D.τ n + D.R n) x) gp yp
  have e6 := row_sum_split
    (fun x => fld D.τ (fun n => mneg D.μ D.τ n - D.R n - D.t n) x) xn yn
  beta_reduce at e1 e2 e3 e4 e5 e6
  have hsN := congrArg (fun z => (1 / D.ν) * z) (sum_fNeg_eq D xn)
  have hsNF := congrArg (fun z => (1 / D.ν) * z) (sum_fNegFix_eq D yn)
  have hsP := congrArg (fun z => (1 / D.ν) * z) (sum_fPos_eq D gp)
  have hsPF := congrArg (fun z => (1 / D.ν) * z) (sum_fPosFix_eq D yp)
  beta_reduce at hsN hsNF hsP hsPF
  have hsC : ∑ j, D.fCol (sc j) = (∑ j, D.Cf (sc j)) + (∑ j, 2 * barrierTrialT D.v (sc j)) -
      (∑ j, Real.log (1 - sc j)) / D.ν := by
    unfold SignedData.fCol
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  have h4' : prefTau D.τ D.ν (Fin.append xn yn) (Fin.append gp yp) =
      -(1 / 2) * ip (powSum D.τ D.ν (Fin.append xn yn)) (powSum D.τ D.ν (Fin.append xn yn)) +
        ip (powSum D.τ D.ν (Fin.append xn yn)) (powSum D.τ D.ν (Fin.append gp yp)) -
        (1 / (2 * D.ν ^ 2)) *
          ∑ b, Real.log (1 - (D.τ * Fin.append xn yn b) * (D.τ * Fin.append xn yn b)) := h4
  unfold SignedData.numB SignedData.denB at hA7
  rw [e1, e2, e3] at hA7
  rw [e4] at h4'
  rw [e5] at hl1
  rw [e6] at hl2
  unfold SignedData.constFix SignedData.constTotal SignedData.eD7 SignedData.Kq
  have hsC' : (1 / D.ν) * ∑ j, D.fCol (sc j) = (1 / D.ν) * ((∑ j, D.Cf (sc j)) +
      (∑ j, 2 * barrierTrialT D.v (sc j)) - (∑ j, Real.log (1 - sc j)) / D.ν) := by rw [hsC]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at h1 h2 hbaseZ hpin hsC' hA7 hsN hsNF hsP hsPF
  ring_nf at hA7 h1 h2 h3 h4' h5 hl1 hl2 hbaseZ hpin hsN hsNF hsP hsPF hsC' ⊢
  linarith only [hA7, h1, h2, h3, h4', h5, hl1, hl2, hbaseZ, hpin, hsN, hsNF, hsP, hsPF, hsC']


/-! ### The A7 interface and the deterministic theorem -/

/-- **The A7 interface with fixed nodes (bound form).**  `LR` is the logarithm of the route II
ratio of the whole configuration; for configurations of the class `Cls` it is bounded by the
consumer's expression at the TRUE positions of the combined sign-split node lists, plus the
spike cost of the positive nodes (free and fixed). -/
def SpikeCompareFixed (D : SignedData) {k q m1 m2 : ℕ}
    (Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ) : Prop :=
  ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ),
    (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
    (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) → Cls xn gp yn yp →
    LR xn gp yn yp / D.ν ^ 2 ≤
      logPref (Fin.append xn yn) (Fin.append gp yp) / D.ν ^ 2 +
        D.numB (Fin.append xn yn) (Fin.append gp yp) - D.denB (Fin.append gp yp) +
        D.spikeTerm (Fin.append gp yp)

/-- **The deterministic theorem with fixed nodes (fixed `N`).** -/
theorem signed_second_energy_fixed_nodes_det (D : SignedData) {k q m1 m2 : ℕ} (hν : 0 < D.ν)
    (he : D.e ∈ Ioo (0 : ℝ) (1 / 8)) (hp : ((k + q : ℕ) : ℝ) ≤ D.ν)
    (hv : Summable (fun j => |D.v j|)) (hR : IsGeom D.τ D.R) (ht : IsGeom D.τ D.t)
    (hμ : ∀ τ, BD (D.μ τ) D.Cb) (hC : 0 ≤ D.Cb)
    (hmass : (((k + m1) + (q + m2) : ℕ) : ℝ) / D.ν = ∑ τ, (D.μ τ).real univ)
    {Cls : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop}
    {LR : (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ}
    (hA7 : SpikeCompareFixed D Cls LR)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ)
    (sc : Fin (k + q) → ℝ)
    (hxn : ∀ b, xn b ∈ Ioo (-1 : ℝ) 0) (hgp : ∀ p, gp p ∈ Ioo (0 : ℝ) 1)
    (hyn : ∀ b, yn b ∈ Ioo (-1 : ℝ) 0) (hyp : ∀ p, yp p ∈ Ioo (0 : ℝ) 1)
    (hinjF : Function.Injective (Fin.append xn gp))
    (hinj : Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)))
    (hs : ∀ j, sc j ∈ Ioo (0 : ℝ) 1) (hsi : Function.Injective sc)
    (hcls : Cls xn gp yn yp) :
    D.constant + pinOffDiagonalInteraction D.ν 0 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / D.ν ^ 2 +
        (∑ i, D.Rf (Fin.append (Fin.append xn yn) (Fin.append gp yp) i)) / D.ν +
        (∑ j, D.Cf (sc j)) / D.ν + LR xn gp yn yp / D.ν ^ 2 ≤
      D.constFix (k + q) ((k + m1) + (q + m2)) +
        (1 / D.ν) * ((∑ b, D.fNeg (xn b)) + ∑ j, D.fNegFix (yn j)) +
        (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosFixS (yp j)) +
        (1 / D.ν) * ∑ j, D.fCol (sc j) := by
  have h := signed_master_fixed D hν he hp hv hR ht hμ hC hmass xn gp yn yp sc hxn hgp hyn hyp
    hinjF hinj hs hsi (LR xn gp yn yp) (D.spikeTerm (Fin.append gp yp))
    (hA7 xn gp yn yp hxn hgp hyn hyp hcls)
  have e := row_sum_split (fun x => D.cs * (if 1 - D.θ < x then 1 else 0)) gp yp
  beta_reduce at e
  have hsp : D.spikeTerm (Fin.append gp yp) + (1 / D.ν) * ((∑ p, D.fPos (gp p)) +
      ∑ j, D.fPosFix (yp j)) =
      (1 / D.ν) * ((∑ p, D.fPosS (gp p)) + ∑ j, D.fPosFixS (yp j)) := by
    unfold SignedData.spikeTerm SignedData.fPosS SignedData.fPosFixS
    rw [e]
    simp only [Finset.sum_add_distrib]
    ring
  linarith only [h, hsp]

/-! ### The contract and the theorem -/

/-- **The contract with fixed nodes**: `SignedTrialBounds` (the free part, kept as is) plus
* the bound `α₁` on the fixed fraction `α = m/n`;
* the η-split parameter `epsSplit = ε = 1 - 2η ∈ (0, 1]`, with remainder `REMC = remC ε`;
* the A7 hypothesis `SpikeCompareFixed` for the combined node lists;
* the fixed-node field sup `fixedSum` (positive nodes carry the spike cost and the remainder
  field), over admissible fixed nodes `FixAdm` (the quadrature cap lives in `FixAdm`), with value
  `ZB c d` at fixed fractions `c = m₁/n`, `d = m₂/n`;
* the budget in `(κ, c, d)`. -/
structure SignedFixedBounds extends SignedTrialBounds where
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  epsSplit : ℝ
  epsSplit_pos : 0 < epsSplit
  epsSplit_le : epsSplit ≤ 1
  ZB : ℝ → ℝ → ℝ
  Clsf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (N k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  FixAdm : ∀ (N m1 m2 : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  spikeFix : ∀ N k q m1 m2, SpikeCompareFixed (D N) (Clsf N k q m1 m2) (LRf N k q m1 m2)
  fixedSum : ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
    ∀ (m1 m2 : ℕ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ),
      (∀ j, yn j ∈ Ioo (-1 : ℝ) 0) → (∀ j, yp j ∈ Ioo (0 : ℝ) 1) →
      FixAdm N m1 m2 yn yp → ((m1 + m2 : ℕ) : ℝ) ≤ α1 * (ncount N : ℝ) →
      (1 / (D N).ν) * ((∑ j, (D N).fNegFix (yn j)) +
          ∑ j, (D N).fPosFixR (remC epsSplit) (((m1 + m2 : ℕ) : ℝ) / (D N).ν) (yp j)) ≤
        ZB ((m1 : ℝ) / (ncount N : ℝ)) ((m2 : ℝ) / (ncount N : ℝ)) + ε
  budgetFix : ∀ κ c d : ℝ, κlo ≤ κ → κ ≤ κhi → 0 ≤ c → 0 ≤ d → c + d ≤ α1 → κ + (c + d) ≤ 1 →
    cInf + (2 * (c + d) - (c + d) ^ 2) * Real.log 2 + κ * MXn + (1 - κ - (c + d)) * MXp +
      (1 - (c + d)) * MY + ZB c d ≤ B

/-- **Theorem `signed_second_energy_fixed_nodes`.**  For every `δ > 0` and all large `N`, every
configuration of `k` free negatives, `q` free positives (with `k + q` columns), `m₁` fixed
negatives and `m₂` fixed positives, `k + m₁ + q + m₂ = n N`, `m₁ + m₂ ≤ α₁ n N`, free negative
fraction in `[κlo, κhi]`, admissible fixed nodes and in the class, has
`constant + E_disc + fields + log(route II ratio)/ν² ≤ B + δ`.  Factor-free statement. -/
theorem signed_second_energy_fixed_nodes (T : SignedFixedBounds) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (k q m1 m2 : ℕ), (k + m1) + (q + m2) = T.ncount N →
      T.κlo ≤ (k : ℝ) / (T.ncount N : ℝ) → (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi →
      ((m1 + m2 : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) →
      ∀ (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ)
        (sc : Fin (k + q) → ℝ),
      (∀ b, xn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, gp p ∈ Ioo (0 : ℝ) 1) →
      (∀ b, yn b ∈ Ioo (-1 : ℝ) 0) → (∀ p, yp p ∈ Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append xn gp) →
      Function.Injective (Fin.append (Fin.append xn yn) (Fin.append gp yp)) →
      (∀ j, sc j ∈ Ioo (0 : ℝ) 1) → Function.Injective sc →
      T.Clsf N k q m1 m2 xn gp yn yp → T.FixAdm N m1 m2 yn yp →
      (T.D N).constant + pinOffDiagonalInteraction (T.D N).ν 0 (Fin.append xn gp) sc +
        (∑ i, ∑ j ∈ Finset.Ioi i,
          Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
            Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / (T.D N).ν ^ 2 +
        (∑ i, (T.D N).Rf (Fin.append (Fin.append xn yn) (Fin.append gp yp) i)) / (T.D N).ν +
        (∑ j, (T.D N).Cf (sc j)) / (T.D N).ν +
        T.LRf N k q m1 m2 xn gp yn yp / (T.D N).ν ^ 2 ≤ T.B + δ := by
  have hε : 0 < δ / 8 := by linarith
  filter_upwards [T.e_mem, T.v_summable, T.R_geom, T.t_geom, T.reference, T.rowNeg hε,
    T.rowPos hε, T.column hε, T.fixedSum hε,
    T.const_tendsto.eventually (gt_mem_nhds (show T.cInf < T.cInf + δ / 8 by linarith))]
    with N he hv hR ht ⟨hμ, hC, hmass⟩ hN hP hCo hF hconst k q m1 m2 hkq hlo hhi hα xn gp yn yp
      sc hxn hgp hyn hyp hinjF hinj hs hsi hcls hadm
  have hνp : (0 : ℝ) < (T.ncount N : ℝ) := by exact_mod_cast T.ncount_pos N
  have hνe := T.ν_eq N
  have hν : 0 < (T.D N).ν := by rw [hνe]; exact hνp
  have hkqR : (((k + m1) + (q + m2) : ℕ) : ℝ) = (T.ncount N : ℝ) := by exact_mod_cast hkq
  have hm10 : (0 : ℝ) ≤ m1 := Nat.cast_nonneg m1
  have hm20 : (0 : ℝ) ≤ m2 := Nat.cast_nonneg m2
  have hpfN : ((k + q : ℕ) : ℝ) ≤ (T.D N).ν := by
    rw [hνe, ← hkqR]; push_cast; linarith
  have hmass' : (((k + m1) + (q + m2) : ℕ) : ℝ) / (T.D N).ν = ∑ τ, ((T.D N).μ τ).real univ := by
    rw [hkqR]; exact hmass
  have h := signed_second_energy_fixed_nodes_det (T.D N) hν he hpfN hv hR ht hμ hC hmass'
    (T.spikeFix N k q m1 m2) xn gp yn yp sc hxn hgp hyn hyp hinjF hinj hs hsi hcls
  set n : ℝ := (T.ncount N : ℝ) with hn
  have hsum : (k : ℝ) + m1 + (q + m2) = n := by
    have := hkqR; push_cast at this; linarith
  set κ : ℝ := (k : ℝ) / n with hκ
  set c : ℝ := (m1 : ℝ) / n with hc
  set d : ℝ := (m2 : ℝ) / n with hd
  have hq : (q : ℝ) / n = 1 - κ - (c + d) := by
    rw [hκ, hc, hd]; field_simp; linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hcd : c + d ≤ T.α1 := by
    rw [hc, hd, ← add_div, div_le_iff₀ hνp]
    have : ((m1 + m2 : ℕ) : ℝ) = (m1 : ℝ) + m2 := by push_cast; ring
    rw [← this]; exact hα
  have hκcd : κ + (c + d) ≤ 1 := by
    have : 0 ≤ (q : ℝ) / n := by positivity
    linarith
  -- free negatives
  have h1 : (1 / (T.D N).ν) * (∑ b, (T.D N).fNeg (xn b)) ≤ κ * (T.MXn + δ / 8) := by
    have hs1 : ∑ b, (T.D N).fNeg (xn b) ≤ (k : ℝ) * (T.MXn + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun b => (T.D N).fNeg (xn b))
        (T.MXn + δ / 8) (fun b _ => hN _ (hxn b))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * ((k : ℝ) * (T.MXn + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = κ * (T.MXn + δ / 8) := by rw [hνe, hκ]; field_simp
  -- free positives (spike cost attached)
  have h2 : (1 / (T.D N).ν) * (∑ p, (T.D N).fPosS (gp p)) ≤
      (1 - κ - (c + d)) * (T.MXp + δ / 8) := by
    have hs1 : ∑ p, (T.D N).fPosS (gp p) ≤ (q : ℝ) * (T.MXp + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun p => (T.D N).fPosS (gp p))
        (T.MXp + δ / 8) (fun p _ => hP _ (hgp p))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * ((q : ℝ) * (T.MXp + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - κ - (c + d)) * (T.MXp + δ / 8) := by rw [hνe, ← hq]; field_simp
  -- columns: `k + q` of them
  have hcol : ((k + q : ℕ) : ℝ) / n = 1 - (c + d) := by
    rw [hc, hd]; push_cast; field_simp; linarith
  have h3 : (1 / (T.D N).ν) * ∑ j, (T.D N).fCol (sc j) ≤ (1 - (c + d)) * (T.MY + δ / 8) := by
    have hs1 : ∑ j, (T.D N).fCol (sc j) ≤ ((k + q : ℕ) : ℝ) * (T.MY + δ / 8) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun j => (T.D N).fCol (sc j))
        (T.MY + δ / 8) (fun j _ => hCo _ (hs j))
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this; exact this
    calc _ ≤ (1 / (T.D N).ν) * (((k + q : ℕ) : ℝ) * (T.MY + δ / 8)) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (1 - (c + d)) * (T.MY + δ / 8) := by rw [hνe, ← hcol]; field_simp
  -- fixed nodes
  have h4 : (1 / (T.D N).ν) * ((∑ j, (T.D N).fNegFix (yn j)) +
      ∑ j, (T.D N).fPosFixS (yp j)) ≤ T.ZB c d + δ / 8 := by
    have hrc : 0 ≤ remC T.epsSplit := by
      unfold remC
      have := T.epsSplit_pos
      positivity
    have hα0 : 0 ≤ (((m1 + m2 : ℕ) : ℝ)) / (T.D N).ν := by positivity
    have hle : ∑ j, (T.D N).fPosFixS (yp j) ≤
        ∑ j, (T.D N).fPosFixR (remC T.epsSplit) (((m1 + m2 : ℕ) : ℝ) / (T.D N).ν) (yp j) :=
      Finset.sum_le_sum fun j _ => fPosFixS_le_fPosFixR _ hrc hα0 (hyp j)
    have := hF m1 m2 yn yp hyn hyp hadm hα
    calc _ ≤ (1 / (T.D N).ν) * ((∑ j, (T.D N).fNegFix (yn j)) +
          ∑ j, (T.D N).fPosFixR (remC T.epsSplit) (((m1 + m2 : ℕ) : ℝ) / (T.D N).ν) (yp j)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := this
  have hb := T.budgetFix κ c d hlo hhi hc0 hd0 hcd hκcd
  have hct : (T.D N).constFix (k + q) ((k + m1) + (q + m2)) =
      (T.D N).constTotal (T.ncount N) + (2 * (c + d) - (c + d) ^ 2) * Real.log 2 := by
    unfold SignedData.constFix
    rw [hkq, hνe, ← hn]
    have h1' : n / n = 1 := by field_simp
    rw [h1', hcol]
    ring
  rw [hct] at h
  simp only [mul_add] at h h4
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hm1 := mul_nonneg hκ0 hδ.le
  have hm2 := mul_nonneg (show 0 ≤ 1 - κ - (c + d) by linarith) hδ.le
  have hm3 := mul_nonneg (show 0 ≤ 1 - (c + d) by linarith) hδ.le
  have hm4 := mul_nonneg (add_nonneg hc0 hd0) hδ.le
  nlinarith only [h, h1, h2, h3, h4, hb, hconst, hδ, hm1, hm2, hm3, hm4]


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

#print axioms CatalanMeasure.Signed.signed_master_fixed
#print axioms CatalanMeasure.Signed.signed_second_energy_fixed_nodes_det
#print axioms CatalanMeasure.Signed.signed_second_energy_fixed_nodes
#print axioms CatalanMeasure.Signed.eta_split
#print axioms CatalanMeasure.Signed.ip_add_le
#print axioms CatalanMeasure.Signed.lemmaR'_linearisation
#print axioms CatalanMeasure.Signed.neg_log_pair_le
#print axioms CatalanMeasure.Signed.remainder_sum_eq
#print axioms CatalanMeasure.Signed.fPosFixS_le_fPosFixR

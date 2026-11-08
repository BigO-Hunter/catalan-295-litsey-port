module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Submission.CatalanMeasure.GenD.Signed.RouteI.MomentSource
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option Elab.async false

/-!
# Route I `MomentInputs` (plan row C8): bounded power streams, source-table assembly

Consumes `MomentSource`. A `BinRec` is a bin of exact cells with its natural seed `s0 = floor (m 2^P)`
and alpha numerator `a`. The floor power stream `s_{k+1} = floor (s_k a / 2^P)` is aggregated over
the bins, `S_k = sum_b s_b(k)`, and the dyadic coefficient of `u^k` is
`coefR k = -ceil (S_k/(2k)) / 2^P`.

* `stream_upper`, `stream_lower`, `stream_err`: stream error against `m alpha^k`.
* `coef_err`: `|coefR j + sum_b m_b alpha_b^j/(2j)| <= coefBudget`.
* `form_poly_bound`: `(1/2) sum_b binTerm <= c0 + sum_k coefR (k+1) u^(k+1) + eta0 + n coefBudget`.
* `recOK_of_prepared`: prepared rounded moments give the per-record hypotheses `RecOK`.
* `const_err`: log enclosures bound the constant coefficient `c0`.
* `gasPart_pos_poly`, `gasPart_neg_poly`: the polynomial bound for the gas part of `CapSource.angular`
  (the interface agreed with C6, `C8-C6-INTERFACE.md`).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MomentInputs


open Real Set intervalIntegral MeasureTheory
open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MomentSource
noncomputable section

/-! ## MomentInputs (C8): bounded power streams and the dyadic gas polynomial -/

/-- Floor power stream at precision `P`: `s0`, then `s_{k+1} = floor (s_k a / 2^P)`. -/
def stream (P a s0 : ℕ) : ℕ → ℕ
  | 0 => s0
  | k + 1 => stream P a s0 k * a / 2 ^ P

lemma stream_succ_bounds (P a s0 k : ℕ) :
    ((stream P a s0 (k + 1) : ℕ) : ℝ) ≤ (stream P a s0 k : ℝ) * a / 2 ^ P ∧
    (stream P a s0 k : ℝ) * a / 2 ^ P - 1 < (stream P a s0 (k + 1) : ℝ) := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have h1 : stream P a s0 (k + 1) * 2 ^ P ≤ stream P a s0 k * a := Nat.div_mul_le_self _ _
  have h2 : stream P a s0 k * a < (stream P a s0 (k + 1) + 1) * 2 ^ P := by
    have h3 := Nat.div_add_mod (stream P a s0 k * a) (2 ^ P)
    have h4 := Nat.mod_lt (stream P a s0 k * a) (by positivity : 0 < 2 ^ P)
    show stream P a s0 k * a < (stream P a s0 k * a / 2 ^ P + 1) * 2 ^ P
    nlinarith
  constructor
  · rw [le_div_iff₀ hd]; exact_mod_cast h1
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]; exact_mod_cast (by nlinarith [h2] : stream P a s0 k * a < (stream P a s0 (k + 1) + 1) * 2 ^ P)

lemma stream_upper (P a s0 : ℕ) (k : ℕ) :
    (stream P a s0 k : ℝ) / 2 ^ P ≤ (s0 : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ^ k := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  induction k with
  | zero => simp [stream]
  | succ k ih =>
    have h := (stream_succ_bounds P a s0 k).1
    have ha : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
    calc (stream P a s0 (k + 1) : ℝ) / 2 ^ P ≤ ((stream P a s0 k : ℝ) / 2 ^ P) * ((a : ℝ) / 2 ^ P) := by
          rw [div_le_iff₀ hd]; calc _ ≤ _ := h
            _ = _ := by field_simp
      _ ≤ (s0 : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ^ k * ((a : ℝ) / 2 ^ P) := mul_le_mul_of_nonneg_right ih ha
      _ = _ := by ring

lemma stream_lower (P a s0 : ℕ) (ha1 : a ≤ 2 ^ P) (k : ℕ) :
    (s0 : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ^ k - k / 2 ^ P ≤ (stream P a s0 k : ℝ) / 2 ^ P := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hα0 : (0 : ℝ) ≤ (a : ℝ) / 2 ^ P := by positivity
  have hα1 : (a : ℝ) / 2 ^ P ≤ 1 := by
    rw [div_le_one hd]; exact_mod_cast ha1
  induction k with
  | zero => simp [stream]
  | succ k ih =>
    have h := (stream_succ_bounds P a s0 k).2
    have h' : ((stream P a s0 k : ℝ) / 2 ^ P) * ((a : ℝ) / 2 ^ P) - 1 / 2 ^ P <
        (stream P a s0 (k + 1) : ℝ) / 2 ^ P := by
      rw [lt_div_iff₀ hd]
      have : ((stream P a s0 k : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) - 1 / 2 ^ P) * 2 ^ P =
          (stream P a s0 k : ℝ) * a / 2 ^ P - 1 := by field_simp
      rw [this]; exact h
    have hk : (0 : ℝ) ≤ (k : ℝ) / 2 ^ P := by positivity
    have e1 := mul_le_mul_of_nonneg_right ih hα0
    push_cast
    have e2 : (k : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ≤ (k : ℝ) / 2 ^ P := by nlinarith
    have e3 : ((k : ℝ) + 1) / 2 ^ P = (k : ℝ) / 2 ^ P + 1 / 2 ^ P := by ring
    rw [e3]
    have e4 : (s0 : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ^ (k + 1) = ((s0 : ℝ) / 2 ^ P * ((a : ℝ) / 2 ^ P) ^ k) * ((a : ℝ) / 2 ^ P) := by ring
    rw [e4]
    nlinarith [h', e1, e2]

/-- ceiling division `ceil (S/(2k))`. -/
def coefNum (k S : ℕ) : ℕ := (S + 2 * k - 1) / (2 * k)

lemma coefNum_bounds {k : ℕ} (hk : 1 ≤ k) (S : ℕ) :
    (S : ℝ) ≤ 2 * k * (coefNum k S : ℝ) ∧ 2 * k * (coefNum k S : ℝ) < S + 2 * k := by
  have h2k : 0 < 2 * k := by omega
  have h1 : coefNum k S * (2 * k) ≤ S + 2 * k - 1 := Nat.div_mul_le_self _ _
  have h3 := Nat.div_add_mod (S + 2 * k - 1) (2 * k)
  have h4 := Nat.mod_lt (S + 2 * k - 1) h2k
  unfold coefNum
  constructor
  · have : S ≤ 2 * k * ((S + 2 * k - 1) / (2 * k)) := by
      generalize (S + 2 * k - 1) / (2 * k) = q at *
      generalize (S + 2 * k - 1) % (2 * k) = r at *
      omega
    exact_mod_cast this
  · have : 2 * k * ((S + 2 * k - 1) / (2 * k)) < S + 2 * k := by
      have : coefNum k S * (2 * k) ≤ S + 2 * k - 1 := h1
      unfold coefNum at this
      rw [mul_comm]; omega
    exact_mod_cast this

lemma abs_pow_sub_pow_le_unit {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (k : ℕ) :
    |x ^ k - y ^ k| ≤ k * |x - y| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + y ^ k * (x - y) := by ring
    rw [e]
    calc |x * (x ^ k - y ^ k) + y ^ k * (x - y)|
        ≤ |x * (x ^ k - y ^ k)| + |y ^ k * (x - y)| := abs_add_le _ _
      _ = x * |x ^ k - y ^ k| + y ^ k * |x - y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx0, abs_of_nonneg (pow_nonneg hy0 k)]
      _ ≤ 1 * (k * |x - y|) + 1 * |x - y| := by
          have h1 : x * |x ^ k - y ^ k| ≤ 1 * (k * |x - y|) :=
            mul_le_mul hx1 ih (abs_nonneg _) zero_le_one
          have h2 : y ^ k * |x - y| ≤ 1 * |x - y| :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hy0 hy1) (abs_nonneg _)
          linarith
      _ = ((k + 1 : ℕ) : ℝ) * |x - y| := by push_cast; ring

/-- One bin record: exact cells plus the natural seed `s0` and alpha numerator `a`. -/
structure BinRec where
  cells : List YCell
  a : ℕ
  s0 : ℕ

/-- Hypotheses on one record at precision `P`: seed `s0 = floor (m 2^P)`, `a <= 2^P`,
`alpha in [0,1]`, and `|a / 2^P - alpha| <= delta`. -/
structure RecOK (P : ℕ) (pa pb pc δ : ℝ) (r : BinRec) : Prop where
  seed_le : (r.s0 : ℝ) ≤ massL r.cells * 2 ^ P
  seed_lt : massL r.cells * 2 ^ P < r.s0 + 1
  a_le : r.a ≤ 2 ^ P
  m_nonneg : 0 ≤ massL r.cells
  alpha_nonneg : 0 ≤ binAlpha pa pb pc r.cells
  alpha_le : binAlpha pa pb pc r.cells ≤ 1
  alpha_err : |(r.a : ℝ) / 2 ^ P - binAlpha pa pb pc r.cells| ≤ δ

lemma stream_err {P : ℕ} {pa pb pc δ : ℝ} {r : BinRec} (h : RecOK P pa pb pc δ r) (j : ℕ) :
    |(stream P r.a r.s0 j : ℝ) / 2 ^ P - massL r.cells * binAlpha pa pb pc r.cells ^ j| ≤
      ((j : ℝ) + 1) / 2 ^ P + massL r.cells * j * δ := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  set m := massL r.cells
  set α := binAlpha pa pb pc r.cells
  have hα0 : (0 : ℝ) ≤ (r.a : ℝ) / 2 ^ P := by positivity
  have hα1 : (r.a : ℝ) / 2 ^ P ≤ 1 := by rw [div_le_one hd]; exact_mod_cast h.a_le
  have hu := stream_upper P r.a r.s0 j
  have hl := stream_lower P r.a r.s0 (by exact_mod_cast h.a_le) j
  have hm1 : (r.s0 : ℝ) / 2 ^ P ≤ m := by rw [div_le_iff₀ hd]; exact h.seed_le
  have hm2 : m < (r.s0 : ℝ) / 2 ^ P + 1 / 2 ^ P := by
    rw [← add_div, lt_div_iff₀ hd]; exact h.seed_lt
  have hm0 : (0 : ℝ) ≤ (r.s0 : ℝ) / 2 ^ P := by positivity
  have hp := abs_pow_sub_pow_le_unit hα0 hα1 h.alpha_nonneg h.alpha_le j
  have hpj : |((r.a : ℝ) / 2 ^ P) ^ j - α ^ j| ≤ j * δ :=
    hp.trans (mul_le_mul_of_nonneg_left h.alpha_err (Nat.cast_nonneg _))
  have hpow1 : ((r.a : ℝ) / 2 ^ P) ^ j ≤ 1 := pow_le_one₀ hα0 hα1
  have hpow0 : 0 ≤ ((r.a : ℝ) / 2 ^ P) ^ j := pow_nonneg hα0 j
  set ah := ((r.a : ℝ) / 2 ^ P) ^ j
  set mh := (r.s0 : ℝ) / 2 ^ P
  rw [abs_le] at hpj ⊢
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hmδ : 0 ≤ m * j * δ := by
    have : 0 ≤ δ := le_trans (abs_nonneg _) h.alpha_err
    exact mul_nonneg (mul_nonneg h.m_nonneg hj0) this
  have k1 : mh * ah - j / 2 ^ P ≤ (stream P r.a r.s0 j : ℝ) / 2 ^ P := hl
  have k2 : (stream P r.a r.s0 j : ℝ) / 2 ^ P ≤ mh * ah := hu
  have t1 : mh * ah ≤ m * α ^ j + m * j * δ := by
    have : mh * ah ≤ m * ah := mul_le_mul_of_nonneg_right hm1 hpow0
    nlinarith [hpj.2, h.m_nonneg]
  have t2 : m * α ^ j - m * j * δ - 1 / 2 ^ P ≤ mh * ah := by
    have : m * ah - 1 / 2 ^ P ≤ mh * ah := by nlinarith
    nlinarith [hpj.1, h.m_nonneg]
  have e : ((j : ℝ) + 1) / 2 ^ P = j / 2 ^ P + 1 / 2 ^ P := by ring
  rw [e]
  constructor <;> nlinarith [k1, k2, t1, t2, div_nonneg hj0 hd.le, (by positivity : (0:ℝ) ≤ 1 / 2 ^ P)]

def Sagg (P : ℕ) (recs : List BinRec) (k : ℕ) : ℕ := (recs.map fun r => stream P r.a r.s0 k).sum

/-- Dyadic coefficient of `u^j` in the half-gas polynomial: `-ceil (S_j/(2j)) / 2^P`. -/
def coefR (P : ℕ) (recs : List BinRec) (j : ℕ) : ℝ := -((coefNum j (Sagg P recs j) : ℕ) : ℝ) / 2 ^ P

/-- Exact coefficient `sum_b m_b alpha_b^j / (2j)` (the coefficient of `-u^j`). -/
def trueCoef (pa pb pc : ℝ) (recs : List BinRec) (j : ℕ) : ℝ :=
  (recs.map fun r => massL r.cells * binAlpha pa pb pc r.cells ^ j / (2 * j)).sum

/-- Per-coefficient error budget. -/
def coefBudget (P : ℕ) (δ : BinRec → ℝ) (recs : List BinRec) : ℝ :=
  1 / 2 ^ P + (recs.map fun r => 1 / 2 ^ P + massL r.cells * δ r / 2).sum

lemma list_sum_div {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map f).sum / c = (l.map fun x => f x / c).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, add_div, ih]

lemma coef_err {P : ℕ} {pa pb pc : ℝ} {δ : BinRec → ℝ} {recs : List BinRec} (h : ∀ r ∈ recs, RecOK P pa pb pc (δ r) r)
    {j : ℕ} (hj : 1 ≤ j) :
    |coefR P recs j + trueCoef pa pb pc recs j| ≤ coefBudget P δ recs := by
  have hd : (0 : ℝ) < 2 ^ P := by positivity
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < 2 * j := by linarith
  set q := coefNum j (Sagg P recs j) with hq
  obtain ⟨hq1, hq2⟩ := coefNum_bounds hj (Sagg P recs j)
  rw [← hq] at hq1 hq2
  set X := (recs.map fun r => (stream P r.a r.s0 j : ℝ) / 2 ^ P / (2 * j)).sum with hX
  have hS : (Sagg P recs j : ℝ) / 2 ^ P / (2 * j) = X := by
    have e : (Sagg P recs j : ℝ) = (recs.map fun r => (stream P r.a r.s0 j : ℝ)).sum := by
      simp [Sagg, Nat.cast_list_sum, List.map_map, Function.comp_def]
    rw [e, list_sum_div, list_sum_div]
  have hq3 : (Sagg P recs j : ℝ) / (2 * j) ≤ q := by rw [div_le_iff₀ hj0]; nlinarith [hq1]
  have hq4 : (q : ℝ) - 1 ≤ (Sagg P recs j : ℝ) / (2 * j) := by rw [le_div_iff₀ hj0]; nlinarith [hq2]
  have hSX : X = (Sagg P recs j : ℝ) / (2 * j) / 2 ^ P := by rw [← hS, div_right_comm]
  have b1 : 0 ≤ (q : ℝ) / 2 ^ P - X ∧ (q : ℝ) / 2 ^ P - X ≤ 1 / 2 ^ P := by
    rw [hSX, ← sub_div]
    constructor
    · exact div_nonneg (by linarith) hd.le
    · exact div_le_div_of_nonneg_right (by linarith) hd.le
  have b2 : |X - trueCoef pa pb pc recs j| ≤
      (recs.map fun r => 1 / 2 ^ P + massL r.cells * δ r / 2).sum := by
    rw [hX]
    apply list_abs_sum_le
    intro r hr
    have he := stream_err (h r hr) j
    have hδ : 0 ≤ δ r := le_trans (abs_nonneg _) (h r hr).alpha_err
    have hm := (h r hr).m_nonneg
    have e : (stream P r.a r.s0 j : ℝ) / 2 ^ P / (2 * j) - massL r.cells * binAlpha pa pb pc r.cells ^ j / (2 * j) =
        ((stream P r.a r.s0 j : ℝ) / 2 ^ P - massL r.cells * binAlpha pa pb pc r.cells ^ j) / (2 * j) := by ring
    rw [e, abs_div, abs_of_pos hj0, div_le_iff₀ hj0]
    refine he.trans ?_
    have : ((j : ℝ) + 1) / 2 ^ P ≤ 2 * j * (1 / 2 ^ P) := by
      rw [mul_one_div, div_le_div_iff_of_pos_right hd]; linarith
    nlinarith [mul_nonneg hm hδ]
  have e : coefR P recs j + trueCoef pa pb pc recs j = -((q : ℝ) / 2 ^ P - X) + (trueCoef pa pb pc recs j - X) := by
    unfold coefR; rw [← hq]; ring
  have h3 := abs_add_le (-((q : ℝ) / 2 ^ P - X)) (trueCoef pa pb pc recs j - X)
  rw [← e, abs_neg, abs_sub_comm (trueCoef pa pb pc recs j) X, abs_of_nonneg b1.1] at h3
  unfold coefBudget
  linarith [b1.2]

/-! ### The dyadic half-gas polynomial bound for one form -/

/-- the exact constant `sum_b (m_b/2) log D_b`. -/
def constTrue (pa pc : ℝ) (recs : List BinRec) : ℝ :=
  (recs.map fun r => massL r.cells / 2 * Real.log (binD pa pc r.cells)).sum

lemma half_binTerm (pa pb pc u : ℝ) (n : ℕ) (l : List YCell) :
    (1 / 2) * binTerm pa pb pc u n l =
      massL l / 2 * Real.log (binD pa pc l) -
        ∑ k ∈ Finset.range n, (massL l * binAlpha pa pb pc l ^ (k + 1) / (2 * ((k : ℝ) + 1))) * u ^ (k + 1) := by
  unfold binTerm
  have h : (1 / 2 : ℝ) * (massL l * ∑ k ∈ Finset.range n, (binAlpha pa pb pc l * u) ^ (k + 1) / ((k : ℝ) + 1)) =
      ∑ k ∈ Finset.range n, (massL l * binAlpha pa pb pc l ^ (k + 1) / (2 * ((k : ℝ) + 1))) * u ^ (k + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  linarith [h]

lemma list_mul_sum {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    c * (l.map f).sum = (l.map fun x => c * f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

lemma list_sum_sub_sum {α : Type*} (l : List α) (c : α → ℝ) (g : α → ℕ → ℝ) (n : ℕ) :
    (l.map fun x => c x - ∑ k ∈ Finset.range n, g x k).sum =
      (l.map c).sum - ∑ k ∈ Finset.range n, (l.map fun x => g x k).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    have : ∑ k ∈ Finset.range n, (g x k + (l.map fun x => g x k).sum) =
        ∑ k ∈ Finset.range n, g x k + ∑ k ∈ Finset.range n, (l.map fun x => g x k).sum :=
      Finset.sum_add_distrib
    rw [this]; ring

theorem form_poly_bound {P : ℕ} {pa pb pc : ℝ} {δ : BinRec → ℝ} {recs : List BinRec}
    (h : ∀ r ∈ recs, RecOK P pa pb pc (δ r) r) {u : ℝ} (hu : |u| ≤ 1) (n : ℕ)
    {c0 η0 : ℝ} (hc0 : |c0 - constTrue pa pc recs| ≤ η0) :
    (1 / 2) * (recs.map fun r => binTerm pa pb pc u n r.cells).sum ≤
      c0 + ∑ k ∈ Finset.range n, coefR P recs (k + 1) * u ^ (k + 1) + η0 +
        n * coefBudget P δ recs := by
  rw [list_mul_sum]
  have e1 : (recs.map fun r => (1 / 2 : ℝ) * binTerm pa pb pc u n r.cells) =
      recs.map fun r => massL r.cells / 2 * Real.log (binD pa pc r.cells) -
        ∑ k ∈ Finset.range n, (massL r.cells * binAlpha pa pb pc r.cells ^ (k + 1) / (2 * ((k : ℝ) + 1))) * u ^ (k + 1) :=
    List.map_congr_left fun r _ => half_binTerm pa pb pc u n r.cells
  rw [e1, list_sum_sub_sum]
  have e2 : ∀ k : ℕ, (recs.map fun r => (massL r.cells * binAlpha pa pb pc r.cells ^ (k + 1) / (2 * ((k : ℝ) + 1))) * u ^ (k + 1)).sum =
      trueCoef pa pb pc recs (k + 1) * u ^ (k + 1) := by
    intro k
    rw [mul_comm (trueCoef pa pb pc recs (k + 1))]
    unfold trueCoef
    rw [list_mul_sum]
    congr 1
    apply List.map_congr_left
    intro r _
    push_cast
    ring
  simp only [e2]
  have hterm : ∀ k ∈ Finset.range n, -coefBudget P δ recs ≤ (coefR P recs (k + 1) + trueCoef pa pb pc recs (k + 1)) * u ^ (k + 1) := by
    intro k _
    have hb := coef_err h (j := k + 1) (by omega)
    have hpow : |u ^ (k + 1)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hu
    have hB0 : 0 ≤ coefBudget P δ recs := le_trans (abs_nonneg _) hb
    have : |(coefR P recs (k + 1) + trueCoef pa pb pc recs (k + 1)) * u ^ (k + 1)| ≤ coefBudget P δ recs := by
      rw [abs_mul]
      calc _ ≤ coefBudget P δ recs * 1 := mul_le_mul hb hpow (abs_nonneg _) hB0
        _ = _ := by ring
    have := (abs_le.1 this).1
    linarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hsplit : ∑ k ∈ Finset.range n, (coefR P recs (k + 1) + trueCoef pa pb pc recs (k + 1)) * u ^ (k + 1) =
      ∑ k ∈ Finset.range n, coefR P recs (k + 1) * u ^ (k + 1) +
        ∑ k ∈ Finset.range n, trueCoef pa pb pc recs (k + 1) * u ^ (k + 1) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intros; ring
  have := (abs_le.1 hc0)
  unfold constTrue at this
  linarith [hsum, hsplit]
/-- The alpha budget of one record from the prepared inputs. -/
def alphaBudget (P : ℕ) (m eA kA eb β eD d0 : ℝ) : ℝ :=
  1 / 2 ^ P + kA / m * eA + eb / β * (1 + eD / d0) + eD / d0

/-- Prepared inputs give a `RecOK` record with `delta = alphaBudget`.  The prepared quantities are
rounded moments `A'`, `B'`, parameters `b'`, `pa'`, `pc'`; `alpha~ = 2 b' A'/(m pa' + pc' B')`;
the stored numerator `a` satisfies `|a/2^P - alpha~| <= 2^-P`. -/
theorem recOK_of_prepared {P : ℕ} {pa pb pc : ℝ} {r : BinRec}
    (hl : PosL r.cells) (hne : r.cells ≠ []) (hw : ∀ c ∈ r.cells, 0 < c.w)
    (ha : 0 < pa) (hb : 0 < pb) (hc : 0 < pc) (hbac : pb ^ 2 ≤ pa * pc)
    (hs1 : (r.s0 : ℝ) ≤ massL r.cells * 2 ^ P) (hs2 : massL r.cells * 2 ^ P < r.s0 + 1)
    (hale : r.a ≤ 2 ^ P)
    {A' B' pa' pb' pc' : ℝ} (hA' : 0 ≤ A') (hpb' : 0 < pb')
    (hD' : 0 < massL r.cells * pa' + pc' * B')
    (hα' : 2 * pb' * A' / (massL r.cells * pa' + pc' * B') ≤ 1)
    (hra : |(r.a : ℝ) / 2 ^ P - 2 * pb' * A' / (massL r.cells * pa' + pc' * B')| ≤ 1 / 2 ^ P)
    {eA eb eD kA β d0 : ℝ}
    (hEA : |physL r.cells id - A'| ≤ eA) (hEb : |pb - pb'| ≤ eb)
    (hED : |(massL r.cells * pa + pc * physL r.cells (fun x => x ^ 2)) -
        (massL r.cells * pa' + pc' * B')| ≤ eD)
    (hkA : 2 * pb * massL r.cells ≤ kA * (massL r.cells * pa + pc * physL r.cells (fun x => x ^ 2)))
    (hd0 : d0 ≤ massL r.cells * pa + pc * physL r.cells (fun x => x ^ 2)) (hd0pos : 0 < d0)
    (hβ : β ≤ pb') (hβpos : 0 < β) (heA : 0 ≤ eA) (heb : 0 ≤ eb) (heD : 0 ≤ eD) :
    RecOK P pa pb pc (alphaBudget P (massL r.cells) eA kA eb β eD d0) r := by
  have hm : 0 < massL r.cells := massL_pos hne hw
  obtain ⟨h0, h1⟩ := binAlpha_mem hl hne hw ha hb hc hbac
  set m := massL r.cells with hmdef
  set D0 := m * pa + pc * physL r.cells (fun x => x ^ 2) with hD0
  have hD0pos : 0 < D0 := lt_of_lt_of_le hd0pos hd0
  have hα : binAlpha pa pb pc r.cells = 2 * pb * physL r.cells id / D0 := binAlpha_eq hm pa pb pc
  refine ⟨hs1, hs2, hale, hm.le, h0, h1, ?_⟩
  rw [hα]
  have hp := alpha_perturb (A := physL r.cells id) (A' := A') (b := pb) (b' := pb') (D0 := D0)
    (D0' := m * pa' + pc' * B') hpb' hD0pos hD' hA' hα' hb.le
  have t1 : 2 * pb * |physL r.cells id - A'| / D0 ≤ kA / m * eA := by
    have : 2 * pb / D0 ≤ kA / m := by
      rw [div_le_div_iff₀ hD0pos hm]; linarith [hkA]
    calc 2 * pb * |physL r.cells id - A'| / D0 = (2 * pb / D0) * |physL r.cells id - A'| := by ring
      _ ≤ kA / m * eA := mul_le_mul this hEA (abs_nonneg _) (le_trans (by positivity) this)
  have t2 : |pb - pb'| * (m * pa' + pc' * B') / (pb' * D0) ≤ eb / β * (1 + eD / d0) := by
    have hD'le : m * pa' + pc' * B' ≤ D0 + eD := by
      have := (abs_le.1 hED).1; linarith
    have e1 : |pb - pb'| * (m * pa' + pc' * B') / (pb' * D0) = (|pb - pb'| / pb') * ((m * pa' + pc' * B') / D0) := by
      field_simp
    rw [e1]
    have f1 : |pb - pb'| / pb' ≤ eb / β :=
      div_le_div₀ heb (le_trans hEb le_rfl) hβpos hβ
    have f2 : (m * pa' + pc' * B') / D0 ≤ 1 + eD / d0 := by
      rw [div_le_iff₀ hD0pos]
      have : eD / d0 * D0 ≥ eD := by
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hd0pos]; nlinarith
      nlinarith
    exact mul_le_mul f1 f2 (by positivity) (by positivity)
  have t3 : |D0 - (m * pa' + pc' * B')| / D0 ≤ eD / d0 := by
    calc _ ≤ eD / D0 := div_le_div_of_nonneg_right (by simpa [hD0] using hED) hD0pos.le
      _ ≤ eD / d0 := div_le_div_of_nonneg_left heD hd0pos hd0
  have : |(r.a : ℝ) / 2 ^ P - 2 * pb * physL r.cells id / D0| ≤
      |(r.a : ℝ) / 2 ^ P - 2 * pb' * A' / (m * pa' + pc' * B')| +
      |2 * pb * physL r.cells id / D0 - 2 * pb' * A' / (m * pa' + pc' * B')| := by
    have h := abs_sub_le ((r.a : ℝ) / 2 ^ P) (2 * pb' * A' / (m * pa' + pc' * B'))
      (2 * pb * physL r.cells id / D0)
    rw [abs_sub_comm (2 * pb' * A' / (m * pa' + pc' * B')) (2 * pb * physL r.cells id / D0)] at h
    exact h
  unfold alphaBudget
  linarith
/-- The constant coefficient: enclosures `l_b` of `log D_b` give a dyadic `c0`. -/
lemma const_err {pa pc : ℝ} {recs : List BinRec} (ℓ : BinRec → ℝ) (e : BinRec → ℝ)
    (hℓ : ∀ r ∈ recs, |ℓ r - Real.log (binD pa pc r.cells)| ≤ e r)
    (hm : ∀ r ∈ recs, 0 ≤ massL r.cells) {c0 η' : ℝ}
    (hc : |c0 - (recs.map fun r => massL r.cells / 2 * ℓ r).sum| ≤ η') :
    |c0 - constTrue pa pc recs| ≤ η' + (recs.map fun r => massL r.cells / 2 * e r).sum := by
  have h := list_abs_sum_le recs (fun r => massL r.cells / 2 * ℓ r)
    (fun r => massL r.cells / 2 * Real.log (binD pa pc r.cells)) (fun r => massL r.cells / 2 * e r)
    (fun r hr => by
      rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg (hm r hr) (by norm_num))]
      exact mul_le_mul_of_nonneg_left (hℓ r hr) (div_nonneg (hm r hr) (by norm_num)))
  unfold constTrue
  have := abs_sub_le c0 (recs.map fun r => massL r.cells / 2 * ℓ r).sum
    (recs.map fun r => massL r.cells / 2 * Real.log (binD pa pc r.cells)).sum
  linarith
/-- Gas bound, positive species: dyadic polynomial in `u = cos theta`. -/
theorem gasPart_pos_poly (S : CapSource) {recs : List BinRec} (i : ℕ) (θ : ℝ)
    (hp : Partitioned (S.gas Sign.pos) (recs.map BinRec.cells)) (hg : PosL (S.gas Sign.pos))
    (hw : ∀ c ∈ S.gas Sign.pos, 0 < c.w) {n : ℕ} (hn : Odd n) {P : ℕ} {δ : BinRec → ℝ}
    (h : ∀ r ∈ recs, RecOK P ((S.rad i) ^ 2) (S.rad i) 1 (δ r) r)
    {c0 η0 : ℝ} (hc0 : |c0 - constTrue ((S.rad i) ^ 2) 1 recs| ≤ η0) :
    gasPart S Sign.pos i θ ≤
      c0 + ∑ k ∈ Finset.range n, coefR P recs (k + 1) * (Real.cos θ) ^ (k + 1) + η0 +
        n * coefBudget P δ recs := by
  have h1 := gasPart_pos_le S i θ hp hg hw hn
  have h2 := form_poly_bound h (Real.abs_cos_le_one θ) n hc0
  exact h1.trans (by simpa [Function.comp_def] using h2)

/-- Gas bound, negative species (direct plus mirror form), in `u = -cos theta`.  Both forms use
the same bins (`hbins`); their records carry different seeds and alpha numerators. -/
theorem gasPart_neg_poly (S : CapSource) {recs₁ recs₂ : List BinRec} (i : ℕ) (θ : ℝ)
    (hp : Partitioned (reflectL (S.gas Sign.neg)) (recs₁.map BinRec.cells))
    (hbins : recs₂.map BinRec.cells = recs₁.map BinRec.cells)
    (hg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2)
    (hw : ∀ c ∈ S.gas Sign.neg, 0 < c.w) {n : ℕ} (hn : Odd n) {P : ℕ} {δ₁ δ₂ : BinRec → ℝ}
    (h₁ : ∀ r ∈ recs₁, RecOK P ((S.rad i) ^ 2) (S.rad i) 1 (δ₁ r) r)
    (h₂ : ∀ r ∈ recs₂, RecOK P 1 (S.rad i) ((S.rad i) ^ 2) (δ₂ r) r)
    {c₁ c₂ η₁ η₂ : ℝ} (hc₁ : |c₁ - constTrue ((S.rad i) ^ 2) 1 recs₁| ≤ η₁)
    (hc₂ : |c₂ - constTrue 1 ((S.rad i) ^ 2) recs₂| ≤ η₂) :
    gasPart S Sign.neg i θ ≤
      (c₁ + ∑ k ∈ Finset.range n, coefR P recs₁ (k + 1) * (-Real.cos θ) ^ (k + 1) + η₁ +
        n * coefBudget P δ₁ recs₁) +
      (c₂ + ∑ k ∈ Finset.range n, coefR P recs₂ (k + 1) * (-Real.cos θ) ^ (k + 1) + η₂ +
        n * coefBudget P δ₂ recs₂) := by
  have hu : |(-Real.cos θ)| ≤ 1 := by rw [abs_neg]; exact Real.abs_cos_le_one θ
  have h1 := gasPart_neg_le S i θ hp hg hw hn
  have e1 := form_poly_bound h₁ hu n hc₁
  have e2 := form_poly_bound h₂ hu n hc₂
  have e2' : 1 / 2 * ((recs₁.map BinRec.cells).map (binTerm 1 (S.rad i) ((S.rad i) ^ 2) (-Real.cos θ) n)).sum ≤
      c₂ + ∑ k ∈ Finset.range n, coefR P recs₂ (k + 1) * (-Real.cos θ) ^ (k + 1) + η₂ +
        n * coefBudget P δ₂ recs₂ := by
    rw [← hbins, List.map_map]; exact e2
  have e1' : 1 / 2 * ((recs₁.map BinRec.cells).map (binTerm ((S.rad i) ^ 2) (S.rad i) 1 (-Real.cos θ) n)).sum ≤
      c₁ + ∑ k ∈ Finset.range n, coefR P recs₁ (k + 1) * (-Real.cos θ) ^ (k + 1) + η₁ +
        n * coefBudget P δ₁ recs₁ := by
    rw [List.map_map]; exact e1
  linarith

/-- The mass-weighted alpha budget of one record: the `A`-error term enters as `kA * eA`, free of the
bin mass, so a tiny bin costs no more than a large one. -/
lemma mass_mul_alphaBudget {P : ℕ} {m eA kA eb β eD d0 : ℝ} (hm : 0 < m) :
    m * alphaBudget P m eA kA eb β eD d0 =
      m / 2 ^ P + kA * eA + m * (eb / β * (1 + eD / d0)) + m * (eD / d0) := by
  unfold alphaBudget
  field_simp

end
end CatalanMeasure.GenD.Signed.RouteI.MomentInputs

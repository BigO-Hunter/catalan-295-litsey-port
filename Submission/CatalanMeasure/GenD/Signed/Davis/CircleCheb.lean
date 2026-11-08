module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Unit-circle norm bounds from one packed Laurent residual

Generic, data-free. For integer coefficient lists `ps`, `lin` and a palindromic list `S`,
put `A(ζ) = ps(ζ)^k * lin(ζ)^ℓ` and
`f = c1 X^n - c2 * A * Ã - c3 X^e * S^2`, where `Ã` is the same expression with
reversed coefficient lists. On `‖ζ‖ = 1` one has `f(ζ) = ζ^n (c1 - c2 |A|² - c3 |S|²)`.
The coefficients of `f` are recovered from the single integer `f(2^K)` by balanced
divide-and-conquer decoding (`decT`), and the check `f_n > Σ_{i≠n}|f_i|` gives
`c2 |A(ζ)|² < c1` on the whole circle. The a-priori coefficient bound `M` is a closed
integer expression in the inputs. No Chebyshev basis, no autocorrelation list.
-/

set_option Elab.async false

namespace CatalanMeasure.GenD.Signed.Davis.CircleCheb

open Polynomial Finset

/-! ### Lists as polynomials -/

noncomputable def polyOfList : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * polyOfList l

/-- Horner evaluation at an integer. -/
def hornerZ (x : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + x * hornerZ x l

/-- Horner evaluation at a complex number. -/
def evC (z : ℂ) : List ℤ → ℂ
  | [] => 0
  | a :: l => (a : ℂ) + z * evC z l

/-- Sum of absolute values. -/
def sumAbs : List ℤ → ℤ
  | [] => 0
  | a :: l => |a| + sumAbs l

theorem polyOfList_eval (x : ℤ) (l : List ℤ) : (polyOfList l).eval x = hornerZ x l := by
  induction l with
  | nil => simp [polyOfList, hornerZ]
  | cons a l ih => simp [polyOfList, hornerZ, ih]

theorem polyOfList_aeval (z : ℂ) (l : List ℤ) : aeval z (polyOfList l) = evC z l := by
  induction l with
  | nil => simp [polyOfList, evC]
  | cons a l ih => simp [polyOfList, evC, ih]

theorem polyOfList_coeff (l : List ℤ) (i : ℕ) : (polyOfList l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [polyOfList]
  | cons a l ih =>
    cases i with
    | zero => simp [polyOfList]
    | succ i => rw [polyOfList, coeff_add, coeff_C_succ, coeff_X_mul, ih]; simp

theorem natDegree_polyOfList_le (l : List ℤ) : (polyOfList l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro i hi
  have hi' : l.length - 1 < i := by exact_mod_cast hi
  rw [polyOfList_coeff]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem eq_polyOfList_range (f : ℤ[X]) {m : ℕ} (hf : f.natDegree < m) :
    f = polyOfList ((List.range m).map f.coeff) := by
  ext i
  rw [polyOfList_coeff]
  by_cases hi : i < m
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]

/-! ### Balanced divide-and-conquer decoding -/

def pow2 (e : ℕ) : ℤ := ((2 ^ e : ℕ) : ℤ)

theorem pow2_mul_pow (K m : ℕ) : pow2 K ^ m = pow2 (K * m) := by
  simp [pow2, pow_mul]

/-- Decode `N` into `2^j` balanced base-`2^K` digits (the top digit is unconstrained). -/
def decT (K : ℕ) : ℕ → ℤ → List ℤ
  | 0, N => [N]
  | j + 1, N =>
    decT K j ((N + pow2 (K * 2 ^ j - 1)) % pow2 (K * 2 ^ j) - pow2 (K * 2 ^ j - 1)) ++
      decT K j ((N + pow2 (K * 2 ^ j - 1)) / pow2 (K * 2 ^ j))

theorem decT_length (K j : ℕ) (N : ℤ) : (decT K j N).length = 2 ^ j := by
  induction j generalizing N with
  | zero => simp [decT]
  | succ j ih => simp [decT, ih, pow_succ]; omega

theorem hornerZ_append (x : ℤ) (a b : List ℤ) :
    hornerZ x (a ++ b) = hornerZ x a + x ^ a.length * hornerZ x b := by
  induction a with
  | nil => simp [hornerZ]
  | cons c a ih => simp [hornerZ, ih, pow_succ]; ring

theorem decT_sound (K j : ℕ) (N : ℤ) : hornerZ (pow2 K) (decT K j N) = N := by
  induction j generalizing N with
  | zero => simp [decT, hornerZ]
  | succ j ih =>
    rw [decT, hornerZ_append, ih, ih, decT_length, pow2_mul_pow]
    have := Int.mul_ediv_add_emod (N + pow2 (K * 2 ^ j - 1)) (pow2 (K * 2 ^ j))
    linarith

/-- Packed uniqueness with strict half-base digit bounds. -/
theorem hornerZ_inj {B : ℤ} (hB : 0 < B) :
    ∀ (a b : List ℤ), a.length = b.length → (∀ x ∈ a, 2 * |x| < B) → (∀ x ∈ b, 2 * |x| < B) →
      hornerZ B a = hornerZ B b → a = b := by
  intro a
  induction a with
  | nil => intro b hl _ _ _; cases b with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x a ih =>
    intro b hl ha hb h
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [hornerZ] at h
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have hd : B ∣ x - y := ⟨hornerZ B b - hornerZ B a, by linarith⟩
      have hxy : x - y = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd hd
        have := abs_sub x y
        have h1 := abs_nonneg x
        have h2 := abs_nonneg y
        linarith [abs_sub x y]
      have hxy' : x = y := by linarith
      subst hxy'
      have : hornerZ B a = hornerZ B b := by
        have := mul_left_cancel₀ hB.ne' (by linarith : B * hornerZ B a = B * hornerZ B b)
        exact this
      have := ih b (by simpa using hl) (fun z hz => ha z (by simp [hz]))
        (fun z hz => hb z (by simp [hz])) this
      rw [this]

/-! ### Coefficient domination -/

def Dom (p q : ℤ[X]) : Prop := ∀ i, |p.coeff i| ≤ q.coeff i

theorem Dom.nonneg {p q : ℤ[X]} (h : Dom p q) (i : ℕ) : 0 ≤ q.coeff i :=
  (abs_nonneg _).trans (h i)

theorem Dom.add {p q p' q' : ℤ[X]} (hp : Dom p p') (hq : Dom q q') : Dom (p + q) (p' + q') := by
  intro i
  rw [coeff_add, coeff_add]
  exact (abs_add_le _ _).trans (add_le_add (hp i) (hq i))

theorem Dom.sub {p q p' q' : ℤ[X]} (hp : Dom p p') (hq : Dom q q') : Dom (p - q) (p' + q') := by
  intro i
  rw [coeff_sub, coeff_add]
  exact (abs_sub _ _).trans (add_le_add (hp i) (hq i))

theorem Dom.mul {p q p' q' : ℤ[X]} (hp : Dom p p') (hq : Dom q q') : Dom (p * q) (p' * q') := by
  intro i
  rw [coeff_mul, coeff_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hp x.1) (hq x.2) (abs_nonneg _) (hp.nonneg x.1)

theorem Dom.pow {p p' : ℤ[X]} (hp : Dom p p') (k : ℕ) : Dom (p ^ k) (p' ^ k) := by
  induction k with
  | zero =>
    intro i; simp only [pow_zero, coeff_one]; split_ifs <;> simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hp

theorem Dom.C_mul (a : ℤ) {p p' : ℤ[X]} (hp : Dom p p') : Dom (C a * p) (C |a| * p') := by
  intro i
  rw [coeff_C_mul, coeff_C_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hp i) (abs_nonneg _)

theorem Dom.refl_X_pow (k : ℕ) : Dom ((X : ℤ[X]) ^ k) (X ^ k) := by
  intro i
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem Dom.polyOfList (l : List ℤ) :
    Dom (polyOfList l) (polyOfList (l.map fun x => |x|)) := by
  induction l with
  | nil => intro i; simp [CircleCheb.polyOfList]
  | cons a l ih =>
    simp only [CircleCheb.polyOfList, List.map_cons]
    refine Dom.add ?_ ?_
    · intro i; simp only [coeff_C]; split_ifs <;> simp
    · intro i
      rcases i with _ | i
      · simp
      · simp only [coeff_X_mul]; exact ih i

theorem coeff_le_eval_one {F : ℤ[X]} (h : ∀ i, 0 ≤ F.coeff i) (i : ℕ) : F.coeff i ≤ F.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases hi : i < F.natDegree + 1
  · exact Finset.single_le_sum (f := fun j => F.coeff j) (fun j _ => h j) (Finset.mem_range.mpr hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Finset.sum_nonneg fun j _ => h j

theorem eval_one_polyOfList_abs (l : List ℤ) :
    (polyOfList (l.map fun x => |x|)).eval 1 = sumAbs l := by
  induction l with
  | nil => simp [polyOfList, sumAbs]
  | cons a l ih => simp [polyOfList, sumAbs, ih]


/-! ### The residual polynomial and its value on the unit circle -/

theorem conj_mul_self_of_norm {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hz]; simp

theorem evC_append (z : ℂ) (a b : List ℤ) :
    evC z (a ++ b) = evC z a + z ^ a.length * evC z b := by
  induction a with
  | nil => simp [evC]
  | cons c a ih => simp [evC, ih, pow_succ]; ring

theorem evC_reverse_mul {z : ℂ} (hz : ‖z‖ = 1) (l : List ℤ) :
    evC z l.reverse * z = z ^ l.length * (starRingEnd ℂ) (evC z l) := by
  have h1 := conj_mul_self_of_norm hz
  induction l with
  | nil => simp [evC]
  | cons a t ih =>
    have e1 : evC z (a :: t).reverse = evC z t.reverse + z ^ t.length * a := by
      simp [List.reverse_cons, evC_append, evC]
    have e2 : evC z (a :: t) = a + z * evC z t := rfl
    rw [e1, e2, List.length_cons, map_add, map_mul, map_intCast]
    linear_combination ih - (z ^ t.length * (starRingEnd ℂ) (evC z t)) * h1

theorem evC_reverse {z : ℂ} (hz : ‖z‖ = 1) {l : List ℤ} (hl : l ≠ []) :
    evC z l.reverse = z ^ (l.length - 1) * (starRingEnd ℂ) (evC z l) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  apply mul_right_cancel₀ hz0
  rw [evC_reverse_mul hz]
  have : l.length = (l.length - 1) + 1 := by
    have := List.length_pos_iff.mpr hl; omega
  conv_lhs => rw [this]
  ring

noncomputable def fPoly (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) : ℤ[X] :=
  C c1 * X ^ n - C c2 * ((polyOfList ps ^ k * polyOfList lin ^ ℓ) *
    (polyOfList ps.reverse ^ k * polyOfList lin.reverse ^ ℓ)) -
    C c3 * X ^ e * polyOfList S ^ 2

theorem aeval_fPoly {ps lin S : List ℤ} {k ℓ n e : ℕ} {c1 c2 c3 : ℤ}
    (hps : ps ≠ []) (hlin : lin ≠ []) (hn : n = k * (ps.length - 1) + ℓ * (lin.length - 1))
    (hS : S.reverse = S) (hSne : S ≠ []) (hSe : e + (S.length - 1) = n)
    {z : ℂ} (hz : ‖z‖ = 1) :
    aeval z (fPoly ps lin S k ℓ n e c1 c2 c3) =
      z ^ n * (((c1 : ℝ) - c2 * Complex.normSq (evC z ps ^ k * evC z lin ^ ℓ) -
        c3 * Complex.normSq (evC z S) : ℝ) : ℂ) := by
  have h1 := conj_mul_self_of_norm hz
  have hR := evC_reverse hz hps
  have hL := evC_reverse hz hlin
  have hG := evC_reverse hz hSne
  rw [hS] at hG
  have hnA := (Complex.mul_conj (evC z ps ^ k * evC z lin ^ ℓ)).symm
  have hnG := (Complex.mul_conj (evC z S)).symm
  have hG2 : evC z S ^ 2 = z ^ (S.length - 1) * (evC z S * (starRingEnd ℂ) (evC z S)) := by
    nth_rewrite 1 [pow_two]
    nth_rewrite 2 [hG]
    ring
  have hzn1 : z ^ n = z ^ (k * (ps.length - 1)) * z ^ (ℓ * (lin.length - 1)) := by
    rw [hn, pow_add]
  have hzn2 : z ^ n = z ^ e * z ^ (S.length - 1) := by rw [← hSe, pow_add]
  have hcast : ((((c1 : ℝ) - c2 * Complex.normSq (evC z ps ^ k * evC z lin ^ ℓ) -
        c3 * Complex.normSq (evC z S) : ℝ)) : ℂ) = (c1 : ℂ) -
        c2 * (evC z ps ^ k * evC z lin ^ ℓ * (starRingEnd ℂ) (evC z ps ^ k * evC z lin ^ ℓ)) -
        c3 * (evC z S * (starRingEnd ℂ) (evC z S)) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hnA, hnG]
  rw [hcast]
  simp only [fPoly, map_sub, map_mul, map_pow, aeval_C, aeval_X, polyOfList_aeval, hR, hL,
    eq_intCast, map_intCast]
  rw [hG2]
  linear_combination ((c2 : ℂ) * (evC z ps ^ k * evC z lin ^ ℓ) *
      ((starRingEnd ℂ) (evC z ps) ^ k * (starRingEnd ℂ) (evC z lin) ^ ℓ)) * hzn1 +
    ((c3 : ℂ) * (evC z S * (starRingEnd ℂ) (evC z S))) * hzn2

/-! ### Positivity of the central coefficient -/

theorem evC_eq_sum (z : ℂ) (c : List ℤ) :
    evC z c = ∑ i ∈ range c.length, (c.getD i 0 : ℂ) * z ^ i := by
  induction c with
  | nil => simp [evC]
  | cons a c ih =>
    rw [List.length_cons, Finset.sum_range_succ', evC, ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, Int.cast_id, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem sumAbs_eq_sum (c : List ℤ) : sumAbs c = ∑ i ∈ range c.length, |c.getD i 0| := by
  induction c with
  | nil => simp [sumAbs]
  | cons a c ih =>
    rw [List.length_cons, Finset.sum_range_succ', sumAbs, ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]; ring

theorem re_pos_of_margin (c : List ℤ) {z : ℂ} (hz : ‖z‖ = 1) {n : ℕ} (hn : n < c.length)
    (hm : sumAbs c < 2 * c.getD n 0) : 0 < ((starRingEnd ℂ z) ^ n * evC z c).re := by
  have h1 := conj_mul_self_of_norm hz
  have hw : ‖(starRingEnd ℂ) z‖ = 1 := by
    have := congrArg norm h1
    rw [norm_mul, hz, norm_one] at this
    simpa using this
  have re_sum : ∀ (s : Finset ℕ) (f : ℕ → ℂ), (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]
  rw [evC_eq_sum, Finset.mul_sum, re_sum]
  have key : ∀ i ∈ range c.length, 0 ≤ (c.getD i 0 : ℝ) *
      ((starRingEnd ℂ z) ^ n * z ^ i).re + |(c.getD i 0 : ℝ)| := by
    intro i _
    have hb : |((starRingEnd ℂ z) ^ n * z ^ i).re| ≤ 1 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_pow, norm_pow, hz, hw]; simp
    have := abs_le.mp hb
    rcases le_total 0 (c.getD i 0 : ℝ) with h | h
    · rw [abs_of_nonneg h]; nlinarith [this.1]
    · rw [abs_of_nonpos h]; nlinarith [this.2]
  have hn1 : ((starRingEnd ℂ z) ^ n * z ^ n).re = 1 := by
    rw [← mul_pow, h1]; simp
  have hsingle := Finset.single_le_sum key (Finset.mem_range.mpr hn)
  have hmR : (sumAbs c : ℝ) < 2 * (c.getD n 0 : ℝ) := by exact_mod_cast hm
  have hs : ((sumAbs c : ℤ) : ℝ) = ∑ i ∈ range c.length, |(c.getD i 0 : ℝ)| := by
    rw [sumAbs_eq_sum]; push_cast; rfl
  have hre : ∀ i ∈ range c.length,
      (((c.getD i 0 : ℂ) * ((starRingEnd ℂ z) ^ n * z ^ i))).re =
      (c.getD i 0 : ℝ) * ((starRingEnd ℂ z) ^ n * z ^ i).re := by
    intro i _
    rw [show ((c.getD i 0 : ℤ) : ℂ) = (((c.getD i 0 : ℤ) : ℝ) : ℂ) by simp, Complex.re_ofReal_mul]
  have hrw : ∀ i ∈ range c.length,
      (starRingEnd ℂ z) ^ n * ((c.getD i 0 : ℂ) * z ^ i) =
      (c.getD i 0 : ℂ) * ((starRingEnd ℂ z) ^ n * z ^ i) := fun i _ => by ring
  rw [Finset.sum_congr rfl (fun i hi => by rw [hrw i hi]), Finset.sum_congr rfl hre]
  have hsum : 0 ≤ ∑ i ∈ range c.length, ((c.getD i 0 : ℝ) *
      ((starRingEnd ℂ z) ^ n * z ^ i).re + |(c.getD i 0 : ℝ)|) :=
    Finset.sum_nonneg key
  rw [Finset.sum_add_distrib, ← hs] at hsum
  rw [hn1, Finset.sum_add_distrib, ← hs] at hsingle
  have hcn : (0 : ℝ) < (c.getD n 0 : ℝ) := by
    have : (0 : ℤ) ≤ sumAbs c := by rw [sumAbs_eq_sum]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : (0 : ℝ) ≤ sumAbs c := by exact_mod_cast this
    linarith
  rw [abs_of_pos hcn] at hsingle
  have hsingle' := hsingle
  linarith [hsingle, hsum, hmR]


/-! ### The finite check and its soundness -/

/-- `f(2^K)` computed from the sources, with exact `2^e` powers (no `Int` power chains). -/
def fValue (K : ℕ) (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) : ℤ :=
  c1 * pow2 (K * n) -
    c2 * ((hornerZ (pow2 K) ps ^ k * hornerZ (pow2 K) lin ^ ℓ) *
      (hornerZ (pow2 K) ps.reverse ^ k * hornerZ (pow2 K) lin.reverse ^ ℓ)) -
    c3 * pow2 (K * e) * hornerZ (pow2 K) S ^ 2

/-- A-priori bound on every coefficient of `f`, from the inputs only. -/
def boundM (ps lin S : List ℤ) (k ℓ : ℕ) (c1 c2 c3 : ℤ) : ℤ :=
  |c1| + |c2| * ((sumAbs ps ^ k * sumAbs lin ^ ℓ) *
    (sumAbs ps.reverse ^ k * sumAbs lin.reverse ^ ℓ)) + |c3| * sumAbs S ^ 2

/-- Structural and size conditions. -/
def Shape (K J : ℕ) (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) : Prop :=
  ps ≠ [] ∧ lin ≠ [] ∧ S ≠ [] ∧ n = k * (ps.length - 1) + ℓ * (lin.length - 1) ∧
    S.reverse = S ∧ e + (S.length - 1) = n ∧ S.length - 1 ≤ n ∧ 0 < c2 ∧ 0 ≤ c3 ∧
    1 ≤ K ∧ 2 * n < 2 ^ J ∧ 2 * boundM ps lin S k ℓ c1 c2 c3 < pow2 K

instance (K J : ℕ) (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) :
    Decidable (Shape K J ps lin S k ℓ n e c1 c2 c3) := by
  unfold Shape; infer_instance

/-- The whole certificate: shape, balanced digits of `f(2^K)`, and the central margin. -/
def checkCircle (K J : ℕ) (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) : Bool :=
  decide (Shape K J ps lin S k ℓ n e c1 c2 c3) &&
    (decT K J (fValue K ps lin S k ℓ n e c1 c2 c3)).all (fun x => decide (2 * |x| < pow2 K)) &&
    decide (sumAbs (decT K J (fValue K ps lin S k ℓ n e c1 c2 c3)) <
      2 * (decT K J (fValue K ps lin S k ℓ n e c1 c2 c3)).getD n 0)

theorem natDegree_fPoly_le (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ)
    (hn : n = k * (ps.length - 1) + ℓ * (lin.length - 1)) (hSe : e + (S.length - 1) = n)
    (hSn : S.length - 1 ≤ n) :
    (fPoly ps lin S k ℓ n e c1 c2 c3).natDegree ≤ 2 * n := by
  have hP := natDegree_polyOfList_le ps
  have hL := natDegree_polyOfList_le lin
  have hPr := natDegree_polyOfList_le ps.reverse
  have hLr := natDegree_polyOfList_le lin.reverse
  have hG := natDegree_polyOfList_le S
  simp only [List.length_reverse] at hPr hLr
  have h1 : (C c1 * (X : ℤ[X]) ^ n).natDegree ≤ n := natDegree_C_mul_X_pow_le _ _
  have hA : (polyOfList ps ^ k * polyOfList lin ^ ℓ).natDegree ≤ n := by
    refine (natDegree_mul_le).trans ?_
    have := natDegree_pow_le (p := polyOfList ps) (n := k)
    have := natDegree_pow_le (p := polyOfList lin) (n := ℓ)
    have : k * (polyOfList ps).natDegree ≤ k * (ps.length - 1) := Nat.mul_le_mul_left _ hP
    have : ℓ * (polyOfList lin).natDegree ≤ ℓ * (lin.length - 1) := Nat.mul_le_mul_left _ hL
    omega
  have hB : (polyOfList ps.reverse ^ k * polyOfList lin.reverse ^ ℓ).natDegree ≤ n := by
    refine (natDegree_mul_le).trans ?_
    have := natDegree_pow_le (p := polyOfList ps.reverse) (n := k)
    have := natDegree_pow_le (p := polyOfList lin.reverse) (n := ℓ)
    have : k * (polyOfList ps.reverse).natDegree ≤ k * (ps.length - 1) := Nat.mul_le_mul_left _ hPr
    have : ℓ * (polyOfList lin.reverse).natDegree ≤ ℓ * (lin.length - 1) := Nat.mul_le_mul_left _ hLr
    omega
  have h2 : (C c2 * ((polyOfList ps ^ k * polyOfList lin ^ ℓ) *
      (polyOfList ps.reverse ^ k * polyOfList lin.reverse ^ ℓ))).natDegree ≤ 2 * n := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, zero_add]
    refine (natDegree_mul_le).trans ?_
    omega
  have h3 : (C c3 * (X : ℤ[X]) ^ e * polyOfList S ^ 2).natDegree ≤ 2 * n := by
    refine (natDegree_mul_le).trans ?_
    have := natDegree_pow_le (p := polyOfList S) (n := 2)
    have : (C c3 * (X : ℤ[X]) ^ e).natDegree ≤ e := natDegree_C_mul_X_pow_le _ _
    have : 2 * (polyOfList S).natDegree ≤ 2 * (S.length - 1) := Nat.mul_le_mul_left _ hG
    omega
  unfold fPoly
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ h2)) h3)
  omega

theorem eval_fPoly (K : ℕ) (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) :
    (fPoly ps lin S k ℓ n e c1 c2 c3).eval (pow2 K) = fValue K ps lin S k ℓ n e c1 c2 c3 := by
  simp only [fPoly, fValue, eval_sub, eval_mul, eval_pow, eval_C, eval_X, polyOfList_eval,
    pow2_mul_pow]

theorem dom_fPoly (ps lin S : List ℤ) (k ℓ n e : ℕ) (c1 c2 c3 : ℤ) :
    ∀ i, |(fPoly ps lin S k ℓ n e c1 c2 c3).coeff i| ≤ boundM ps lin S k ℓ c1 c2 c3 := by
  have hP := Dom.polyOfList ps
  have hL := Dom.polyOfList lin
  have hPr := Dom.polyOfList ps.reverse
  have hLr := Dom.polyOfList lin.reverse
  have hG := Dom.polyOfList S
  have hd : Dom (fPoly ps lin S k ℓ n e c1 c2 c3)
      (C |c1| * X ^ n + C |c2| * ((polyOfList (ps.map fun x => |x|) ^ k *
        polyOfList (lin.map fun x => |x|) ^ ℓ) *
        (polyOfList (ps.reverse.map fun x => |x|) ^ k *
          polyOfList (lin.reverse.map fun x => |x|) ^ ℓ)) +
        C |c3| * X ^ e * polyOfList (S.map fun x => |x|) ^ 2) := by
    unfold fPoly
    refine Dom.sub (Dom.sub (Dom.C_mul c1 (Dom.refl_X_pow n)) (Dom.C_mul c2 ?_)) ?_
    · exact ((hP.pow k).mul (hL.pow ℓ)).mul ((hPr.pow k).mul (hLr.pow ℓ))
    · exact (Dom.C_mul c3 (Dom.refl_X_pow e)).mul (hG.pow 2)
  intro i
  refine (hd i).trans ?_
  have hnn := hd.nonneg
  refine (coeff_le_eval_one hnn i).trans (le_of_eq ?_)
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, one_pow, mul_one, one_mul,
    eval_one_polyOfList_abs, boundM]

theorem circle_normSq_lt {K J : ℕ} {ps lin S : List ℤ} {k ℓ n e : ℕ} {c1 c2 c3 : ℤ}
    (h : checkCircle K J ps lin S k ℓ n e c1 c2 c3 = true) {z : ℂ} (hz : ‖z‖ = 1) :
    (c2 : ℝ) * Complex.normSq (evC z ps ^ k * evC z lin ^ ℓ) < c1 := by
  simp only [checkCircle, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hshape, hdig⟩, hmar⟩ := h
  obtain ⟨hps, hlin, hSne, hn, hS, hSe, hSn, hc2, hc3, hK, hJ, hM⟩ := hshape
  set N := fValue K ps lin S k ℓ n e c1 c2 c3 with hN
  set f := fPoly ps lin S k ℓ n e c1 c2 c3 with hf
  have hdeg : f.natDegree < 2 ^ J :=
    lt_of_le_of_lt (natDegree_fPoly_le ps lin S k ℓ n e c1 c2 c3 hn hSe hSn) hJ
  have hB0 : 0 < pow2 K := by unfold pow2; positivity
  have hfe : f = polyOfList ((List.range (2 ^ J)).map f.coeff) := eq_polyOfList_range f hdeg
  have hlf : ((List.range (2 ^ J)).map f.coeff).length = (decT K J N).length := by
    simp [decT_length]
  have hpack : hornerZ (pow2 K) ((List.range (2 ^ J)).map f.coeff) =
      hornerZ (pow2 K) (decT K J N) := by
    rw [decT_sound, ← polyOfList_eval, ← hfe, hf, eval_fPoly]
  have hcoef := dom_fPoly ps lin S k ℓ n e c1 c2 c3
  have hlist : (List.range (2 ^ J)).map f.coeff = decT K J N := by
    refine hornerZ_inj hB0 _ _ hlf ?_ hdig hpack
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    have := hcoef i
    have h2 : 2 * |f.coeff i| ≤ 2 * boundM ps lin S k ℓ c1 c2 c3 := by linarith
    linarith
  have hfc : f = polyOfList (decT K J N) := by rw [← hlist]; exact hfe
  have hnlen : n < (decT K J N).length := by
    rw [decT_length]
    omega
  have hre := re_pos_of_margin (decT K J N) hz hnlen hmar
  have hev := aeval_fPoly (c1 := c1) (c2 := c2) (c3 := c3) hps hlin hn hS hSne hSe hz
  rw [← hf, hfc, polyOfList_aeval] at hev
  have h1 := conj_mul_self_of_norm hz
  have hone : (starRingEnd ℂ z) ^ n * z ^ n = 1 := by rw [← mul_pow, h1, one_pow]
  rw [hev, ← mul_assoc, hone, one_mul, Complex.ofReal_re] at hre
  have h3 : (0 : ℝ) ≤ c3 * Complex.normSq (evC z S) :=
    mul_nonneg (by exact_mod_cast hc3) (Complex.normSq_nonneg _)
  linarith

end CatalanMeasure.GenD.Signed.Davis.CircleCheb

#print axioms CatalanMeasure.GenD.Signed.Davis.CircleCheb.decT_sound
#print axioms CatalanMeasure.GenD.Signed.Davis.CircleCheb.aeval_fPoly
#print axioms CatalanMeasure.GenD.Signed.Davis.CircleCheb.re_pos_of_margin
#print axioms CatalanMeasure.GenD.Signed.Davis.CircleCheb.circle_normSq_lt

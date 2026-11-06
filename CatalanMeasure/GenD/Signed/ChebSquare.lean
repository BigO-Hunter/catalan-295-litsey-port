module

public import OAI.NumberTheory.Catalan.Estimates.RealEnergyChebyshev
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Shared Chebyshev square soundness

C-SQ is a data-free real-interval interface. Coefficient inputs are exact integer lists;
all dyadic scaling is explicit. Source-to-polynomial bounds belong to callers.
No imported certificate or ArcsineDenominator declaration is modified here.
-/

set_option Elab.async false

namespace CatalanMeasure.Signed.ChebSquare

open Polynomial

/-- The degree-`n` Chebyshev basis function. -/
noncomputable def basis (n : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

@[simp] theorem basis_zero (x : ℝ) : basis 0 x = 1 := by
  simp [basis]

/-- Exact doubled product; the absolute index uses the evenness of `T`. -/
theorem basis_mul (i j : ℕ) (x : ℝ) :
    2 * basis i x * basis j x =
      basis (i + j) x + basis ((i : ℤ) - j).natAbs x := by
  have h := congrArg (Polynomial.eval x)
    (Polynomial.Chebyshev.T_mul_T ℝ (i : ℤ) (j : ℤ))
  simpa only [basis, Nat.cast_add, Polynomial.Chebyshev.T_natAbs,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat] using h

theorem abs_basis_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |basis n x| ≤ 1 := by
  exact OAI.InternalCatalan.energy_chebyshev_abs_le_one n hx

/-- A single forward traversal, with no repeated indexed lookup. -/
def l1 (c : List ℤ) : ℤ :=
  match c with
  | [] => 0
  | a :: tail => |a| + l1 tail

/-- Unscaled list evaluation beginning at an arbitrary Chebyshev index. -/
noncomputable def rawSum : List ℤ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: tail, k, x => (a : ℝ) * basis k x + rawSum tail (k + 1) x

@[simp] theorem rawSum_nil (k : ℕ) (x : ℝ) : rawSum [] k x = 0 := rfl

@[simp] theorem rawSum_cons (a : ℤ) (tail : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (a :: tail) k x = (a : ℝ) * basis k x + rawSum tail (k + 1) x := rfl

theorem abs_rawSum_le (c : List ℤ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |rawSum c k x| ≤ (l1 c : ℝ) := by
  induction c generalizing k with
  | nil => simp [rawSum, l1]
  | cons a tail ih =>
    calc
      |rawSum (a :: tail) k x| ≤ |(a : ℝ) * basis k x| + |rawSum tail (k + 1) x| :=
        abs_add_le _ _
      _ ≤ |(a : ℝ)| + (l1 tail : ℝ) := by
        rw [abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_basis_le_one k hx))
          (ih (k + 1))
      _ = (l1 (a :: tail) : ℝ) := by simp [l1]

theorem rawSum_pos_of_margin (r : List ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hm : l1 r.tail < r.headD 0) :
    0 < rawSum r 0 x := by
  cases r with
  | nil => simp [l1] at hm
  | cons a tail =>
    have ht := abs_rawSum_le tail 1 hx
    have hlo := (abs_le.mp ht).1
    have hmargin : (l1 tail : ℝ) < (a : ℝ) := by
      change l1 tail < a at hm
      exact_mod_cast hm
    simp only [rawSum_cons, basis_zero, mul_one]
    linarith


/-- Zero-extended coefficient addition; one structural list traversal. -/
def addZ : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a :: tail, [] => a :: tail
  | a :: tail, b :: rest => (a + b) :: addZ tail rest

@[simp] theorem rawSum_addZ (a b : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (addZ a b) k x = rawSum a k x + rawSum b k x := by
  induction a generalizing b k with
  | nil => simp [addZ]
  | cons a tail ih =>
    cases b with
    | nil => simp [addZ]
    | cons b rest => simp [addZ, ih]; ring

def smulZ (a : ℤ) (b : List ℤ) : List ℤ := b.map (a * ·)

@[simp] theorem rawSum_smulZ (a : ℤ) (b : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (smulZ a b) k x = (a : ℝ) * rawSum b k x := by
  induction b generalizing k with
  | nil => simp [smulZ]
  | cons b tail ih =>
    change ((a * b : ℤ) : ℝ) * basis k x + rawSum (smulZ a tail) (k + 1) x =
      (a : ℝ) * ((b : ℝ) * basis k x + rawSum tail (k + 1) x)
    rw [ih (k + 1)]
    push_cast
    ring

/-- Prefix zeros without indexed lookups. -/
def shiftZ : ℕ → List ℤ → List ℤ
  | 0, c => c
  | n + 1, c => 0 :: shiftZ n c

@[simp] theorem rawSum_shiftZ (n : ℕ) (c : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (shiftZ n c) k x = rawSum c (k + n) x := by
  induction n generalizing k with
  | zero => simp [shiftZ]
  | succ n ih => simp [shiftZ, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def monoZ (n : ℕ) (a : ℤ) : List ℤ := shiftZ n [a]

@[simp] theorem rawSum_monoZ (n : ℕ) (a : ℤ) (x : ℝ) :
    rawSum (monoZ n a) 0 x = (a : ℝ) * basis n x := by
  simp [monoZ]

/-- Exact scalar reference row for the doubled Chebyshev product.
This reference is not advertised as a Kronecker implementation. -/
def mulRowZ (i : ℕ) (a : ℤ) : List ℤ → ℕ → List ℤ
  | [], _ => []
  | b :: tail, j =>
      addZ (addZ (monoZ (i + j) (a * b))
        (monoZ ((i : ℤ) - j).natAbs (a * b))) (mulRowZ i a tail (j + 1))

theorem rawSum_mulRowZ (i : ℕ) (a : ℤ) (b : List ℤ) (j : ℕ) (x : ℝ) :
    rawSum (mulRowZ i a b j) 0 x = 2 * (a : ℝ) * basis i x * rawSum b j x := by
  induction b generalizing j with
  | nil => simp [mulRowZ]
  | cons b tail ih =>
    simp only [mulRowZ, rawSum_addZ, rawSum_monoZ, rawSum_cons, ih]
    push_cast
    have h := basis_mul i j x
    calc
      (a : ℝ) * b * basis (i + j) x +
          (a : ℝ) * b * basis ((i : ℤ) - j).natAbs x +
          2 * a * basis i x * rawSum tail (j + 1) x =
        (a : ℝ) * b * (basis (i + j) x + basis ((i : ℤ) - j).natAbs x) +
          2 * a * basis i x * rawSum tail (j + 1) x := by ring
      _ = 2 * (a : ℝ) * basis i x * ((b : ℝ) * basis j x + rawSum tail (j + 1) x) := by
        rw [← h]
        ring

/-- Scalar exact doubled-product reference; future packed consumers must prove an equality
with this reference, rather than assuming packing soundness. -/
def mulZ : List ℤ → ℕ → List ℤ → List ℤ
  | [], _, _ => []
  | a :: tail, i, b => addZ (mulRowZ i a b 0) (mulZ tail (i + 1) b)

theorem rawSum_mulZ (a : List ℤ) (i : ℕ) (b : List ℤ) (x : ℝ) :
    rawSum (mulZ a i b) 0 x = 2 * rawSum a i x * rawSum b 0 x := by
  induction a generalizing i with
  | nil => simp [mulZ]
  | cons a tail ih =>
    simp only [mulZ, rawSum_addZ, rawSum_mulRowZ, rawSum_cons, ih]
    ring

/-- Append decomposition, used to ignore harmless trailing zero coefficients. -/
theorem rawSum_append (a b : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (a ++ b) k x = rawSum a k x + rawSum b (k + a.length) x := by
  induction a generalizing k with
  | nil => simp
  | cons a tail ih => simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]; ring

@[simp] theorem rawSum_replicate_zero (n k : ℕ) (x : ℝ) :
    rawSum (List.replicate n 0) k x = 0 := by
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- A bounded, linear zero-extension binding. -/
def padZ (n : ℕ) (c : List ℤ) : List ℤ := c ++ List.replicate (n - c.length) 0

@[simp] theorem rawSum_padZ (n : ℕ) (c : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (padZ n c) k x = rawSum c k x := by
  simp [padZ, rawSum_append]

/-- Exact coefficient equality modulo trailing zeros. Two linear traversals suffice. -/
def CoeffEq (a b : List ℤ) : Prop :=
  padZ (max a.length b.length) a = padZ (max a.length b.length) b

instance (a b : List ℤ) : Decidable (CoeffEq a b) := by
  unfold CoeffEq
  infer_instance

theorem CoeffEq.eval {a b : List ℤ} (h : CoeffEq a b) (k : ℕ) (x : ℝ) :
    rawSum a k x = rawSum b k x := by
  have he := congrArg (fun c => rawSum c k x) h
  simpa only [rawSum_padZ] using he

/-- Linear structural Horner binding for signed packed coefficients.
No Kronecker no-carry theorem is assumed by C-SQ. A packed producer must supply its own
proved equality with the scalar product reference. -/
def packZ (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: tail => a + base * packZ base tail

/-- One general positive denominator is applied after summing integer coefficients.
Odd factors are allowed, in particular the powers of five in the S1 normalization. -/
noncomputable def chebSum (c : List ℤ) (denominator : ℕ) (x : ℝ) : ℝ :=
  rawSum c 0 x / (denominator : ℝ)

/-- Integer numerator of twice the exact Chebyshev product. The output denominator is
`2*Da*Db`. This is a scalar semantic reference, not an unproved packed algorithm. -/
def chebMulQ (a b : List ℤ) : List ℤ := mulZ a 0 b

theorem chebSum_chebMulQ (a b : List ℤ) (Da Db : ℕ)
    (hDa : 0 < Da) (hDb : 0 < Db) (x : ℝ) :
    chebSum (chebMulQ a b) (2 * Da * Db) x = chebSum a Da x * chebSum b Db x := by
  have ha : (Da : ℝ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hb : (Db : ℝ) ≠ 0 := by exact_mod_cast hDb.ne'
  simp only [chebSum, chebMulQ, rawSum_mulZ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  <;> ring

/-- Remove a common two-power by one exact linear coefficient binding; the remaining
positive denominator may still have odd factors. -/
theorem chebSum_rescale (a b : List ℤ) (D k : ℕ) (hD : 0 < D)
    (h : a = smulZ ((2 : ℤ) ^ k) b) (x : ℝ) :
    chebSum a (D * 2 ^ k) x = chebSum b D x := by
  subst a
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
  simp only [chebSum, rawSum_smulZ, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- Exact doubled Chebyshev numerator of `1-x²`. -/
theorem rawSum_weight (x : ℝ) : rawSum [1, 0, -1] 0 x = 2 * (1 - x ^ 2) := by
  norm_num [rawSum, basis, Polynomial.Chebyshev.T_two]
  <;> ring

/-- An integer-only coefficient identity. The common polynomial denominator D is general;
the scalar cap difference denominator is cross-multiplied once as well. -/
def SquareIdentity (p q s r : List ℤ) (denominator : ℕ) (cap ε : ℚ) : Prop :=
  let d : ℤ := denominator
  let c : ℚ := cap - ε
  let g : ℤ := c.den
  CoeffEq
    (addZ [8 * c.num * d ^ 2] (smulZ (-8 * g * d) p))
    (addZ (smulZ (4 * g) (chebMulQ q q))
      (addZ (smulZ g (chebMulQ [1, 0, -1] (chebMulQ s s)))
        (smulZ (8 * g * d) r)))

instance (p q s r : List ℤ) (D : ℕ) (cap ε : ℚ) :
    Decidable (SquareIdentity p q s r D cap ε) := by
  unfold SquareIdentity
  infer_instance

theorem SquareIdentity.eval {p q s r : List ℤ} {D : ℕ} {cap ε : ℚ}
    (h : SquareIdentity p q s r D cap ε) (hD : 0 < D) (x : ℝ) :
    (cap : ℝ) - ε - chebSum p D x =
      chebSum q D x ^ 2 + (1 - x ^ 2) * chebSum s D x ^ 2 + chebSum r D x := by
  let c : ℚ := cap - ε
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hg : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.pos.ne'
  have he := CoeffEq.eval h 0 x
  change rawSum (addZ [8 * c.num * (D : ℤ) ^ 2]
    (smulZ (-8 * (c.den : ℤ) * D) p)) 0 x = _ at he
  simp only [rawSum_addZ, rawSum_smulZ, chebMulQ, rawSum_mulZ] at he
  rw [rawSum_weight] at he
  simp only [rawSum_cons, rawSum_nil, basis_zero, mul_one] at he
  push_cast at he
  have hn : (c.num : ℝ) * (D : ℝ) ^ 2 - (c.den : ℝ) * D * rawSum p 0 x =
      (c.den : ℝ) * rawSum q 0 x ^ 2 +
      (c.den : ℝ) * (1 - x ^ 2) * rawSum s 0 x ^ 2 +
      (c.den : ℝ) * D * rawSum r 0 x := by
    linear_combination (1 / 8 : ℝ) * he
  have hc : (cap : ℝ) - (ε : ℝ) = (c.num : ℝ) / (c.den : ℝ) := by
    rw [← Rat.cast_sub]
    exact Rat.cast_def c
  rw [hc]
  simp only [chebSum]
  field_simp [hd, hg]
  linear_combination hn

/-- Weighted C-SQ on the closed interval, including empty/trailing-zero coefficient lists. -/
theorem chebSum_add_lt_of_square (p q s r : List ℤ) (D : ℕ) (hD : 0 < D) (cap ε : ℚ)
    (hid : SquareIdentity p q s r D cap ε)
    (hm : l1 r.tail < r.headD 0)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : chebSum p D x + ε < cap := by
  have hid' := hid.eval hD x
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  have hr : 0 < chebSum r D x := div_pos (rawSum_pos_of_margin r hx hm) hd
  have hw : 0 ≤ 1 - x ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)
    nlinarith
  have hq := sq_nonneg (chebSum q D x)
  have hs := mul_nonneg hw (sq_nonneg (chebSum s D x))
  linarith

/-- Domain-polymorphic consumer, so the same checker applies pointwise to complex circles. -/
theorem le_cap_of_cheb_square {α : Type*} {f : α → ℝ} {S : Set α} (φ : α → ℝ)
    (p q s r : List ℤ) (D : ℕ) (hD : 0 < D) (cap ε : ℚ)
    (hφ : ∀ x ∈ S, φ x ∈ Set.Icc (-1 : ℝ) 1)
    (hf : ∀ x ∈ S, f x ≤ chebSum p D (φ x) + ε)
    (hid : SquareIdentity p q s r D cap ε)
    (hm : l1 r.tail < r.headD 0) : ∀ x ∈ S, f x < cap := by
  intro x hx
  exact (hf x hx).trans_lt (chebSum_add_lt_of_square p q s r D hD cap ε hid hm (hφ x hx))

/-! One tiny weighted regression with denominator10, exercising an odd factor5. -/
set_option profiler true in
 theorem tiny_weighted_identity : SquareIdentity [0] [0] [10] [15, 0, 5] 10 2 0 := by
  -- kcost: 0.02 s estimated; at most200 tiny integer/list operations including full binding.
  decide +kernel

set_option profiler true in
 theorem tiny_weighted_cap {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    chebSum [0] 10 x < 2 := by
  have hm : l1 ([15, 0, 5] : List ℤ).tail < ([15, 0, 5] : List ℤ).headD 0 := by
    -- kcost: 0.005 s estimated; one linear3-coefficient remainder check.
    decide +kernel
  simpa using chebSum_add_lt_of_square [0] [0] [10] [15, 0, 5] 10 (by norm_num) 2 0
    tiny_weighted_identity hm hx

#print axioms chebSum_chebMulQ
#print axioms chebSum_add_lt_of_square
#print axioms le_cap_of_cheb_square
#print axioms tiny_weighted_cap

end CatalanMeasure.Signed.ChebSquare
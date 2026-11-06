module

public import CatalanMeasure.GenD.Signed.RouteI.MarkedTransferSource
public import CatalanMeasure.GenD.Signed.ChebSquare
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section
set_option Elab.async false

/-!
# C5 `MarkedTransfer`: packed Laurent adapter and the anchor-1 free-row cap

Data-free. `LaurentBound` is the finite binding of a candidate cap/tail/coefficient set: the
P → H map is linear (`Hlist`: reverse, map, append), the identity `H = k(4 LA^2 - (1-Z^2)^2 LB^2) + Rc`
is an ordinary polynomial identity in `Z` (what the centred packed evaluation at `2k` proves, R2),
with the Laurent shifts `Z^d` explicit (`lift`, `liftC`). `LaurentBound.lt_cap` proves the weighted
C-SQ conclusion on all of `[-1,1]` by evaluating at `Z = e^{i theta}` (so interior `x` are covered).
`anchor1_freeRow_cap` is the terminal: `FreeRowCap t 0 c0` and the reference-difference cap give
`FreeRowCap t 1 (c0 + dCap)`; both signs, `rowDom = [-1,0) ∪ (0,1)`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MarkedTransfer

open CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.MarkedTransferSource
open CatalanMeasure.Signed.ChebSquare
open Polynomial

noncomputable section

/-! ### Lists as polynomials in `Z`, and the symmetric (Laurent) lift -/

/-- The ordinary polynomial of a coefficient list (index = power of `Z`). -/
def ofList : List ℤ → ℤ[X]
  | [] => 0
  | a :: t => C a + X * ofList t

/-- Evaluation of a coefficient list at a complex point (one forward traversal). -/
def evZ (z : ℂ) : List ℤ → ℂ
  | [] => 0
  | a :: t => (a : ℂ) + z * evZ z t

theorem aeval_ofList (z : ℂ) (l : List ℤ) : aeval z (ofList l) = evZ z l := by
  induction l with
  | nil => simp [ofList, evZ]
  | cons a t ih => simp [ofList, evZ, ih]

/-- The packed value is the polynomial value (Horner). -/
theorem eval_ofList (B : ℤ) (l : List ℤ) : (ofList l).eval B = packZ B l := by
  induction l with
  | nil => simp [ofList, packZ]
  | cons a t ih => simp [ofList, packZ, ih]

theorem evZ_append (z : ℂ) (l₁ l₂ : List ℤ) :
    evZ z (l₁ ++ l₂) = evZ z l₁ + z ^ l₁.length * evZ z l₂ := by
  induction l₁ with
  | nil => simp [evZ]
  | cons a t ih => simp only [List.cons_append, evZ, ih, List.length_cons, pow_succ]; ring

theorem evZ_reverse (z w : ℂ) (h : z * w = 1) (t : List ℤ) :
    evZ z t.reverse = z ^ t.length * (w * evZ w t) := by
  induction t with
  | nil => simp [evZ]
  | cons a t ih =>
    rw [List.reverse_cons, evZ_append, ih]
    simp only [evZ, List.length_cons, List.length_reverse, mul_zero, add_zero, pow_succ]
    linear_combination (-(z ^ t.length) * ((a : ℂ) + w * evZ w t)) * h

/-- Symmetric list with centre `c` and arms `t`: `reverse t ++ c :: t`. -/
def liftC (c : ℤ) (t : List ℤ) : List ℤ := t.reverse ++ c :: t

/-- The symmetric lift of a Chebyshev coefficient list: `L_d(a)(Z) = 2 Z^d Σ a_j T_j`. -/
def lift (a : List ℤ) : List ℤ := liftC (2 * a.headD 0) a.tail

theorem evZ_liftC (z w : ℂ) (h : z * w = 1) (c : ℤ) (t : List ℤ) :
    evZ z (liftC c t) = z ^ t.length * (c + z * evZ z t + w * evZ w t) := by
  rw [liftC, evZ_append, evZ_reverse z w h]
  simp only [evZ, List.length_reverse]
  ring

/-! ### The unit circle -/

/-- `e^{iθ}` and `e^{-iθ}`. -/
def zc (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
def wc (θ : ℝ) : ℂ := Complex.exp (-θ * Complex.I)

theorem zc_mul_wc (θ : ℝ) : zc θ * wc θ = 1 := by
  simp only [zc, wc, ← Complex.exp_add]
  have : (θ : ℂ) * Complex.I + -(θ : ℂ) * Complex.I = 0 := by ring
  rw [this, Complex.exp_zero]

theorem zc_ne_zero (θ : ℝ) : zc θ ≠ 0 := Complex.exp_ne_zero _

theorem basis_cos (k : ℕ) (θ : ℝ) : basis k (Real.cos θ) = Real.cos (k * θ) := by
  unfold basis
  simp

theorem zc_pow_add_wc_pow (θ : ℝ) (k : ℕ) :
    zc θ ^ k + wc θ ^ k = 2 * ((basis k (Real.cos θ) : ℝ) : ℂ) := by
  rw [basis_cos, zc, wc, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.ofReal_cos]
  have h := Complex.two_cos (((k * θ : ℝ)) : ℂ)
  rw [h]
  push_cast
  congr 2 <;> ring_nf

theorem sym_eval (θ : ℝ) (t : List ℤ) (k : ℕ) :
    zc θ ^ k * evZ (zc θ) t + wc θ ^ k * evZ (wc θ) t =
      2 * ((rawSum t k (Real.cos θ) : ℝ) : ℂ) := by
  induction t generalizing k with
  | nil => simp [evZ]
  | cons a t ih =>
    have h1 := zc_pow_add_wc_pow θ k
    have h2 := ih (k + 1)
    simp only [evZ, rawSum_cons]
    push_cast
    linear_combination (a : ℂ) * h1 + h2

theorem evZ_liftC_cos (θ : ℝ) (c : ℤ) (t : List ℤ) :
    evZ (zc θ) (liftC c t) =
      zc θ ^ t.length * ((c + 2 * rawSum t 1 (Real.cos θ) : ℝ) : ℂ) := by
  rw [evZ_liftC _ _ (zc_mul_wc θ)]
  have h := sym_eval θ t 1
  simp only [pow_one] at h
  push_cast
  linear_combination (zc θ ^ t.length) * h

theorem rawSum_head_tail (p : List ℤ) (x : ℝ) :
    rawSum p 0 x = (p.headD 0 : ℝ) + rawSum p.tail 1 x := by
  cases p with
  | nil => simp
  | cons a t => simp

theorem evZ_lift_cos (θ : ℝ) (a : List ℤ) :
    evZ (zc θ) (lift a) = zc θ ^ a.tail.length * ((2 * rawSum a 0 (Real.cos θ) : ℝ) : ℂ) := by
  rw [lift, evZ_liftC_cos, rawSum_head_tail]
  push_cast
  ring


/-! ### The linear P → H binding and the Laurent identity -/

/-- `H = reverse v ++ [2(capN - tailN - e p0)] ++ v`, `v = map (-e ·) p.tail`: two forward
traversals, a reverse and an append; no random access. `e = Df/dP`. -/
def Hlist (e : ℕ) (capN tailN : ℤ) (p : List ℤ) : List ℤ :=
  liftC (2 * (capN - tailN - e * p.headD 0)) (p.tail.map (fun c => -(e : ℤ) * c))

/-- Non-source hypotheses of the packed C-SQ consumer. The polynomial identity is the one the packed
evaluation at `2k` supplies (R2 `polynomial_eq_of_packed_eval`, centred guard `< β/2`).
`Df = e dP` is the common denominator of the cap and the tail; `capN/Df`, `tailN/Df` are the cap and
the whole tail; `rc` is the centre of the symmetric residual `Rc = liftC rc rt`; `k ≥ 0` the product
scale. -/
structure LaurentBound (p a b rt : List ℤ) (dP Df e k : ℕ) (capN tailN rc : ℤ) : Prop where
  dP_pos : 0 < dP
  Df_pos : 0 < Df
  e_mul : e * dP = Df
  len_p : p.tail.length = 2 * a.tail.length
  len_b : b.tail.length + 1 = a.tail.length
  len_r : rt.length = p.tail.length
  poly : ofList (Hlist e capN tailN p) =
    C (k : ℤ) * (4 * ofList (lift a) ^ 2 - (1 - X ^ 2) ^ 2 * ofList (lift b) ^ 2) +
      ofList (liftC rc rt)
  margin : 2 * l1 rt < rc

theorem rawSum_map_neg_mul (e : ℕ) (t : List ℤ) (k : ℕ) (x : ℝ) :
    rawSum (t.map (fun c => -(e : ℤ) * c)) k x = -(e : ℝ) * rawSum t k x := by
  have := rawSum_smulZ (-(e : ℤ)) t k x
  simpa [smulZ] using this

theorem LaurentBound.eq_cos {p a b rt : List ℤ} {dP Df e k : ℕ} {capN tailN rc : ℤ}
    (h : LaurentBound p a b rt dP Df e k capN tailN rc) (θ : ℝ) :
    2 * ((capN : ℝ) - tailN - e * rawSum p 0 (Real.cos θ)) =
      16 * k * (rawSum a 0 (Real.cos θ) ^ 2 +
        (1 - Real.cos θ ^ 2) * rawSum b 0 (Real.cos θ) ^ 2) + rc +
        2 * rawSum rt 1 (Real.cos θ) := by
  have hev := congrArg (aeval (zc θ)) h.poly
  simp only [map_add, map_mul, map_sub, map_pow, map_one, aeval_X, aeval_ofList,
    map_ofNat, map_natCast] at hev
  obtain ⟨m, hbm⟩ : ∃ m, b.tail.length = m := ⟨_, rfl⟩
  have hm : a.tail.length = m + 1 := by have := h.len_b; omega
  simp only [Hlist, evZ_lift_cos, evZ_liftC_cos, List.length_map, rawSum_map_neg_mul, h.len_p,
    h.len_r, hm, hbm] at hev
  have hzw := zc_mul_wc θ
  have hs : zc θ + wc θ = 2 * ((Real.cos θ : ℝ) : ℂ) := by
    have := zc_pow_add_wc_pow θ 1
    simpa [basis_cos] using this
  have hq : (1 - zc θ ^ 2) ^ 2 = 4 * zc θ ^ 2 * (((Real.cos θ : ℝ) : ℂ) ^ 2 - 1) := by
    have h1 : (1 - zc θ ^ 2) ^ 2 = zc θ ^ 2 * ((zc θ + wc θ) ^ 2 - 4) := by
      linear_combination (-(1 + zc θ * wc θ + 2 * zc θ ^ 2)) * hzw
    rw [h1, hs]; ring
  rw [hq] at hev
  have hz : zc θ ^ (2 * (m + 1)) ≠ 0 := pow_ne_zero _ (zc_ne_zero θ)
  have key : zc θ ^ (2 * (m + 1)) *
      (((2 * ((capN : ℝ) - tailN - e * rawSum p 0 (Real.cos θ)) : ℝ)) : ℂ) =
    zc θ ^ (2 * (m + 1)) *
      ((16 * k * (rawSum a 0 (Real.cos θ) ^ 2 +
        (1 - Real.cos θ ^ 2) * rawSum b 0 (Real.cos θ) ^ 2) + rc +
        2 * rawSum rt 1 (Real.cos θ) : ℝ) : ℂ) := by
    have hp := rawSum_head_tail p (Real.cos θ)
    push_cast at hev hp ⊢
    rw [hp]
    push_cast
    linear_combination hev
  have := mul_left_cancel₀ hz key
  exact_mod_cast this

/-- Weighted C-SQ on `[-1,1]` from the packed Laurent identity: the conclusion of
`chebSum_add_lt_of_square`, without passing through the coefficient-list `SquareIdentity`. -/
theorem LaurentBound.lt_cap {p a b rt : List ℤ} {dP Df e k : ℕ} {capN tailN rc : ℤ}
    (h : LaurentBound p a b rt dP Df e k capN tailN rc) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    chebSum p dP x + (tailN : ℝ) / Df < (capN : ℝ) / Df := by
  have hc := Real.cos_arccos hx.1 hx.2
  have heq := h.eq_cos (Real.arccos x)
  rw [hc] at heq
  have hr := abs_rawSum_le rt 1 hx
  have hmar : (2 * (l1 rt : ℝ)) < rc := by exact_mod_cast h.margin
  have hrr := (abs_le.mp hr).1
  have hw : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < (capN : ℝ) - tailN - e * rawSum p 0 x := by
    have h1 := mul_nonneg hk (add_nonneg (sq_nonneg (rawSum a 0 x))
      (mul_nonneg hw (sq_nonneg (rawSum b 0 x))))
    nlinarith
  have hDf : (Df : ℝ) = e * dP := by exact_mod_cast h.e_mul.symm
  have hDpos : (0 : ℝ) < Df := by exact_mod_cast h.Df_pos
  have hdP : (0 : ℝ) < dP := by exact_mod_cast h.dP_pos
  have heN : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · have h1 := h.e_mul
      have h2 := h.Df_pos
      subst h0
      omega
    · exact h0
  have he : (0 : ℝ) < e := by exact_mod_cast heN
  rw [← sub_pos]
  have : (capN : ℝ) / Df - (chebSum p dP x + (tailN : ℝ) / Df) =
      ((capN : ℝ) - tailN - e * rawSum p 0 x) / Df := by
    unfold chebSum
    rw [hDf]
    field_simp
    ring
  rw [this]
  exact div_pos hpos hDpos

#print axioms LaurentBound.lt_cap

/-! ### Consumers -/

/-- One sign: source majorant plus Laurent bound give the strict cap. -/
theorem refDiff_lt_of_laurent {S : CapSource} {σ : Sign} {p a b rt : List ℤ}
    {dP Df e k : ℕ} {capN tailN rc : ℤ}
    (hs : SourceMajorant S σ p dP ((tailN : ℝ) / Df))
    (hl : LaurentBound p a b rt dP Df e k capN tailN rc) :
    ∀ x ∈ CapSource.rowDom, signOf x = σ → refDiff S x < (capN : ℝ) / Df :=
  fun x hx hsg => (hs x hx hsg).trans_lt (hl.lt_cap (two_abs_sub_one_mem hx))

/-- Both signs (two sign-specific certificates, one common cap `capN/Df`). -/
theorem refDiff_le_of_laurent_signs {S : CapSource}
    {pn an bn rn pp ap bp rp : List ℤ} {dPn dPp Df en ep kn kp : ℕ}
    {capN tailN tailP rcn rcp : ℤ}
    (hsn : SourceMajorant S Sign.neg pn dPn ((tailN : ℝ) / Df))
    (hln : LaurentBound pn an bn rn dPn Df en kn capN tailN rcn)
    (hsp : SourceMajorant S Sign.pos pp dPp ((tailP : ℝ) / Df))
    (hlp : LaurentBound pp ap bp rp dPp Df ep kp capN tailP rcp) :
    ∀ x ∈ CapSource.rowDom, refDiff S x ≤ (capN : ℝ) / Df := by
  intro x hx
  cases hsg : signOf x
  · exact (refDiff_lt_of_laurent hsn hln x hx hsg).le
  · exact (refDiff_lt_of_laurent hsp hlp x hx hsg).le

/-- Terminal: anchor-1 FREE-row cap from the anchor-0 cap and the reference-difference cap. -/
theorem anchor1_freeRow_cap (S : CapSource) {t : Trunc} {c0 dCap : ℝ}
    (h0 : S.FreeRowCap t 0 c0) (hD : ∀ x ∈ CapSource.rowDom, refDiff S x ≤ dCap) :
    S.FreeRowCap t 1 (c0 + dCap) := by
  intro x hx
  have h := freeRow_sub_freeRow S t x
  have := h0 x hx
  have := hD x hx
  linarith

/-- The C5 numbers: `-2579777/1000000 + 818131429/(5*10^10) = -128170718571/(5*10^10)`. -/
theorem anchor1_freeRow_cap_c5 (S : CapSource) {t : Trunc}
    (h0 : S.FreeRowCap t 0 (-2579777 / 1000000))
    (hD : ∀ x ∈ CapSource.rowDom, refDiff S x ≤ 818131429 / 50000000000) :
    S.FreeRowCap t 1 (-128170718571 / 50000000000) := by
  have := anchor1_freeRow_cap S h0 hD
  norm_num at this ⊢
  exact this

/-- Full chain: two certificates with `capN / Df = 818131429/(5*10^10)`. -/
theorem anchor1_freeRow_cap_of_laurent (S : CapSource) {t : Trunc}
    {pn an bn rn pp ap bp rp : List ℤ} {dPn dPp Df en ep kn kp : ℕ}
    {capN tailN tailP rcn rcp : ℤ}
    (hcap : (capN : ℝ) / Df = 818131429 / 50000000000)
    (h0 : S.FreeRowCap t 0 (-2579777 / 1000000))
    (hsn : SourceMajorant S Sign.neg pn dPn ((tailN : ℝ) / Df))
    (hln : LaurentBound pn an bn rn dPn Df en kn capN tailN rcn)
    (hsp : SourceMajorant S Sign.pos pp dPp ((tailP : ℝ) / Df))
    (hlp : LaurentBound pp ap bp rp dPp Df ep kp capN tailP rcp) :
    S.FreeRowCap t 1 (-128170718571 / 50000000000) := by
  apply anchor1_freeRow_cap_c5 S h0
  rw [← hcap]
  exact refDiff_le_of_laurent_signs hsn hln hsp hlp

#print axioms anchor1_freeRow_cap_of_laurent
#print axioms eval_ofList

end

end CatalanMeasure.GenD.Signed.RouteI.MarkedTransfer

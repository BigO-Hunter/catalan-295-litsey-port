module

public import CatalanMeasure.CellCert.Cell
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section

/-!
# Sound Taylor-model cell bound with point coefficients and an exact quadratic maximum

Lean counterpart of the repaired arb bound `lfarb.taylor_box_ub`
(`g-joint-cert-2026-10-29/scripts/lfarb.py`, NOTES section 16.2).  For a field `s + g` on the cell
`[c - r, c + r]` the bound is

`min V (A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{k=3}^{M-1} B_k r^k + B_M r^M) + G`,

where

* `A0 ≥ s(c)`, `l1 ≤ s'(c) ≤ u1`, `A2 ≥ s''(c)/2` are the **point** Taylor coefficients at the
  centre (enclosures, not box-wide bounds);
* `qs a A r` is the **exact maximum** of `a y + A y²` over `|y| ≤ r` (vertex if it lies in the
  cell, else an endpoint);
* `B_k ≥ |s^{(k)}(c)| / k!` for `3 ≤ k < M`, and `B_M ≥ |s^{(M)}(ξ)| / M!` for **all** `ξ` in the
  cell (the remainder enclosure);
* `V` is an optional crude upper bound of `s` on the cell and `G ≥ g` on the cell is a separately
  bounded piece (the `max(g0, gb)` of `taylor_box_ub`).

The old second-order box form `f(m) + |f'(m)| r + max(0, f'') r²/2` is *not* proved here: it is
unsound and non-convergent on the polynomial-density potentials (NOTES 16.1).

Layers:

1. `quadSupR`, `quad_le_quadSupR`, `quadSupR_attained`: the exact quadratic maximum.
2. `IsTower`, `tmUBR`, `taylor_cell_ub`, `taylor_cell_ub_full`: the generic theorem for any
   derivative tower (reusing `CellCert.taylor_tower'`).
3. `quadSupQ`, `tmUBQ`, `tmUBQ_cast`: the same bound on rationals, structurally recursive, for
   `decide +kernel`.
4. Pole (log) fields: `F' = Σ_q Re[ρ_q/(x - p_q)]` with the pole towers `qt` of `CellCert`.
   Point coefficients are exact rationals (`poleCoeff`, from `poleVal`); the remainder is the
   derivative bound of the log terms from the distance of the cell to the nearest pole
   (`poleRemQ`).  `poleCellCheck` is the Boolean checker, `poleCellCheck_sound` its soundness.

Not in this module: a derivation of the crude box evaluation `V` for pole sums (the `v` fallback of
`taylor_box_ub`, which wins when a pole is at distance `≤ r` from the cell; such cells are bisected
or take `V` from elsewhere), and the value certificate `F(c) ≤ A0` (the consumer's hypothesis).
-/

namespace CatalanMeasure.GenD.Signed.TaylorCell

open Set Nat CatalanMeasure.CellCert

/-! ### 1. The exact maximum of `a y + A y²` over `|y| ≤ r` -/

/-- Exact maximum of `y ↦ a y + A y²` over `|y| ≤ r` (the `_quad_sup` of `lfarb.py`): the vertex
value `a²/(-4A)` if `A < 0` and the vertex lies in the cell, else the larger endpoint value. -/
noncomputable def quadSupR (a A r : ℝ) : ℝ :=
  if A < 0 ∧ |a| ≤ -2 * A * r then a ^ 2 / (-4 * A) else |a| * r + A * r ^ 2

theorem quad_le_quadSupR (a A r y : ℝ) (hy : |y| ≤ r) :
    a * y + A * y ^ 2 ≤ quadSupR a A r := by
  have hr : 0 ≤ r := (abs_nonneg y).trans hy
  unfold quadSupR
  split_ifs with h
  · obtain ⟨hA, -⟩ := h
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg (a + 2 * A * y)]
  · have hay : a * y ≤ |a| * |y| := by rw [← abs_mul]; exact le_abs_self _
    have hy2 : y ^ 2 ≤ r ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le y]) ((le_abs_self y).trans hy)
    by_cases hA : 0 ≤ A
    · nlinarith [mul_le_mul_of_nonneg_left hy2 hA, mul_le_mul_of_nonneg_left hy (abs_nonneg a)]
    · replace hA : A < 0 := not_le.mp hA
      have hlt : -2 * A * r < |a| := by
        by_contra hc
        exact h ⟨hA, not_lt.mp hc⟩
      have hAs : 0 ≤ A * (|y| - r) := mul_nonneg_of_nonpos_of_nonpos hA.le (by linarith)
      have hsq : A * |y| ^ 2 = A * y ^ 2 := by rw [sq_abs]
      have key : 0 ≤ (r - |y|) * (|a| + A * (r + |y|)) := by
        refine mul_nonneg (by linarith) ?_
        nlinarith
      nlinarith

/-- The maximum is attained: `quadSupR` is the *exact* maximum, not merely an upper bound. -/
theorem quadSupR_attained (a A r : ℝ) (hr : 0 ≤ r) :
    ∃ y : ℝ, |y| ≤ r ∧ a * y + A * y ^ 2 = quadSupR a A r := by
  unfold quadSupR
  split_ifs with h
  · obtain ⟨hA, ha⟩ := h
    refine ⟨-a / (2 * A), ?_, ?_⟩
    · have h2 : |2 * A| = -2 * A := by rw [abs_of_neg (by linarith)]; ring
      rw [abs_div, abs_neg, h2, div_le_iff₀ (by linarith)]
      linarith
    · have : A ≠ 0 := hA.ne
      field_simp
      ring
  · by_cases ha : 0 ≤ a
    · exact ⟨r, by rw [abs_of_nonneg hr], by rw [abs_of_nonneg ha]⟩
    · replace ha : a < 0 := not_le.mp ha
      exact ⟨-r, by rw [abs_neg, abs_of_nonneg hr], by rw [abs_of_neg ha]; ring⟩

/-- Interval form: `a₁ ∈ [l₁, u₁]` and `a₂ ≤ A₂` (the maximum is convex in `a₁`, monotone in
`a₂`, as in `taylor_box_ub`). -/
theorem quad_le_max (l1 u1 a1 a2 A2 r y : ℝ) (hy : |y| ≤ r) (h1l : l1 ≤ a1) (h1u : a1 ≤ u1)
    (h2 : a2 ≤ A2) :
    a1 * y + a2 * y ^ 2 ≤ max (quadSupR l1 A2 r) (quadSupR u1 A2 r) := by
  have hy2 : a2 * y ^ 2 ≤ A2 * y ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg y)
  rcases le_total 0 y with hy0 | hy0
  · have h3 : a1 * y ≤ u1 * y := mul_le_mul_of_nonneg_right h1u hy0
    have h4 := quad_le_quadSupR u1 A2 r y hy
    exact (by linarith : a1 * y + a2 * y ^ 2 ≤ quadSupR u1 A2 r).trans (le_max_right _ _)
  · have h3 : a1 * y ≤ l1 * y := mul_le_mul_of_nonpos_right h1l hy0
    have h4 := quad_le_quadSupR l1 A2 r y hy
    exact (by linarith : a1 * y + a2 * y ^ 2 ≤ quadSupR l1 A2 r).trans (le_max_left _ _)

/-! ### 2. The generic Taylor-model theorem for a derivative tower -/

/-- `f j` is the `j`-th derivative of `f 0` on the cell `[c - r, c + r]`, for `j ≤ M`
(continuity on the closed cell, derivatives on the open cell; the interface of
`CellCert.taylor_tower'`). -/
structure IsTower (f : ℕ → ℝ → ℝ) (c r : ℝ) (M : ℕ) : Prop where
  cont : ∀ j ≤ M, ContinuousOn (f j) (Icc (c - r) (c + r))
  der : ∀ j < M, ∀ x ∈ Ioo (c - r) (c + r), HasDerivAt (f j) (f (j + 1) x) x

theorem IsTower.add {f g : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hf : IsTower f c r M)
    (hg : IsTower g c r M) : IsTower (fun j x => f j x + g j x) c r M where
  cont j hj := (hf.cont j hj).add (hg.cont j hj)
  der j hj x hx := (hf.der j hj x hx).add (hg.der j hj x hx)

theorem IsTower.sub {f g : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hf : IsTower f c r M)
    (hg : IsTower g c r M) : IsTower (fun j x => f j x - g j x) c r M where
  cont j hj := (hf.cont j hj).sub (hg.cont j hj)
  der j hj x hx := (hf.der j hj x hx).sub (hg.der j hj x hx)

theorem IsTower.smul {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (w : ℝ) (hf : IsTower f c r M) :
    IsTower (fun j x => w * f j x) c r M where
  cont j hj := (hf.cont j hj).const_smul w
  der j hj x hx := (hf.der j hj x hx).const_mul w

/-- Smooth parts: a `C^M` function on `ℝ` has the tower `iteratedDeriv`. -/
theorem isTower_iteratedDeriv {f : ℝ → ℝ} {M : ℕ} (hf : ContDiff ℝ (M : WithTop ℕ∞) f)
    (c r : ℝ) : IsTower (fun j => iteratedDeriv j f) c r M where
  cont j hj := (hf.continuous_iteratedDeriv j (by exact_mod_cast hj)).continuousOn
  der j hj x _ := by
    have hd := (hf.differentiable_iteratedDeriv j (by exact_mod_cast hj)) x
    simpa [iteratedDeriv_succ] using hd.hasDerivAt

/-- The bound of `taylor_box_ub` (without the crude `V` and the separate piece `G`):
`A0 + max (qs l1 A2 r) (qs u1 A2 r) + Σ_{k=3}^{M-1} B_k r^k + B_M r^M`. -/
noncomputable def tmUBR (A0 l1 u1 A2 r : ℝ) (B : ℕ → ℝ) (BM : ℝ) (M : ℕ) : ℝ :=
  A0 + max (quadSupR l1 A2 r) (quadSupR u1 A2 r) + ∑ k ∈ Finset.Ico 3 M, B k * r ^ k + BM * r ^ M

/-- **The soundness theorem (generic form).**  Taylor model of order `M ≥ 3` with point
coefficients at the centre `c` and an exact quadratic maximum: for every `x` in the cell,
`f 0 x ≤ tmUBR ...`.  Hypotheses: point value, first coefficient enclosure, second coefficient
upper bound, bounds of the point coefficients `3 ≤ k < M`, and the remainder enclosure of
`f M / M!` over the whole cell. -/
theorem taylor_cell_ub {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hM : 3 ≤ M) (hf : IsTower f c r M)
    {A0 l1 u1 A2 BM : ℝ} {B : ℕ → ℝ}
    (h0 : f 0 c ≤ A0) (h1l : l1 ≤ f 1 c) (h1u : f 1 c ≤ u1) (h2 : f 2 c / 2 ≤ A2)
    (hB : ∀ k, 3 ≤ k → k < M → |f k c| / (k ! : ℝ) ≤ B k)
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f M x| / (M ! : ℝ) ≤ BM) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ tmUBR A0 l1 u1 A2 r B BM M := by
  intro x hx
  have hxr : |x - c| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hr : 0 ≤ r := (abs_nonneg _).trans hxr
  have hcI : c ∈ Icc (c - r) (c + r) := ⟨by linarith, by linarith⟩
  have hfac : (0 : ℝ) < (M ! : ℝ) := by positivity
  have hbd : ∀ y ∈ Icc (c - r) (c + r), |f M y| ≤ (M ! : ℝ) * BM := by
    intro y hy
    have := hBM y hy
    rw [div_le_iff₀ hfac] at this
    linarith
  have htay := taylor_tower' c r ((M ! : ℝ) * BM) M f hf.cont
    (fun j hj y hy => hf.der j hj y hy) hbd x hx
  have hBM0 : 0 ≤ BM := (div_nonneg (abs_nonneg _) hfac.le).trans (hBM c hcI)
  have hrem : |f 0 x - ∑ j ∈ Finset.range M, f j c * (x - c) ^ j / (j ! : ℝ)| ≤ BM * r ^ M := by
    refine htay.trans ?_
    have e : (M ! : ℝ) * BM * |x - c| ^ M / (M ! : ℝ) = BM * |x - c| ^ M := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxr M) hBM0
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => f j c * (x - c) ^ j / (j ! : ℝ)) hM
  have h3 : ∑ j ∈ Finset.range 3, f j c * (x - c) ^ j / (j ! : ℝ) =
      f 0 c + f 1 c * (x - c) + (f 2 c / 2) * (x - c) ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  have hmid : ∑ j ∈ Finset.Ico 3 M, f j c * (x - c) ^ j / (j ! : ℝ) ≤
      ∑ k ∈ Finset.Ico 3 M, B k * r ^ k := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hk3, hkM⟩ := Finset.mem_Ico.mp hk
    have hk0 : (0 : ℝ) < (k ! : ℝ) := by positivity
    have hBk := hB k hk3 hkM
    have e : f k c * (x - c) ^ k / (k ! : ℝ) = (f k c / (k ! : ℝ)) * (x - c) ^ k := by ring
    rw [e]
    calc (f k c / (k ! : ℝ)) * (x - c) ^ k ≤ |f k c / (k ! : ℝ)| * |x - c| ^ k := by
          rw [← abs_pow, ← abs_mul]; exact le_abs_self _
      _ ≤ B k * r ^ k := by
          have hab : |f k c / (k ! : ℝ)| = |f k c| / (k ! : ℝ) := by
            rw [abs_div, Nat.abs_cast]
          rw [hab]
          exact mul_le_mul hBk (pow_le_pow_left₀ (abs_nonneg _) hxr k)
            (by positivity) ((div_nonneg (abs_nonneg _) hk0.le).trans hBk)
  have hq := quad_le_max l1 u1 (f 1 c) (f 2 c / 2) A2 r (x - c) hxr h1l h1u h2
  have hrem2 := (abs_le.mp hrem).2
  unfold tmUBR
  linarith

/-- **The full form of `taylor_box_ub`:** `min(v, Taylor model) + max(g0, gb)`, with `V` a crude
upper bound of `f 0` on the cell (the plain interval evaluation `cb[0].upper()`) and `G` an upper
bound of the separately bounded piece `g`. -/
theorem taylor_cell_ub_full {f : ℕ → ℝ → ℝ} {c r : ℝ} {M : ℕ} (hM : 3 ≤ M)
    (hf : IsTower f c r M) {A0 l1 u1 A2 BM V G : ℝ} {B : ℕ → ℝ} {g : ℝ → ℝ}
    (h0 : f 0 c ≤ A0) (h1l : l1 ≤ f 1 c) (h1u : f 1 c ≤ u1) (h2 : f 2 c / 2 ≤ A2)
    (hB : ∀ k, 3 ≤ k → k < M → |f k c| / (k ! : ℝ) ≤ B k)
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f M x| / (M ! : ℝ) ≤ BM)
    (hV : ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ V) (hG : ∀ x ∈ Icc (c - r) (c + r), g x ≤ G) :
    ∀ x ∈ Icc (c - r) (c + r),
      f 0 x + g x ≤ min V (tmUBR A0 l1 u1 A2 r B BM M) + G := by
  intro x hx
  have h := taylor_cell_ub hM hf h0 h1l h1u h2 hB hBM x hx
  have := le_min (hV x hx) h
  linarith [hG x hx]

/-! ### 3. The same bound on rationals (for `decide +kernel`) -/

/-- `quadSupR` on rationals (no square roots; one division). -/
def quadSupQ (a A r : ℚ) : ℚ :=
  if A < 0 ∧ qabs' a ≤ -2 * A * r then a ^ 2 / (-4 * A) else qabs' a * r + A * r ^ 2

theorem quadSupQ_cast (a A r : ℚ) :
    ((quadSupQ a A r : ℚ) : ℝ) = quadSupR (a : ℝ) (A : ℝ) (r : ℝ) := by
  unfold quadSupQ quadSupR
  have hc : (A < 0 ∧ qabs' a ≤ -2 * A * r) ↔
      ((A : ℝ) < 0 ∧ |(a : ℝ)| ≤ -2 * (A : ℝ) * (r : ℝ)) := by
    rw [← qabs'_cast]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  split_ifs with h1 h2 h3
  · push_cast; ring
  · exact absurd (hc.mp h1) h2
  · exact absurd (hc.mpr h3) h1
  · push_cast; rw [qabs'_cast]

theorem qmax_cast (a b : ℚ) : ((qmax a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  unfold qmax
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (by exact_mod_cast (not_le.mp h).le)]

/-- `Σ_i B_i r^(k₀ + i)`. -/
def powSumQ (r : ℚ) : ℕ → List ℚ → ℚ
  | _, [] => 0
  | k, b :: bs => b * r ^ k + powSumQ r (k + 1) bs

theorem powSumQ_cast (r : ℚ) (Bl : List ℚ) :
    ∀ k : ℕ, ((powSumQ r k Bl : ℚ) : ℝ) =
      ∑ i ∈ Finset.range Bl.length, ((Bl.getD i 0 : ℚ) : ℝ) * (r : ℝ) ^ (k + i) := by
  induction Bl with
  | nil => intro k; simp [powSumQ]
  | cons b bs ih =>
    intro k
    rw [powSumQ, List.length_cons, Finset.sum_range_succ']
    push_cast
    rw [ih (k + 1)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show k + (i + 1) = k + 1 + i by omega]

/-- The Taylor-model bound on rationals.  `Bl = [B_3, ..., B_{M-1}]`, `M = |Bl| + 3`, and `BM`
bounds `|f^{(M)}|/M!` on the cell. -/
def tmUBQ (A0 l1 u1 A2 r : ℚ) (Bl : List ℚ) (BM : ℚ) : ℚ :=
  A0 + qmax (quadSupQ l1 A2 r) (quadSupQ u1 A2 r) + powSumQ r 3 Bl + BM * r ^ (Bl.length + 3)

theorem tmUBQ_cast (A0 l1 u1 A2 r : ℚ) (Bl : List ℚ) (BM : ℚ) :
    ((tmUBQ A0 l1 u1 A2 r Bl BM : ℚ) : ℝ) =
      tmUBR (A0 : ℝ) (l1 : ℝ) (u1 : ℝ) (A2 : ℝ) (r : ℝ)
        (fun k => ((Bl.getD (k - 3) 0 : ℚ) : ℝ)) (BM : ℝ) (Bl.length + 3) := by
  unfold tmUBQ tmUBR
  push_cast
  rw [qmax_cast, quadSupQ_cast, quadSupQ_cast, powSumQ_cast r Bl 3,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]

/-- Rational form of the generic theorem. -/
theorem taylor_cell_ub_rat {f : ℕ → ℝ → ℝ} {c r : ℝ} (Bl : List ℚ)
    (hf : IsTower f c r (Bl.length + 3)) {A0 l1 u1 A2 BM : ℚ}
    (h0 : f 0 c ≤ (A0 : ℝ)) (h1l : (l1 : ℝ) ≤ f 1 c) (h1u : f 1 c ≤ (u1 : ℝ))
    (h2 : f 2 c / 2 ≤ (A2 : ℝ))
    (hB : ∀ i < Bl.length, |f (3 + i) c| / ((3 + i) ! : ℝ) ≤ ((Bl.getD i 0 : ℚ) : ℝ))
    (hBM : ∀ x ∈ Icc (c - r) (c + r), |f (Bl.length + 3) x| / ((Bl.length + 3) ! : ℝ) ≤ (BM : ℝ))
    (rq : ℚ) (hrq : (rq : ℝ) = r) :
    ∀ x ∈ Icc (c - r) (c + r), f 0 x ≤ ((tmUBQ A0 l1 u1 A2 rq Bl BM : ℚ) : ℝ) := by
  intro x hx
  rw [tmUBQ_cast, hrq]
  refine taylor_cell_ub (by omega) hf h0 h1l h1u h2 ?_ hBM x hx
  intro k hk3 hkM
  have := hB (k - 3) (by omega)
  rwa [show 3 + (k - 3) = k by omega] at this

/-! ### 4. Pole (log) fields -/

/-- Casting a list sum of rationals. -/
theorem cast_list_sum_q {α : Type*} (L : List α) (g : α → ℚ) :
    (((L.map g).sum : ℚ) : ℝ) = (L.map (fun a => ((g a : ℚ) : ℝ))).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- The derivative tower of a field `F` whose derivative is the pole sum `Σ_q Re[ρ_q/(x-p_q)]`
(`F = Σ_q Re[ρ_q log(x - p_q)] + const`): `F^{(j+1)} = Σ_q qt q j`. -/
noncomputable def poleTower (poles : List PoleR) (F : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => F
  | j + 1 => fun x => (poles.map (fun q => qt q j x)).sum

theorem poleTower_zero (poles : List PoleR) (F : ℝ → ℝ) : poleTower poles F 0 = F := rfl

theorem poleTower_succ (poles : List PoleR) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    poleTower poles F (j + 1) x = (poles.map (fun q => qt q j x)).sum := rfl

theorem isTower_poleTower (poles : List PoleR) (F : ℝ → ℝ) (c r : ℝ) (M : ℕ)
    (hne : ∀ y ∈ Icc (c - r) (c + r), ∀ q ∈ poles, (y : ℂ) ≠ q.pc)
    (hF : ∀ y ∈ Icc (c - r) (c + r),
      HasDerivAt F ((poles.map (fun q => qt q 0 y)).sum) y) :
    IsTower (poleTower poles F) c r M where
  cont j _ y hy := by
    cases j with
    | zero => exact (hF y hy).continuousAt.continuousWithinAt
    | succ j => exact (hasDerivAt_listsum_qt poles j y (hne y hy)).continuousAt.continuousWithinAt
  der j _ y hy := by
    have hyc : y ∈ Icc (c - r) (c + r) := ⟨hy.1.le, hy.2.le⟩
    cases j with
    | zero => exact hF y hyc
    | succ j => exact hasDerivAt_listsum_qt poles j y (hne y hyc)

/-- Exact rational Taylor coefficient `F^{(k)}(c)/k! = Σ_q poleVal q c (k-1) / k!`, `k ≥ 1`. -/
def poleCoeff (poles : List PoleR) (c : ℚ) (k : ℕ) : ℚ :=
  (poles.map (fun q => poleVal q c (k - 1))).sum / ((k ! : ℕ) : ℚ)

theorem poleCoeff_spec (poles : List PoleR) (F : ℝ → ℝ) (c : ℚ) (k : ℕ) :
    ((poleCoeff poles c (k + 1) : ℚ) : ℝ) = poleTower poles F (k + 1) (c : ℝ) / ((k + 1)! : ℝ) := by
  unfold poleCoeff
  rw [poleTower_succ, Rat.cast_div, cast_list_sum_q, Rat.cast_natCast]
  simp only [Nat.add_sub_cancel, poleVal_spec]

/-- Rational lower bound for the distance of a pole `p` to the cell `[lo, hi]`:
`max(g, |Im p|, 0.7071 (g + |Im p|))` with `g` the real gap (`‖z‖ ≥ (|Re z| + |Im z|)/√2`).
This is at least as sharp as `poleDl` and within a few percent of the true distance. -/
def poleGap (q : PoleR) (lo hi : ℚ) : ℚ := qmax 0 (qmax (lo - q.pr) (q.pr - hi))

def poleDist (q : PoleR) (lo hi : ℚ) : ℚ :=
  qmax (qmax (poleGap q lo hi) (qabs' q.pi)) ((7071 / 10000) * (poleGap q lo hi + qabs' q.pi))

theorem poleDist_le_norm (q : PoleR) (lo hi : ℚ) (y : ℝ) (h1 : (lo : ℝ) ≤ y) (h2 : y ≤ (hi : ℝ)) :
    ((poleDist q lo hi : ℚ) : ℝ) ≤ ‖(y : ℂ) - q.pc‖ := by
  set z : ℂ := (y : ℂ) - q.pc with hz
  have hre : z.re = y - q.pr := by simp [hz, PoleR.pc]
  have him : z.im = -(q.pi : ℝ) := by simp [hz, PoleR.pc]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    have := Complex.sq_norm_sub_sq_re z
    linarith
  have hg : ((poleGap q lo hi : ℚ) : ℝ) ≤ |z.re| := by
    unfold poleGap
    refine qmax_cast_le _ _ _ (by rw [Rat.cast_zero]; exact abs_nonneg _)
      (qmax_cast_le _ _ _ ?_ ?_)
    · push_cast; rw [hre]; linarith [le_abs_self (y - q.pr)]
    · push_cast; rw [hre]; linarith [neg_abs_le (y - q.pr)]
  have hb : ((qabs' q.pi : ℚ) : ℝ) = |z.im| := by rw [qabs'_cast, him, abs_neg]
  have hre_le : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have him_le : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hgn : 0 ≤ ((poleGap q lo hi : ℚ) : ℝ) := by
    unfold poleGap
    have : ((0 : ℚ) : ℝ) ≤ ((qmax 0 (qmax (lo - q.pr) (q.pr - hi)) : ℚ) : ℝ) := by
      rw [qmax_cast]; push_cast; exact le_max_left _ _
    simpa using this
  unfold poleDist
  refine qmax_cast_le _ _ _ (qmax_cast_le _ _ _ (hg.trans hre_le) (by rw [hb]; exact him_le)) ?_
  push_cast
  rw [hb]
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  have hx : 0 ≤ |z.re| + |z.im| := by positivity
  have hsum : (7071 / 10000 : ℝ) * (((poleGap q lo hi : ℚ) : ℝ) + |z.im|) ≤
      (7071 / 10000 : ℝ) * (|z.re| + |z.im|) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith
  have h3 : ‖z‖ < (7071 / 10000 : ℝ) * (|z.re| + |z.im|) := lt_of_lt_of_le hcon hsum
  have h4 : ‖z‖ ^ 2 < ((7071 / 10000 : ℝ) * (|z.re| + |z.im|)) ^ 2 := by
    apply pow_lt_pow_left₀ h3 hn (by norm_num)
  have h5 : z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
  have h6 : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  nlinarith [sq_nonneg (|z.re| - |z.im|)]

/-- Remainder bound of the pole terms (the derivative bound of log terms from the distance to the
nearest pole): `Σ_q (|Re ρ_q| + |Im ρ_q|) / (M dist_q^M)`, an upper bound of `|F^{(M)}|/M!`
over the cell `[lo, hi]` (`M ≥ 1`). -/
def poleRemQ (poles : List PoleR) (lo hi : ℚ) (M : ℕ) : ℚ :=
  (poles.map (fun q => (qabs' q.rr + qabs' q.ri) / ((M : ℚ) * poleDist q lo hi ^ M))).sum

theorem poleTower_rem (poles : List PoleR) (F : ℝ → ℝ) (lo hi : ℚ)
    (hdl : ∀ q ∈ poles, 0 < poleDist q lo hi) (m : ℕ) (y : ℝ) (h1 : (lo : ℝ) ≤ y)
    (h2 : y ≤ (hi : ℝ)) :
    |poleTower poles F (m + 1) y| / ((m + 1)! : ℝ) ≤ ((poleRemQ poles lo hi (m + 1) : ℚ) : ℝ) := by
  have hfac : (0 : ℝ) < ((m + 1)! : ℝ) := by positivity
  rw [poleTower_succ, div_le_iff₀ hfac]
  have hb : |(poles.map (fun q => qt q m y)).sum| ≤
      (poles.map (fun q => (|(q.rr : ℝ)| + |(q.ri : ℝ)|) * (m ! : ℝ) /
        ((poleDist q lo hi : ℚ) : ℝ) ^ (m + 1))).sum := by
    refine (abs_list_sum_le poles _).trans (List.sum_le_sum (fun q hq => ?_))
    exact qt_bound q m y _ (by exact_mod_cast hdl q hq) (poleDist_le_norm q lo hi y h1 h2)
  refine hb.trans ?_
  unfold poleRemQ
  rw [cast_list_sum_q, ← List.sum_map_mul_right]
  refine List.sum_le_sum (fun q hq => ?_)
  have hd : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl q hq
  push_cast
  rw [qabs'_cast, qabs'_cast]
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  apply le_of_eq
  field_simp

/-- Boolean check of the supplied coefficient bounds: `|a_k| ≤ B_k` for `k = k₀, k₀+1, ...`. -/
def coeffBoundsOK (poles : List PoleR) (c : ℚ) : ℕ → List ℚ → Bool
  | _, [] => true
  | k, b :: bs => decide (qabs' (poleCoeff poles c k) ≤ b) && coeffBoundsOK poles c (k + 1) bs

theorem coeffBoundsOK_spec (poles : List PoleR) (c : ℚ) :
    ∀ (Bl : List ℚ) (k : ℕ), coeffBoundsOK poles c k Bl = true →
      ∀ i < Bl.length, qabs' (poleCoeff poles c (k + i)) ≤ Bl.getD i 0 := by
  intro Bl
  induction Bl with
  | nil => intro k _ i hi; simp at hi
  | cons b bs ih =>
    intro k h i hi
    simp only [coeffBoundsOK, Bool.and_eq_true, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have := ih (k + 1) h.2 j (by simpa using hi)
      rw [show k + 1 + j = k + (j + 1) by omega] at this
      simpa using this

/-- The Boolean checker for one cell `[lo, hi]` of a pole field `F` (all data are rationals):
the poles are away from the cell, `l1 ≤ a₁ ≤ u1`, `a₂ ≤ A2`, `|a_k| ≤ B_k` (`3 ≤ k < M`), the
remainder `poleRemQ ≤ BM`, and the Taylor-model bound `tmUBQ ≤ T`. -/
def poleCellCheck (poles : List PoleR) (lo hi A0 l1 u1 A2 : ℚ) (Bl : List ℚ) (BM T : ℚ) : Bool :=
  decide (lo ≤ hi) &&
  poles.all (fun q => decide (0 < poleDist q lo hi)) &&
  decide (l1 ≤ poleCoeff poles ((lo + hi) / 2) 1) &&
  decide (poleCoeff poles ((lo + hi) / 2) 1 ≤ u1) &&
  decide (poleCoeff poles ((lo + hi) / 2) 2 ≤ A2) &&
  coeffBoundsOK poles ((lo + hi) / 2) 3 Bl &&
  decide (poleRemQ poles lo hi (Bl.length + 3) ≤ BM) &&
  decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

/-- **The soundness theorem every Phase 2 per-cell sup check applies (pole fields).**  If the
checker accepts, then `F ≤ T` on the whole cell `[lo, hi]`, given that `F' = Σ_q Re[ρ_q/(x-p_q)]`
on the cell and `F(centre) ≤ A0`. -/
theorem poleCellCheck_sound (poles : List PoleR) (F : ℝ → ℝ) (lo hi A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ)
    (hchk : poleCellCheck poles lo hi A0 l1 u1 A2 Bl BM T = true)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : F (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), F x ≤ (T : ℝ) := by
  simp only [poleCellCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hlh, hdl⟩, hl1⟩, hu1⟩, hA2⟩, hB⟩, hBM⟩, hT⟩ := hchk
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have hdl' : ∀ q ∈ poles, 0 < poleDist q lo hi := fun q hq => by simpa using hdl q hq
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hne : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), ∀ q ∈ poles, (y : ℂ) ≠ q.pc := by
    intro y hy q hq heq
    rw [hcell] at hy
    have := poleDist_le_norm q lo hi y hy.1 hy.2
    rw [heq, sub_self, norm_zero] at this
    have h2 : (0 : ℝ) < ((poleDist q lo hi : ℚ) : ℝ) := by exact_mod_cast hdl' q hq
    linarith
  have hF' : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      HasDerivAt F ((poles.map (fun q => qt q 0 y)).sum) y := by
    intro y hy; rw [hcell] at hy; exact hF y hy
  have hT0 := isTower_poleTower poles F (c : ℝ) (r : ℝ) (Bl.length + 3) hne hF'
  have hcoef := coeffBoundsOK_spec poles c Bl 3 hB
  intro x hx
  rw [← hcell] at hx
  have key := taylor_cell_ub_rat (f := poleTower poles F) (c := (c : ℝ)) (r := (r : ℝ)) Bl hT0
    (A0 := A0) (l1 := l1) (u1 := u1) (A2 := A2) (BM := BM)
    (by simpa [poleTower_zero] using h0)
    (by
      have := poleCoeff_spec poles F c 0
      have h1' : (l1 : ℝ) ≤ ((poleCoeff poles c 1 : ℚ) : ℝ) := by exact_mod_cast hl1
      simpa [this] using h1')
    (by
      have := poleCoeff_spec poles F c 0
      have h1' : ((poleCoeff poles c 1 : ℚ) : ℝ) ≤ (u1 : ℝ) := by exact_mod_cast hu1
      simpa [this] using h1')
    (by
      have := poleCoeff_spec poles F c 1
      have h2' : ((poleCoeff poles c 2 : ℚ) : ℝ) ≤ (A2 : ℝ) := by exact_mod_cast hA2
      rw [this] at h2'
      simpa [Nat.factorial] using h2')
    (by
      intro i hi
      have h1 := hcoef i hi
      have h2 := poleCoeff_spec poles F c (2 + i)
      have h3 : ((qabs' (poleCoeff poles c (3 + i)) : ℚ) : ℝ) ≤ ((Bl.getD i 0 : ℚ) : ℝ) := by
        exact_mod_cast h1
      rw [qabs'_cast] at h3
      rw [show 3 + i = 2 + i + 1 by omega] at h3 ⊢
      rw [h2] at h3
      rwa [abs_div, Nat.abs_cast] at h3)
    (by
      intro y hy
      rw [hcell] at hy
      have := poleTower_rem poles F lo hi hdl' (Bl.length + 2) y hy.1 hy.2
      have hrem : ((poleRemQ poles lo hi (Bl.length + 2 + 1) : ℚ) : ℝ) ≤ (BM : ℝ) := by
        exact_mod_cast hBM
      exact this.trans hrem)
    r (by simp [hr])
  have := key x hx
  refine this.trans ?_
  exact_mod_cast hT

/-- The checker with a separately bounded piece `g ≤ G` on the cell (the `+ max(g0, gb)` of
`taylor_box_ub`; for example `-log|x|/(2ν)` near `0`, bounded by its endpoint value). -/
theorem poleCellCheck_sound_add (poles : List PoleR) (F g : ℝ → ℝ) (lo hi A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T G : ℚ)
    (hchk : poleCellCheck poles lo hi A0 l1 u1 A2 Bl BM T = true)
    (hF : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), HasDerivAt F ((poles.map (fun q => qt q 0 x)).sum) x)
    (h0 : F (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (hg : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), g x ≤ (G : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), F x + g x ≤ (T : ℝ) + (G : ℝ) := by
  intro x hx
  have := poleCellCheck_sound poles F lo hi A0 l1 u1 A2 Bl BM T hchk hF h0 x hx
  linarith [hg x hx]

/-! ### 5. Derivative lemmas for the fields (hypothesis `hF` of the checker) -/

/-- `w · log |y - p|` has derivative `Re[w/(x - p)]` (the real pole `p`, real weight `w`). -/
theorem hasDerivAt_log_abs_sub (w p : ℚ) (x : ℝ) (hx : x ≠ (p : ℝ)) :
    HasDerivAt (fun y => (w : ℝ) * Real.log |y - p|) (qt ⟨w, 0, p, 0⟩ 0 x) x := by
  rw [qt_real]
  have h1 : HasDerivAt (fun y : ℝ => y - (p : ℝ)) 1 x := (hasDerivAt_id x).sub_const _
  have h2 := (h1.log (sub_ne_zero.mpr hx)).const_mul (w : ℝ)
  simp only [Real.log_abs] at *
  refine h2.congr_deriv ?_
  ring

/-- `w · log |1 - a y|` has derivative `Re[w/(x - 1/a)]` (the pole `1/a`), `a ≠ 0`. -/
theorem hasDerivAt_log_abs_one_sub (w a : ℚ) (ha : a ≠ 0) (x : ℝ) (hx : (1 : ℝ) - a * x ≠ 0) :
    HasDerivAt (fun y => (w : ℝ) * Real.log |1 - a * y|) (qt ⟨w, 0, 1 / a, 0⟩ 0 x) x := by
  rw [qt_real]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have h1 : HasDerivAt (fun y : ℝ => 1 - (a : ℝ) * y) (-(a : ℝ)) x := by
    simpa using ((hasDerivAt_id x).const_mul (a : ℝ)).const_sub 1
  have h2 := (h1.log hx).const_mul (w : ℝ)
  simp only [Real.log_abs] at *
  refine h2.congr_deriv ?_
  have : x - ((1 / a : ℚ) : ℝ) = -(1 - (a : ℝ) * x) / a := by
    push_cast; field_simp; ring
  rw [this]
  field_simp

/-- `Re[ρ log (y - p)]` for a non-real pole `p` has derivative `Re[ρ/(x - p)]`. -/
theorem hasDerivAt_re_clog (q : PoleR) (hq : q.pi ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (q.rho * Complex.log ((y : ℂ) - q.pc)).re) (qt q 0 x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) - q.pc) 1 x :=
    ((hasDerivAt_id x).ofReal_comp).sub_const _
  have hs : ((x : ℂ) - q.pc) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    simp [PoleR.pc, hq]
  have h2 := (h1.clog_real hs).const_mul q.rho
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h2
  refine h3.congr_deriv ?_
  simp [qt, qe]

/-! ### 6. Regression: `log x ≤ 23/100` on `[3/4, 5/4]` through the whole chain -/

example : ∀ x ∈ Icc ((3 / 4 : ℚ) : ℝ) ((5 / 4 : ℚ) : ℝ), Real.log x ≤ ((23 / 100 : ℚ) : ℝ) := by
  refine poleCellCheck_sound [⟨1, 0, 0, 0⟩] Real.log (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (23 / 100) (by decide +kernel) ?_ ?_
  · intro x hx
    have hx0 : x ≠ 0 := by
      have : (0 : ℝ) < ((3 / 4 : ℚ) : ℝ) := by norm_num
      exact (lt_of_lt_of_le this hx.1).ne'
    simpa [qt_real] using Real.hasDerivAt_log hx0
  · norm_num

/-- Negative controls: the model value is `0.2251987...` (true sup `log (5/4) = 0.2231...`); the
checker accepts `0.2252`, rejects `0.2251` (model value above), `0.22` (below the true sup), and a
coefficient bound that is too small. -/
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (2252 / 10000) = true := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (2251 / 10000) = false := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 5, 1 / 6, 1 / 7] (5 / 4) (22 / 100) = false := by decide +kernel
example : poleCellCheck [⟨1, 0, 0, 0⟩] (3 / 4) (5 / 4) 0 1 1 (-1 / 2)
    [1 / 3, 1 / 4, 1 / 6, 1 / 6, 1 / 7] (5 / 4) (23 / 100) = false := by decide +kernel

end CatalanMeasure.GenD.Signed.TaylorCell

#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quad_le_quadSupR
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quadSupR_attained
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub_full
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.tmUBQ_cast
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleCellCheck_sound
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_log_abs_sub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_log_abs_one_sub
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.hasDerivAt_re_clog
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.quad_le_max
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_iteratedDeriv
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.taylor_cell_ub_rat
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleTower_rem
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleDist_le_norm
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.poleCellCheck_sound_add
#print axioms CatalanMeasure.GenD.Signed.TaylorCell.isTower_poleTower

module

public import CatalanMeasure.GenD.Signed.Data.Cells.Core

@[expose] public section

/-! # Chebyshev piece certificate

A wide cell `[lo, hi]` (centre `c`, radius `r`) of a field `f` with Taylor tower of order `n + 1`
is bounded by the Taylor model

  `f x ≤ A0 + Σ_{i<n} t_i y^{i+1} + Σ_{i<n} e_i r^{i+1} + BM r^{n+1}`,   `y = x - c`, `|y| ≤ r`,

where `|f^{(k)}(c)/k! - t| ≤ e`.  The ordinary cell (`cellV`) bounds the polynomial
`A0 + Σ t_i y^{i+1}` term by term (`Σ |t_i| r^{i+1}`).  Here the polynomial `p(u)`, `y = r u`,
`u ∈ [-1, 1]`, is bounded through its Chebyshev expansion: for rational data `γ_0, …, γ_m`,

  `p = Σ γ_j T_j + δ`   (`δ` computed exactly by the checker),   so
  `p(u) ≤ γ_0 + Σ_{j≥1} |γ_j| + Σ |δ_k|`        (`|T_j| ≤ 1`, `|u| ≤ 1`).

`chebMono γ` is the monomial list of `Σ γ_j T_j` (three-term recurrence on integer lists);
the data `γ` is untrusted, only the final inequality is checked.

* `chebPoly_le`: the polynomial bound (generic, any list `a`).
* `chebCore`: abstract piece theorem (same conclusion as `cellCore`).
* `chebCellV_sound`: field-level piece, the **same conclusion and `BlockFacts` hypothesis as
  `cellV_sound`** (`∀ x ∈ Icc lo hi, fieldTower fq (poleF fq.poles) 0 x ≤ T`, `BlockFacts` of order
  `n + 1`), so a piece replaces a block of cells with the same consumers.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

/-! ### 1. The Chebyshev sequence -/

/-- `T_n(u)` by the three-term recurrence. -/
noncomputable def chT (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => u
  | n + 2 => 2 * u * chT u (n + 1) - chT u n

theorem chT_cos (θ : ℝ) : ∀ n : ℕ, chT (Real.cos θ) n = Real.cos ((n : ℝ) * θ) ∧
    chT (Real.cos θ) (n + 1) = Real.cos (((n : ℝ) + 1) * θ) := by
  intro n
  induction n with
  | zero => simp [chT]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by push_cast; exact h1, ?_⟩
    have e : chT (Real.cos θ) (n + 1 + 1) =
        2 * Real.cos θ * chT (Real.cos θ) (n + 1) - chT (Real.cos θ) n := rfl
    rw [e, h0, h1]
    have a1 : ((n : ℝ) + 1) * θ + θ = (((n + 1 : ℕ) : ℝ) + 1) * θ := by push_cast; ring
    have a2 : ((n : ℝ) + 1) * θ - θ = (n : ℝ) * θ := by ring
    rw [← a1]
    have c1 := Real.cos_add (((n : ℝ) + 1) * θ) θ
    have c2 := Real.cos_sub (((n : ℝ) + 1) * θ) θ
    rw [a2] at c2
    rw [c1, c2]
    ring

theorem abs_chT_le (u : ℝ) (hu : |u| ≤ 1) (n : ℕ) : |chT u n| ≤ 1 := by
  have h := abs_le.mp hu
  have hc : Real.cos (Real.arccos u) = u := Real.cos_arccos h.1 h.2
  have := (chT_cos (Real.arccos u) n).1
  rw [hc] at this
  rw [this]
  exact Real.abs_cos_le_one _

/-! ### 2. List polynomials -/

/-- `Σ |a_k|` -/
def absSum : List ℚ → ℚ
  | [] => 0
  | a :: as => qabs' a + absSum as

def vsubQ (a b : List ℚ) : List ℚ := vecAdd a (b.map (fun x => (-1) * x))

/-- `2 u · l` -/
def x2 (l : List ℚ) : List ℚ := 0 :: l.map (fun x => 2 * x)

/-- Running `T_j, T_{j+1}` and the accumulated `Σ γ_i T_{j+i}`. -/
def chebAcc : List ℚ → List ℚ → List ℚ → List ℚ → List ℚ
  | [], _, _, acc => acc
  | g :: gs, tj, tj1, acc =>
    chebAcc gs tj1 (vsubQ (x2 tj1) tj) (vecAdd acc (tj.map (fun x => g * x)))

/-- Monomial coefficients of `Σ γ_j T_j`. -/
def chebMono (γ : List ℚ) : List ℚ := chebAcc γ [1] [0, 1] []

/-- `γ_0 + Σ_{j≥1} |γ_j|` -/
def chebUB : List ℚ → ℚ
  | [] => 0
  | g :: gs => g + absSum gs

/-- The polynomial bound: Chebyshev part plus the exact remainder `a - Σ γ_j T_j`. -/
def chebPolyUB (a γ : List ℚ) : ℚ := chebUB γ + absSum (vsubQ a (chebMono γ))

theorem polyTow_smul (g : ℚ) : ∀ (l : List ℚ) (x : ℝ),
    polyTow (l.map (fun a => g * a)) 0 x = (g : ℝ) * polyTow l 0 x := by
  intro l x
  induction l with
  | nil => simp [polyTow]
  | cons a as ih =>
    simp only [List.map_cons, polyTow, ih]
    push_cast
    ring

theorem polyTow_vsubQ (a b : List ℚ) (x : ℝ) :
    polyTow (vsubQ a b) 0 x = polyTow a 0 x - polyTow b 0 x := by
  unfold vsubQ
  rw [polyTow_vecAdd, polyTow_smul]
  push_cast
  ring

theorem polyTow_x2 (l : List ℚ) (x : ℝ) : polyTow (x2 l) 0 x = 2 * x * polyTow l 0 x := by
  unfold x2
  simp only [polyTow, polyTow_smul]
  push_cast
  ring

/-- `Σ γ_i T_{j+i}(u)` -/
noncomputable def chSum (u : ℝ) : List ℚ → ℕ → ℝ
  | [], _ => 0
  | g :: gs, j => (g : ℝ) * chT u j + chSum u gs (j + 1)

theorem chebAcc_spec (u : ℝ) : ∀ (γ tj tj1 acc : List ℚ) (j : ℕ),
    polyTow tj 0 u = chT u j → polyTow tj1 0 u = chT u (j + 1) →
    polyTow (chebAcc γ tj tj1 acc) 0 u = polyTow acc 0 u + chSum u γ j := by
  intro γ
  induction γ with
  | nil => intro tj tj1 acc j _ _; simp [chebAcc, chSum]
  | cons g gs ih =>
    intro tj tj1 acc j h0 h1
    unfold chebAcc
    have h2 : polyTow (vsubQ (x2 tj1) tj) 0 u = chT u (j + 2) := by
      rw [polyTow_vsubQ, polyTow_x2, h0, h1]
      rfl
    rw [ih tj1 _ _ (j + 1) h1 h2, polyTow_vecAdd, polyTow_smul, h0, chSum]
    ring

theorem chSum_le (u : ℝ) (hu : |u| ≤ 1) : ∀ (γ : List ℚ) (j : ℕ),
    chSum u γ j ≤ ((absSum γ : ℚ) : ℝ) := by
  intro γ
  induction γ with
  | nil => intro j; simp [chSum, absSum]
  | cons g gs ih =>
    intro j
    simp only [chSum, absSum]
    push_cast
    rw [qabs'_cast]
    have h1 : (g : ℝ) * chT u j ≤ |(g : ℝ)| := by
      calc (g : ℝ) * chT u j ≤ |(g : ℝ) * chT u j| := le_abs_self _
        _ = |(g : ℝ)| * |chT u j| := abs_mul _ _
        _ ≤ |(g : ℝ)| * 1 := mul_le_mul_of_nonneg_left (abs_chT_le u hu j) (abs_nonneg _)
        _ = |(g : ℝ)| := mul_one _
    linarith [ih (j + 1)]

theorem polyTow_abs_le (u : ℝ) (hu : |u| ≤ 1) : ∀ (l : List ℚ),
    |polyTow l 0 u| ≤ ((absSum l : ℚ) : ℝ) := by
  intro l
  induction l with
  | nil => simp [polyTow, absSum]
  | cons a as ih =>
    simp only [polyTow, absSum]
    push_cast
    rw [qabs'_cast]
    calc |(a : ℝ) + u * polyTow as 0 u| ≤ |(a : ℝ)| + |u * polyTow as 0 u| := abs_add_le _ _
      _ = |(a : ℝ)| + |u| * |polyTow as 0 u| := by rw [abs_mul]
      _ ≤ |(a : ℝ)| + 1 * ((absSum as : ℚ) : ℝ) := by
          gcongr
      _ = _ := by ring

/-- **The Chebyshev polynomial bound.**  If `chebPolyUB a γ ≤ B` then `a(u) ≤ B` on `[-1, 1]`;
`γ` is untrusted data (any `γ` is sound, a good one makes the bound tight). -/
theorem chebPoly_le (a γ : List ℚ) (u : ℝ) (hu : |u| ≤ 1) :
    polyTow a 0 u ≤ ((chebPolyUB a γ : ℚ) : ℝ) := by
  have hm := chebAcc_spec u γ [1] [0, 1] [] 0 (by simp [polyTow, chT]) (by simp [polyTow, chT])
  have hmono : polyTow (chebMono γ) 0 u = chSum u γ 0 := by
    unfold chebMono; rw [hm]; simp [polyTow]
  have hsplit : polyTow a 0 u = chSum u γ 0 + polyTow (vsubQ a (chebMono γ)) 0 u := by
    rw [polyTow_vsubQ, hmono]; ring
  have hc : chSum u γ 0 ≤ ((chebUB γ : ℚ) : ℝ) := by
    cases γ with
    | nil => simp [chSum, chebUB]
    | cons g gs =>
      simp only [chSum, chebUB, chT]
      push_cast
      have := chSum_le u hu gs 1
      linarith
  have hd := (abs_le.mp (polyTow_abs_le u hu (vsubQ a (chebMono γ)))).2
  unfold chebPolyUB
  push_cast
  linarith

/-! ### 3. The Taylor-model piece -/

/-- `[l_{k0}, l_{k0+1}, …]` (`m` entries starting at index `k0`) -/
def colList (l : List ℚ) (k0 : ℕ) : ℕ → List ℚ
  | 0 => []
  | m + 1 => l.getD k0 0 :: colList l (k0 + 1) m

theorem colList_length (l : List ℚ) (k0 m : ℕ) : (colList l k0 m).length = m := by
  induction m generalizing k0 with
  | zero => rfl
  | succ m ih => simp [colList, ih]

theorem colList_getD (l : List ℚ) : ∀ (m k0 i : ℕ), i < m → (colList l k0 m).getD i 0 = l.getD (k0 + i) 0 := by
  intro m
  induction m with
  | zero => intro k0 i h; omega
  | succ m ih =>
    intro k0 i h
    cases i with
    | zero => simp [colList]
    | succ i =>
      simp only [colList, List.getD_cons_succ]
      rw [ih (k0 + 1) i (by omega)]
      congr 1; omega

/-- `[a_k r^(k0+k)]` -/
def sclPow (r : ℚ) : ℕ → List ℚ → List ℚ
  | _, [] => []
  | k, a :: as => a * r ^ k :: sclPow r (k + 1) as

theorem polyTow_sclPow (r : ℚ) (u : ℝ) : ∀ (l : List ℚ) (k : ℕ),
    polyTow (sclPow r k l) 0 u = (r : ℝ) ^ k * polyTow l 0 ((r : ℝ) * u) := by
  intro l
  induction l with
  | nil => intro k; simp [sclPow, polyTow]
  | cons a as ih =>
    intro k
    simp only [sclPow, polyTow, ih]
    push_cast
    ring

theorem polyTow_sum : ∀ (l : List ℚ) (x : ℝ),
    polyTow l 0 x = ∑ i ∈ Finset.range l.length, ((l.getD i 0 : ℚ) : ℝ) * x ^ i := by
  intro l x
  induction l with
  | nil => simp [polyTow]
  | cons a as ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [polyTow, ih, List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The bound of a piece: Chebyshev bound of `A0 + Σ t_i r^(i+1) u^(i+1)`, the coefficient errors
`Σ e_i r^(i+1)` and the Lagrange remainder `BM r^(n+1)`. -/
def chebPieceUB (A0 r : ℚ) (ts ee γ : List ℚ) (BM : ℚ) (n : ℕ) : ℚ :=
  chebPolyUB (A0 :: sclPow r 1 ts) γ + powSumQ r 1 ee + BM * r ^ (n + 1)

/-- **Abstract Chebyshev piece** (the analogue of `cellCore`): a tower on `[lo, hi]` with enclosed
point coefficients `cs ± es` (indices `1..n`), a block remainder bound `BM` of order `n + 1`, and
the Chebyshev check `chebPieceUB ≤ T`. -/
theorem chebCore {f : ℕ → ℝ → ℝ} (lo hi A0 : ℚ) (n : ℕ) (BM T : ℚ) (cs es γ : List ℚ)
    (hT0 : IsTower f (((lo + hi) / 2 : ℚ) : ℝ) (((hi - lo) / 2 : ℚ) : ℝ) (n + 1))
    (hspec : ∀ k, 1 ≤ k → k ≤ n →
      |f k (((lo + hi) / 2 : ℚ) : ℝ) / (k.factorial : ℝ) - ((cs.getD k 0 : ℚ) : ℝ)| ≤
        ((es.getD k 0 : ℚ) : ℝ))
    (hlo : lo < hi)
    (hT : chebPieceUB A0 ((hi - lo) / 2) (colList cs 1 n) (colList es 1 n) γ BM n ≤ T)
    (h0 : f 0 (((lo + hi) / 2 : ℚ) : ℝ) ≤ (A0 : ℝ))
    (blo bhi : ℚ) (hb1 : blo ≤ lo) (hb2 : hi ≤ bhi)
    (hBM : ∀ x ∈ Icc (blo : ℝ) (bhi : ℝ),
      |f (n + 1) x| / ((n + 1).factorial : ℝ) ≤ (BM : ℝ)) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), f 0 x ≤ (T : ℝ) := by
  set c : ℚ := (lo + hi) / 2 with hc
  set r : ℚ := (hi - lo) / 2 with hr
  have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
  have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
  have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
    rw [e1, e2]
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
    simp only [hr]; push_cast; linarith
  intro x hx
  rw [← hcell] at hx
  have hxr : |x - (c : ℝ)| ≤ (r : ℝ) := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcI : (c : ℝ) ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) :=
    ⟨by linarith, by linarith⟩
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hsub : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), y ∈ Icc (blo : ℝ) (bhi : ℝ) := by
    intro y hy
    rw [hcell] at hy
    exact ⟨le_trans (by exact_mod_cast hb1) hy.1, le_trans hy.2 (by exact_mod_cast hb2)⟩
  have hbd : ∀ y ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)),
      |f (n + 1) y| ≤ ((n + 1).factorial : ℝ) * (BM : ℝ) := by
    intro y hy
    have := hBM y (hsub y hy)
    rw [div_le_iff₀ hfac] at this
    linarith
  have htay := CatalanMeasure.CellCert.taylor_tower' (c : ℝ) (r : ℝ)
    (((n + 1).factorial : ℝ) * (BM : ℝ)) (n + 1) f hT0.cont
    (fun j hj y hy => hT0.der j hj y hy) hbd x hx
  have hBM0 : (0 : ℝ) ≤ (BM : ℝ) := (div_nonneg (abs_nonneg _) hfac.le).trans (hBM c (hsub _ hcI))
  have hrem : |f 0 x - ∑ j ∈ Finset.range (n + 1), f j (c : ℝ) * (x - c) ^ j / ((j.factorial : ℕ) : ℝ)|
      ≤ (BM : ℝ) * (r : ℝ) ^ (n + 1) := by
    refine htay.trans ?_
    have e : ((n + 1).factorial : ℝ) * (BM : ℝ) * |x - c| ^ (n + 1) / ((n + 1).factorial : ℝ) =
        (BM : ℝ) * |x - c| ^ (n + 1) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hxr (n + 1)) hBM0
  -- the coefficient terms
  have hterm : ∀ i ∈ Finset.range n,
      f (i + 1) (c : ℝ) * (x - c) ^ (i + 1) / (((i + 1).factorial : ℕ) : ℝ) ≤
        ((cs.getD (i + 1) 0 : ℚ) : ℝ) * (x - c) ^ (i + 1) +
          ((es.getD (i + 1) 0 : ℚ) : ℝ) * (r : ℝ) ^ (i + 1) := by
    intro i hi'
    have hin := Finset.mem_range.mp hi'
    have hs := abs_le.mp (hspec (i + 1) (by omega) (by omega))
    have hpow : |x - c| ^ (i + 1) ≤ (r : ℝ) ^ (i + 1) := pow_le_pow_left₀ (abs_nonneg _) hxr _
    have hy : (x - c) ^ (i + 1) ≤ |x - c| ^ (i + 1) := by
      rw [← abs_pow]; exact le_abs_self _
    have hy' : -|x - c| ^ (i + 1) ≤ (x - c) ^ (i + 1) := by
      rw [← abs_pow]; exact neg_abs_le _
    have hE : (0 : ℝ) ≤ ((es.getD (i + 1) 0 : ℚ) : ℝ) := by
      have := hs.1; have := hs.2; linarith
    set g : ℝ := f (i + 1) (c : ℝ) / (((i + 1).factorial : ℕ) : ℝ) with hg
    have e : f (i + 1) (c : ℝ) * (x - c) ^ (i + 1) / (((i + 1).factorial : ℕ) : ℝ) =
        g * (x - c) ^ (i + 1) := by rw [hg]; ring
    rw [e]
    have hdiff : (g - ((cs.getD (i + 1) 0 : ℚ) : ℝ)) * (x - c) ^ (i + 1) ≤
        ((es.getD (i + 1) 0 : ℚ) : ℝ) * (r : ℝ) ^ (i + 1) := by
      have habs : |(g - ((cs.getD (i + 1) 0 : ℚ) : ℝ)) * (x - c) ^ (i + 1)| ≤
          ((es.getD (i + 1) 0 : ℚ) : ℝ) * (r : ℝ) ^ (i + 1) := by
        rw [abs_mul, abs_pow]
        exact mul_le_mul (abs_le.mpr hs) hpow (pow_nonneg (abs_nonneg _) _) hE
      exact (le_abs_self _).trans habs
    nlinarith [hdiff]
  have hsum1 : ∑ i ∈ Finset.range n, f (i + 1) (c : ℝ) * (x - c) ^ (i + 1) / (((i + 1).factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.range n, (((cs.getD (i + 1) 0 : ℚ) : ℝ) * (x - c) ^ (i + 1) +
          ((es.getD (i + 1) 0 : ℚ) : ℝ) * (r : ℝ) ^ (i + 1)) :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum1
  -- polynomial and error sums in list form
  have hpoly : ∑ i ∈ Finset.range n, ((cs.getD (i + 1) 0 : ℚ) : ℝ) * (x - c) ^ (i + 1) =
      (x - c) * polyTow (colList cs 1 n) 0 (x - c) := by
    rw [polyTow_sum, colList_length, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi' => ?_)
    have hin := Finset.mem_range.mp hi'
    rw [colList_getD cs n 1 i hin, show 1 + i = i + 1 by omega]
    ring
  have herr : ∑ i ∈ Finset.range n, ((es.getD (i + 1) 0 : ℚ) : ℝ) * (r : ℝ) ^ (i + 1) =
      ((powSumQ r 1 (colList es 1 n) : ℚ) : ℝ) := by
    rw [powSumQ_cast, colList_length]
    refine Finset.sum_congr rfl (fun i hi' => ?_)
    have hin := Finset.mem_range.mp hi'
    rw [colList_getD es n 1 i hin, show 1 + i = i + 1 by omega]
  rw [hpoly, herr] at hsum1
  -- the Chebyshev bound
  set u : ℝ := (x - c) / (r : ℝ) with hu
  have hu1 : |u| ≤ 1 := by
    rw [hu, abs_div, abs_of_pos hrpos, div_le_one hrpos]; exact hxr
  have hyu : (r : ℝ) * u = x - c := by rw [hu]; field_simp
  have hcheb := chebPoly_le (A0 :: sclPow r 1 (colList cs 1 n)) γ u hu1
  have hcons : polyTow (A0 :: sclPow r 1 (colList cs 1 n)) 0 u =
      (A0 : ℝ) + (x - c) * polyTow (colList cs 1 n) 0 (x - c) := by
    simp only [polyTow]
    rw [polyTow_sclPow, hyu]
    have : u * ((r : ℝ) ^ 1) = x - c := by rw [pow_one, mul_comm]; exact hyu
    rw [← this]; ring
  rw [hcons] at hcheb
  have hsplit := Finset.sum_range_succ' (fun j => f j (c : ℝ) * (x - c) ^ j / ((j.factorial : ℕ) : ℝ)) n
  have h00 : f 0 (c : ℝ) * (x - c) ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ) = f 0 (c : ℝ) := by simp
  simp only [h00] at hsplit
  have hrem' := (abs_le.mp hrem).2
  have hTR : ((chebPieceUB A0 r (colList cs 1 n) (colList es 1 n) γ BM n : ℚ) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hT
  unfold chebPieceUB at hTR
  push_cast at hTR
  linarith

/-! ### 4. The field-level piece -/

/-- One Chebyshev piece of a field; the data and checks mirror `cellV`, with the polynomial
Taylor-model bound replaced by `chebPieceUB`. -/
def chebCellV (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (blo bhi lo hi : ℚ) (A0 : ℚ)
    (n : ℕ) (γ : List ℚ) (BM T : ℚ) : Bool :=
  match logsOf nLc ((lo + hi) / 2) fq.plogs, anchorUB2 nLc Pc nLp nAp Pp fq ((lo + hi) / 2) with
  | some (Ls, εs), some v =>
    decide (v ≤ A0) && decide (blo ≤ lo) && decide (hi ≤ bhi) && decide (lo < hi) &&
    (let cs := fieldCoefs fq Ls ((lo + hi) / 2) n
     let es := plogErrSum ((lo + hi) / 2) n fq.plogs εs
     decide (chebPieceUB A0 ((hi - lo) / 2) (colList cs 1 n) (colList es 1 n) γ BM n ≤ T))
  | _, _ => false

/-- **`chebCell` soundness**: same conclusion and same block hypothesis (`BlockFacts` of order
`n + 1`, the shape `Bl.length + 3` of `cellV_sound` with `n = Bl.length + 2`) as `cellV_sound`. -/
theorem chebCellV_sound (fq : FieldQ) (nLc Pc nLp nAp Pp : ℕ) (blo bhi lo hi : ℚ) (A0 : ℚ)
    (n : ℕ) (γ : List ℚ) (BM T : ℚ)
    (hchk : chebCellV fq nLc Pc nLp nAp Pp blo bhi lo hi A0 n γ BM T = true)
    (hB : BlockFacts fq blo bhi (n + 1) BM) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold chebCellV at hchk
  split at hchk
  · rename_i Ls εs v hls hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨hvA, hb1⟩, hb2⟩, hlo⟩, hT⟩ := hchk
    set c : ℚ := (lo + hi) / 2 with hc
    set r : ℚ := (hi - lo) / 2 with hr
    have hLs := logsOf_spec nLc c fq.plogs Ls εs hls
    have e1 : (c : ℝ) - (r : ℝ) = (lo : ℝ) := by simp only [hc, hr]; push_cast; ring
    have e2 : (c : ℝ) + (r : ℝ) = (hi : ℝ) := by simp only [hc, hr]; push_cast; ring
    have hcell : Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)) = Icc (lo : ℝ) (hi : ℝ) := by
      rw [e1, e2]
    have hsub : ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
      intro x hx
      exact ⟨le_trans (by exact_mod_cast hb1) hx.1, le_trans hx.2 (by exact_mod_cast hb2)⟩
    have hsub' : ∀ x ∈ Icc ((c : ℝ) - (r : ℝ)) ((c : ℝ) + (r : ℝ)), x ∈ Icc (blo : ℝ) (bhi : ℝ) := by
      intro x hx; rw [hcell] at hx; exact hsub x hx
    have hrpos : (0 : ℝ) ≤ (r : ℝ) := by
      have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
      simp only [hr]; push_cast; linarith
    have hnec : ∀ t ∈ fq.plogs, c - t.2 ≠ 0 := by
      intro t ht hz
      have hcm : (c : ℝ) ∈ Icc (blo : ℝ) (bhi : ℝ) := hsub' _ ⟨by linarith, by linarith⟩
      apply hB.plog t ht c hcm
      have : c = t.2 := by linarith
      rw [this]
    have hT0 := isTower_fieldTower fq (poleF fq.poles) (c : ℝ) (r : ℝ) (n + 1)
      (fun t ht y hy => hB.plog t ht y (hsub' y hy))
      (fun y hy q hq => hB.pole q hq y (hsub' y hy))
      (fun y hy => hB.deriv y (hsub' y hy))
    have h0 : fieldTower fq (poleF fq.poles) 0 (c : ℝ) ≤ (A0 : ℝ) :=
      (anchorUB2_spec nLc Pc nLp nAp Pp fq c v hv).trans (by exact_mod_cast hvA)
    exact chebCore (f := fun j x => fieldTower fq (poleF fq.poles) j x) lo hi A0 n BM T
      (fieldCoefs fq Ls c n) (plogErrSum c n fq.plogs εs) γ hT0
      (fun k hk1 hk => fieldCoefs_approx fq (poleF fq.poles) Ls εs c n hLs hnec k hk1 hk)
      hlo hT h0 blo bhi hb1 hb2 hB.tail
  · simp at hchk

/-! ### 5. Regression (a toy polynomial, no field data)

`u²` has Chebyshev data `[1/2, 0, 1/2]` (`T₂ = 2u² - 1`), so `chebPolyUB [0,0,1] γ = 1` with zero
remainder.  A deliberately rounded `γ` still gives a sound (larger) bound.

kcost: `chebMono γ` for `m + 1` Chebyshev terms is `m + 1` rounds of three list passes of length
`≤ m + 2`, about `5 (m + 1)²` rational operations: 45 for the toy (`m = 2`); a real piece of
Taylor order `n ≈ 40` costs about `10⁴` operations, one `decide +kernel` per piece. -/

theorem cheb_toy_exact : chebPolyUB [0, 0, 1] [1 / 2, 0, 1 / 2] = 1 := by decide +kernel

theorem cheb_toy_rounded : chebPolyUB [0, 0, 1] [1 / 2, 0, 3 / 7] ≤ 1 + 1 / 7 := by decide +kernel

theorem cheb_toy_sound (u : ℝ) (hu : |u| ≤ 1) : u ^ 2 ≤ 1 := by
  have := chebPoly_le [0, 0, 1] [1 / 2, 0, 1 / 2] u hu
  rw [show chebPolyUB [0, 0, 1] [1 / 2, 0, 1 / 2] = 1 from cheb_toy_exact] at this
  have h2 : polyTow [0, 0, 1] 0 u = u ^ 2 := by simp [polyTow]; ring
  rw [h2] at this
  exact_mod_cast this

#print axioms chebPoly_le
#print axioms chebCore
#print axioms chebCellV_sound
#print axioms cheb_toy_exact
#print axioms cheb_toy_rounded
#print axioms cheb_toy_sound

end CatalanMeasure.GenD.Signed.Data.Cells

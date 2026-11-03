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
* `chebFieldPiece_sound` (section 6): Taylor-free piece, monotone log/arg enclosures per term.
* `chebMergePiece_sound` (section 8): Taylor-merged piece.  Poles and plog sites far from the piece
  (`r ≤ qb |c - p|`, `qb ≤ 1/2`) are replaced by the degree-`M` Taylor polynomial of
  `Re[ρ log (x - p)]` at the centre (rational Gaussian coefficients, rounded to `2^-P`) and merged into
  the polynomial before the Chebyshev bound, with the series tail
  `qb^(M+1)/((M+1)(1-qb))` and the rounding in the error; near terms use the monotone enclosures.
-/

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval OAI.InternalCatalan

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

/-! ### 6. The Taylor-free field piece

For a field `f = poly + Σ_t P_t log|x - e_t| + Σ_q Re[ρ_q log(x - p_q)]` on `[lo, hi]` there is no
remainder term: every part is bounded exactly.

* `poly` and each `P_t`: `polyUBc` / `polyLBc` (Chebyshev bound of the exact Taylor shift at the
  centre, rescaled to `u ∈ [-1, 1]`, upper bound of the polynomial and of its negative).
* `log|x - e|` and `log|x - p|`: `(x - a)² + b²` lies between its endpoint values on a piece that does
  not straddle `a`, so `log` lies between the two endpoint logarithms (`logBand`, `logQ` enclosures).
* `arg(x - p)`: monotone in `x` (`arg_between`), enclosed by its endpoint values (`argQ`).
* products `P · log` and `w · arg`: sign-aware interval products (`iv4`, `mul_le_max2`).

The conclusion is that of `cellV_sound`.  The checker needs `lo < hi`, each `e_t` outside `[lo, hi]`, each
real pole outside `[lo, hi]` and each complex pole with `Re p ∉ (lo, hi)` (split the piece at `Re p`),
and `ri = 0 ∨ pi ≠ 0`. -/

theorem polyTow_shiftL (p : List ℚ) (c : ℚ) (y : ℝ) :
    polyTow (shiftL c p.length p) 0 y = polyTow p 0 (y + c) := by
  rw [polyTow_sum, shiftL_length, polyTow_taylor p c (y + c)]
  simp only [add_sub_cancel_right]

/-- Chebyshev upper bound of a polynomial on `[c - r, c + r]`. -/
def polyUBc (p : List ℚ) (c r : ℚ) (γ : List ℚ) : ℚ :=
  chebPolyUB (sclPow r 0 (shiftLK c p.length p)) γ

theorem polyUBc_le (p : List ℚ) (c r : ℚ) (γ : List ℚ) (hr : 0 < (r : ℝ)) (x : ℝ)
    (hx : |x - (c : ℝ)| ≤ (r : ℝ)) : polyTow p 0 x ≤ ((polyUBc p c r γ : ℚ) : ℝ) := by
  have hu : |(x - (c : ℝ)) / (r : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hx
  have h := chebPoly_le (sclPow r 0 (shiftLK c p.length p)) γ ((x - (c : ℝ)) / (r : ℝ)) hu
  rw [polyTow_sclPow, shiftLK_eq'] at h
  have e : (r : ℝ) * ((x - (c : ℝ)) / (r : ℝ)) = x - (c : ℝ) := by field_simp
  rw [e, polyTow_shiftL, sub_add_cancel] at h
  unfold polyUBc
  rw [shiftLK_eq']
  simpa using h

/-- Chebyshev lower bound: minus the upper bound of the negated polynomial. -/
def polyLBc (p : List ℚ) (c r : ℚ) (γ : List ℚ) : ℚ :=
  -polyUBc (p.map (fun a => (-1 : ℚ) * a)) c r γ

theorem polyLBc_le (p : List ℚ) (c r : ℚ) (γ : List ℚ) (hr : 0 < (r : ℝ)) (x : ℝ)
    (hx : |x - (c : ℝ)| ≤ (r : ℝ)) : ((polyLBc p c r γ : ℚ) : ℝ) ≤ polyTow p 0 x := by
  have h := polyUBc_le (p.map (fun a => (-1 : ℚ) * a)) c r γ hr x hx
  rw [polyTow_smul] at h
  unfold polyLBc
  push_cast at h ⊢
  linarith

theorem mul_le_max2 {w L ll lu : ℝ} (h1 : ll ≤ L) (h2 : L ≤ lu) :
    w * L ≤ max (w * ll) (w * lu) := by
  rcases le_total 0 w with h | h
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_left h2 h)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_left h1 h)

def iv4 (pl pu ll lu : ℚ) : ℚ := max (max (pl * ll) (pl * lu)) (max (pu * ll) (pu * lu))

theorem mul_le_iv4 {P L pl pu ll lu : ℝ} (hP1 : pl ≤ P) (hP2 : P ≤ pu) (hL1 : ll ≤ L)
    (hL2 : L ≤ lu) : P * L ≤ max (max (pl * ll) (pl * lu)) (max (pu * ll) (pu * lu)) := by
  have h1 : P * L ≤ max (P * ll) (P * lu) := mul_le_max2 hL1 hL2
  have a1 : P * ll ≤ max (pl * ll) (pu * ll) := by
    rcases le_total 0 ll with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hP2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hP1 h)
  have a2 : P * lu ≤ max (pl * lu) (pu * lu) := by
    rcases le_total 0 lu with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hP2 h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hP1 h)
  refine h1.trans (max_le ?_ ?_)
  · exact a1.trans (max_le (le_max_of_le_left (le_max_left _ _))
      (le_max_of_le_right (le_max_left _ _)))
  · exact a2.trans (max_le (le_max_of_le_left (le_max_right _ _))
      (le_max_of_le_right (le_max_right _ _)))

theorem mul_le_iv4_cast {P L : ℝ} {pl pu ll lu : ℚ} (hP1 : (pl : ℝ) ≤ P) (hP2 : P ≤ (pu : ℝ))
    (hL1 : (ll : ℝ) ≤ L) (hL2 : L ≤ (lu : ℝ)) : P * L ≤ ((iv4 pl pu ll lu : ℚ) : ℝ) := by
  have := mul_le_iv4 hP1 hP2 hL1 hL2
  unfold iv4
  push_cast
  exact this

/-! #### logarithm band -/

/-- Enclosure `[LL, LU]` of `log ((x - a)² + b²)` on `[lo, hi]`, when the piece does not straddle `a`. -/
def logBand (nL : ℕ) (a b lo hi : ℚ) : Option (ℚ × ℚ) :=
  if hi ≤ a ∨ a ≤ lo then
    match logQ nL (min ((lo - a) ^ 2 + b ^ 2) ((hi - a) ^ 2 + b ^ 2)),
        logQ nL (max ((lo - a) ^ 2 + b ^ 2) ((hi - a) ^ 2 + b ^ 2)) with
    | some (l1, e1), some (l2, e2) => some (l1 - e1, l2 + e2)
    | _, _ => none
  else none

theorem logBand_spec {nL : ℕ} {a b lo hi LL LU : ℚ} (h : logBand nL a b lo hi = some (LL, LU))
    (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (LL : ℝ) ≤ Real.log ((x - (a : ℝ)) ^ 2 + (b : ℝ) ^ 2) ∧
      Real.log ((x - (a : ℝ)) ^ 2 + (b : ℝ) ^ 2) ≤ (LU : ℝ) := by
  unfold logBand at h
  split_ifs at h with hs
  · split at h
    · rename_i l1 e1 l2 e2 h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hp1, hE1⟩ := logQ_spec h1
      obtain ⟨hp2, hE2⟩ := logQ_spec h2
      have hp1' := (Rat.cast_pos (K := ℝ)).mpr hp1
      have hs' : (hi : ℝ) ≤ (a : ℝ) ∨ (a : ℝ) ≤ (lo : ℝ) := by
        rcases hs with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      have hlo := hx.1
      have hhi := hx.2
      have hD : (min (((lo : ℝ) - a) ^ 2 + (b : ℝ) ^ 2) (((hi : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)) ≤
            (x - a) ^ 2 + (b : ℝ) ^ 2 ∧
          (x - a) ^ 2 + (b : ℝ) ^ 2 ≤
            max (((lo : ℝ) - a) ^ 2 + (b : ℝ) ^ 2) (((hi : ℝ) - a) ^ 2 + (b : ℝ) ^ 2) := by
        rcases hs' with h | h
        · have k1 : ((hi : ℝ) - a) ^ 2 ≤ (x - a) ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0 : ℝ) ≤ 2 * a - x - hi)]
          have k2 : (x - a) ^ 2 ≤ ((lo : ℝ) - a) ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.2 hlo) (by linarith : (0 : ℝ) ≤ 2 * a - lo - x)]
          have k3 := le_max_left (((lo : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)
            (((hi : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)
          exact ⟨(min_le_right _ _).trans (by linarith), by linarith⟩
        · have k1 : ((lo : ℝ) - a) ^ 2 ≤ (x - a) ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.2 hlo) (by linarith : (0 : ℝ) ≤ x + lo - 2 * a)]
          have k2 : (x - a) ^ 2 ≤ ((hi : ℝ) - a) ^ 2 := by
            nlinarith [mul_nonneg (sub_nonneg.2 hhi) (by linarith : (0 : ℝ) ≤ hi + x - 2 * a)]
          have k3 := le_max_right (((lo : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)
            (((hi : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)
          exact ⟨(min_le_left _ _).trans (by linarith), by linarith⟩
      have hpos : (0 : ℝ) < (min (((lo : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)
          (((hi : ℝ) - a) ^ 2 + (b : ℝ) ^ 2)) := by
        have := hp1'
        push_cast at this
        exact this
      have hl1 := Real.log_le_log hpos hD.1
      have hl2 := Real.log_le_log (hpos.trans_le hD.1) hD.2
      have e1' := Enc.ge_lower hE1
      have e2' := Enc.le_upper hE2
      push_cast at e1' e2' ⊢
      constructor <;> linarith
    · simp at h

theorem logBand_spec0 {nL : ℕ} {a lo hi LL LU : ℚ} (h : logBand nL a 0 lo hi = some (LL, LU))
    (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (LL : ℝ) ≤ Real.log ((x - (a : ℝ)) ^ 2) ∧ Real.log ((x - (a : ℝ)) ^ 2) ≤ (LU : ℝ) := by
  obtain ⟨h1, h2⟩ := logBand_spec h x hx
  simp only [Rat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

/-! #### argument -/

theorem sdiv_mono {b a1 a2 : ℝ} (hb : b ≠ 0) (h : a1 ≤ a2) :
    a1 / Real.sqrt (a1 * a1 + b * b) ≤ a2 / Real.sqrt (a2 * a2 + b * b) := by
  have hb2 : 0 < b * b := mul_self_pos.mpr hb
  have p1 : 0 < a1 * a1 + b * b := by nlinarith [mul_self_nonneg a1]
  have p2 : 0 < a2 * a2 + b * b := by nlinarith [mul_self_nonneg a2]
  have r1 := Real.sqrt_pos.mpr p1
  have r2 := Real.sqrt_pos.mpr p2
  have s1 : Real.sqrt (a1 * a1 + b * b) ^ 2 = a1 * a1 + b * b := Real.sq_sqrt p1.le
  have s2 : Real.sqrt (a2 * a2 + b * b) ^ 2 = a2 * a2 + b * b := Real.sq_sqrt p2.le
  set R1 := Real.sqrt (a1 * a1 + b * b)
  set R2 := Real.sqrt (a2 * a2 + b * b)
  rw [div_le_div_iff₀ r1 r2]
  have key : ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y → X ^ 2 ≤ Y ^ 2 → X ≤ Y := by
    intro X Y hX hY hXY
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos (sub_pos.2 hc) (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hY hc) hY)]
  by_cases h1 : 0 ≤ a1
  · have h2 : 0 ≤ a2 := h1.trans h
    apply key _ _ (mul_nonneg h1 r2.le) (mul_nonneg h2 r1.le)
    rw [mul_pow, mul_pow, s1, s2]
    have hsq : a1 * a1 ≤ a2 * a2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq hb2.le]
  · by_cases h2 : a2 ≤ 0
    · have h1' : a1 ≤ 0 := by linarith
      have := key ((-a2) * R1) ((-a1) * R2) (mul_nonneg (by linarith) r1.le)
        (mul_nonneg (by linarith) r2.le) (by
          rw [mul_pow, mul_pow, s1, s2]
          have hsq : a2 * a2 ≤ a1 * a1 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hsq hb2.le])
      nlinarith
    · push_neg at h1 h2
      nlinarith [mul_pos h2 r1, mul_pos (neg_pos.2 h1) r2]

theorem arg_between {b a1 a a2 : ℝ} (hb : b ≠ 0) (h1 : a1 ≤ a) (h2 : a ≤ a2) :
    min (Complex.arg ⟨a1, b⟩) (Complex.arg ⟨a2, b⟩) ≤ Complex.arg ⟨a, b⟩ ∧
      Complex.arg ⟨a, b⟩ ≤ max (Complex.arg ⟨a1, b⟩) (Complex.arg ⟨a2, b⟩) := by
  have hn : ∀ t : ℝ, ‖(⟨t, b⟩ : ℂ)‖ = Real.sqrt (t * t + b * b) := by
    intro t
    rw [Complex.norm_def, Complex.normSq_apply]
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have e : ∀ t : ℝ, Complex.arg ⟨t, b⟩ = -Real.arccos (t / Real.sqrt (t * t + b * b)) := by
      intro t
      rw [Complex.arg_of_im_neg hneg, hn]
    have m1 : Complex.arg ⟨a1, b⟩ ≤ Complex.arg ⟨a, b⟩ := by
      rw [e, e]; exact neg_le_neg (Real.arccos_le_arccos (sdiv_mono hb h1))
    have m2 : Complex.arg ⟨a, b⟩ ≤ Complex.arg ⟨a2, b⟩ := by
      rw [e, e]; exact neg_le_neg (Real.arccos_le_arccos (sdiv_mono hb h2))
    exact ⟨(min_le_left _ _).trans m1, m2.trans (le_max_right _ _)⟩
  · have e : ∀ t : ℝ, Complex.arg ⟨t, b⟩ = Real.arccos (t / Real.sqrt (t * t + b * b)) := by
      intro t
      rw [Complex.arg_of_im_pos hpos, hn]
    have m1 : Complex.arg ⟨a, b⟩ ≤ Complex.arg ⟨a1, b⟩ := by
      rw [e, e]; exact Real.arccos_le_arccos (sdiv_mono hb h1)
    have m2 : Complex.arg ⟨a2, b⟩ ≤ Complex.arg ⟨a, b⟩ := by
      rw [e, e]; exact Real.arccos_le_arccos (sdiv_mono hb h2)
    exact ⟨(min_le_right _ _).trans m2, m1.trans (le_max_left _ _)⟩

/-! #### one pole -/

/-- Upper bound of `Re[ρ log(x - p)]` on `[lo, hi]`:
`(rr/2) log((x - pr)² + pi²) - ri · arg(x - pr - i pi)`. -/
def poleUB (nL nA : ℕ) (q : PoleR) (lo hi : ℚ) : Option ℚ :=
  match logBand nL q.pr q.pi lo hi with
  | none => none
  | some (LL, LU) =>
    if q.ri = 0 then some (max (q.rr / 2 * LL) (q.rr / 2 * LU))
    else if q.pi = 0 then none
    else
      match argQ nA (lo - q.pr) (-q.pi), argQ nA (hi - q.pr) (-q.pi) with
      | some (v1, e1), some (v2, e2) =>
        some (max (q.rr / 2 * LL) (q.rr / 2 * LU) +
          max ((-q.ri) * min (v1 - e1) (v2 - e2)) ((-q.ri) * max (v1 + e1) (v2 + e2)))
      | _, _ => none

theorem pole_term_eq (q : PoleR) (x : ℝ) :
    (q.rho * Complex.log ((x : ℂ) - q.pc)).re =
      (q.rr : ℝ) * (Real.log ((x - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) / 2) -
        (q.ri : ℝ) * Complex.arg ⟨x - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ := by
  have hz : (x : ℂ) - q.pc = ⟨x - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ := by
    apply Complex.ext <;> simp [PoleR.pc]
  rw [hz, barrierComplexLog_weighted_re]
  have e : (x - (q.pr : ℝ)) ^ 2 + (((-q.pi : ℚ) : ℝ)) ^ 2 = (x - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2 := by
    push_cast; ring
  simp only [PoleR.rho, e]

theorem poleUB_le (nL nA : ℕ) (q : PoleR) (lo hi v : ℚ) (h : poleUB nL nA q lo hi = some v)
    (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (q.rho * Complex.log ((x : ℂ) - q.pc)).re ≤ (v : ℝ) := by
  unfold poleUB at h
  split at h
  · simp at h
  · rename_i LL LU hl
    obtain ⟨hL1, hL2⟩ := logBand_spec hl x hx
    rw [pole_term_eq]
    have hA : (q.rr : ℝ) * (Real.log ((x - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) / 2) =
        ((q.rr / 2 : ℚ) : ℝ) * Real.log ((x - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) := by
      push_cast; ring
    have hA' := mul_le_max2 (w := ((q.rr / 2 : ℚ) : ℝ)) hL1 hL2
    split_ifs at h with hri hpi
    · simp only [Option.some.injEq] at h
      subst h
      have hri' : (q.ri : ℝ) = 0 := by exact_mod_cast hri
      rw [hri', hA]
      push_cast at hA' ⊢
      linarith
    · split at h
      · rename_i v1 e1 v2 e2 ha1 ha2
        simp only [Option.some.injEq] at h
        subst h
        have hq : (q.pi : ℝ) ≠ 0 := by exact_mod_cast hpi
        have hb : ((-q.pi : ℚ) : ℝ) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hq
        have hb1 := argQ_spec ha1
        have hb2 := argQ_spec ha2
        have hbt := arg_between (b := ((-q.pi : ℚ) : ℝ))
          (a1 := ((lo - q.pr : ℚ) : ℝ)) (a := x - (q.pr : ℝ)) (a2 := ((hi - q.pr : ℚ) : ℝ)) hb
          (by push_cast; linarith [hx.1]) (by push_cast; linarith [hx.2])
        have hb1' := abs_le.mp hb1
        have hb2' := abs_le.mp hb2
        set A := Complex.arg ⟨x - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩
        have hAL : (((min (v1 - e1) (v2 - e2) : ℚ)) : ℝ) ≤ A := by
          push_cast
          refine le_trans ?_ hbt.1
          rcases min_cases (Complex.arg ⟨((lo - q.pr : ℚ) : ℝ), ((-q.pi : ℚ) : ℝ)⟩)
            (Complex.arg ⟨((hi - q.pr : ℚ) : ℝ), ((-q.pi : ℚ) : ℝ)⟩) with ⟨hm, _⟩ | ⟨hm, _⟩
          · rw [hm]; exact (min_le_left _ _).trans (by linarith [hb1'.1])
          · rw [hm]; exact (min_le_right _ _).trans (by linarith [hb2'.1])
        have hAU : A ≤ (((max (v1 + e1) (v2 + e2) : ℚ)) : ℝ) := by
          push_cast
          refine le_trans hbt.2 ?_
          rcases max_cases (Complex.arg ⟨((lo - q.pr : ℚ) : ℝ), ((-q.pi : ℚ) : ℝ)⟩)
            (Complex.arg ⟨((hi - q.pr : ℚ) : ℝ), ((-q.pi : ℚ) : ℝ)⟩) with ⟨hm, _⟩ | ⟨hm, _⟩
          · rw [hm]; exact (le_max_left _ _).trans' (by linarith [hb1'.2])
          · rw [hm]; exact (le_max_right _ _).trans' (by linarith [hb2'.2])
        have hB := mul_le_max2 (w := ((-q.ri : ℚ) : ℝ)) hAL hAU
        rw [hA]
        push_cast at hA' hB ⊢
        linarith
      · simp at h

/-! #### lists of terms and the piece -/

/-- Bound of `P_t log|x - e_t|`; `g` holds the (upper, lower) Chebyshev data of `P_t`. -/
def plogUB (nL : ℕ) (t : List ℚ × ℚ) (g : List ℚ × List ℚ) (lo hi : ℚ) : Option ℚ :=
  match logBand nL t.2 0 lo hi with
  | none => none
  | some (LL, LU) =>
    some (iv4 (polyLBc t.1 ((lo + hi) / 2) ((hi - lo) / 2) g.2)
      (polyUBc t.1 ((lo + hi) / 2) ((hi - lo) / 2) g.1) (LL / 2) (LU / 2))

theorem plogUB_le (nL : ℕ) (t : List ℚ × ℚ) (g : List ℚ × List ℚ) (lo hi v : ℚ) (hlo : lo < hi)
    (h : plogUB nL t g lo hi = some v) (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)| ≤ (v : ℝ) := by
  unfold plogUB at h
  split at h
  · simp at h
  · rename_i LL LU hl
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hL1, hL2⟩ := logBand_spec0 hl x hx
    have hr : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
      have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
      push_cast; linarith
    have hxc : |x - ((((lo + hi) / 2 : ℚ)) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
      push_cast
      exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hP1 := polyLBc_le t.1 ((lo + hi) / 2) ((hi - lo) / 2) g.2 hr x hxc
    have hP2 := polyUBc_le t.1 ((lo + hi) / 2) ((hi - lo) / 2) g.1 hr x hxc
    have hlg : Real.log |x - (t.2 : ℝ)| = Real.log ((x - (t.2 : ℝ)) ^ 2) / 2 := by
      rw [Real.log_pow, Real.log_abs]
      push_cast; ring
    rw [hlg]
    apply mul_le_iv4_cast hP1 hP2
    · have e : ((LL / 2 : ℚ) : ℝ) = (LL : ℝ) / 2 := by push_cast; ring
      rw [e]; linarith
    · have e : ((LU / 2 : ℚ) : ℝ) = (LU : ℝ) / 2 := by push_cast; ring
      rw [e]; linarith

def plogsUB (nL : ℕ) (lo hi : ℚ) :
    List (List ℚ × ℚ) → List (List ℚ × List ℚ) → Option ℚ
  | [], [] => some 0
  | t :: ts, g :: gs =>
    match plogUB nL t g lo hi, plogsUB nL lo hi ts gs with
    | some a, some b => some (a + b)
    | _, _ => none
  | _, _ => none

theorem plogsUB_le (nL : ℕ) (lo hi : ℚ) (hlo : lo < hi) :
    ∀ (ts : List (List ℚ × ℚ)) (gs : List (List ℚ × List ℚ)) (v : ℚ),
      plogsUB nL lo hi ts gs = some v → ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
        (ts.map (fun t => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|)).sum ≤ (v : ℝ) := by
  intro ts
  induction ts with
  | nil =>
    intro gs v h x _
    cases gs with
    | nil => simp only [plogsUB, Option.some.injEq] at h; subst h; simp
    | cons g gs => simp [plogsUB] at h
  | cons t ts ih =>
    intro gs v h x hx
    cases gs with
    | nil => simp [plogsUB] at h
    | cons g gs =>
      unfold plogsUB at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.map_cons, List.sum_cons]
        have h1 := plogUB_le nL t g lo hi a hlo ha x hx
        have h2 := ih gs b hb x hx
        push_cast
        linarith
      · simp at h

def polesUB (nL nA : ℕ) (lo hi : ℚ) : List PoleR → Option ℚ
  | [] => some 0
  | q :: qs =>
    match poleUB nL nA q lo hi, polesUB nL nA lo hi qs with
    | some a, some b => some (a + b)
    | _, _ => none

theorem polesUB_le (nL nA : ℕ) (lo hi : ℚ) :
    ∀ (qs : List PoleR) (v : ℚ), polesUB nL nA lo hi qs = some v →
      ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), poleF qs x ≤ (v : ℝ) := by
  intro qs
  induction qs with
  | nil =>
    intro v h x _
    simp only [polesUB, Option.some.injEq] at h
    subst h
    simp [poleF]
  | cons q qs ih =>
    intro v h x hx
    unfold polesUB at h
    split at h
    · rename_i a b ha hb
      simp only [Option.some.injEq] at h
      subst h
      have h1 := poleUB_le nL nA q lo hi a ha x hx
      have h2 := ih b hb x hx
      have e : poleF (q :: qs) x = (q.rho * Complex.log ((x : ℂ) - q.pc)).re + poleF qs x := by
        simp [poleF]
      rw [e]
      push_cast
      linarith
    · simp at h

theorem fieldTower_zero (fq : FieldQ) (F : ℝ → ℝ) (x : ℝ) :
    fieldTower fq F 0 x = polyTow fq.poly 0 x +
      (fq.plogs.map (fun t => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|)).sum + F x := by
  simp [fieldTower, plogSumTower, poleTower_zero, mulTower_zero, logTower]

/-- Bound of a field on `[lo, hi]`, or `none` when a check fails. -/
def fieldPieceUB (fq : FieldQ) (nL nA : ℕ) (lo hi : ℚ) (γ0 : List ℚ)
    (γs : List (List ℚ × List ℚ)) : Option ℚ :=
  if lo < hi then
    match plogsUB nL lo hi fq.plogs γs, polesUB nL nA lo hi fq.poles with
    | some a, some b =>
      some (polyUBc fq.poly ((lo + hi) / 2) ((hi - lo) / 2) γ0 + a + b)
    | _, _ => none
  else none

/-- The Boolean checker of a Taylor-free piece. -/
def chebFieldPiece (fq : FieldQ) (nL nA : ℕ) (lo hi : ℚ) (γ0 : List ℚ)
    (γs : List (List ℚ × List ℚ)) (T : ℚ) : Bool :=
  match fieldPieceUB fq nL nA lo hi γ0 γs with
  | some v => decide (v ≤ T)
  | none => false

/-- **Taylor-free piece soundness**: same conclusion as `cellV_sound`, no `BlockFacts`, no Taylor
radius.  The data `γ0`, `γs` (Chebyshev coefficients) are untrusted. -/
theorem chebFieldPiece_sound (fq : FieldQ) (nL nA : ℕ) (lo hi : ℚ) (γ0 : List ℚ)
    (γs : List (List ℚ × List ℚ)) (T : ℚ)
    (hchk : chebFieldPiece fq nL nA lo hi γ0 γs T = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold chebFieldPiece at hchk
  split at hchk
  · rename_i v hv
    simp only [decide_eq_true_eq] at hchk
    unfold fieldPieceUB at hv
    split_ifs at hv with hlo
    · split at hv
      · rename_i a b ha hb
        simp only [Option.some.injEq] at hv
        subst hv
        intro x hx
        have hr : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
          have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
          push_cast; linarith
        have hxc : |x - ((((lo + hi) / 2 : ℚ)) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
          push_cast
          exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have h1 := polyUBc_le fq.poly ((lo + hi) / 2) ((hi - lo) / 2) γ0 hr x hxc
        have h2 := plogsUB_le nL lo hi hlo fq.plogs γs a ha x hx
        have h3 := polesUB_le nL nA lo hi fq.poles b hb x hx
        have hT : ((polyUBc fq.poly ((lo + hi) / 2) ((hi - lo) / 2) γ0 + a + b : ℚ) : ℝ) ≤
            (T : ℝ) := by
          exact_mod_cast hchk
        rw [fieldTower_zero]
        push_cast at hT
        linarith
      · simp at hv
  · simp at hchk

/-! ### 7. Regression: a piece wider than the Taylor model allows

`f(x) = 1 + x²/2 + x log|x| + ½ log|x + 1/50| + Re[(1 - i/2) log(x - (1 + i)/100)]` on `[1/100, 1]`
(centre `101/200`, half-width `99/200`).  The complex pole `(1+i)/100` is at distance `0.49510` from
the centre, so `r/d = 0.9998`: the Taylor remainder `BM r^(n+1)` does not decay with the order and no
Taylor cell of this width can close at any order.  The logarithmic singularity `0` is at distance
`0.505` (`r/d = 0.980`), the real pole `-1/50` at `0.525`.  The piece ends at `Re p = 1/100`.

kcost: `shiftLK` of three coefficients, 8 `logQ` (table, series order 12), 2 `argQ` (order 24),
three Chebyshev bounds of 1 to 3 terms: about 3000 reduction steps, 1 s (estimated); a real piece
costs one degree-`d` shift (`shiftLK`, about 1 s at `d = 400`), `5 m²` rational operations per
Chebyshev bound of `m` terms, and one `logQ`/`argQ` per endpoint and term. -/

def toyFQ : FieldQ where
  poly := [1, 0, 1 / 2]
  plogs := [([0, 1], 0)]
  poles := [⟨1 / 2, 0, -1 / 50, 0⟩, ⟨1, -1 / 2, 1 / 100, 1 / 100⟩]

def toyG0 : List ℚ := [190203 / 160000, 9999 / 40000, 9801 / 160000]

def toyGs : List (List ℚ × List ℚ) := [([101 / 200, 99 / 200], [-101 / 200, -99 / 200])]

theorem toy_piece_check : chebFieldPiece toyFQ 12 24 (1 / 100) 1 toyG0 toyGs (3 / 2) = true := by
  decide +kernel

theorem toy_piece_sound : ∀ x ∈ Icc (((1 / 100 : ℚ)) : ℝ) (((1 : ℚ)) : ℝ),
    fieldTower toyFQ (poleF toyFQ.poles) 0 x ≤ (((3 / 2 : ℚ)) : ℝ) :=
  chebFieldPiece_sound toyFQ 12 24 (1 / 100) 1 toyG0 toyGs (3 / 2) toy_piece_check

/-- the same piece with a tighter threshold fails (the checker is not vacuous) -/
theorem toy_piece_tight :
    chebFieldPiece toyFQ 12 24 (1 / 100) 1 toyG0 toyGs (1 / 2) = false := by
  decide +kernel

#print axioms chebFieldPiece_sound
#print axioms toy_piece_check
#print axioms toy_piece_sound


/-- `Σ_{k<M} (-1)^k u^(k+1)/(k+1)`, the degree-`M` Taylor polynomial of `log (1 + u)` -/
noncomputable def logPS (M : ℕ) (u : ℂ) : ℂ :=
  ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * u ^ (k + 1) / ((k : ℂ) + 1)

theorem norm_log_one_add_sub_logPS_le (M : ℕ) {u : ℂ} {s : ℝ} (hu : ‖u‖ ≤ s) (hs : s < 1) :
    ‖Complex.log (1 + u) - logPS M u‖ ≤ s ^ (M + 1) / (((M : ℝ) + 1) * (1 - s)) := by
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu hs
  have hs0 : 0 ≤ s := (norm_nonneg u).trans hu
  have hS := Complex.hasSum_taylorSeries_log hu1
  set f : ℕ → ℂ := fun n => (-1) ^ (n + 1) * u ^ n / n with hf
  have hsum : ∑ i ∈ Finset.range (M + 1), f i = logPS M u := by
    rw [Finset.sum_range_succ']
    simp only [hf, logPS]
    have h0 : (-1 : ℂ) ^ (0 + 1) * u ^ 0 / ((0 : ℕ) : ℂ) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    have : (-1 : ℂ) ^ (k + 1 + 1) = (-1) ^ k := by
      rw [pow_succ, pow_succ]; ring
    rw [this]
  have hdec := hS.summable.sum_add_tsum_nat_add (M + 1)
  rw [hS.tsum_eq, hsum] at hdec
  have hrest : Complex.log (1 + u) - logPS M u = ∑' i, f (i + (M + 1)) := by
    rw [← hdec]; ring
  rw [hrest]
  have hg : HasSum (fun i : ℕ => s ^ (M + 1) / ((M : ℝ) + 1) * s ^ i)
      (s ^ (M + 1) / ((M : ℝ) + 1) * (1 - s)⁻¹) :=
    (hasSum_geometric_of_lt_one hs0 hs).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun i => f (i + (M + 1))) (fun i => by
    simp only [hf, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_natCast]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h1 : ‖u‖ ^ (i + (M + 1)) ≤ s ^ (i + (M + 1)) := pow_le_pow_left₀ (norm_nonneg u) hu _
    have h2 : ((M : ℝ) + 1) ≤ ((i + (M + 1) : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg i : (0:ℝ) ≤ i)]
    calc ‖u‖ ^ (i + (M + 1)) / ((i + (M + 1) : ℕ) : ℝ) ≤ s ^ (i + (M + 1)) / ((i + (M + 1) : ℕ) : ℝ) := by
          gcongr
      _ ≤ s ^ (i + (M + 1)) / ((M : ℝ) + 1) := by
          apply div_le_div_of_nonneg_left (by positivity) hM h2
      _ = s ^ (M + 1) / ((M : ℝ) + 1) * s ^ i := by ring)
  refine hb.trans (le_of_eq ?_)
  have : (1 - s) ≠ 0 := by linarith
  field_simp


/-- `log (z + y) = log z + log (1 + y/z)` for real `y` with `|y| < ‖z‖` (any branch position) -/
theorem clog_add_real (z : ℂ) (y : ℝ) (hz : z ≠ 0) (hy : |y| < ‖z‖) :
    Complex.log (z + y) = Complex.log z + Complex.log (1 + y / z) := by
  set w : ℂ := 1 + (y : ℂ) / z with hw
  have hzw : z * w = z + y := by rw [hw]; field_simp
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : z + (y : ℂ) ≠ 0 := by
    intro h
    have : z = -(y : ℂ) := by linear_combination h
    rw [this] at hy
    simp at hy
  have hw0 : w ≠ 0 := by
    intro h; apply hz'; rw [← hzw, h, mul_zero]
  have hyz : ‖(y : ℂ) / z‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_lt_one hnz]; exact hy
  have hre : 0 < w.re := by
    have h1 : |((y : ℂ) / z).re| ≤ ‖(y : ℂ) / z‖ := Complex.abs_re_le_norm _
    have h2 := abs_le.mp h1
    have : w.re = 1 + ((y : ℂ) / z).re := by rw [hw]; simp
    rw [this]; linarith [h2.1]
  have hargw : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hexp : Complex.exp (Complex.log (z + y) - Complex.log z - Complex.log w) = 1 := by
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hz', Complex.exp_log hz,
      Complex.exp_log hw0, ← hzw]
    field_simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.log_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im] at him
  have hsame : (z + (y : ℂ)).im = z.im := by simp
  have hdiff : |Complex.arg (z + y) - Complex.arg z| ≤ Real.pi := by
    rcases lt_or_ge z.im 0 with h | h
    · have a1 := Complex.neg_pi_lt_arg (z + y)
      have a2 := Complex.neg_pi_lt_arg z
      have b1 : Complex.arg (z + y) < 0 := Complex.arg_neg_iff.mpr (by rw [hsame]; exact h)
      have b2 : Complex.arg z < 0 := Complex.arg_neg_iff.mpr h
      rw [abs_le]; constructor <;> linarith
    · have a1 := Complex.arg_nonneg_iff.mpr (show 0 ≤ (z + (y : ℂ)).im by rw [hsame]; exact h)
      have a2 := Complex.arg_nonneg_iff.mpr h
      have b1 := Complex.arg_le_pi (z + y)
      have b2 := Complex.arg_le_pi z
      rw [abs_le]; constructor <;> linarith
  have hpi := Real.pi_pos
  have habs := abs_le.mp hdiff
  have habw := abs_lt.mp hargw
  have h2pi : (n : ℝ) * (2 * Real.pi) = Complex.arg (z + y) - Complex.arg z - Complex.arg w := by
    linarith [him]
  have hn1 : (n : ℝ) < 1 := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    nlinarith
  have hn2 : (-1 : ℝ) < n := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    nlinarith
  have hn0 : n = 0 := by
    have a : n < 1 := by exact_mod_cast hn1
    have b : -1 < n := by exact_mod_cast hn2
    omega
  subst hn0
  simp at hn
  have : Complex.log (z + y) = Complex.log z + Complex.log w := by
    linear_combination hn
  exact this

theorem clog_series (z : ℂ) (y s : ℝ) (hz : z ≠ 0) (hy : |y| ≤ s * ‖z‖) (hs : s < 1) (M : ℕ) :
    ‖Complex.log (z + y) - Complex.log z - logPS M (y / z)‖ ≤
      s ^ (M + 1) / (((M : ℝ) + 1) * (1 - s)) := by
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlt : |y| < ‖z‖ := by
    calc |y| ≤ s * ‖z‖ := hy
      _ < 1 * ‖z‖ := by gcongr
      _ = ‖z‖ := one_mul _
  rw [clog_add_real z y hz hlt]
  have hu : ‖(y : ℂ) / z‖ ≤ s := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hnz]; exact hy
  have := norm_log_one_add_sub_logPS_le M hu hs
  have e : Complex.log z + Complex.log (1 + (y : ℂ) / z) - Complex.log z - logPS M (y / z) =
      Complex.log (1 + (y : ℂ) / z) - logPS M (y / z) := by ring
  rw [e]; exact this


/-! ### 8. Taylor-merge -/

def geoQ (r : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => geoQ r n + r ^ (n + 1)

theorem geoQ_cast (r : ℚ) : ∀ n : ℕ, ((geoQ r n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, (r : ℝ) ^ (k + 1) := by
  intro n
  induction n with
  | zero => simp [geoQ]
  | succ n ih => rw [geoQ, Finset.sum_range_succ]; push_cast; rw [ih]

theorem polyTow_mapRange (M : ℕ) : ∀ (f : ℕ → ℚ) (x : ℝ),
    polyTow ((List.range M).map f) 0 x = ∑ k ∈ Finset.range M, (f k : ℝ) * x ^ k := by
  induction M with
  | zero => intro f x; simp [polyTow]
  | succ M ih =>
    intro f x
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, polyTow, Finset.sum_range_succ']
    have := ih (f ∘ Nat.succ) x
    simp only [Function.comp] at this
    show (f 0 : ℝ) + x * polyTow ((List.range M).map (f ∘ Nat.succ)) 0 x = _
    rw [this, Finset.mul_sum]
    simp only [pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [pow_succ]; ring

/-- coefficient of `y^(k+1)` in `Re[ρ log (1 + y/z)]`, `z = c - p` -/
def poleCoef (q : PoleR) (c : ℚ) (k : ℕ) : ℚ :=
  (-1) ^ k / ((k : ℚ) + 1) *
    (q.rr * (cpowQ (uOf q c) (k + 1)).1 - q.ri * (cpowQ (uOf q c) (k + 1)).2)

theorem pole_series_re (q : PoleR) (c : ℚ) (M : ℕ) (y : ℝ) :
    (q.rho * logPS M ((y : ℂ) / ((c : ℂ) - q.pc))).re =
      ∑ k ∈ Finset.range M, (poleCoef q c k : ℝ) * y ^ (k + 1) := by
  unfold logPS
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hW := cpowQ_spec q c (k + 1)
  set W := (((c : ℂ) - q.pc)⁻¹) ^ (k + 1) with hWdef
  have h1 : ((y : ℂ) / ((c : ℂ) - q.pc)) ^ (k + 1) = ((y ^ (k + 1) : ℝ) : ℂ) * W := by
    rw [div_eq_mul_inv, mul_pow]; push_cast; rfl
  rw [h1]
  have h2 : q.rho * ((-1 : ℂ) ^ k * (((y ^ (k + 1) : ℝ) : ℂ) * W) / ((k : ℂ) + 1)) =
      (((-1 : ℝ) ^ k * y ^ (k + 1) / ((k : ℝ) + 1) : ℝ) : ℂ) * (q.rho * W) := by
    push_cast; ring
  rw [h2, Complex.re_ofReal_mul]
  have h3 : (q.rho * W).re = (q.rr : ℝ) * ((cpowQ (uOf q c) (k + 1)).1 : ℝ) -
      (q.ri : ℝ) * ((cpowQ (uOf q c) (k + 1)).2 : ℝ) := by
    rw [← hW]; simp [PoleR.rho, Complex.mul_re]
  rw [h3]; unfold poleCoef; push_cast; ring

theorem norm_rho_le (q : PoleR) (rb : ℚ) (h0 : 0 ≤ rb) (h : q.rr ^ 2 + q.ri ^ 2 ≤ rb ^ 2) :
    ‖q.rho‖ ≤ (rb : ℝ) := by
  rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_le_iff]
  refine ⟨by exact_mod_cast h0, ?_⟩
  have h' : ((q.rr : ℝ)) ^ 2 + (q.ri : ℝ) ^ 2 ≤ (rb : ℝ) ^ 2 := by exact_mod_cast h
  simp only [PoleR.rho]
  nlinarith [h']


/-- enclosure of `arg (c - p)`, only needed when `ri ≠ 0` -/
def poleArg (nA : ℕ) (q : PoleR) (c : ℚ) : Option (ℚ × ℚ) :=
  if q.ri = 0 then some (0, 0) else argQ nA (c - q.pr) (-q.pi)

/-- Centre constant: `|Re[ρ log z] - (rr/2) lg + ri av| ≤ |rr|/2 eg + |ri| ea` -/
theorem pole_const_spec (nL nA : ℕ) (q : PoleR) (c : ℚ) (lg eg av ea : ℚ)
    (hlg : logQ nL ((c - q.pr) ^ 2 + q.pi ^ 2) = some (lg, eg))
    (harg : poleArg nA q c = some (av, ea)) :
    |(q.rho * Complex.log ((c : ℂ) - q.pc)).re - (((q.rr / 2 * lg - q.ri * av : ℚ)) : ℝ)| ≤
      ((qabs' q.rr / 2 * eg + qabs' q.ri * ea : ℚ) : ℝ) := by
  have hz : (c : ℂ) - q.pc = (((c : ℝ) : ℂ)) - q.pc := by simp
  rw [hz, pole_term_eq]
  obtain ⟨_, hL⟩ := logQ_spec hlg
  unfold Enc at hL
  have hL' : |Real.log (((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) - (lg : ℝ)| ≤ (eg : ℝ) := by
    have : (((c - q.pr) ^ 2 + q.pi ^ 2 : ℚ) : ℝ) = ((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2 := by
      push_cast; ring
    rw [this] at hL; exact hL
  have hA : |(q.ri : ℝ) * (Complex.arg ⟨(c : ℝ) - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ - (av : ℝ))| ≤
      (|(q.ri : ℝ)| * (ea : ℝ)) := by
    by_cases hri : q.ri = 0
    · simp [hri]
    · have harg' : argQ nA (c - q.pr) (-q.pi) = some (av, ea) := by
        unfold poleArg at harg; rwa [if_neg hri] at harg
      have := argQ_spec harg'
      have e : (⟨(c : ℝ) - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ : ℂ) =
          ⟨((c - q.pr : ℚ) : ℝ), ((-q.pi : ℚ) : ℝ)⟩ := by
        apply Complex.ext <;> simp
      rw [e, abs_mul]
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hlin : (q.rr : ℝ) * (Real.log (((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) / 2) -
        (q.ri : ℝ) * Complex.arg ⟨(c : ℝ) - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ -
        (((q.rr / 2 * lg - q.ri * av : ℚ)) : ℝ) =
      (q.rr : ℝ) / 2 * (Real.log (((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) - (lg : ℝ)) -
        (q.ri : ℝ) * (Complex.arg ⟨(c : ℝ) - (q.pr : ℝ), ((-q.pi : ℚ) : ℝ)⟩ - (av : ℝ)) := by
    push_cast; ring
  rw [hlin]
  have h1 : |(q.rr : ℝ) / 2 * (Real.log (((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2) - (lg : ℝ))| ≤
      |(q.rr : ℝ)| / 2 * (eg : ℝ) := by
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left hL' (by positivity)
  have h2 := (abs_sub _ _).trans (add_le_add h1 hA)
  have e : ((qabs' q.rr / 2 * eg + qabs' q.ri * ea : ℚ) : ℝ) =
      |(q.rr : ℝ)| / 2 * (eg : ℝ) + |(q.ri : ℝ)| * (ea : ℝ) := by
    push_cast; rw [qabs'_cast, qabs'_cast]
  rw [e]; exact h2

/-- the degree-`M` Taylor polynomial (rounded to `2^-P`) of `Re[ρ log (x - p)]` at the centre `c`,
with a bound on the error on `|x - c| ≤ r` (series tail with the data `qb ≥ r/|c - p|`,
`rb ≥ |ρ|`, centre constants from `logQ`/`argQ`, rounding) -/
def poleApx (nL nA M P : ℕ) (c r qb rb : ℚ) (q : PoleR) : Option (List ℚ × ℚ) :=
  if 0 < qb ∧ qb ≤ 1 / 2 ∧ 0 ≤ rb ∧ q.rr ^ 2 + q.ri ^ 2 ≤ rb ^ 2 ∧
      r ^ 2 ≤ qb ^ 2 * ((c - q.pr) ^ 2 + q.pi ^ 2) then
    match logQ nL ((c - q.pr) ^ 2 + q.pi ^ 2),
        poleArg nA q c with
    | some (lg, eg), some (av, ea) =>
      some (dyRound P (q.rr / 2 * lg - q.ri * av) ::
          (List.range M).map (fun k => dyRound P (poleCoef q c k)),
        qabs' q.rr / 2 * eg + qabs' q.ri * ea + 1 / 2 ^ P * (1 + geoQ r M) +
          rb * (qb ^ (M + 1) / (((M : ℚ) + 1) * (1 - qb))))
    | _, _ => none
  else none

theorem abs_combine4 {E1 E2 S T b1 pp g t : ℝ} (h1 : |E1| ≤ b1) (h2 : 0 ≤ E2) (h2' : E2 ≤ pp)
    (h3 : |S| ≤ pp * g) (h4 : |T| ≤ t) :
    |E1 + E2 + S + T| ≤ b1 + pp * (1 + g) + t := by
  have a1 := abs_le.mp h1
  have a3 := abs_le.mp h3
  have a4 := abs_le.mp h4
  have : pp * (1 + g) = pp + pp * g := by ring
  rw [abs_le]
  constructor <;> linarith

theorem poleApx_spec {nL nA M P : ℕ} {c r qb rb : ℚ} {q : PoleR} {A : List ℚ} {B : ℚ}
    (h : poleApx nL nA M P c r qb rb q = some (A, B)) (hr : 0 < r) (x : ℝ)
    (hx : |x - (c : ℝ)| ≤ (r : ℝ)) :
    |(q.rho * Complex.log ((x : ℂ) - q.pc)).re - polyTow A 0 (x - (c : ℝ))| ≤ (B : ℝ) := by
  unfold poleApx at h
  split_ifs at h with hc
  obtain ⟨hqb0, hqb1, hrb0, hrb, hr2⟩ := hc
  split at h
  · rename_i lg eg av ea hlg harg
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    set y : ℝ := x - (c : ℝ) with hy
    set z : ℂ := (c : ℂ) - q.pc with hzdef
    have hzre : z.re = (c : ℝ) - (q.pr : ℝ) := by simp [hzdef, PoleR.pc]
    have hzim : z.im = -(q.pi : ℝ) := by simp [hzdef, PoleR.pc]
    have hnz2 : ‖z‖ ^ 2 = ((c : ℝ) - (q.pr : ℝ)) ^ 2 + (q.pi : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]; ring
    have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hr2' : (r : ℝ) ^ 2 ≤ (qb : ℝ) ^ 2 * ‖z‖ ^ 2 := by
      rw [hnz2]
      have : ((r ^ 2 : ℚ) : ℝ) ≤ ((qb ^ 2 * ((c - q.pr) ^ 2 + q.pi ^ 2) : ℚ) : ℝ) := by
        exact_mod_cast hr2
      push_cast at this
      exact this
    have hqb0' : (0 : ℝ) < (qb : ℝ) := by exact_mod_cast hqb0
    have hqb1' : (qb : ℝ) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hqb1; push_cast at this; linarith
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hr2'
      nlinarith
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hrz : (r : ℝ) ≤ (qb : ℝ) * ‖z‖ := by
      have h1 : ((r : ℝ)) ^ 2 ≤ ((qb : ℝ) * ‖z‖) ^ 2 := by rw [mul_pow]; exact hr2'
      exact (pow_le_pow_iff_left₀ hr'.le (by positivity) (two_ne_zero)).mp h1
    have hyz : |y| ≤ (qb : ℝ) * ‖z‖ := hx.trans hrz
    have hser := clog_series z y (qb : ℝ) hz0 hyz (by linarith) M
    have hxz : (x : ℂ) - q.pc = z + (y : ℂ) := by simp [hy, hzdef]
    -- split the logarithm
    set D := Complex.log (z + y) - Complex.log z - logPS M (y / z) with hD
    have hsplit : (q.rho * Complex.log ((x : ℂ) - q.pc)).re =
        (q.rho * Complex.log z).re + (q.rho * logPS M (y / z)).re + (q.rho * D).re := by
      rw [hxz, hD, ← Complex.add_re, ← Complex.add_re]
      congr 1; ring
    have hT3 : |(q.rho * D).re| ≤
        (rb : ℝ) * ((qb : ℝ) ^ (M + 1) / (((M : ℝ) + 1) * (1 - (qb : ℝ)))) := by
      calc |(q.rho * D).re| ≤ ‖q.rho * D‖ := Complex.abs_re_le_norm _
        _ = ‖q.rho‖ * ‖D‖ := norm_mul _ _
        _ ≤ (rb : ℝ) * ((qb : ℝ) ^ (M + 1) / (((M : ℝ) + 1) * (1 - (qb : ℝ)))) :=
            mul_le_mul (norm_rho_le q rb hrb0 hrb) hser (norm_nonneg _) (by exact_mod_cast hrb0)
    have hT1 := pole_const_spec nL nA q c lg eg av ea hlg harg
    have hT2 := pole_series_re q c M y
    rw [← hzdef] at hT2
    -- polynomial value
    set cf : ℕ → ℚ := fun k => dyRound P (poleCoef q c k) with hcf
    have hpoly : polyTow (dyRound P (q.rr / 2 * lg - q.ri * av) :: (List.range M).map cf) 0 y =
        (dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ) +
          ∑ k ∈ Finset.range M, (cf k : ℝ) * y ^ (k + 1) := by
      have hc : polyTow (dyRound P (q.rr / 2 * lg - q.ri * av) :: (List.range M).map cf) 0 y =
          (dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ) + y * polyTow ((List.range M).map cf) 0 y := rfl
      rw [hc, polyTow_mapRange, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    have hcoef : |∑ k ∈ Finset.range M, ((poleCoef q c k : ℝ) - (cf k : ℝ)) * y ^ (k + 1)| ≤
        (1 / 2 ^ P : ℝ) * (∑ k ∈ Finset.range M, (r : ℝ) ^ (k + 1)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      obtain ⟨d0, d1⟩ := dyRound_spec P (poleCoef q c k)
      have d0' : (0 : ℝ) ≤ (poleCoef q c k : ℝ) - (cf k : ℝ) := by
        have := (Rat.cast_le (K := ℝ)).mpr d0; push_cast at this; exact this
      have d1' : (poleCoef q c k : ℝ) - (cf k : ℝ) ≤ 1 / 2 ^ P := by
        have := (Rat.cast_le (K := ℝ)).mpr d1; push_cast at this; exact this
      rw [abs_mul, abs_of_nonneg d0', abs_pow]
      have hp : |y| ^ (k + 1) ≤ (r : ℝ) ^ (k + 1) := pow_le_pow_left₀ (abs_nonneg _) hx _
      exact mul_le_mul d1' hp (by positivity) (by positivity)
    obtain ⟨k0, k1⟩ := dyRound_spec P (q.rr / 2 * lg - q.ri * av)
    have k0' : (0 : ℝ) ≤ ((q.rr / 2 * lg - q.ri * av : ℚ) : ℝ) -
        (dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).mpr k0; push_cast at this ⊢; linarith
    have k1' : ((q.rr / 2 * lg - q.ri * av : ℚ) : ℝ) -
        (dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ) ≤ 1 / 2 ^ P := by
      have := (Rat.cast_le (K := ℝ)).mpr k1; push_cast at this ⊢; linarith
    rw [hsplit, hpoly, hT2]
    have hsum : ∑ k ∈ Finset.range M, (poleCoef q c k : ℝ) * y ^ (k + 1) -
        ∑ k ∈ Finset.range M, (cf k : ℝ) * y ^ (k + 1) =
        ∑ k ∈ Finset.range M, ((poleCoef q c k : ℝ) - (cf k : ℝ)) * y ^ (k + 1) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
    have hgeo := geoQ_cast r M
    have hBcast : (((qabs' q.rr / 2 * eg + qabs' q.ri * ea + 1 / 2 ^ P * (1 + geoQ r M) +
        rb * (qb ^ (M + 1) / (((M : ℚ) + 1) * (1 - qb))) : ℚ)) : ℝ) =
        ((qabs' q.rr / 2 * eg + qabs' q.ri * ea : ℚ) : ℝ) + 1 / 2 ^ P *
          (1 + ∑ k ∈ Finset.range M, (r : ℝ) ^ (k + 1)) +
        (rb : ℝ) * ((qb : ℝ) ^ (M + 1) / (((M : ℝ) + 1) * (1 - (qb : ℝ)))) := by
      push_cast
      rw [hgeo]
    rw [hBcast]
    have hfin : (q.rho * Complex.log z).re + ∑ k ∈ Finset.range M, (poleCoef q c k : ℝ) * y ^ (k + 1) +
        (q.rho * D).re - ((dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ) +
          ∑ k ∈ Finset.range M, (cf k : ℝ) * y ^ (k + 1)) =
        ((q.rho * Complex.log z).re - ((q.rr / 2 * lg - q.ri * av : ℚ) : ℝ)) +
          (((q.rr / 2 * lg - q.ri * av : ℚ) : ℝ) -
            (dyRound P (q.rr / 2 * lg - q.ri * av) : ℝ)) +
          ∑ k ∈ Finset.range M, ((poleCoef q c k : ℝ) - (cf k : ℝ)) * y ^ (k + 1) +
            (q.rho * D).re := by
      rw [← hsum]; ring
    rw [hfin]
    exact abs_combine4 hT1 k0' k1' hcoef hT3
  · simp at h


/-! #### terms, lists, and the merged piece -/

/-- `g ≤ polyTow A (x - c) + B` on `[lo, hi]`, `c = (lo + hi)/2` -/
def Bnd (lo hi : ℚ) (g : ℝ → ℝ) (A : List ℚ) (B : ℚ) : Prop :=
  ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), g x ≤ polyTow A 0 (x - (((lo + hi) / 2 : ℚ) : ℝ)) + (B : ℝ)

theorem Bnd.zero (lo hi : ℚ) : Bnd lo hi (fun _ => 0) [] 0 := by
  intro x _; simp [polyTow]

theorem Bnd.add {lo hi : ℚ} {g1 g2 : ℝ → ℝ} {A1 A2 : List ℚ} {B1 B2 : ℚ}
    (h1 : Bnd lo hi g1 A1 B1) (h2 : Bnd lo hi g2 A2 B2) :
    Bnd lo hi (fun x => g1 x + g2 x) (vecAdd A1 A2) (B1 + B2) := by
  intro x hx
  have a := h1 x hx
  have b := h2 x hx
  rw [polyTow_vecAdd, Rat.cast_add]
  linarith

theorem hx_abs (lo hi : ℚ) (x : ℝ) (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    |x - (((lo + hi) / 2 : ℚ) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
  push_cast
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem abs_polyTow_le_absSum (l : List ℚ) (c r : ℚ) (hr : 0 < (r : ℝ)) (x : ℝ)
    (hx : |x - (c : ℝ)| ≤ (r : ℝ)) :
    |polyTow l 0 (x - (c : ℝ))| ≤ ((absSum (sclPow r 0 l) : ℚ) : ℝ) := by
  have hu : |(x - (c : ℝ)) / (r : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hx
  have h := polyTow_abs_le ((x - (c : ℝ)) / (r : ℝ)) hu (sclPow r 0 l)
  rw [polyTow_sclPow] at h
  have e : (r : ℝ) * ((x - (c : ℝ)) / (r : ℝ)) = x - (c : ℝ) := by field_simp
  rw [e] at h
  simpa using h

theorem polyTow_le_cheb (l γ : List ℚ) (c r : ℚ) (hr : 0 < (r : ℝ)) (x : ℝ)
    (hx : |x - (c : ℝ)| ≤ (r : ℝ)) :
    polyTow l 0 (x - (c : ℝ)) ≤ ((chebPolyUB (sclPow r 0 l) γ : ℚ) : ℝ) := by
  have hu : |(x - (c : ℝ)) / (r : ℝ)| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]; exact hx
  have h := chebPoly_le (sclPow r 0 l) γ ((x - (c : ℝ)) / (r : ℝ)) hu
  rw [polyTow_sclPow] at h
  have e : (r : ℝ) * ((x - (c : ℝ)) / (r : ℝ)) = x - (c : ℝ) := by field_simp
  rw [e] at h
  simpa using h

/-- Bound of `P(x) log|x - e|`: Taylor-merge (`poleApx` of the pole `1 · log (x - e)`, times the
exactly shifted `P`, error `sup |P| · B`) when the data `qb` allows, else the monotone `plogUB`. -/
def plogTerm (nL nA Ml P : ℕ) (lo hi : ℚ) (t : List ℚ × ℚ) (d : ℚ × (List ℚ × List ℚ)) :
    Option (List ℚ × ℚ) :=
  match poleApx nL nA Ml P ((lo + hi) / 2) ((hi - lo) / 2) d.1 1 ⟨1, 0, t.2, 0⟩ with
  | some (A, B) =>
    some (pmulQ (shiftLK ((lo + hi) / 2) t.1.length t.1) A,
      absSum (sclPow ((hi - lo) / 2) 0 (shiftLK ((lo + hi) / 2) t.1.length t.1)) * B)
  | none => (plogUB nL t d.2 lo hi).map (fun v => ([], v))

theorem plogTerm_bnd {nL nA Ml P : ℕ} {lo hi : ℚ} (hlo : lo < hi) {t : List ℚ × ℚ}
    {d : ℚ × (List ℚ × List ℚ)} {A : List ℚ} {B : ℚ}
    (h : plogTerm nL nA Ml P lo hi t d = some (A, B)) :
    Bnd lo hi (fun x => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|) A B := by
  intro x hx
  show polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)| ≤ _
  have hr : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
    have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
    push_cast; linarith
  have hxc := hx_abs lo hi x hx
  unfold plogTerm at h
  split at h
  · rename_i A0 B0 hpa
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    set c : ℚ := (lo + hi) / 2 with hc
    set r : ℚ := (hi - lo) / 2 with hr'
    have hap := poleApx_spec hpa (by exact_mod_cast hr) x hxc
    have hre : (((⟨1, 0, t.2, 0⟩ : PoleR)).rho * Complex.log ((x : ℂ) - (⟨1, 0, t.2, 0⟩ : PoleR).pc)).re =
        Real.log |x - (t.2 : ℝ)| := by
      rw [re_clog_real _ rfl rfl]
      simp
    rw [hre] at hap
    set Psh := shiftLK c t.1.length t.1 with hPsh
    have hP : polyTow t.1 0 x = polyTow Psh 0 (x - (c : ℝ)) := by
      rw [hPsh, shiftLK_eq', polyTow_shiftL, sub_add_cancel]
    have hPm := abs_polyTow_le_absSum Psh c r hr x hxc
    rw [l0_pmul, hP]
    set Pv := polyTow Psh 0 (x - (c : ℝ)) with hPv
    set Lg := Real.log |x - (t.2 : ℝ)| with hLg
    set Ap := polyTow A0 0 (x - (c : ℝ)) with hAp
    have hB0 : (0 : ℝ) ≤ (B0 : ℝ) := (abs_nonneg _).trans hap
    have h1 : Pv * Lg - Pv * Ap ≤ ((absSum (sclPow r 0 Psh) : ℚ) : ℝ) * (B0 : ℝ) := by
      calc Pv * Lg - Pv * Ap = Pv * (Lg - Ap) := by ring
        _ ≤ |Pv * (Lg - Ap)| := le_abs_self _
        _ = |Pv| * |Lg - Ap| := abs_mul _ _
        _ ≤ ((absSum (sclPow r 0 Psh) : ℚ) : ℝ) * (B0 : ℝ) :=
            mul_le_mul hPm hap (abs_nonneg _) ((abs_nonneg _).trans hPm)
    push_cast
    linarith
  · rename_i hpa
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, hAB⟩ := h
    simp only [Prod.mk.injEq] at hAB
    obtain ⟨rfl, rfl⟩ := hAB
    have := plogUB_le nL t d.2 lo hi v hlo hv x hx
    have e0 : polyTow [] 0 (x - (((lo + hi) / 2 : ℚ) : ℝ)) = 0 := rfl
    rw [e0, zero_add]
    exact this

/-- Bound of a pole term `Re[ρ log (x - p)]`. -/
def poleTerm (nL nA M P : ℕ) (lo hi : ℚ) (q : PoleR) (d : ℚ × ℚ) : Option (List ℚ × ℚ) :=
  match poleApx nL nA M P ((lo + hi) / 2) ((hi - lo) / 2) d.1 d.2 q with
  | some ab => some ab
  | none => (poleUB nL nA q lo hi).map (fun v => ([], v))

theorem poleTerm_bnd {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi) {q : PoleR} {d : ℚ × ℚ}
    {A : List ℚ} {B : ℚ} (h : poleTerm nL nA M P lo hi q d = some (A, B)) :
    Bnd lo hi (fun x => (q.rho * Complex.log ((x : ℂ) - q.pc)).re) A B := by
  intro x hx
  show (q.rho * Complex.log ((x : ℂ) - q.pc)).re ≤ _
  have hr : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
    have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
    push_cast; linarith
  have hxc := hx_abs lo hi x hx
  unfold poleTerm at h
  split at h
  · rename_i hpa
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hap := poleApx_spec hpa (by exact_mod_cast hr) x hxc
    have := (abs_le.mp hap).2
    linarith
  · rename_i hpa
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, hAB⟩ := h
    simp only [Prod.mk.injEq] at hAB
    obtain ⟨rfl, rfl⟩ := hAB
    have := poleUB_le nL nA q lo hi v hv x hx
    have e0 : polyTow [] 0 (x - (((lo + hi) / 2 : ℚ) : ℝ)) = 0 := rfl
    rw [e0, zero_add]
    exact this

def plogsM (nL nA Ml P : ℕ) (lo hi : ℚ) :
    List (List ℚ × ℚ) → List (ℚ × (List ℚ × List ℚ)) → Option (List ℚ × ℚ)
  | [], [] => some ([], 0)
  | t :: ts, d :: ds =>
    match plogTerm nL nA Ml P lo hi t d, plogsM nL nA Ml P lo hi ts ds with
    | some a, some b => some (vecAdd a.1 b.1, a.2 + b.2)
    | _, _ => none
  | _, _ => none

theorem plogsM_bnd {nL nA Ml P : ℕ} {lo hi : ℚ} (hlo : lo < hi) :
    ∀ (ts : List (List ℚ × ℚ)) (ds : List (ℚ × (List ℚ × List ℚ))) (A : List ℚ) (B : ℚ),
      plogsM nL nA Ml P lo hi ts ds = some (A, B) →
      Bnd lo hi (fun x => (ts.map (fun t => polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)|)).sum) A B := by
  intro ts
  induction ts with
  | nil =>
    intro ds A B h
    cases ds with
    | nil =>
      simp only [plogsM, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using Bnd.zero lo hi
    | cons d ds => simp [plogsM] at h
  | cons t ts ih =>
    intro ds A B h
    cases ds with
    | nil => simp [plogsM] at h
    | cons d ds =>
      unfold plogsM at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := (plogTerm_bnd hlo ha).add (ih ds b.1 b.2 hb)
        simpa using this
      · simp at h

def polesM (nL nA M P : ℕ) (lo hi : ℚ) : List PoleR → List (ℚ × ℚ) → Option (List ℚ × ℚ)
  | [], [] => some ([], 0)
  | q :: qs, d :: ds =>
    match poleTerm nL nA M P lo hi q d, polesM nL nA M P lo hi qs ds with
    | some a, some b => some (vecAdd a.1 b.1, a.2 + b.2)
    | _, _ => none
  | _, _ => none

theorem polesM_bnd {nL nA M P : ℕ} {lo hi : ℚ} (hlo : lo < hi) :
    ∀ (qs : List PoleR) (ds : List (ℚ × ℚ)) (A : List ℚ) (B : ℚ),
      polesM nL nA M P lo hi qs ds = some (A, B) → Bnd lo hi (fun x => poleF qs x) A B := by
  intro qs
  induction qs with
  | nil =>
    intro ds A B h
    cases ds with
    | nil =>
      simp only [polesM, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := Bnd.zero lo hi
      simpa [poleF] using this
    | cons d ds => simp [polesM] at h
  | cons q qs ih =>
    intro ds A B h
    cases ds with
    | nil => simp [polesM] at h
    | cons d ds =>
      unfold polesM at h
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := (poleTerm_bnd hlo ha).add (ih ds b.1 b.2 hb)
        intro x hx
        show poleF (q :: qs) x ≤ _
        have h2 := this x hx
        have e : poleF (q :: qs) x = (q.rho * Complex.log ((x : ℂ) - q.pc)).re + poleF qs x := by
          simp [poleF]
        rw [e]
        exact h2
      · simp at h

/-- Same-site plog entries are added exactly (first occurrence order): the leading polynomials of
sites that cancel in the field (`P_e` and `-P_e + small`) are then small, which the tail bound `sup|P_e|`
needs. -/
def addSite (t : List ℚ × ℚ) : List (List ℚ × ℚ) → List (List ℚ × ℚ)
  | [] => [t]
  | s :: ss => if s.2 = t.2 then (vecAdd s.1 t.1, s.2) :: ss else s :: addSite t ss

def mergeSites (l : List (List ℚ × ℚ)) : List (List ℚ × ℚ) :=
  l.foldl (fun acc t => addSite t acc) []

theorem addSite_sum (t : List ℚ × ℚ) (x : ℝ) : ∀ l : List (List ℚ × ℚ),
    ((addSite t l).map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum =
      polyTow t.1 0 x * Real.log |x - (t.2 : ℝ)| +
        (l.map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum := by
  intro l
  induction l with
  | nil => simp [addSite]
  | cons s ss ih =>
    unfold addSite
    by_cases h : s.2 = t.2
    · rw [if_pos h]
      simp only [List.map_cons, List.sum_cons, polyTow_vecAdd, h]
      push_cast
      ring
    · rw [if_neg h]
      simp only [List.map_cons, List.sum_cons, ih]
      ring

theorem mergeSites_sum (x : ℝ) : ∀ (l acc : List (List ℚ × ℚ)),
    ((l.foldl (fun a t => addSite t a) acc).map
        (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum =
      (l.map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum +
        (acc.map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, addSite_sum]
    ring

theorem mergeSites_eq (x : ℝ) (l : List (List ℚ × ℚ)) :
    ((mergeSites l).map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum =
      (l.map (fun s => polyTow s.1 0 x * Real.log |x - (s.2 : ℝ)|)).sum := by
  unfold mergeSites
  rw [mergeSites_sum]
  simp

/-- The bound of a Taylor-merged piece: the Chebyshev bound of the merged polynomial
(`poly` shifted exactly to the centre, plus the Taylor polynomials of the far plog sites and poles)
plus the error terms and the monotone fallback bounds of the near terms. -/
def mergeUB (fq : FieldQ) (nL nA Mp Ml P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (γ : List ℚ) : Option ℚ :=
  if lo < hi then
    match plogsM nL nA Ml P lo hi (mergeSites fq.plogs) pd, polesM nL nA Mp P lo hi fq.poles qd with
    | some a, some b =>
      some (chebPolyUB (sclPow ((hi - lo) / 2) 0
          (vecAdd (shiftLK ((lo + hi) / 2) fq.poly.length fq.poly) (vecAdd a.1 b.1))) γ + a.2 + b.2)
    | _, _ => none
  else none

def chebMergePiece (fq : FieldQ) (nL nA Mp Ml P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (γ : List ℚ) (T : ℚ) : Bool :=
  match mergeUB fq nL nA Mp Ml P lo hi pd qd γ with
  | some v => decide (v ≤ T)
  | none => false

/-- **Taylor-merged piece soundness**: same conclusion as `cellV_sound`, no `BlockFacts`.  The data
`pd` (per plog site: `qb ≥ r/|c - e|`, fallback Chebyshev data), `qd` (per pole: `qb ≥ r/|c - p|`,
`rb ≥ |ρ|`) and `γ` are untrusted: a term whose data fail the checked conditions falls back to its
monotone enclosure. -/
theorem chebMergePiece_sound (fq : FieldQ) (nL nA Mp Ml P : ℕ) (lo hi : ℚ)
    (pd : List (ℚ × (List ℚ × List ℚ))) (qd : List (ℚ × ℚ)) (γ : List ℚ) (T : ℚ)
    (hchk : chebMergePiece fq nL nA Mp Ml P lo hi pd qd γ T = true) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), fieldTower fq (poleF fq.poles) 0 x ≤ (T : ℝ) := by
  unfold chebMergePiece at hchk
  split at hchk
  · rename_i v hv
    simp only [decide_eq_true_eq] at hchk
    unfold mergeUB at hv
    split_ifs at hv with hlo
    · split at hv
      · rename_i a b ha hb
        simp only [Option.some.injEq] at hv
        subst hv
        intro x hx
        have hr : (0 : ℝ) < (((hi - lo) / 2 : ℚ) : ℝ) := by
          have : (lo : ℝ) < (hi : ℝ) := by exact_mod_cast hlo
          push_cast; linarith
        have hxc := hx_abs lo hi x hx
        have h2 := plogsM_bnd hlo (mergeSites fq.plogs) pd a.1 a.2 ha x hx
        beta_reduce at h2
        rw [mergeSites_eq] at h2
        have h3 := polesM_bnd hlo fq.poles qd b.1 b.2 hb x hx
        have h1 : polyTow fq.poly 0 x =
            polyTow (shiftLK ((lo + hi) / 2) fq.poly.length fq.poly) 0
              (x - (((lo + hi) / 2 : ℚ) : ℝ)) := by
          rw [shiftLK_eq', polyTow_shiftL, sub_add_cancel]
        have h4 := polyTow_le_cheb
          (vecAdd (shiftLK ((lo + hi) / 2) fq.poly.length fq.poly) (vecAdd a.1 b.1)) γ
          ((lo + hi) / 2) ((hi - lo) / 2) hr x hxc
        rw [polyTow_vecAdd, polyTow_vecAdd] at h4
        have hT : ((chebPolyUB (sclPow ((hi - lo) / 2) 0
            (vecAdd (shiftLK ((lo + hi) / 2) fq.poly.length fq.poly) (vecAdd a.1 b.1))) γ + a.2 + b.2 :
            ℚ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hchk
        rw [fieldTower_zero, h1]
        rw [Rat.cast_add, Rat.cast_add] at hT
        beta_reduce at h3
        linarith
      · simp at hv
  · simp at hchk

/-! ### 9. Regression of the Taylor-merged piece

`f(x) = 1 + x²/2 + x log|x + 3| + ½ · ½ log (x - 2)² + Re[(1 - i/2) log (x - (-2 + i))]` on `[0, 1]`
(centre `1/2`, `r = 1/2`; true maximum `3.8767`).  The plog site `-3` is at `q = r/|c - e| = 1/7`,
the poles `2` and `-2 + i` at `q = 1/3`, `q = 0.186`; the data `qb = 1/7, 1/3, 1/5` and `rb = 1/2, 6/5`
pass the rational tests.  With `γ = []` the Chebyshev bound is the monomial bound `Σ |a_k| r^k`.
`mergeUB` (`#eval`): 3.8983 (all Taylor), 3.8899 (plog by fallback), 4.2326 (poles by fallback),
4.2233 (all by fallback).

kcost: one `shiftLK` of 3 and 2 coefficients, 3 `logQ` and 1 `argQ` (series orders 12 and 24), degree-10
series (30 rational coefficients with `dyRound 64`), `pmulQ` of 2 by 11 terms, one
`absSum`/`vsubQ` of length 13: about 5000 reduction steps, 1 s (estimated). -/

def toyMFQ : FieldQ where
  poly := [1, 0, 1 / 2]
  plogs := [([0, 1], -3)]
  poles := [⟨1 / 2, 0, 2, 0⟩, ⟨1, -1 / 2, -2, 1⟩]

def toyMpd : List (ℚ × (List ℚ × List ℚ)) := [(1 / 7, ([1 / 2, 1 / 2], [-1 / 2, -1 / 2]))]
def toyMqd : List (ℚ × ℚ) := [(1 / 3, 1 / 2), (1 / 5, 6 / 5)]
def toyMpd0 : List (ℚ × (List ℚ × List ℚ)) := [(0, ([1 / 2, 1 / 2], [-1 / 2, -1 / 2]))]
def toyMqd0 : List (ℚ × ℚ) := [(0, 0), (0, 0)]

theorem toy_merge_check : chebMergePiece toyMFQ 12 24 10 10 64 0 1 toyMpd toyMqd [] (39 / 10) = true := by
  decide +kernel

/-- the same piece with a threshold below the bound fails -/
theorem toy_merge_tight : chebMergePiece toyMFQ 12 24 10 10 64 0 1 toyMpd toyMqd [] (389 / 100) = false := by
  decide +kernel

/-- the plog site by fallback, the poles merged -/
theorem toy_merge_mixed : chebMergePiece toyMFQ 12 24 10 10 64 0 1 toyMpd0 toyMqd [] (39 / 10) = true := by
  decide +kernel

/-- every term by fallback: a larger bound, still sound -/
theorem toy_merge_fallback :
    chebMergePiece toyMFQ 12 24 10 10 64 0 1 toyMpd0 toyMqd0 [] (43 / 10) = true := by
  decide +kernel

theorem toy_merge_fallback_tight :
    chebMergePiece toyMFQ 12 24 10 10 64 0 1 toyMpd0 toyMqd0 [] (39 / 10) = false := by
  decide +kernel

theorem toy_merge_sound : ∀ x ∈ Icc (((0 : ℚ)) : ℝ) (((1 : ℚ)) : ℝ),
    fieldTower toyMFQ (poleF toyMFQ.poles) 0 x ≤ (((39 / 10 : ℚ)) : ℝ) :=
  chebMergePiece_sound toyMFQ 12 24 10 10 64 0 1 toyMpd toyMqd [] (39 / 10) toy_merge_check

#print axioms chebMergePiece_sound
#print axioms toy_merge_check
#print axioms toy_merge_tight
#print axioms toy_merge_mixed
#print axioms toy_merge_fallback
#print axioms toy_merge_sound

end CatalanMeasure.GenD.Signed.Data.Cells

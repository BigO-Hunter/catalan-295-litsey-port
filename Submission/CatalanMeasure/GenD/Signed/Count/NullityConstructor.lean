module

public import Submission.CatalanMeasure.GenD.Interface
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
set_option Elab.async false

/-!
# Count layer: an all-`N` `NullityLB` from finitely many eventual affine lower bounds

A *count piece* is a window `a·N < p ≤ b·N` with an affine lower bound
`ν(N,p) ≥ c0·N + c1·p - 2`.  Given finitely many pieces and a common threshold `N0` at which
each piece's bound is proved (for all primes of its window with the raw `H < p²` gate), the
function `kap = max (0, ⌈c0 N + c1 p - 2⌉ …)` is a genuine `NullityLB`: below `N0` and off the
windows it is `0`, so `kap ≤ ν` for EVERY `N, p`.  No statement about small-scale matrices is
needed, and `N0` may be chosen noncomputably.
-/

namespace CatalanMeasure.GenD.Signed.Count.NullityConstructor
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
noncomputable section

/-- A window with its affine nullity lower bound `c0 N + c1 p - 2`. -/
structure CountPiece where
  a : ℝ
  b : ℝ
  c0 : ℝ
  c1 : ℝ

open Classical in
/-- Ceiling value of one piece at `(N, p)`, zero off its window or below the threshold. -/
def CountPiece.kap (w : CountPiece) (N0 N p : ℕ) : ℕ :=
  if N0 ≤ N ∧ w.a * N < p ∧ (p : ℝ) ≤ w.b * N then ⌈w.c0 * N + w.c1 * p - 2⌉₊ else 0

/-- The finite maximum (with `0`). -/
def countKap (ws : List CountPiece) (N0 N p : ℕ) : ℕ :=
  ws.foldr (fun w acc => max (w.kap N0 N p) acc) 0

theorem kap_le_countKap {ws : List CountPiece} {w : CountPiece} (hw : w ∈ ws) (N0 N p : ℕ) :
    w.kap N0 N p ≤ countKap ws N0 N p := by
  induction ws with
  | nil => simp at hw
  | cons v vs ih =>
    simp only [countKap, List.foldr_cons]
    rcases List.mem_cons.mp hw with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem countKap_le {ws : List CountPiece} {n : ℕ} (N0 N p : ℕ)
    (h : ∀ w ∈ ws, w.kap N0 N p ≤ n) : countKap ws N0 N p ≤ n := by
  induction ws with
  | nil => simp [countKap]
  | cons v vs ih =>
    simp only [countKap, List.foldr_cons]
    exact max_le (h v (List.mem_cons_self)) (ih fun w hw => h w (List.mem_cons_of_mem _ hw))

/-- **The constructor.**  `hpiece` is the eventual affine bound for each window (the output of
the host count, relation bound and uniform-error layers). -/
def countLB (P : Parameters) (ws : List CountPiece) (N0 : ℕ)
    (hpiece : ∀ w ∈ ws, ∀ N p : ℕ, N0 ≤ N → 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 →
      w.a * N < p → (p : ℝ) ≤ w.b * N →
      haveI : Fact p.Prime := ⟨hp⟩
      w.c0 * N + w.c1 * p - 2 ≤ (nullity P N p : ℝ)) : NullityLB P where
  kap := countKap ws N0
  ok := by
    intro N p hN hp hp2 hH
    haveI : Fact p.Prime := ⟨hp⟩
    refine countKap_le N0 N p fun w hw => ?_
    unfold CountPiece.kap
    split_ifs with hc
    · refine Nat.ceil_le.mpr ?_
      exact hpiece w hw N p hc.1 hN hp hp2 hH hc.2.1 hc.2.2
    · exact Nat.zero_le _

/-- **First WinCert clause.**  In a window, past the threshold, the constructed `kap` dominates
the affine bound. -/
theorem countLB_kap_ge (P : Parameters) (ws : List CountPiece) (N0 : ℕ) hpiece
    {w : CountPiece} (hw : w ∈ ws) {N p : ℕ} (hN : N0 ≤ N) (h1 : w.a * N < p)
    (h2 : (p : ℝ) ≤ w.b * N) :
    w.c0 * N + w.c1 * p - 2 ≤ ((countLB P ws N0 hpiece).kap N p : ℝ) := by
  have h : w.kap N0 N p ≤ countKap ws N0 N p := kap_le_countKap hw N0 N p
  have hk : w.kap N0 N p = ⌈w.c0 * N + w.c1 * p - 2⌉₊ := by
    unfold CountPiece.kap; rw [if_pos ⟨hN, h1, h2⟩]
  calc w.c0 * N + w.c1 * p - 2 ≤ (⌈w.c0 * N + w.c1 * p - 2⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (countKap ws N0 N p : ℝ) := by rw [← hk]; exact_mod_cast h

end
end CatalanMeasure.GenD.Signed.Count.NullityConstructor
#print axioms CatalanMeasure.GenD.Signed.Count.NullityConstructor.countLB
#print axioms CatalanMeasure.GenD.Signed.Count.NullityConstructor.countLB_kap_ge

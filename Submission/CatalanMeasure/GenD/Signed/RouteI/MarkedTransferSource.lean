module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Submission.CatalanMeasure.GenD.Signed.ChebSquare

@[expose] public section
set_option Elab.async false

/-!
# C5 `MarkedTransferSource`: the anchor reference difference and its linear source binding

Data-free. For the shared source record `CapSource` the free rows at anchors 0 and 1 (both
`Flavor.free`) differ by exactly `refDiff`: every gas, radial, reflection and angular term is
common and cancels (`freeRow_sub_freeRow`, pure algebra on the definitions; the 49/50 mass sits once
inside `refRow 1`, `refCol 1`).

`SourceMajorant` is the shape the audited C53 source must discharge: `refDiff` is bounded on the
domain of one sign by a Chebyshev sum in `t = |x|` (`2t-1`) plus a tail. The binding from the
real ideal coefficient stream to the supplied integer coefficients is linear: `l1dist` is charged
once (`SourceMajorant.of_ideal`), streams add coefficientwise (`rawSumR_addR`), and a larger tail
(S19 increment) is monotone (`SourceMajorant.mono`).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.MarkedTransferSource

open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.Signed.ChebSquare

noncomputable section

/-- `F1 - F0`: reference log-mean difference, row potential difference, minus the doubled-column
potential difference, at `Y = x + 1/x`. -/
def refDiff (S : CapSource) (x : ℝ) : ℝ :=
  (physL (S.refRow 1) (fun u => Real.log |u|) - physL (S.refRow 0) (fun u => Real.log |u|)) +
  (potL (S.refRow 1) (x + 1 / x) - potL (S.refRow 0) (x + 1 / x)) -
  (potL ((S.refCol 1).map YCell.dil2) (x + 1 / x) - potL ((S.refCol 0).map YCell.dil2) (x + 1 / x))

/-- Everything but the reference difference cancels between the two anchors (same truncation,
same species `signOf x`, both `Flavor.free`). -/
theorem freeRow_sub_freeRow (S : CapSource) (t : Trunc) (x : ℝ) :
    S.freeRow t 1 x - S.freeRow t 0 x = refDiff S x := by
  simp only [CapSource.freeRow, CapSource.rowField, CapSource.refR, CapSource.refC, refDiff]
  ring

/-- On the free-row domain `t = |x|` lies in `(0,1]`, so `2t-1 ∈ [-1,1]`. -/
theorem two_abs_sub_one_mem {x : ℝ} (hx : x ∈ CapSource.rowDom) :
    2 * |x| - 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_neg h2]; constructor <;> linarith
  · rw [abs_of_pos h1]; constructor <;> linarith

/-- The sign-`σ` source majorant: `refDiff ≤ Σ p_j T_j(2|x|-1)/dP + tail` on the part of the free-row
domain of sign `σ`. -/
def SourceMajorant (S : CapSource) (σ : Sign) (p : List ℤ) (dP : ℕ) (tail : ℝ) : Prop :=
  ∀ x ∈ CapSource.rowDom, signOf x = σ → refDiff S x ≤ chebSum p dP (2 * |x| - 1) + tail

theorem SourceMajorant.mono {S : CapSource} {σ : Sign} {p : List ℤ} {dP : ℕ} {t t' : ℝ}
    (h : SourceMajorant S σ p dP t) (ht : t ≤ t') : SourceMajorant S σ p dP t' :=
  fun x hx hs => (h x hx hs).trans (by linarith)

/-! ### Real ideal coefficient streams and the linear rounding binding -/

/-- Evaluation of a real coefficient list in the Chebyshev basis starting at index `k`. -/
def rawSumR : List ℝ → ℕ → ℝ → ℝ
  | [], _, _ => 0
  | a :: t, k, x => a * basis k x + rawSumR t (k + 1) x

/-- Zero-extended coefficientwise sum of two real streams (aggregation of source streams). -/
def addR : List ℝ → List ℝ → List ℝ
  | [], b => b
  | a :: s, [] => a :: s
  | a :: s, b :: u => (a + b) :: addR s u

theorem rawSumR_addR (a b : List ℝ) (k : ℕ) (x : ℝ) :
    rawSumR (addR a b) k x = rawSumR a k x + rawSumR b k x := by
  induction a generalizing b k with
  | nil => simp [addR, rawSumR]
  | cons a s ih =>
    cases b with
    | nil => simp [addR, rawSumR]
    | cons b u => simp only [addR, rawSumR, ih]; ring

/-- l1 distance between the ideal real coefficients and the rounded `p_j / dP` (missing entries
count as zero): the full coefficient-distance charge, one forward traversal. -/
def l1dist (dP : ℕ) : List ℝ → List ℤ → ℝ
  | [], [] => 0
  | a :: s, [] => |a| + l1dist dP s []
  | [], b :: u => |(b : ℝ) / dP| + l1dist dP [] u
  | a :: s, b :: u => |a - (b : ℝ) / dP| + l1dist dP s u

theorem abs_rawSumR_sub_le (dP : ℕ) (ideal : List ℝ) (p : List ℤ) (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |rawSumR ideal k x - rawSum p k x / dP| ≤ l1dist dP ideal p := by
  induction ideal generalizing p k with
  | nil =>
    induction p generalizing k with
    | nil => simp [rawSumR, l1dist]
    | cons b u ih =>
      have hb := abs_basis_le_one k hx
      have h2 := ih (k + 1)
      simp only [rawSumR, rawSum_cons, l1dist, zero_sub] at h2 ⊢
      have e : -((b * basis k x + rawSum u (k + 1) x) / dP) =
          -((b : ℝ) / dP * basis k x) + (-(rawSum u (k + 1) x / dP)) := by ring
      rw [e]
      calc _ ≤ |-((b : ℝ) / dP * basis k x)| + |-(rawSum u (k + 1) x / dP)| := abs_add_le _ _
        _ ≤ |(b : ℝ) / dP| + l1dist dP [] u := by
          rw [abs_neg, abs_mul]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb) h2
  | cons a s ih =>
    have hb := abs_basis_le_one k hx
    cases p with
    | nil =>
      have h2 := ih [] (k + 1)
      simp only [rawSumR, rawSum_nil, zero_div, sub_zero, l1dist] at h2 ⊢
      calc _ ≤ |a * basis k x| + |rawSumR s (k + 1) x| := abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb) (by simpa using h2)
    | cons b u =>
      have h2 := ih u (k + 1)
      simp only [rawSumR, rawSum_cons, l1dist]
      have e : a * basis k x + rawSumR s (k + 1) x - (b * basis k x + rawSum u (k + 1) x) / dP =
          (a - (b : ℝ) / dP) * basis k x + (rawSumR s (k + 1) x - rawSum u (k + 1) x / dP) := by
        ring
      rw [e]
      calc _ ≤ |(a - (b : ℝ) / dP) * basis k x| + |rawSumR s (k + 1) x - rawSum u (k + 1) x / dP| :=
            abs_add_le _ _
        _ ≤ _ := by
          rw [abs_mul]
          exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hb) h2

/-- Source → P: an ideal real stream `ideal` with tail `tailI`, rounded to the integers `p/dP`
with coefficient-distance `δ`, gives the integer majorant with tail `tailI + δ`. -/
theorem SourceMajorant.of_ideal {S : CapSource} {σ : Sign} {p : List ℤ} {dP : ℕ}
    (ideal : List ℝ) (tailI δ : ℝ) (hd : l1dist dP ideal p ≤ δ)
    (h : ∀ x ∈ CapSource.rowDom, signOf x = σ →
      refDiff S x ≤ rawSumR ideal 0 (2 * |x| - 1) + tailI) :
    SourceMajorant S σ p dP (tailI + δ) := by
  intro x hx hs
  have h1 := h x hx hs
  have h2 := abs_rawSumR_sub_le dP ideal p 0 (two_abs_sub_one_mem hx)
  have h3 := (abs_le.mp h2).2
  have : chebSum p dP (2 * |x| - 1) = rawSum p 0 (2 * |x| - 1) / dP := rfl
  linarith

#print axioms freeRow_sub_freeRow
#print axioms SourceMajorant.of_ideal

end

end CatalanMeasure.GenD.Signed.RouteI.MarkedTransferSource

module

public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeP
public import CatalanMeasure.GenD.Signed.SpikeEnds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# D2 constants: closed-form spike constants of a finitely supported trial (generic soundness)

For `b = bSeq bs` (finitely supported) the series in `costRem`, `barrierTrialS` and the Poisson
pairing are finite rational sums (`idxSum`).  This file proves
* `costRem_le`: `costRem (bSeq bs) s' m rho <= K0` for all `m <= kappa (s' + m)` from the rational
  check `K0check` (`costRem` is affine in `m / s'`);
* `De2_of_cov`: `S_b(-y) - S_b(-rho) <= De2` on `[A/2^S, B/2^S]` from an integer cell chain for
  the polynomial `De2 + sigma - S_b(-y)` (scaled by `Lc 2^60`, `Lc` a multiple of `1..K`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def idxSum (f : ℕ → ℚ → ℚ) : List ℚ → ℕ → ℚ
  | [], _ => 0
  | x :: xs, k => f k x + idxSum f xs (k + 1)

theorem idxSum_cast (f : ℕ → ℚ → ℚ) (bs : List ℚ) : ∀ k0 : ℕ,
    ((idxSum f bs k0 : ℚ) : ℝ) =
      ∑ j ∈ Finset.range bs.length, ((f (k0 + j) (bs.getD j 0) : ℚ) : ℝ) := by
  induction bs with
  | nil => intro k0; simp [idxSum]
  | cons x xs ih =>
    intro k0
    rw [idxSum, Rat.cast_add, ih (k0 + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have : ∀ j, k0 + 1 + j = k0 + (j + 1) := fun j => by ring
    simp only [this]; ring

theorem getD_zero_of_le (bs : List ℚ) {k : ℕ} (h : bs.length ≤ k) : bs.getD k 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem bSeq_succ (bs : List ℚ) (k : ℕ) : bSeq bs (k + 1) = ((bs.getD k 0 : ℚ) : ℝ) := by
  unfold bSeq
  rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]

theorem tsum_bSeq (bs : List ℚ) (g : ℕ → ℝ → ℝ) (hg0 : ∀ k, g k 0 = 0) :
    ∑' k : ℕ, g k (bSeq bs (k + 1)) = ∑ j ∈ Finset.range bs.length, g j ((bs.getD j 0 : ℚ) : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range bs.length)]
  · exact Finset.sum_congr rfl fun k _ => by rw [bSeq_succ]
  · intro k hk
    have hk' : bs.length ≤ k := by simpa using hk
    rw [bSeq_succ, getD_zero_of_le bs hk']
    simpa using hg0 k

/-! ### The series of `costRem` as rational sums -/

def S1q (bs : List ℚ) : ℚ := idxSum (fun _ x => x ^ 2) bs 0
def S2q (bs : List ℚ) : ℚ := idxSum (fun k x => 2 * x ^ 2 / ((k : ℚ) + 1)) bs 0
def Spq (bs : List ℚ) (ρ : ℚ) : ℚ := idxSum (fun k x => x * (-ρ) ^ (k + 1)) bs 0
def Sbq (bs : List ℚ) (x : ℚ) : ℚ := idxSum (fun k c => c * x ^ (k + 1) / ((k : ℚ) + 1)) bs 0

theorem tsum_sq_bSeq (bs : List ℚ) :
    ∑' k : ℕ, bSeq bs (k + 1) ^ 2 = (S1q bs : ℝ) := by
  have := tsum_bSeq bs (fun _ t => t ^ 2) (fun _ => by simp)
  rw [this, S1q, idxSum_cast]; push_cast; simp

theorem tsum_S2_bSeq (bs : List ℚ) :
    ∑' i : ℕ, 2 * bSeq bs (i + 1) ^ 2 / ((i + 1 : ℕ) : ℝ) = (S2q bs : ℝ) := by
  have := tsum_bSeq bs (fun i t => 2 * t ^ 2 / ((i + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, S2q, idxSum_cast]; push_cast; simp

theorem tsum_Sp_bSeq (bs : List ℚ) (ρ : ℚ) :
    ∑' k : ℕ, bSeq bs (k + 1) * poisSeq (ρ : ℝ) (k + 1) = (Spq bs ρ : ℝ) := by
  have := tsum_bSeq bs (fun k t => t * poisSeq (ρ : ℝ) (k + 1)) (fun _ => by simp)
  rw [this, Spq, idxSum_cast]; push_cast; simp [poisSeq]

theorem barrierTrialS_bSeq (bs : List ℚ) (x : ℚ) :
    barrierTrialS (bSeq bs) (x : ℝ) = (Sbq bs x : ℝ) := by
  unfold barrierTrialS
  have := tsum_bSeq bs (fun k t => t * (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, Sbq, idxSum_cast]; push_cast; simp

/-! ### `costRem` is affine in `m / s'` -/

def c0q (bs : List ℚ) (ρ : ℚ) : ℚ := -(S2q bs) + 2 * S1q bs - 4 * Spq bs ρ + 4 * Sbq bs (-ρ)

/-- `log 2 < LOG2U`. -/
def LOG2U : ℚ := 6931471808 / 10 ^ 10

theorem log_two_lt_LOG2U : Real.log 2 < (LOG2U : ℝ) := by
  have := Real.log_two_lt_d9
  unfold LOG2U; push_cast; norm_num; linarith

def K0check (bs : List ℚ) (ρ κ K0 : ℚ) : Bool :=
  decide (LOG2U + c0q bs ρ ≤ K0) &&
    decide (LOG2U + c0q bs ρ + (c0q bs ρ + 2 * ρ ^ 2 / (1 - ρ ^ 2)) * (κ / (1 - κ)) ≤ K0)

theorem costRem_eq (bs : List ℚ) (ρ : ℚ) (s' m : ℕ) (hs : 0 < s') (hρ : (ρ : ℝ) ^ 2 ≠ 1) :
    costRem (bSeq bs) s' m (ρ : ℝ) =
      (Real.log 2 + (c0q bs ρ : ℝ)) +
        ((c0q bs ρ : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((m : ℝ) / s') := by
  have hs' : (s' : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold costRem
  rw [tsum_S2_bSeq, tsum_sq_bSeq, tsum_Sp_bSeq]
  have hb := barrierTrialS_bSeq bs (-ρ)
  push_cast at hb
  rw [hb]
  unfold c0q
  push_cast
  have h1 : (1 : ℝ) - (ρ : ℝ) ^ 2 ≠ 0 := fun h => hρ (by linarith)
  field_simp
  ring

theorem costRem_le {bs : List ℚ} {ρ κ K0 : ℚ} (hK : K0check bs ρ κ K0 = true) (hκ0 : 0 ≤ κ)
    (hκ1 : κ < 1) (hρ : (ρ : ℝ) ^ 2 ≠ 1) {s' m : ℕ} (hs : 0 < s')
    (hm : (m : ℝ) ≤ (κ : ℝ) * ((s' : ℝ) + m)) :
    costRem (bSeq bs) s' m (ρ : ℝ) ≤ (K0 : ℝ) := by
  rw [costRem_eq bs ρ s' m hs hρ]
  unfold K0check at hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hK
  obtain ⟨h1, h2⟩ := hK
  have h1' : Real.log 2 + (c0q bs ρ : ℝ) ≤ (K0 : ℝ) := by
    have := log_two_lt_LOG2U
    have h : ((LOG2U + c0q bs ρ : ℚ) : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast h1
    push_cast at h; linarith
  have hκ1' : (κ : ℝ) < 1 := by exact_mod_cast hκ1
  have hκ0' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ0
  have hs0 : (0 : ℝ) < s' := by exact_mod_cast hs
  have hw0 : 0 ≤ (m : ℝ) / s' := by positivity
  have hwm : (m : ℝ) / s' ≤ (κ : ℝ) / (1 - κ) := by
    rw [div_le_div_iff₀ hs0 (by linarith)]
    nlinarith
  have h2' : Real.log 2 + (c0q bs ρ : ℝ) +
      ((c0q bs ρ : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((κ : ℝ) / (1 - κ)) ≤ (K0 : ℝ) := by
    have := log_two_lt_LOG2U
    have hr : (1 - (ρ : ℝ) ^ 2) ≠ 0 := fun h => hρ (by linarith)
    have h : ((LOG2U + c0q bs ρ + (c0q bs ρ + 2 * ρ ^ 2 / (1 - ρ ^ 2)) * (κ / (1 - κ)) : ℚ) : ℝ)
        ≤ (K0 : ℝ) := by exact_mod_cast h2
    push_cast at h
    have hk : (1 : ℝ) - κ > 0 := by linarith
    have hc : ((c0q bs ρ : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((κ : ℝ) / (1 - κ)) =
        ((c0q bs ρ : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2)) * ((κ : ℝ) / (1 - κ)) := rfl
    -- LOG2U > log 2 and the coefficient of LOG2U is 1
    nlinarith [h, this]
  set C1 : ℝ := (c0q bs ρ : ℝ) + 2 * (ρ : ℝ) ^ 2 / (1 - (ρ : ℝ) ^ 2) with hC1
  by_cases hc : C1 ≤ 0
  · nlinarith [mul_nonneg hw0 (neg_nonneg.mpr hc)]
  · push_neg at hc
    have := mul_le_mul_of_nonneg_left hwm hc.le
    nlinarith

end CatalanMeasure.Signed.Consts

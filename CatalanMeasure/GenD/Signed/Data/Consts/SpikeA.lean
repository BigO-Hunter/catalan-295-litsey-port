module

public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeC

/-!
# D2 constants: absolute sums of a finitely supported trial (`hA`, `hA1`, `hB1`)

* `tsum_abs_bSeq`: `sum' |b_j| = sum_k |bs_k|` (exact rational sum `absq`);
* `abs_barrierTrialS_le`: `|S_b(x)| <= sum_k |bs_k| / (k+1)` for `|x| <= 1` (`absSq`), the crude
  phantom bounds `A1`, `B1` of `SpikeTrialCert`.
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Cert OAI.InternalCatalan CatalanMeasure.Signed

def absq (as : List ℚ) : ℚ := idxSum (fun _ x => |x|) as 0
def absSq (as : List ℚ) : ℚ := idxSum (fun k x => |x| / ((k : ℚ) + 1)) as 0

theorem bSeq_zero (as : List ℚ) : bSeq as 0 = 0 := by simp [bSeq]

theorem tsum_abs_bSeq (as : List ℚ) : ∑' j : ℕ, |bSeq as j| = (absq as : ℝ) := by
  have hs : Summable (fun j : ℕ => |bSeq as j|) := by
    refine summable_of_ne_finset_zero (s := Finset.range (as.length + 1)) fun j hj => ?_
    have hj' : as.length + 1 ≤ j := by simpa using hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : as.length ≤ k := by omega
    rw [bSeq_succ, getD_zero_of_le as hk]; simp
  rw [hs.tsum_eq_zero_add, bSeq_zero, abs_zero, zero_add]
  have := tsum_bSeq as (fun _ t => |t|) (fun _ => by simp)
  rw [this, absq, idxSum_cast]
  push_cast
  simp

theorem abs_barrierTrialS_le (as : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |barrierTrialS (bSeq as) x| ≤ (absSq as : ℝ) := by
  unfold barrierTrialS
  have := tsum_bSeq as (fun k t => t * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) (fun _ => by simp)
  rw [this, absSq, idxSum_cast]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hxp : |x| ^ (j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hc0 : 0 ≤ |((as.getD j 0 : ℚ) : ℝ)| := abs_nonneg _
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hj]
  push_cast
  simp only [zero_add]
  have hj' : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  refine div_le_div_of_nonneg_right ?_ hj'.le
  calc |((as.getD j 0 : ℚ) : ℝ)| * |x| ^ (j + 1) ≤ |((as.getD j 0 : ℚ) : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left hxp hc0
    _ = |((as.getD j 0 : ℚ) : ℝ)| := mul_one _

/-- Bool form of the divisibility hypothesis of `De2_of_cov`. -/
theorem divAll {Lc : ℤ} {n : ℕ}
    (h : (List.range n).all (fun i => decide ((((i : ℕ) : ℤ) + 1) ∣ Lc)) = true) :
    ∀ i < n, (((i : ℕ) : ℤ) + 1) ∣ Lc := by
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this

end CatalanMeasure.Signed.Consts

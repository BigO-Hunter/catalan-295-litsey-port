module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell2,kappa0,markedP cubic. Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [21868450160462394832153883141757143, 132754583271786199487991268207755264, 553903557517154253058877881181011968, -87788082519181287751680000000000000]
def MP : List ℤ := raw_ints% [5651480290167608185549540337120589248, 10662503325574555203624777670589587776, 6322815763157358999581405854541455680, 1399580810269593269257848521072457152]
theorem mob_checked : mobCell ns 2 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-21868450160462394832153883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^2) (((1 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-21868450160462394832153883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudgetPilot.condition

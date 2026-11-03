module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row56
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [58658813539490632666982474679277009, 554417269092320435423995634103877632, -425149238460352550250081059409494016, -2705733928634139279360000000000000]
def MP : List ℤ := raw_ints% [14671482990686940506018561720245908544, 41978629289092945026625371965627587776, 38225978248711853498518574532879473856, 10921537684234483117191124287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-58658813539490632666982474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-58658813539490632666982474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row56
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row56.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row56.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row56.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row57
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [15514724172885949648742474679277009, 130769467700860901640955634103877632, 474820409747943269095838940590505984, 0]
def MP : List ℤ := raw_ints% [12774691869459341935563521720245908544, 28634637569197159074901851965627587776, 20844481169008065419496494532879473856, 4984535469270248280158164287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-15514724172885949648742474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-15514724172885949648742474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row57
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row57.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row57.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row57.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row58
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [11382653182657556483942474679277009, 66376585414420618463995634103877632, 276951778758577126529438940590505984, -43894041259590643875840000000000000]
def MP : List ℤ := raw_ints% [6932616667012052279284481720245908544, 15831324669383280644468571965627587776, 11709242205207169093946414532879473856, 2854428244095531372638164287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-11382653182657556483942474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-11382653182657556483942474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row58
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row58.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row58.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row58.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row59
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [59156886452295865306982474679277009, 554416562870847954143995634103877632, -425149238460352550250081059409494016, -2705733928634139279360000000000000]
def MP : List ℤ := raw_ints% [14703337058019355994018561720245908544, 42074202790633751191105371965627587776, 38321563049796219363478574532879473856, 10953403051110458305671124287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-59156886452295865306982474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556292983043807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-59156886452295865306982474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556292983043807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row59
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row59.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row59.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row59.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row60
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell2,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [30132592140919181161753883141757143, 261540347844666765841911268207755264, 949640819495886538191677881181011968, 0]
def MP : List ℤ := raw_ints% [9911694740517042000589540337120589248, 17953312100069365442764617670589587776, 9970103256571151036527325854541455680, 1928485897018827594352248521072457152]
theorem mob_checked : mobCell ns 2 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-30132592140919181161753883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^2) (((1 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-30132592140919181161753883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row60
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row60.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row60.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row60.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row62
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell2,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [117416916699739012478233883141757143, 1108834538184640870847991268207755264, -850298476920705100500162118818988032, -5411467857268278558720000000000000]
def MP : List ℤ := raw_ints% [21849429904197462051615460337120589248, 54625559320575577860955977670589587776, 40285400617304144329388765854541455680, 7514682668783296798606968521072457152]
theorem mob_checked : mobCell ns 2 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-117416916699739012478233883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^2) (((1 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-117416916699739012478233883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row62
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row62.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row62.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row62.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row63
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell2,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [31128737966529646441753883141757143, 261538935401721803281911268207755264, 949640819495886538191677881181011968, 0]
def MP : List ℤ := raw_ints% [9975425474268992377549540337120589248, 18144526900412335974604617670589587776, 10161340656001240969327325854541455680, 1992239229857897372272248521072457152]
theorem mob_checked : mobCell ns 2 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-31128737966529646441753883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^2) (((1 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-31128737966529646441753883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row63
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row63.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row63.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row63.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row64
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell2,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [22864595986072860112153883141757143, 132753170828841236927991268207755264, 553903557517154253058877881181011968, -87788082519181287751680000000000000]
def MP : List ℤ := raw_ints% [5715211023919558562509540337120589248, 10853718125917525735464777670589587776, 6514053162587448932381405854541455680, 1463334143108663047177848521072457152]
theorem mob_checked : mobCell ns 2 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-22864595986072860112153883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^2) (((1 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-22864595986072860112153883141757143/191255842556220631154688000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((191255842556220631154688000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row64
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row64.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row64.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget07.Row64.condition

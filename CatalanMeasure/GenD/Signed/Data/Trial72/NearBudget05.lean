module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row40
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [1635172074340929982145795077469433233408, 4788006286061721437833998652085964374016, 4670970893601906660162983534481176002560, 1518136681881115204474779959864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row40
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row40.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row40.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row40.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row41
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [3401703814683898439656051717469433233408, 9205931011372508297299439932085964374016, 8206427432914009597686634094481176002560, 2402200237752341015559026999864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row41
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row41.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row41.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row41.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row42
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [535765612385807772857284919864644861952, 1428637080973556788600013024706693169152, 1250496314455612949012579872536998707200, 357624845867863933269851767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row42
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row42.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row42.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row42.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row43
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [473710297194863629653915959864644861952, 1304570895756337461645312224706693169152, 1188485444429337765261248032536998707200, 357624845867863933269851767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row43
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row43.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row43.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row43.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row44
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [1357773853066089440738162999864644861952, 3073495691671589390627143904706693169152, 2073346682946422607643051552536998707200, 357624845867863933269851767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row44
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row44.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row44.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row44.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row45
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [1580191997072059347678148919864644861952, 4561915382902003893640397024706693169152, 4383773764253752434630755872536998707200, 1402050378423807888668507767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row45
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row45.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row45.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row45.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row46
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [1518136681881115204474779959864644861952, 4437849197684784566685696224706693169152, 4321762894227477250879424032536998707200, 1402050378423807888668507767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row46
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row46.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row46.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row46.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row47
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell7,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [2402200237752341015559026999864644861952, 6206773993600036495667527904706693169152, 5206624132744562093261227552536998707200, 1402050378423807888668507767694950400000]
theorem mob_checked : mobCell ns 7 (0) (1) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (0) (1) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((0/1 : ℚ) : ℚ) : ℝ) (((1/128 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((0 : ℤ) : ℝ)/2^7) (((1 : ℤ) : ℝ)/2^7) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row47
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row47.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row47.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget05.Row47.condition

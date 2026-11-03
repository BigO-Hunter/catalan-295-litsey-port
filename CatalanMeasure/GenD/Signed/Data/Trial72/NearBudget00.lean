module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row0
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [120530467870345803411129821402966072, 285789857876606285328208374085810344, 218097525672217197679411388924393640, 52838135665956715762332836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row0.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row0.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row0.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row1
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [87473899948518658092729821402966072, 204537349467943404908368374085810344, 154067756922420381356851388924393640, 37004307402995634541212836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row1.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row1.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row1.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row2
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [469667766105625128677049821402966072, 1184961765357093575798608374085810344, 955862061098658282607411388924393640, 240569588788465351266972836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row2.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row2.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row2.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row3
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [124515051172787664531129821402966072, 297743399744305985040208374085810344, 230050859500291013743411388924393640, 56822510928772693234332836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row3
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row3.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row3.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row3.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row4
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [91458483250960519212729821402966072, 216490891335643104620368374085810344, 166021090750494197420851388924393640, 40988682665811612013212836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row4
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row4.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row4.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row4.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row5
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell0,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [473652349408066989797049821402966072, 1196915307224793275510608374085810344, 967815394926732098671411388924393640, 244553964051281328738972836241549368]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row5
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row5.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row5.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row5.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row6
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [422705085327653726098662689932394944, 1029782781285572976726336548998202688, 807668733648268849669453238122562880, 200591037690349599041779379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row6
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row6.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row6.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row6.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row7
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [296034459223965076329702689932394944, 715884038818161318056256548998202688, 558494215628606498760013238122562880, 138644636034410257033459379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row7
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row7.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row7.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget00.Row7.condition

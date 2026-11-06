module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row8
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [1924556710307722810135782689932394944, 4837056951990119515181376548998202688, 3890336592107416728724813238122562880, 977837877366295539460339379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row8
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row8.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row8.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row8.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row9
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [454580087430181545874662689932394944, 1125406955434652901462336548998202688, 903292075638845239813453238122562880, 232465207634373884225779379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row9
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row9.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row9.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row9.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row10
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [327909461326492896105702689932394944, 811508212967241242792256548998202688, 654117557619182888904013238122562880, 170518805978434542217459379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row10
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row10.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row10.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row10.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row11
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell1,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [1956431712410250629911782689932394944, 4932681126139199439917376548998202688, 3985959934097993118868813238122562880, 1009712047310319824644339379056755136]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row11.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row11.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row11.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row12
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [1604728301522796792334235032454041088, 3990602422259510166826244693552933376, 3199456794070798105675320709590428160, 813582673334084731183311048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row12.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row12.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row12.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row13
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [1109157088275282056267675032454041088, 2757230034724343258164484693552933376, 2216647835951198530799160709590428160, 568574889502137328902351048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row13
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row13.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row13.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row13.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row14
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [7822703018930364315682715032454041088, 19640817216756972505672964693552933376, 15793320176471197416523320709590428160, 3975207505585864742314191048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row14
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row14.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row14.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row14.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row15
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [1859721661074991073806235032454041088, 4755579172282078872874244693552933376, 3964430215459352673355320709590428160, 1068572704252264874287311048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row15
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row15.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row15.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget01.Row15.condition

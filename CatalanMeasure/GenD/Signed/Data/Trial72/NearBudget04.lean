module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row32
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell5,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [544292892954040141750422841123036463104, 1383406934085036079181075695570978603008, 1133773611837472067591494199131621294080, 294659572233417405676622464683679154176]
theorem mob_checked : mobCell ns 6 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 6 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/64 : ℚ) : ℚ) : ℝ) (((1/32 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^6) (((2 : ℤ) : ℝ)/2^6) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row32
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row32.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row32.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row32.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row33
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell5,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [265105591125985751164996921123036463104, 749873136800529680569865455570978603008, 704688995056063452836944439131621294080, 219921449381519523432075904683679154176]
theorem mob_checked : mobCell ns 6 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 6 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/64 : ℚ) : ℚ) : ℝ) (((1/32 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^6) (((2 : ℤ) : ℝ)/2^6) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row33
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row33.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row33.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row33.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row34
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell5,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [234011265783510240385256761123036463104, 672181768609009863072552175570978603008, 642567012118115870455519799131621294080, 204396509292616247768224384683679154176]
theorem mob_checked : mobCell ns 6 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 6 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/64 : ℚ) : ℚ) : ℝ) (((1/32 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^6) (((2 : ℤ) : ℝ)/2^6) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row34
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row34.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row34.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row34.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row35
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell5,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [674846510588686945886358841123036463104, 1775067573956399586733331695570978603008, 1525434038676258670288198199131621294080, 425212976835487304957006464683679154176]
theorem mob_checked : mobCell ns 6 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 6 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/64 : ℚ) : ℚ) : ℝ) (((1/32 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^6) (((2 : ℤ) : ℝ)/2^6) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row35
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row35.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row35.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row35.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row36
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [714944358235596993213535237469433233408, 1965135339191079068899946812085964374016, 1785956593341289848543696494481176002560, 535765612385807772857284919864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row36
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row36.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row36.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row36.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row37
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [590744837524370787902723077469433233408, 1654725427742351474526990652085964374016, 1537690887412844316278183534481176002560, 473710297194863629653915959864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row37
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row37.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row37.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row37.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row38
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [2357276577867339245412979717469433233408, 6072650153053138333992431932085964374016, 5073147426724947253801834094481176002560, 1357773853066089440738162999864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row38
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row38.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row38.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row38.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row39
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell6,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [1759371595052156187456607237469433233408, 5098416197510449032206954812085964374016, 4919236599530352192428496494481176002560, 1580191997072059347678148919864644861952]
theorem mob_checked : mobCell ns 7 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 7 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/128 : ℚ) : ℚ) : ℝ) (((1/64 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^7) (((2 : ℤ) : ℝ)/2^7) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row39
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row39.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row39.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget04.Row39.condition

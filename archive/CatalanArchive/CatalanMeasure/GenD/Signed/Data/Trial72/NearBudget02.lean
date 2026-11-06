module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row16
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [1364150447827476337739675032454041088, 3522206784746911964212484693552933376, 2981621257339753098479160709590428160, 823564920420317472006351048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row16
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row16.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row16.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row16.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row17
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell2,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [8077696378482558597154715032454041088, 20405793966779541211720964693552933376, 16558293597859751984203320709590428160, 4230197536504044885418191048491535872]
theorem mob_checked : mobCell ns 3 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 3 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/8 : ℚ) : ℚ) : ℝ) (((1/4 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^3) (((2 : ℤ) : ℝ)/2^3) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row17
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row17.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row17.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row17.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row18
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 10841172903565743969911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [6508661386672677849466488387932286976, 16491149063743857899897914907333578752, 13521187675710018549447437490563665920, 3538699998638838499016010971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9971979318913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row18
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row18.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row18.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row18.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row19
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 7056329762313596524151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [4548599116017098631218808387932286976, 11602104678272149717287994907333578752, 9617730071149719907465997490563665920, 2564224508894668821396810971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792307967010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row19
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row19.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row19.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row19.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row20
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [170528815206462828288007625434375, 61063973714772388173431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [31801660044686917938513528387932286976, 79934189495206341057217594907333578752, 64422997617496272098032397490563665920, 16290469693918124495109450971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-54569220866068105052162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856464267010721243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row20
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row20.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row20.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row20.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row21
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 10841224913472214881911167569100800, 4054606765021018628192052480835584, 0]
def MP : List ℤ := raw_ints% [8548581634018118994298488387932286976, 22610896491244124780921914907333578752, 19640921788674228876999437490563665920, 5578606931448223090376010971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-9972027158913986625781/87960930222080000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-46619096437687797359111/1099511627776000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row21
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row21.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row21.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row21.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row22
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 7056381772220067436151167569100800, 3707378916044772909152052480835584, 0]
def MP : List ℤ := raw_ints% [6588519363362539776050808387932286976, 17721852105772416598311994907333578752, 15737464184113930235017997490563665920, 4604131441704053412756810971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-792313806854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10406918153109205841/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row22.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row22.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row22.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row23
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval0,cell3,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [668549718105224556288007625434375, 61064025724678859085431167569100800, -2524504825500194135967947519164416, -1526941275515781120000000000000]
def MP : List ℤ := raw_ints% [33841580292032359083345528387932286976, 86053936922706607938241594907333578752, 70542731730460482425584397490563665920, 18330376626727509086469450971162374144]
theorem mob_checked : mobCell ns 4 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 4 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/16 : ℚ) : ℚ) : ℝ) (((1/8 : ℚ) : ℚ) : ℝ),
    (((-213935909793671858012162440139/30600934808995300984750080000000000 : ℚ) : ℚ) : ℝ) + (((-6856470106854471243/10737418240000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((7086493096890794159/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((3429/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^4) (((2 : ℤ) : ℝ)/2^4) := by
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row23
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row23.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row23.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget02.Row23.condition

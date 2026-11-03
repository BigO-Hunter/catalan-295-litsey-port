module

public import CatalanMeasure.GenD.Signed.Data.Consts.ShareP
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row48
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [6980856260000838729519327019120759, 130770173922333382920955634103877632, 474820409747943269095838940590505984, 0]
def MP : List ℤ := raw_ints% [4900571519442219925970511213708035000, 10380070584653780093460999579984546600, 7008067430476786947202143400026000168, 1528568365265226779711655033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-6980856260000838729519327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-6980856260000838729519327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row48
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row48.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row48.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row48.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row49
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [2848785269772445564719327019120759, 66377291635893099743995634103877632, 276951778758577126529438940590505984, -43894041259590643875840000000000000]
def MP : List ℤ := raw_ints% [2418270515237216223698511213708035000, 5300416644214546986394119579984546600, 3636561052677055691496543400026000168, 798308964959315572676775033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-2848785269772445564719327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-2848785269772445564719327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row49
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row49.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row49.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row49.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row50
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa0,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [50623018539410754387759327019120759, 554417269092320435423995634103877632, -425149238460352550250081059409494016, -2705733928634139279360000000000000]
def MP : List ℤ := raw_ints% [1417482521941956002258511213708035000, 5468441204283016338432519579984546600, 5817901962247654733913183400026000168, 1769649013835228537018535033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-50623018539410754387759327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-50623018539410754387759327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556294965465682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row50
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row50.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row50.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row50.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row51
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa1/2,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [7478929172806071369519327019120759, 130769467700860901640955634103877632, 474820409747943269095838940590505984, 0]
def MP : List ℤ := raw_ints% [4904550452972881936850511213708035000, 10392010210131656051220999579984546600, 7020009880840552830082143400026000168, 1532550123681778715711655033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-7478929172806071369519327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-7478929172806071369519327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014249745198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row51
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row51.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row51.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row51.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row52
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa1/2,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [3346858182577678204719327019120759, 66376585414420618463995634103877632, 276951778758577126529438940590505984, -43894041259590643875840000000000000]
def MP : List ℤ := raw_ints% [2422249448767878234578511213708035000, 5312356269692422944154119579984546600, 3648503503040821574376543400026000168, 802290723375867508676775033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-3346858182577678204719327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-3346858182577678204719327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186324545543807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row52
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row52.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row52.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row52.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row53
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell0,kappa1/2,markedS polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [51121091452215987027759327019120759, 554416562870847954143995634103877632, -425149238460352550250081059409494016, -2705733928634139279360000000000000]
def MP : List ℤ := raw_ints% [1421461455472618013138511213708035000, 5480380829760892296192519579984546600, 5829844412611420616793183400026000168, 1773630772251780473018535033749488568]
theorem mob_checked : mobCell ns 1 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 1 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/2 : ℚ) : ℚ) : ℝ) (((1/1 : ℚ) : ℚ) : ℝ),
    (((-51121091452215987027759327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556292983043807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^1) (((2 : ℤ) : ℝ)/2^1) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-51121091452215987027759327019120759/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-1556292983043807958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((2386857900262258609743/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((12152349/429496729600 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row53
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row53.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row53.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row53.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row54
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa0,markedN polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [15016651260080717008742474679277009, 130770173922333382920955634103877632, 474820409747943269095838940590505984, 0]
def MP : List ℤ := raw_ints% [12742837802126926447563521720245908544, 28539064067656352910421851965627587776, 20748896367923699554536494532879473856, 4952670102394273091678164287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-15016651260080717008742474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-15016651260080717008742474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-6014282225198095545768537/4398046511104000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-10918789295961258705195797/2199023255552000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((0/1 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row54
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row54.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row54.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row54.condition

namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row55
open CatalanMeasure.Signed.Consts CatalanMeasure.CellCert
noncomputable section
/-! Actual interval1,cell1,kappa0,markedP polynomial (quadratic padded with zero when needed). Frozen near-budget-conditions SHA256 96bc4fab693a8bae451147c4aa68b39df152a2550eb3428db8c1c25b2c3a0674. This proves one listed polynomial condition, not the final four budget outputs. -/
def ns : List ℤ := raw_ints% [10884580269852323843942474679277009, 66377291635893099743995634103877632, 276951778758577126529438940590505984, -43894041259590643875840000000000000]
def MP : List ℤ := raw_ints% [6900762599679636791284481720245908544, 15735751167842474479988571965627587776, 11613657404122803228986414532879473856, 2822562877219556184158164287497794624]
theorem mob_checked : mobCell ns 2 (1) (2) = MP := by
  -- kcost: 0.010 s estimated; fewer than100 integer transform operations, degree3.
  decide +kernel

theorem positive_checked : (shareN MP 3 2 (1) (2) 1 0 0 1 0).all (fun n => decide (0 ≤ n)) = true := by
  -- kcost: 0.010 s estimated; fewer than100 integer operations,5 comparisons.
  decide +kernel

theorem condition : ∀ x ∈ Set.Icc (((1/4 : ℚ) : ℚ) : ℝ) (((1/2 : ℚ) : ℚ) : ℝ),
    (((-10884580269852323843942474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
    (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3 ≤ 0 := by
  intro x hx
  have hx' : x ∈ Set.Icc (((1 : ℤ) : ℝ)/2^2) (((2 : ℤ) : ℝ)/2^2) := by
    norm_num at hx ⊢
    exact hx
  have h := share_cell_Icc (Pn := ns) (MP := MP) (m := 3)
    (by decide +kernel) mob_checked (by decide +kernel) positive_checked hx'
  simp only [Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, mul_one, sub_zero] at h
  have he : zv ns x = (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) *
      -((((-10884580269852323843942474679277009/95627921278110315577344000000000000000 : ℚ) : ℚ) : ℝ) + (((-186326527965682958893/268435456000000000000000 : ℚ) : ℚ) : ℝ)*x +
      (((-1554852934737741390257/536870912000000000000000 : ℚ) : ℚ) : ℝ)*x^2 + (((98571353/214748364800 : ℚ) : ℚ) : ℝ)*x^3) := by
    norm_num [ns, zv_cons, zv_nil]
    ring
  rw [he] at h
  have hd : (0 : ℝ) < (((95627921278110315577344000000000000000/1 : ℚ) : ℚ) : ℝ) := by norm_num
  have hp := (mul_nonneg_iff_of_pos_left hd).mp h
  linarith

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row55
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row55.mob_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row55.positive_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearBudget06.Row55.condition

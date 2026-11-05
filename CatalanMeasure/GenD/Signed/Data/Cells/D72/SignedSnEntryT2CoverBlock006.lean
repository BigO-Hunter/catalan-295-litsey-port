module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core095
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core103
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2End01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core109
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell096 : ∀ y ∈ Icc ((((-1250031102988653 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-3071716865061 : ℚ) / 13743895347200) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P095Lo : ℝ) (ceSignedSnEntryT2P095Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P095Lo, ceSignedSnEntryT2P095Hi, SignedSnEntryT2Core095Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P095Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core095Literal.q2] at h ⊢
  exact h

private theorem cell097 : ∀ y ∈ Icc ((((-3071716865061 : ℚ) / 13743895347200) : ℚ) : ℝ) ((((-4893402627133347 : ℚ) / 21990232555520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P096Lo : ℝ) (ceSignedSnEntryT2P096Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P096Lo, ceSignedSnEntryT2P096Hi, SignedSnEntryT2Core096Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P096Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core096Literal.q2] at h ⊢
  exact h

private theorem cell098 : ∀ y ∈ Icc ((((-4893402627133347 : ℚ) / 21990232555520000) : ℚ) : ℝ) ((((-9765460897302441 : ℚ) / 43980465111040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P097Lo : ℝ) (ceSignedSnEntryT2P097Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P097Lo, ceSignedSnEntryT2P097Hi, SignedSnEntryT2Core097Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P097Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core097Literal.q2] at h ⊢
  exact h

private theorem cell099 : ∀ y ∈ Icc ((((-9765460897302441 : ℚ) / 43980465111040000) : ℚ) : ℝ) ((((-1944554436674787 : ℚ) / 8796093022208000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P098Lo : ℝ) (ceSignedSnEntryT2P098Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P098Lo, ceSignedSnEntryT2P098Hi, SignedSnEntryT2Core098Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P098Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core098Literal.q2] at h ⊢
  exact h

private theorem cell100 : ∀ y ∈ Icc ((((-1944554436674787 : ℚ) / 8796093022208000) : ℚ) : ℝ) ((((-4850713913204841 : ℚ) / 21990232555520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P099Lo : ℝ) (ceSignedSnEntryT2P099Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P099Lo, ceSignedSnEntryT2P099Hi, SignedSnEntryT2Core099Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P099Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core099Literal.q2] at h ⊢
  exact h

private theorem cell101 : ∀ y ∈ Icc ((((-4850713913204841 : ℚ) / 21990232555520000) : ℚ) : ℝ) ((((-1207342389060147 : ℚ) / 5497558138880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P100Lo : ℝ) (ceSignedSnEntryT2P100Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P100Lo, ceSignedSnEntryT2P100Hi, SignedSnEntryT2Core100Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P100Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core100Literal.q2] at h ⊢
  exact h

private theorem cell102 : ∀ y ∈ Icc ((((-1207342389060147 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-2393340421156041 : ℚ) / 10995116277760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P101Lo : ℝ) (ceSignedSnEntryT2P101Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P101Lo, ceSignedSnEntryT2P101Hi, SignedSnEntryT2Core101Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P101Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core101Literal.q2] at h ⊢
  exact h

private theorem cell103 : ∀ y ∈ Icc ((((-2393340421156041 : ℚ) / 10995116277760000) : ℚ) : ℝ) ((((-592999016047947 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P102Lo : ℝ) (ceSignedSnEntryT2P102Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P102Lo, ceSignedSnEntryT2P102Hi, SignedSnEntryT2Core102Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P102Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core102Literal.q2] at h ⊢
  exact h

private theorem cell104 : ∀ y ∈ Icc ((((-592999016047947 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-285827329541847 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P103Lo : ℝ) (ceSignedSnEntryT2P103Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P103Lo, ceSignedSnEntryT2P103Hi, SignedSnEntryT2Core103Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P103Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core103Literal.q2] at h ⊢
  exact h

private theorem cell105 : ∀ y ∈ Icc ((((-285827329541847 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-132241486288797 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P104Lo : ℝ) (ceSignedSnEntryT2P104Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P104Lo, ceSignedSnEntryT2P104Hi, SignedSnEntryT2Core104Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P104Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core104Literal.q2] at h ⊢
  exact h

private theorem cell106 : ∀ y ∈ Icc ((((-132241486288797 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-243138615613341 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P105Lo : ℝ) (ceSignedSnEntryT2P105Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P105Lo, ceSignedSnEntryT2P105Hi, SignedSnEntryT2Core105Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P105Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core105Literal.q2] at h ⊢
  exact h

private theorem cell107 : ∀ y ∈ Icc ((((-243138615613341 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-464932874262429 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P106Lo : ℝ) (ceSignedSnEntryT2P106Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P106Lo, ceSignedSnEntryT2P106Hi, SignedSnEntryT2Core106Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P106Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core106Literal.q2] at h ⊢
  exact h

private theorem cell108 : ∀ y ∈ Icc ((((-464932874262429 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-181704278312121 : ℚ) / 1099511627776000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P107Lo : ℝ) (ceSignedSnEntryT2P107Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P107Lo, ceSignedSnEntryT2P107Hi, SignedSnEntryT2Core107Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P107Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core107Literal.q2] at h ⊢
  exact h

private theorem cell109 : ∀ y ∈ Icc ((((-181704278312121 : ℚ) / 1099511627776000) : ℚ) : ℝ) ((((-103281 : ℚ) / 640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P108Lo : ℝ) (ceSignedSnEntryT2P108Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P108Lo, ceSignedSnEntryT2P108Hi, SignedSnEntryT2Core108Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P108Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core108Literal.q2] at h ⊢
  exact h

theorem endIdentity110 : fieldNFCheck ceSignedSnEntryT2E01FullFq ceSignedSnEntryT2Fq = true := by decide +kernel
    
private theorem cell110 : ∀ y ∈ Icc ((((-103281 : ℚ) / 640000) : ℚ) : ℝ) ((((-102031 : ℚ) / 640000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2E01Lo : ℝ) (ceSignedSnEntryT2E01Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2E01Lo, ceSignedSnEntryT2E01Hi, SignedSnEntryT2End01Literal.q2, ceSignedSnEntryT2E01EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2E01Full y hx
  rw [fieldNFCheck_sound endIdentity110 y] at h
  simp only [ceSignedSnEntryT2E01FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2End01Literal.q2, ceSignedSnEntryT2E01Target, ceSignedSnEntryT2E01EndLiteral.q2] at h ⊢
  exact h

private theorem cell111 : ∀ y ∈ Icc ((((-102031 : ℚ) / 640000) : ℚ) : ℝ) ((((-323119 : ℚ) / 2048000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P109Lo : ℝ) (ceSignedSnEntryT2P109Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P109Lo, ceSignedSnEntryT2P109Hi, SignedSnEntryT2Core109Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P109Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core109Literal.q2] at h ⊢
  exact h

theorem cover006 : ∀ y ∈ Icc ((((-1250031102988653 : ℚ) / 5497558138880000) : ℚ) : ℝ) ((((-323119 : ℚ) / 2048000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell096 cell097) (cover_union cell098 cell099)) (cover_union (cover_union cell100 cell101) (cover_union cell102 cell103))) (cover_union (cover_union (cover_union cell104 cell105) (cover_union cell106 cell107)) (cover_union (cover_union cell108 cell109) (cover_union cell110 cell111))))
#print axioms cover006
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover

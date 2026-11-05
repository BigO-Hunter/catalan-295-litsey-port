module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Core062
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell048 : ∀ y ∈ Icc ((((-134446067152401 : ℚ) / 171798691840000) : ℚ) : ℝ) ((((-2129792717474163 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P047Lo : ℝ) (ceSignedSnEntryT2P047Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P047Lo, ceSignedSnEntryT2P047Hi, SignedSnEntryT2Core047Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P047Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core047Literal.q2] at h ⊢
  exact h

private theorem cell049 : ∀ y ∈ Icc ((((-2129792717474163 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-210844836050991 : ℚ) / 274877906944000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P048Lo : ℝ) (ceSignedSnEntryT2P048Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P048Lo, ceSignedSnEntryT2P048Hi, SignedSnEntryT2Core048Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P048Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core048Literal.q2] at h ⊢
  exact h

private theorem cell050 : ∀ y ∈ Icc ((((-210844836050991 : ℚ) / 274877906944000) : ℚ) : ℝ) ((((-516439911645351 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P049Lo : ℝ) (ceSignedSnEntryT2P049Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P049Lo, ceSignedSnEntryT2P049Hi, SignedSnEntryT2Core049Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P049Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core049Literal.q2] at h ⊢
  exact h

private theorem cell051 : ∀ y ∈ Icc ((((-516439911645351 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-1011535466326449 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P050Lo : ℝ) (ceSignedSnEntryT2P050Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P050Lo, ceSignedSnEntryT2P050Hi, SignedSnEntryT2Core050Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P050Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core050Literal.q2] at h ⊢
  exact h

private theorem cell052 : ∀ y ∈ Icc ((((-1011535466326449 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-400345315137729 : ℚ) / 549755813888000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P051Lo : ℝ) (ceSignedSnEntryT2P051Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P051Lo, ceSignedSnEntryT2P051Hi, SignedSnEntryT2Core051Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P051Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core051Literal.q2] at h ⊢
  exact h

private theorem cell053 : ∀ y ∈ Icc ((((-400345315137729 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((-968846752397943 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P052Lo : ℝ) (ceSignedSnEntryT2P052Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P052Lo, ceSignedSnEntryT2P052Hi, SignedSnEntryT2Core052Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P052Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core052Literal.q2] at h ⊢
  exact h

private theorem cell054 : ∀ y ∈ Icc ((((-968846752397943 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-1916349147831633 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P053Lo : ℝ) (ceSignedSnEntryT2P053Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P053Lo, ceSignedSnEntryT2P053Hi, SignedSnEntryT2Core053Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P053Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core053Literal.q2] at h ⊢
  exact h

private theorem cell055 : ∀ y ∈ Icc ((((-1916349147831633 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-94750239543369 : ℚ) / 137438953472000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P054Lo : ℝ) (ceSignedSnEntryT2P054Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P054Lo, ceSignedSnEntryT2P054Hi, SignedSnEntryT2Core054Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P054Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core054Literal.q2] at h ⊢
  exact h

private theorem cell056 : ∀ y ∈ Icc ((((-94750239543369 : ℚ) / 137438953472000) : ℚ) : ℝ) ((((-1830971719974621 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P055Lo : ℝ) (ceSignedSnEntryT2P055Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P055Lo, ceSignedSnEntryT2P055Hi, SignedSnEntryT2Core055Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P055Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core055Literal.q2] at h ⊢
  exact h

private theorem cell057 : ∀ y ∈ Icc ((((-1830971719974621 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-28275427547037 : ℚ) / 42949672960000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P056Lo : ℝ) (ceSignedSnEntryT2P056Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P056Lo, ceSignedSnEntryT2P056Hi, SignedSnEntryT2Core056Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P056Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core056Literal.q2] at h ⊢
  exact h

private theorem cell058 : ∀ y ∈ Icc ((((-28275427547037 : ℚ) / 42949672960000) : ℚ) : ℝ) ((((-883469324540931 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P057Lo : ℝ) (ceSignedSnEntryT2P057Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P057Lo, ceSignedSnEntryT2P057Hi, SignedSnEntryT2Core057Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P057Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core057Literal.q2] at h ⊢
  exact h

private theorem cell059 : ∀ y ∈ Icc ((((-883469324540931 : ℚ) / 1374389534720000) : ℚ) : ℝ) ((((-431062483788339 : ℚ) / 687194767360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P058Lo : ℝ) (ceSignedSnEntryT2P058Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P058Lo, ceSignedSnEntryT2P058Hi, SignedSnEntryT2Core058Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P058Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core058Literal.q2] at h ⊢
  exact h

private theorem cell060 : ∀ y ∈ Icc ((((-431062483788339 : ℚ) / 687194767360000) : ℚ) : ℝ) ((((-1702905578189103 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P059Lo : ℝ) (ceSignedSnEntryT2P059Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P059Lo, ceSignedSnEntryT2P059Hi, SignedSnEntryT2Core059Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P059Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core059Literal.q2] at h ⊢
  exact h

private theorem cell061 : ∀ y ∈ Icc ((((-1702905578189103 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-33631224424497 : ℚ) / 54975581388800) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P060Lo : ℝ) (ceSignedSnEntryT2P060Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P060Lo, ceSignedSnEntryT2P060Hi, SignedSnEntryT2Core060Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P060Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core060Literal.q2] at h ⊢
  exact h

private theorem cell062 : ∀ y ∈ Icc ((((-33631224424497 : ℚ) / 54975581388800) : ℚ) : ℝ) ((((-1617528150332091 : ℚ) / 2748779069440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P061Lo : ℝ) (ceSignedSnEntryT2P061Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P061Lo, ceSignedSnEntryT2P061Hi, SignedSnEntryT2Core061Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P061Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core061Literal.q2] at h ⊢
  exact h

private theorem cell063 : ∀ y ∈ Icc ((((-1617528150332091 : ℚ) / 2748779069440000) : ℚ) : ℝ) ((((-798091896683919 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT2P062Lo : ℝ) (ceSignedSnEntryT2P062Hi : ℝ) := by
    norm_num [ceSignedSnEntryT2P062Lo, ceSignedSnEntryT2P062Hi, SignedSnEntryT2Core062Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT2P062Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT2Core062Literal.q2] at h ⊢
  exact h

theorem cover003 : ∀ y ∈ Icc ((((-134446067152401 : ℚ) / 171798691840000) : ℚ) : ℝ) ((((-798091896683919 : ℚ) / 1374389534720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell048 cell049) (cover_union cell050 cell051)) (cover_union (cover_union cell052 cell053) (cover_union cell054 cell055))) (cover_union (cover_union (cover_union cell056 cell057) (cover_union cell058 cell059)) (cover_union (cover_union cell060 cell061) (cover_union cell062 cell063))))
#print axioms cover003
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1End01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core061
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell048 : ∀ y ∈ Icc ((((-909608440823683 : ℚ) / 4947802324992000) : ℚ) : ℝ) ((((-6533620885880207 : ℚ) / 37108517437440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P047Lo : ℝ) (ceSignedSnEntryT1P047Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P047Lo, ceSignedSnEntryT1P047Hi, SignedSnEntryT1Core047Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P047Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core047Literal.q2] at h ⊢
  exact h

private theorem cell049 : ∀ y ∈ Icc ((((-6533620885880207 : ℚ) / 37108517437440000) : ℚ) : ℝ) ((((-8519199567641999 : ℚ) / 49478023249920000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P048Lo : ℝ) (ceSignedSnEntryT1P048Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P048Lo, ceSignedSnEntryT1P048Hi, SignedSnEntryT1Core048Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P048Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core048Literal.q2] at h ⊢
  exact h

private theorem cell050 : ∀ y ∈ Icc ((((-8519199567641999 : ℚ) / 49478023249920000) : ℚ) : ℝ) ((((-50538312565257163 : ℚ) / 296868139499520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P049Lo : ℝ) (ceSignedSnEntryT1P049Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P049Lo, ceSignedSnEntryT1P049Hi, SignedSnEntryT1Core049Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P049Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core049Literal.q2] at h ⊢
  exact h

private theorem cell051 : ∀ y ∈ Icc ((((-50538312565257163 : ℚ) / 296868139499520000) : ℚ) : ℝ) ((((-12490356931165583 : ℚ) / 74217034874880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P050Lo : ℝ) (ceSignedSnEntryT1P050Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P050Lo, ceSignedSnEntryT1P050Hi, SignedSnEntryT1Core050Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P050Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core050Literal.q2] at h ⊢
  exact h

private theorem cell052 : ∀ y ∈ Icc ((((-12490356931165583 : ℚ) / 74217034874880000) : ℚ) : ℝ) ((((-4880765804347267 : ℚ) / 29686813949952000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P051Lo : ℝ) (ceSignedSnEntryT1P051Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P051Lo, ceSignedSnEntryT1P051Hi, SignedSnEntryT1Core051Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P051Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core051Literal.q2] at h ⊢
  exact h

private theorem cell053 : ∀ y ∈ Icc ((((-4880765804347267 : ℚ) / 29686813949952000) : ℚ) : ℝ) ((((-48230773202877839 : ℚ) / 296868139499520000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P052Lo : ℝ) (ceSignedSnEntryT1P052Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P052Lo, ceSignedSnEntryT1P052Hi, SignedSnEntryT1Core052Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P052Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core052Literal.q2] at h ⊢
  exact h

private theorem cell054 : ∀ y ∈ Icc ((((-48230773202877839 : ℚ) / 296868139499520000) : ℚ) : ℝ) ((((-95884661565160847 : ℚ) / 593736278999040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P053Lo : ℝ) (ceSignedSnEntryT1P053Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P053Lo, ceSignedSnEntryT1P053Hi, SignedSnEntryT1Core053Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P053Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core053Literal.q2] at h ⊢
  exact h

private theorem cell055 : ∀ y ∈ Icc ((((-95884661565160847 : ℚ) / 593736278999040000) : ℚ) : ℝ) ((((-191192438289726863 : ℚ) / 1187472557998080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P054Lo : ℝ) (ceSignedSnEntryT1P054Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P054Lo, ceSignedSnEntryT1P054Hi, SignedSnEntryT1Core054Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P054Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core054Literal.q2] at h ⊢
  exact h

private theorem cell056 : ∀ y ∈ Icc ((((-191192438289726863 : ℚ) / 1187472557998080000) : ℚ) : ℝ) ((((-821873 : ℚ) / 5120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P055Lo : ℝ) (ceSignedSnEntryT1P055Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P055Lo, ceSignedSnEntryT1P055Hi, SignedSnEntryT1Core055Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P055Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core055Literal.q2] at h ⊢
  exact h

theorem endIdentity57 : fieldNFCheck ceSignedSnEntryT1E01FullFq ceSignedSnEntryT1Fq = true := by decide +kernel
    
private theorem cell057 : ∀ y ∈ Icc ((((-821873 : ℚ) / 5120000) : ℚ) : ℝ) ((((-820623 : ℚ) / 5120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1E01Lo : ℝ) (ceSignedSnEntryT1E01Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1E01Lo, ceSignedSnEntryT1E01Hi, SignedSnEntryT1End01Literal.q2, ceSignedSnEntryT1E01EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1E01Full y hx
  rw [fieldNFCheck_sound endIdentity57 y] at h
  simp only [ceSignedSnEntryT1E01FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1End01Literal.q2, ceSignedSnEntryT1E01Target, ceSignedSnEntryT1E01EndLiteral.q2] at h ⊢
  exact h

private theorem cell058 : ∀ y ∈ Icc ((((-820623 : ℚ) / 5120000) : ℚ) : ℝ) ((((-629422841 : ℚ) / 3932160000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P056Lo : ℝ) (ceSignedSnEntryT1P056Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P056Lo, ceSignedSnEntryT1P056Hi, SignedSnEntryT1Core056Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P056Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core056Literal.q2] at h ⊢
  exact h

private theorem cell059 : ∀ y ∈ Icc ((((-629422841 : ℚ) / 3932160000) : ℚ) : ℝ) ((((-156743993 : ℚ) / 983040000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P057Lo : ℝ) (ceSignedSnEntryT1P057Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P057Lo, ceSignedSnEntryT1P057Hi, SignedSnEntryT1Core057Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P057Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core057Literal.q2] at h ⊢
  exact h

private theorem cell060 : ∀ y ∈ Icc ((((-156743993 : ℚ) / 983040000) : ℚ) : ℝ) ((((-15592837 : ℚ) / 98304000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P058Lo : ℝ) (ceSignedSnEntryT1P058Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P058Lo, ceSignedSnEntryT1P058Hi, SignedSnEntryT1Core058Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P058Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core058Literal.q2] at h ⊢
  exact h

private theorem cell061 : ∀ y ∈ Icc ((((-15592837 : ℚ) / 98304000) : ℚ) : ℝ) ((((-38574281 : ℚ) / 245760000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P059Lo : ℝ) (ceSignedSnEntryT1P059Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P059Lo, ceSignedSnEntryT1P059Hi, SignedSnEntryT1Core059Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P059Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core059Literal.q2] at h ⊢
  exact h

private theorem cell062 : ∀ y ∈ Icc ((((-38574281 : ℚ) / 245760000) : ℚ) : ℝ) ((((-25444313 : ℚ) / 163840000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P060Lo : ℝ) (ceSignedSnEntryT1P060Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P060Lo, ceSignedSnEntryT1P060Hi, SignedSnEntryT1Core060Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P060Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core060Literal.q2] at h ⊢
  exact h

private theorem cell063 : ∀ y ∈ Icc ((((-25444313 : ℚ) / 163840000) : ℚ) : ℝ) ((((-18879329 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P061Lo : ℝ) (ceSignedSnEntryT1P061Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P061Lo, ceSignedSnEntryT1P061Hi, SignedSnEntryT1Core061Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P061Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core061Literal.q2] at h ⊢
  exact h

theorem cover003 : ∀ y ∈ Icc ((((-909608440823683 : ℚ) / 4947802324992000) : ℚ) : ℝ) ((((-18879329 : ℚ) / 122880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell048 cell049) (cover_union cell050 cell051)) (cover_union (cover_union cell052 cell053) (cover_union cell054 cell055))) (cover_union (cover_union (cover_union cell056 cell057) (cover_union cell058 cell059)) (cover_union (cover_union cell060 cell061) (cover_union cell062 cell063))))
#print axioms cover003
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover

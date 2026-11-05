module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Core046
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell032 : ∀ y ∈ Icc ((((-17400489037513463 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-16246719356323801 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P031Lo : ℝ) (ceSignedSnEntryT1P031Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P031Lo, ceSignedSnEntryT1P031Hi, SignedSnEntryT1Core031Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P031Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core031Literal.q2] at h ⊢
  exact h

private theorem cell033 : ∀ y ∈ Icc ((((-16246719356323801 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-13939179993944477 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P032Lo : ℝ) (ceSignedSnEntryT1P032Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P032Lo, ceSignedSnEntryT1P032Hi, SignedSnEntryT1Core032Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P032Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core032Literal.q2] at h ⊢
  exact h

private theorem cell034 : ∀ y ∈ Icc ((((-13939179993944477 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-5527377895485161 : ℚ) / 9277129359360000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P033Lo : ℝ) (ceSignedSnEntryT1P033Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P033Lo, ceSignedSnEntryT1P033Hi, SignedSnEntryT1Core033Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P033Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core033Literal.q2] at h ⊢
  exact h

private theorem cell035 : ∀ y ∈ Icc ((((-5527377895485161 : ℚ) / 9277129359360000) : ℚ) : ℝ) ((((-165016435163011 : ℚ) / 309237645312000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P034Lo : ℝ) (ceSignedSnEntryT1P034Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P034Lo, ceSignedSnEntryT1P034Hi, SignedSnEntryT1Core034Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P034Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core034Literal.q2] at h ⊢
  exact h

private theorem cell036 : ∀ y ∈ Icc ((((-165016435163011 : ℚ) / 309237645312000) : ℚ) : ℝ) ((((-907814620888463 : ℚ) / 2061584302080000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P035Lo : ℝ) (ceSignedSnEntryT1P035Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P035Lo, ceSignedSnEntryT1P035Hi, SignedSnEntryT1Core035Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P035Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core035Literal.q2] at h ⊢
  exact h

private theorem cell037 : ∀ y ∈ Icc ((((-907814620888463 : ℚ) / 2061584302080000) : ℚ) : ℝ) ((((-1403312381361301 : ℚ) / 3710851743744000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P036Lo : ℝ) (ceSignedSnEntryT1P036Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P036Lo, ceSignedSnEntryT1P036Hi, SignedSnEntryT1Core036Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P036Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core036Literal.q2] at h ⊢
  exact h

private theorem cell038 : ∀ y ∈ Icc ((((-1403312381361301 : ℚ) / 3710851743744000) : ℚ) : ℝ) ((((-13456238973018179 : ℚ) / 37108517437440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P037Lo : ℝ) (ceSignedSnEntryT1P037Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P037Lo, ceSignedSnEntryT1P037Hi, SignedSnEntryT1Core037Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P037Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core037Literal.q2] at h ⊢
  exact h

private theorem cell039 : ∀ y ∈ Icc ((((-13456238973018179 : ℚ) / 37108517437440000) : ℚ) : ℝ) ((((-1073279511035279 : ℚ) / 3092376453120000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P038Lo : ℝ) (ceSignedSnEntryT1P038Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P038Lo, ceSignedSnEntryT1P038Hi, SignedSnEntryT1Core038Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P038Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core038Literal.q2] at h ⊢
  exact h

private theorem cell040 : ∀ y ∈ Icc ((((-1073279511035279 : ℚ) / 3092376453120000) : ℚ) : ℝ) ((((-5862792225616843 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P039Lo : ℝ) (ceSignedSnEntryT1P039Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P039Lo, ceSignedSnEntryT1P039Hi, SignedSnEntryT1Core039Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P039Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core039Literal.q2] at h ⊢
  exact h

private theorem cell041 : ∀ y ∈ Icc ((((-5862792225616843 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-1321476846255503 : ℚ) / 4638564679680000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P040Lo : ℝ) (ceSignedSnEntryT1P040Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P040Lo, ceSignedSnEntryT1P040Hi, SignedSnEntryT1Core040Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P040Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core040Literal.q2] at h ⊢
  exact h

private theorem cell042 : ∀ y ∈ Icc ((((-1321476846255503 : ℚ) / 4638564679680000) : ℚ) : ℝ) ((((-9994929929449193 : ℚ) / 37108517437440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P041Lo : ℝ) (ceSignedSnEntryT1P041Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P041Lo, ceSignedSnEntryT1P041Hi, SignedSnEntryT1Core041Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P041Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core041Literal.q2] at h ⊢
  exact h

private theorem cell043 : ∀ y ∈ Icc ((((-9994929929449193 : ℚ) / 37108517437440000) : ℚ) : ℝ) ((((-8841160248259531 : ℚ) / 37108517437440000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P042Lo : ℝ) (ceSignedSnEntryT1P042Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P042Lo, ceSignedSnEntryT1P042Hi, SignedSnEntryT1Core042Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P042Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core042Literal.q2] at h ⊢
  exact h

private theorem cell044 : ∀ y ∈ Icc ((((-8841160248259531 : ℚ) / 37108517437440000) : ℚ) : ℝ) ((((-82642754076647 : ℚ) / 371085174374400) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P043Lo : ℝ) (ceSignedSnEntryT1P043Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P043Lo, ceSignedSnEntryT1P043Hi, SignedSnEntryT1Core043Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P043Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core043Literal.q2] at h ⊢
  exact h

private theorem cell045 : ∀ y ∈ Icc ((((-82642754076647 : ℚ) / 371085174374400) : ℚ) : ℝ) ((((-14797896293544907 : ℚ) / 74217034874880000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P044Lo : ℝ) (ceSignedSnEntryT1P044Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P044Lo, ceSignedSnEntryT1P044Hi, SignedSnEntryT1Core044Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P044Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core044Literal.q2] at h ⊢
  exact h

private theorem cell046 : ∀ y ∈ Icc ((((-14797896293544907 : ℚ) / 74217034874880000) : ℚ) : ℝ) ((((-3555252863237519 : ℚ) / 18554258718720000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P045Lo : ℝ) (ceSignedSnEntryT1P045Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P045Lo, ceSignedSnEntryT1P045Hi, SignedSnEntryT1Core045Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P045Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core045Literal.q2] at h ⊢
  exact h

private theorem cell047 : ∀ y ∈ Icc ((((-3555252863237519 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-909608440823683 : ℚ) / 4947802324992000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT1P046Lo : ℝ) (ceSignedSnEntryT1P046Hi : ℝ) := by
    norm_num [ceSignedSnEntryT1P046Lo, ceSignedSnEntryT1P046Hi, SignedSnEntryT1Core046Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT1P046Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT1Core046Literal.q2] at h ⊢
  exact h

theorem cover002 : ∀ y ∈ Icc ((((-17400489037513463 : ℚ) / 18554258718720000) : ℚ) : ℝ) ((((-909608440823683 : ℚ) / 4947802324992000) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 y ≤ ((((-8736680003909 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell032 cell033) (cover_union cell034 cell035)) (cover_union (cover_union cell036 cell037) (cover_union cell038 cell039))) (cover_union (cover_union (cover_union cell040 cell041) (cover_union cell042 cell043)) (cover_union (cover_union cell044 cell045) (cover_union cell046 cell047))))
#print axioms cover002
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Cover

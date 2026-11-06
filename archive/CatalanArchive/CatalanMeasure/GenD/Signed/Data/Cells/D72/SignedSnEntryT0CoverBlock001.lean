module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core030
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell016 : ∀ y ∈ Icc ((((-144114089637838849 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((-72056495599976449 : ℚ) / 72057594037927936) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P015Lo : ℝ) (ceSignedSnEntryT0P015Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P015Lo, ceSignedSnEntryT0P015Hi, SignedSnEntryT0Core015Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P015Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core015Literal.q2] at h ⊢
  exact h

private theorem cell017 : ∀ y ∈ Icc ((((-72056495599976449 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((-36027698581045249 : ℚ) / 36028797018963968) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P016Lo : ℝ) (ceSignedSnEntryT0P016Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P016Lo, ceSignedSnEntryT0P016Hi, SignedSnEntryT0Core016Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P016Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core016Literal.q2] at h ⊢
  exact h

private theorem cell018 : ∀ y ∈ Icc ((((-36027698581045249 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((-18013300071579649 : ℚ) / 18014398509481984) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P017Lo : ℝ) (ceSignedSnEntryT0P017Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P017Lo, ceSignedSnEntryT0P017Hi, SignedSnEntryT0Core017Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P017Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core017Literal.q2] at h ⊢
  exact h

private theorem cell019 : ∀ y ∈ Icc ((((-18013300071579649 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((-9006100816846849 : ℚ) / 9007199254740992) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P018Lo : ℝ) (ceSignedSnEntryT0P018Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P018Lo, ceSignedSnEntryT0P018Hi, SignedSnEntryT0Core018Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P018Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core018Literal.q2] at h ⊢
  exact h

private theorem cell020 : ∀ y ∈ Icc ((((-9006100816846849 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((-4502501189480449 : ℚ) / 4503599627370496) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P019Lo : ℝ) (ceSignedSnEntryT0P019Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P019Lo, ceSignedSnEntryT0P019Hi, SignedSnEntryT0Core019Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P019Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core019Literal.q2] at h ⊢
  exact h

private theorem cell021 : ∀ y ∈ Icc ((((-4502501189480449 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((-18008906320035845 : ℚ) / 18014398509481984) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P020Lo : ℝ) (ceSignedSnEntryT0P020Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P020Lo, ceSignedSnEntryT0P020Hi, SignedSnEntryT0Core020Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P020Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core020Literal.q2] at h ⊢
  exact h

private theorem cell022 : ∀ y ∈ Icc ((((-18008906320035845 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((-9003903941074947 : ℚ) / 9007199254740992) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P021Lo : ℝ) (ceSignedSnEntryT0P021Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P021Lo, ceSignedSnEntryT0P021Hi, SignedSnEntryT0Core021Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P021Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core021Literal.q2] at h ⊢
  exact h

private theorem cell023 : ∀ y ∈ Icc ((((-9003903941074947 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((-18006709444263943 : ℚ) / 18014398509481984) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P022Lo : ℝ) (ceSignedSnEntryT0P022Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P022Lo, ceSignedSnEntryT0P022Hi, SignedSnEntryT0Core022Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P022Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core022Literal.q2] at h ⊢
  exact h

private theorem cell024 : ∀ y ∈ Icc ((((-18006709444263943 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((-2250701375797249 : ℚ) / 2251799813685248) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P023Lo : ℝ) (ceSignedSnEntryT0P023Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P023Lo, ceSignedSnEntryT0P023Hi, SignedSnEntryT0Core023Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P023Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core023Literal.q2] at h ⊢
  exact h

private theorem cell025 : ∀ y ∈ Icc ((((-2250701375797249 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((-1124801468955649 : ℚ) / 1125899906842624) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P024Lo : ℝ) (ceSignedSnEntryT0P024Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P024Lo, ceSignedSnEntryT0P024Hi, SignedSnEntryT0Core024Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P024Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core024Literal.q2] at h ⊢
  exact h

private theorem cell026 : ∀ y ∈ Icc ((((-1124801468955649 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((-2248504500025347 : ℚ) / 2251799813685248) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P025Lo : ℝ) (ceSignedSnEntryT0P025Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P025Lo, ceSignedSnEntryT0P025Hi, SignedSnEntryT0Core025Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P025Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core025Literal.q2] at h ⊢
  exact h

private theorem cell027 : ∀ y ∈ Icc ((((-2248504500025347 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((-561851515534849 : ℚ) / 562949953421312) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P026Lo : ℝ) (ceSignedSnEntryT0P026Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P026Lo, ceSignedSnEntryT0P026Hi, SignedSnEntryT0Core026Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P026Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core026Literal.q2] at h ⊢
  exact h

private theorem cell028 : ∀ y ∈ Icc ((((-561851515534849 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((-280376538824449 : ℚ) / 281474976710656) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P027Lo : ℝ) (ceSignedSnEntryT0P027Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P027Lo, ceSignedSnEntryT0P027Hi, SignedSnEntryT0Core027Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P027Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core027Literal.q2] at h ⊢
  exact h

private theorem cell029 : ∀ y ∈ Icc ((((-280376538824449 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((-139639050469249 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P028Lo : ℝ) (ceSignedSnEntryT0P028Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P028Lo, ceSignedSnEntryT0P028Hi, SignedSnEntryT0Core028Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P028Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core028Literal.q2] at h ⊢
  exact h

private theorem cell030 : ∀ y ∈ Icc ((((-139639050469249 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-69270306291649 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P029Lo : ℝ) (ceSignedSnEntryT0P029Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P029Lo, ceSignedSnEntryT0P029Hi, SignedSnEntryT0Core029Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P029Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core029Literal.q2] at h ⊢
  exact h

private theorem cell031 : ∀ y ∈ Icc ((((-69270306291649 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-34085934202849 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P030Lo : ℝ) (ceSignedSnEntryT0P030Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P030Lo, ceSignedSnEntryT0P030Hi, SignedSnEntryT0Core030Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P030Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core030Literal.q2] at h ⊢
  exact h

theorem cover001 : ∀ y ∈ Icc ((((-144114089637838849 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((-34085934202849 : ℚ) / 35184372088832) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union cell016 cell017) (cover_union cell018 cell019)) (cover_union (cover_union cell020 cell021) (cover_union cell022 cell023))) (cover_union (cover_union (cover_union cell024 cell025) (cover_union cell026 cell027)) (cover_union (cover_union cell028 cell029) (cover_union cell030 cell031))))
#print axioms cover001
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover

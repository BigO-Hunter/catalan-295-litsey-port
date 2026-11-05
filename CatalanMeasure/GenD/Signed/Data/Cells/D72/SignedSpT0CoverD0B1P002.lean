module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0065
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B1P002L032 : ∀ x ∈ Icc ((((49233 : ℚ) / 57344) : ℚ) : ℝ) ((((3133 : ℚ) / 3584) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0050Lo : ℝ) (ceSignedSpT0P0050Hi : ℝ) := by
    norm_num [ceSignedSpT0P0050Lo, ceSignedSpT0P0050Hi, SignedSpT0P0050Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0050Bound x h'
  norm_num [SignedSpT0P0050Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L033 : ∀ x ∈ Icc ((((3133 : ℚ) / 3584) : ℚ) : ℝ) ((((7289 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0051Lo : ℝ) (ceSignedSpT0P0051Hi : ℝ) := by
    norm_num [ceSignedSpT0P0051Lo, ceSignedSpT0P0051Hi, SignedSpT0P0051Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0051Bound x h'
  norm_num [SignedSpT0P0051Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L034 : ∀ x ∈ Icc ((((7289 : ℚ) / 8192) : ℚ) : ℝ) ((((25959 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0052Lo : ℝ) (ceSignedSpT0P0052Hi : ℝ) := by
    norm_num [ceSignedSpT0P0052Lo, ceSignedSpT0P0052Hi, SignedSpT0P0052Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0052Bound x h'
  norm_num [SignedSpT0P0052Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L035 : ∀ x ∈ Icc ((((25959 : ℚ) / 28672) : ℚ) : ℝ) ((((52813 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0053Lo : ℝ) (ceSignedSpT0P0053Hi : ℝ) := by
    norm_num [ceSignedSpT0P0053Lo, ceSignedSpT0P0053Hi, SignedSpT0P0053Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0053Bound x h'
  norm_num [SignedSpT0P0053Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L036 : ∀ x ∈ Icc ((((52813 : ℚ) / 57344) : ℚ) : ℝ) ((((106521 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0054Lo : ℝ) (ceSignedSpT0P0054Hi : ℝ) := by
    norm_num [ceSignedSpT0P0054Lo, ceSignedSpT0P0054Hi, SignedSpT0P0054Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0054Bound x h'
  norm_num [SignedSpT0P0054Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L037 : ∀ x ∈ Icc ((((106521 : ℚ) / 114688) : ℚ) : ℝ) ((((13427 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0055Lo : ℝ) (ceSignedSpT0P0055Hi : ℝ) := by
    norm_num [ceSignedSpT0P0055Lo, ceSignedSpT0P0055Hi, SignedSpT0P0055Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0055Bound x h'
  norm_num [SignedSpT0P0055Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L038 : ∀ x ∈ Icc ((((13427 : ℚ) / 14336) : ℚ) : ℝ) ((((15473 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0056Lo : ℝ) (ceSignedSpT0P0056Hi : ℝ) := by
    norm_num [ceSignedSpT0P0056Lo, ceSignedSpT0P0056Hi, SignedSpT0P0056Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0056Bound x h'
  norm_num [SignedSpT0P0056Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L039 : ∀ x ∈ Icc ((((15473 : ℚ) / 16384) : ℚ) : ℝ) ((((54603 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0057Lo : ℝ) (ceSignedSpT0P0057Hi : ℝ) := by
    norm_num [ceSignedSpT0P0057Lo, ceSignedSpT0P0057Hi, SignedSpT0P0057Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0057Bound x h'
  norm_num [SignedSpT0P0057Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L040 : ∀ x ∈ Icc ((((54603 : ℚ) / 57344) : ℚ) : ℝ) ((((110101 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0058Lo : ℝ) (ceSignedSpT0P0058Hi : ℝ) := by
    norm_num [ceSignedSpT0P0058Lo, ceSignedSpT0P0058Hi, SignedSpT0P0058Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0058Bound x h'
  norm_num [SignedSpT0P0058Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L041 : ∀ x ∈ Icc ((((110101 : ℚ) / 114688) : ℚ) : ℝ) ((((221097 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0059Lo : ℝ) (ceSignedSpT0P0059Hi : ℝ) := by
    norm_num [ceSignedSpT0P0059Lo, ceSignedSpT0P0059Hi, SignedSpT0P0059Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0059Bound x h'
  norm_num [SignedSpT0P0059Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L042 : ∀ x ∈ Icc ((((221097 : ℚ) / 229376) : ℚ) : ℝ) ((((27749 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0060Lo : ℝ) (ceSignedSpT0P0060Hi : ℝ) := by
    norm_num [ceSignedSpT0P0060Lo, ceSignedSpT0P0060Hi, SignedSpT0P0060Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0060Bound x h'
  norm_num [SignedSpT0P0060Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L043 : ∀ x ∈ Icc ((((27749 : ℚ) / 28672) : ℚ) : ℝ) ((((31841 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0061Lo : ℝ) (ceSignedSpT0P0061Hi : ℝ) := by
    norm_num [ceSignedSpT0P0061Lo, ceSignedSpT0P0061Hi, SignedSpT0P0061Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0061Bound x h'
  norm_num [SignedSpT0P0061Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L044 : ∀ x ∈ Icc ((((31841 : ℚ) / 32768) : ℚ) : ℝ) ((((111891 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0062Lo : ℝ) (ceSignedSpT0P0062Hi : ℝ) := by
    norm_num [ceSignedSpT0P0062Lo, ceSignedSpT0P0062Hi, SignedSpT0P0062Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0062Bound x h'
  norm_num [SignedSpT0P0062Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L045 : ∀ x ∈ Icc ((((111891 : ℚ) / 114688) : ℚ) : ℝ) ((((224677 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0063Lo : ℝ) (ceSignedSpT0P0063Hi : ℝ) := by
    norm_num [ceSignedSpT0P0063Lo, ceSignedSpT0P0063Hi, SignedSpT0P0063Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0063Bound x h'
  norm_num [SignedSpT0P0063Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L046 : ∀ x ∈ Icc ((((224677 : ℚ) / 229376) : ℚ) : ℝ) ((((450249 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0064Lo : ℝ) (ceSignedSpT0P0064Hi : ℝ) := by
    norm_num [ceSignedSpT0P0064Lo, ceSignedSpT0P0064Hi, SignedSpT0P0064Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0064Bound x h'
  norm_num [SignedSpT0P0064Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P002L047 : ∀ x ∈ Icc ((((450249 : ℚ) / 458752) : ℚ) : ℝ) ((((56393 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0065Lo : ℝ) (ceSignedSpT0P0065Hi : ℝ) := by
    norm_num [ceSignedSpT0P0065Lo, ceSignedSpT0P0065Hi, SignedSpT0P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0065Bound x h'
  norm_num [SignedSpT0P0065Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B1P002 : ∀ x ∈ Icc ((((49233 : ℚ) / 57344) : ℚ) : ℝ) ((((56393 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P002L032 SignedSpT0CoverD0B1P002L033) (cover_union SignedSpT0CoverD0B1P002L034 SignedSpT0CoverD0B1P002L035)) (cover_union (cover_union SignedSpT0CoverD0B1P002L036 SignedSpT0CoverD0B1P002L037) (cover_union SignedSpT0CoverD0B1P002L038 SignedSpT0CoverD0B1P002L039))) (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P002L040 SignedSpT0CoverD0B1P002L041) (cover_union SignedSpT0CoverD0B1P002L042 SignedSpT0CoverD0B1P002L043)) (cover_union (cover_union SignedSpT0CoverD0B1P002L044 SignedSpT0CoverD0B1P002L045) (cover_union SignedSpT0CoverD0B1P002L046 SignedSpT0CoverD0B1P002L047))))
#print axioms SignedSpT0CoverD0B1P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

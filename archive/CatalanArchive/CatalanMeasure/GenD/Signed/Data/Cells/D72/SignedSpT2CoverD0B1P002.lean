module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0065
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B1P002L032 : ∀ x ∈ Icc ((((49233 : ℚ) / 57344) : ℚ) : ℝ) ((((3133 : ℚ) / 3584) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0050Lo : ℝ) (ceSignedSpT2P0050Hi : ℝ) := by
    norm_num [ceSignedSpT2P0050Lo, ceSignedSpT2P0050Hi, SignedSpT2P0050Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0050Bound x h'
  norm_num [SignedSpT2P0050Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L033 : ∀ x ∈ Icc ((((3133 : ℚ) / 3584) : ℚ) : ℝ) ((((7289 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0051Lo : ℝ) (ceSignedSpT2P0051Hi : ℝ) := by
    norm_num [ceSignedSpT2P0051Lo, ceSignedSpT2P0051Hi, SignedSpT2P0051Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0051Bound x h'
  norm_num [SignedSpT2P0051Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L034 : ∀ x ∈ Icc ((((7289 : ℚ) / 8192) : ℚ) : ℝ) ((((25959 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0052Lo : ℝ) (ceSignedSpT2P0052Hi : ℝ) := by
    norm_num [ceSignedSpT2P0052Lo, ceSignedSpT2P0052Hi, SignedSpT2P0052Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0052Bound x h'
  norm_num [SignedSpT2P0052Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L035 : ∀ x ∈ Icc ((((25959 : ℚ) / 28672) : ℚ) : ℝ) ((((52813 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0053Lo : ℝ) (ceSignedSpT2P0053Hi : ℝ) := by
    norm_num [ceSignedSpT2P0053Lo, ceSignedSpT2P0053Hi, SignedSpT2P0053Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0053Bound x h'
  norm_num [SignedSpT2P0053Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L036 : ∀ x ∈ Icc ((((52813 : ℚ) / 57344) : ℚ) : ℝ) ((((106521 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0054Lo : ℝ) (ceSignedSpT2P0054Hi : ℝ) := by
    norm_num [ceSignedSpT2P0054Lo, ceSignedSpT2P0054Hi, SignedSpT2P0054Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0054Bound x h'
  norm_num [SignedSpT2P0054Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L037 : ∀ x ∈ Icc ((((106521 : ℚ) / 114688) : ℚ) : ℝ) ((((13427 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0055Lo : ℝ) (ceSignedSpT2P0055Hi : ℝ) := by
    norm_num [ceSignedSpT2P0055Lo, ceSignedSpT2P0055Hi, SignedSpT2P0055Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0055Bound x h'
  norm_num [SignedSpT2P0055Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L038 : ∀ x ∈ Icc ((((13427 : ℚ) / 14336) : ℚ) : ℝ) ((((15473 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0056Lo : ℝ) (ceSignedSpT2P0056Hi : ℝ) := by
    norm_num [ceSignedSpT2P0056Lo, ceSignedSpT2P0056Hi, SignedSpT2P0056Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0056Bound x h'
  norm_num [SignedSpT2P0056Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L039 : ∀ x ∈ Icc ((((15473 : ℚ) / 16384) : ℚ) : ℝ) ((((54603 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0057Lo : ℝ) (ceSignedSpT2P0057Hi : ℝ) := by
    norm_num [ceSignedSpT2P0057Lo, ceSignedSpT2P0057Hi, SignedSpT2P0057Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0057Bound x h'
  norm_num [SignedSpT2P0057Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L040 : ∀ x ∈ Icc ((((54603 : ℚ) / 57344) : ℚ) : ℝ) ((((110101 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0058Lo : ℝ) (ceSignedSpT2P0058Hi : ℝ) := by
    norm_num [ceSignedSpT2P0058Lo, ceSignedSpT2P0058Hi, SignedSpT2P0058Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0058Bound x h'
  norm_num [SignedSpT2P0058Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L041 : ∀ x ∈ Icc ((((110101 : ℚ) / 114688) : ℚ) : ℝ) ((((221097 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0059Lo : ℝ) (ceSignedSpT2P0059Hi : ℝ) := by
    norm_num [ceSignedSpT2P0059Lo, ceSignedSpT2P0059Hi, SignedSpT2P0059Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0059Bound x h'
  norm_num [SignedSpT2P0059Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L042 : ∀ x ∈ Icc ((((221097 : ℚ) / 229376) : ℚ) : ℝ) ((((27749 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0060Lo : ℝ) (ceSignedSpT2P0060Hi : ℝ) := by
    norm_num [ceSignedSpT2P0060Lo, ceSignedSpT2P0060Hi, SignedSpT2P0060Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0060Bound x h'
  norm_num [SignedSpT2P0060Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L043 : ∀ x ∈ Icc ((((27749 : ℚ) / 28672) : ℚ) : ℝ) ((((31841 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0061Lo : ℝ) (ceSignedSpT2P0061Hi : ℝ) := by
    norm_num [ceSignedSpT2P0061Lo, ceSignedSpT2P0061Hi, SignedSpT2P0061Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0061Bound x h'
  norm_num [SignedSpT2P0061Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L044 : ∀ x ∈ Icc ((((31841 : ℚ) / 32768) : ℚ) : ℝ) ((((111891 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0062Lo : ℝ) (ceSignedSpT2P0062Hi : ℝ) := by
    norm_num [ceSignedSpT2P0062Lo, ceSignedSpT2P0062Hi, SignedSpT2P0062Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0062Bound x h'
  norm_num [SignedSpT2P0062Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L045 : ∀ x ∈ Icc ((((111891 : ℚ) / 114688) : ℚ) : ℝ) ((((224677 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0063Lo : ℝ) (ceSignedSpT2P0063Hi : ℝ) := by
    norm_num [ceSignedSpT2P0063Lo, ceSignedSpT2P0063Hi, SignedSpT2P0063Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0063Bound x h'
  norm_num [SignedSpT2P0063Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L046 : ∀ x ∈ Icc ((((224677 : ℚ) / 229376) : ℚ) : ℝ) ((((450249 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0064Lo : ℝ) (ceSignedSpT2P0064Hi : ℝ) := by
    norm_num [ceSignedSpT2P0064Lo, ceSignedSpT2P0064Hi, SignedSpT2P0064Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0064Bound x h'
  norm_num [SignedSpT2P0064Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P002L047 : ∀ x ∈ Icc ((((450249 : ℚ) / 458752) : ℚ) : ℝ) ((((56393 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0065Lo : ℝ) (ceSignedSpT2P0065Hi : ℝ) := by
    norm_num [ceSignedSpT2P0065Lo, ceSignedSpT2P0065Hi, SignedSpT2P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0065Bound x h'
  norm_num [SignedSpT2P0065Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B1P002 : ∀ x ∈ Icc ((((49233 : ℚ) / 57344) : ℚ) : ℝ) ((((56393 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P002L032 SignedSpT2CoverD0B1P002L033) (cover_union SignedSpT2CoverD0B1P002L034 SignedSpT2CoverD0B1P002L035)) (cover_union (cover_union SignedSpT2CoverD0B1P002L036 SignedSpT2CoverD0B1P002L037) (cover_union SignedSpT2CoverD0B1P002L038 SignedSpT2CoverD0B1P002L039))) (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P002L040 SignedSpT2CoverD0B1P002L041) (cover_union SignedSpT2CoverD0B1P002L042 SignedSpT2CoverD0B1P002L043)) (cover_union (cover_union SignedSpT2CoverD0B1P002L044 SignedSpT2CoverD0B1P002L045) (cover_union SignedSpT2CoverD0B1P002L046 SignedSpT2CoverD0B1P002L047))))
#print axioms SignedSpT2CoverD0B1P002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

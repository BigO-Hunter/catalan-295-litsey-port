module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0064
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverD1B0P003L048 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0049Lo : ℝ) (ceSignedSpmTopT0P0049Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0049Lo, ceSignedSpmTopT0P0049Hi, SignedSpmTopT0P0049Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0049Bound x h'
  norm_num [SignedSpmTopT0P0049Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L049 : ∀ x ∈ Icc ((((9007189591056393 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0050Lo : ℝ) (ceSignedSpmTopT0P0050Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0050Lo, ceSignedSpmTopT0P0050Hi, SignedSpmTopT0P0050Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0050Bound x h'
  norm_num [SignedSpmTopT0P0050Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L050 : ∀ x ∈ Icc ((((1125898833099777 : ℚ) / 1125899906842624) : ℚ) : ℝ) ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0051Lo : ℝ) (ceSignedSpmTopT0P0051Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0051Lo, ceSignedSpmTopT0P0051Hi, SignedSpmTopT0P0051Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0051Bound x h'
  norm_num [SignedSpmTopT0P0051Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L051 : ∀ x ∈ Icc ((((9007191738540039 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0052Lo : ℝ) (ceSignedSpmTopT0P0052Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0052Lo, ceSignedSpmTopT0P0052Hi, SignedSpmTopT0P0052Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0052Bound x h'
  norm_num [SignedSpmTopT0P0052Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L052 : ∀ x ∈ Icc ((((4503596406140931 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0053Lo : ℝ) (ceSignedSpmTopT0P0053Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0053Lo, ceSignedSpmTopT0P0053Hi, SignedSpmTopT0P0053Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0053Bound x h'
  norm_num [SignedSpmTopT0P0053Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L053 : ∀ x ∈ Icc ((((9007193886023685 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0054Lo : ℝ) (ceSignedSpmTopT0P0054Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0054Lo, ceSignedSpmTopT0P0054Hi, SignedSpmTopT0P0054Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0054Bound x h'
  norm_num [SignedSpmTopT0P0054Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L054 : ∀ x ∈ Icc ((((18014388845789193 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0055Lo : ℝ) (ceSignedSpmTopT0P0055Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0055Lo, ceSignedSpmTopT0P0055Hi, SignedSpmTopT0P0055Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0055Bound x h'
  norm_num [SignedSpmTopT0P0055Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L055 : ∀ x ∈ Icc ((((2251798739941377 : ℚ) / 2251799813685248) : ℚ) : ℝ) ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0056Lo : ℝ) (ceSignedSpmTopT0P0056Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0056Lo, ceSignedSpmTopT0P0056Hi, SignedSpmTopT0P0056Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0056Bound x h'
  norm_num [SignedSpmTopT0P0056Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L056 : ∀ x ∈ Icc ((((18014390993272839 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0057Lo : ℝ) (ceSignedSpmTopT0P0057Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0057Lo, ceSignedSpmTopT0P0057Hi, SignedSpmTopT0P0057Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0057Bound x h'
  norm_num [SignedSpmTopT0P0057Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L057 : ∀ x ∈ Icc ((((9007196033507331 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0058Lo : ℝ) (ceSignedSpmTopT0P0058Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0058Lo, ceSignedSpmTopT0P0058Hi, SignedSpmTopT0P0058Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0058Bound x h'
  norm_num [SignedSpmTopT0P0058Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L058 : ∀ x ∈ Icc ((((18014393140756485 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0059Lo : ℝ) (ceSignedSpmTopT0P0059Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0059Lo, ceSignedSpmTopT0P0059Hi, SignedSpmTopT0P0059Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0059Bound x h'
  norm_num [SignedSpmTopT0P0059Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L059 : ∀ x ∈ Icc ((((36028787355254793 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0060Lo : ℝ) (ceSignedSpmTopT0P0060Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0060Lo, ceSignedSpmTopT0P0060Hi, SignedSpmTopT0P0060Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0060Bound x h'
  norm_num [SignedSpmTopT0P0060Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L060 : ∀ x ∈ Icc ((((4503598553624577 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0061Lo : ℝ) (ceSignedSpmTopT0P0061Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0061Lo, ceSignedSpmTopT0P0061Hi, SignedSpmTopT0P0061Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0061Bound x h'
  norm_num [SignedSpmTopT0P0061Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L061 : ∀ x ∈ Icc ((((36028789502738439 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0062Lo : ℝ) (ceSignedSpmTopT0P0062Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0062Lo, ceSignedSpmTopT0P0062Hi, SignedSpmTopT0P0062Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0062Bound x h'
  norm_num [SignedSpmTopT0P0062Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L062 : ∀ x ∈ Icc ((((18014395288240131 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0063Lo : ℝ) (ceSignedSpmTopT0P0063Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0063Lo, ceSignedSpmTopT0P0063Hi, SignedSpmTopT0P0063Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0063Bound x h'
  norm_num [SignedSpmTopT0P0063Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P003L063 : ∀ x ∈ Icc ((((36028791650222085 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0064Lo : ℝ) (ceSignedSpmTopT0P0064Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0064Lo, ceSignedSpmTopT0P0064Hi, SignedSpmTopT0P0064Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0064Bound x h'
  norm_num [SignedSpmTopT0P0064Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT0CoverD1B0P003 : ∀ x ∈ Icc ((((4503594258657285 : ℚ) / 4503599627370496) : ℚ) : ℝ) ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P003L048 SignedSpmTopT0CoverD1B0P003L049) (cover_union SignedSpmTopT0CoverD1B0P003L050 SignedSpmTopT0CoverD1B0P003L051)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P003L052 SignedSpmTopT0CoverD1B0P003L053) (cover_union SignedSpmTopT0CoverD1B0P003L054 SignedSpmTopT0CoverD1B0P003L055))) (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P003L056 SignedSpmTopT0CoverD1B0P003L057) (cover_union SignedSpmTopT0CoverD1B0P003L058 SignedSpmTopT0CoverD1B0P003L059)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P003L060 SignedSpmTopT0CoverD1B0P003L061) (cover_union SignedSpmTopT0CoverD1B0P003L062 SignedSpmTopT0CoverD1B0P003L063))))
#print axioms SignedSpmTopT0CoverD1B0P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

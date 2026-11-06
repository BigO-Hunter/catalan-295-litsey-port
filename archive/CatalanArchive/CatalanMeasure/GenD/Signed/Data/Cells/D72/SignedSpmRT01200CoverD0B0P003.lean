module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0063
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT01200CoverD0B0P003L048 : ∀ x ∈ Icc ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ) ((((28070749 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0048Lo : ℝ) (ceSignedSpmRT01200P0048Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0048Lo, ceSignedSpmRT01200P0048Hi, SignedSpmRT01200P0048Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0048Bound x h'
  norm_num [SignedSpmRT01200P0048Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L049 : ∀ x ∈ Icc ((((28070749 : ℚ) / 29000000) : ℚ) : ℝ) ((((225466243 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0049Lo : ℝ) (ceSignedSpmRT01200P0049Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0049Lo, ceSignedSpmRT01200P0049Hi, SignedSpmRT01200P0049Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0049Bound x h'
  norm_num [SignedSpmRT01200P0049Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L050 : ∀ x ∈ Icc ((((225466243 : ℚ) / 232000000) : ℚ) : ℝ) ((((113183247 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0050Lo : ℝ) (ceSignedSpmRT01200P0050Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0050Lo, ceSignedSpmRT01200P0050Hi, SignedSpmRT01200P0050Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0050Bound x h'
  norm_num [SignedSpmRT01200P0050Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L051 : ∀ x ∈ Icc ((((113183247 : ℚ) / 116000000) : ℚ) : ℝ) ((((45453349 : ℚ) / 46400000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0051Lo : ℝ) (ceSignedSpmRT01200P0051Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0051Lo, ceSignedSpmRT01200P0051Hi, SignedSpmRT01200P0051Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0051Bound x h'
  norm_num [SignedSpmRT01200P0051Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L052 : ∀ x ∈ Icc ((((45453349 : ℚ) / 46400000) : ℚ) : ℝ) ((((57041749 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0052Lo : ℝ) (ceSignedSpmRT01200P0052Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0052Lo, ceSignedSpmRT01200P0052Hi, SignedSpmRT01200P0052Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0052Bound x h'
  norm_num [SignedSpmRT01200P0052Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L053 : ∀ x ∈ Icc ((((57041749 : ℚ) / 58000000) : ℚ) : ℝ) ((((457234243 : ℚ) / 464000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0053Lo : ℝ) (ceSignedSpmRT01200P0053Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0053Lo, ceSignedSpmRT01200P0053Hi, SignedSpmRT01200P0053Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0053Bound x h'
  norm_num [SignedSpmRT01200P0053Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L054 : ∀ x ∈ Icc ((((457234243 : ℚ) / 464000000) : ℚ) : ℝ) ((((229067247 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0054Lo : ℝ) (ceSignedSpmRT01200P0054Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0054Lo, ceSignedSpmRT01200P0054Hi, SignedSpmRT01200P0054Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0054Bound x h'
  norm_num [SignedSpmRT01200P0054Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L055 : ∀ x ∈ Icc ((((229067247 : ℚ) / 232000000) : ℚ) : ℝ) ((((91806949 : ℚ) / 92800000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0055Lo : ℝ) (ceSignedSpmRT01200P0055Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0055Lo, ceSignedSpmRT01200P0055Hi, SignedSpmRT01200P0055Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0055Bound x h'
  norm_num [SignedSpmRT01200P0055Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L056 : ∀ x ∈ Icc ((((91806949 : ℚ) / 92800000) : ℚ) : ℝ) ((((114983749 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0056Lo : ℝ) (ceSignedSpmRT01200P0056Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0056Lo, ceSignedSpmRT01200P0056Hi, SignedSpmRT01200P0056Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0056Bound x h'
  norm_num [SignedSpmRT01200P0056Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L057 : ∀ x ∈ Icc ((((114983749 : ℚ) / 116000000) : ℚ) : ℝ) ((((920770243 : ℚ) / 928000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0057Lo : ℝ) (ceSignedSpmRT01200P0057Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0057Lo, ceSignedSpmRT01200P0057Hi, SignedSpmRT01200P0057Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0057Bound x h'
  norm_num [SignedSpmRT01200P0057Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L058 : ∀ x ∈ Icc ((((920770243 : ℚ) / 928000000) : ℚ) : ℝ) ((((460835247 : ℚ) / 464000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0058Lo : ℝ) (ceSignedSpmRT01200P0058Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0058Lo, ceSignedSpmRT01200P0058Hi, SignedSpmRT01200P0058Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0058Bound x h'
  norm_num [SignedSpmRT01200P0058Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L059 : ∀ x ∈ Icc ((((460835247 : ℚ) / 464000000) : ℚ) : ℝ) ((((184514149 : ℚ) / 185600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0059Lo : ℝ) (ceSignedSpmRT01200P0059Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0059Lo, ceSignedSpmRT01200P0059Hi, SignedSpmRT01200P0059Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0059Bound x h'
  norm_num [SignedSpmRT01200P0059Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L060 : ∀ x ∈ Icc ((((184514149 : ℚ) / 185600000) : ℚ) : ℝ) ((((230867749 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0060Lo : ℝ) (ceSignedSpmRT01200P0060Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0060Lo, ceSignedSpmRT01200P0060Hi, SignedSpmRT01200P0060Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0060Bound x h'
  norm_num [SignedSpmRT01200P0060Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L061 : ∀ x ∈ Icc ((((230867749 : ℚ) / 232000000) : ℚ) : ℝ) ((((1847842243 : ℚ) / 1856000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0061Lo : ℝ) (ceSignedSpmRT01200P0061Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0061Lo, ceSignedSpmRT01200P0061Hi, SignedSpmRT01200P0061Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0061Bound x h'
  norm_num [SignedSpmRT01200P0061Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L062 : ∀ x ∈ Icc ((((1847842243 : ℚ) / 1856000000) : ℚ) : ℝ) ((((924371247 : ℚ) / 928000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0062Lo : ℝ) (ceSignedSpmRT01200P0062Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0062Lo, ceSignedSpmRT01200P0062Hi, SignedSpmRT01200P0062Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0062Bound x h'
  norm_num [SignedSpmRT01200P0062Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P003L063 : ∀ x ∈ Icc ((((924371247 : ℚ) / 928000000) : ℚ) : ℝ) ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0063Lo : ℝ) (ceSignedSpmRT01200P0063Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0063Lo, ceSignedSpmRT01200P0063Hi, SignedSpmRT01200P0063Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0063Bound x h'
  norm_num [SignedSpmRT01200P0063Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT01200CoverD0B0P003 : ∀ x ∈ Icc ((((223665741 : ℚ) / 232000000) : ℚ) : ℝ) ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT01200CoverD0B0P003L048 SignedSpmRT01200CoverD0B0P003L049) (cover_union SignedSpmRT01200CoverD0B0P003L050 SignedSpmRT01200CoverD0B0P003L051)) (cover_union (cover_union SignedSpmRT01200CoverD0B0P003L052 SignedSpmRT01200CoverD0B0P003L053) (cover_union SignedSpmRT01200CoverD0B0P003L054 SignedSpmRT01200CoverD0B0P003L055))) (cover_union (cover_union (cover_union SignedSpmRT01200CoverD0B0P003L056 SignedSpmRT01200CoverD0B0P003L057) (cover_union SignedSpmRT01200CoverD0B0P003L058 SignedSpmRT01200CoverD0B0P003L059)) (cover_union (cover_union SignedSpmRT01200CoverD0B0P003L060 SignedSpmRT01200CoverD0B0P003L061) (cover_union SignedSpmRT01200CoverD0B0P003L062 SignedSpmRT01200CoverD0B0P003L063))))
#print axioms SignedSpmRT01200CoverD0B0P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover

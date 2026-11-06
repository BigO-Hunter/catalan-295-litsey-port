module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200P0072
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT21200CoverD0B0P004L064 : ∀ x ∈ Icc ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ) ((((462635749 : ℚ) / 464000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0064Lo : ℝ) (ceSignedSpmRT21200P0064Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0064Lo, ceSignedSpmRT21200P0064Hi, SignedSpmRT21200P0064Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0064Bound x h'
  norm_num [SignedSpmRT21200P0064Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L065 : ∀ x ∈ Icc ((((462635749 : ℚ) / 464000000) : ℚ) : ℝ) ((((1851443247 : ℚ) / 1856000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0065Lo : ℝ) (ceSignedSpmRT21200P0065Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0065Lo, ceSignedSpmRT21200P0065Hi, SignedSpmRT21200P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0065Bound x h'
  norm_num [SignedSpmRT21200P0065Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L066 : ∀ x ∈ Icc ((((1851443247 : ℚ) / 1856000000) : ℚ) : ℝ) ((((740757349 : ℚ) / 742400000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0066Lo : ℝ) (ceSignedSpmRT21200P0066Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0066Lo, ceSignedSpmRT21200P0066Hi, SignedSpmRT21200P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0066Bound x h'
  norm_num [SignedSpmRT21200P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L067 : ∀ x ∈ Icc ((((740757349 : ℚ) / 742400000) : ℚ) : ℝ) ((((926171749 : ℚ) / 928000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0067Lo : ℝ) (ceSignedSpmRT21200P0067Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0067Lo, ceSignedSpmRT21200P0067Hi, SignedSpmRT21200P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0067Bound x h'
  norm_num [SignedSpmRT21200P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L068 : ∀ x ∈ Icc ((((926171749 : ℚ) / 928000000) : ℚ) : ℝ) ((((3705587247 : ℚ) / 3712000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0068Lo : ℝ) (ceSignedSpmRT21200P0068Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0068Lo, ceSignedSpmRT21200P0068Hi, SignedSpmRT21200P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0068Bound x h'
  norm_num [SignedSpmRT21200P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L069 : ∀ x ∈ Icc ((((3705587247 : ℚ) / 3712000000) : ℚ) : ℝ) ((((1853243749 : ℚ) / 1856000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0069Lo : ℝ) (ceSignedSpmRT21200P0069Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0069Lo, ceSignedSpmRT21200P0069Hi, SignedSpmRT21200P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0069Bound x h'
  norm_num [SignedSpmRT21200P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L070 : ∀ x ∈ Icc ((((1853243749 : ℚ) / 1856000000) : ℚ) : ℝ) ((((3707387749 : ℚ) / 3712000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0070Lo : ℝ) (ceSignedSpmRT21200P0070Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0070Lo, ceSignedSpmRT21200P0070Hi, SignedSpmRT21200P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0070Bound x h'
  norm_num [SignedSpmRT21200P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L071 : ∀ x ∈ Icc ((((3707387749 : ℚ) / 3712000000) : ℚ) : ℝ) ((((7415675749 : ℚ) / 7424000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0071Lo : ℝ) (ceSignedSpmRT21200P0071Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0071Lo, ceSignedSpmRT21200P0071Hi, SignedSpmRT21200P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0071Bound x h'
  norm_num [SignedSpmRT21200P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT21200CoverD0B0P004L072 : ∀ x ∈ Icc ((((7415675749 : ℚ) / 7424000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT21200P0072Lo : ℝ) (ceSignedSpmRT21200P0072Hi : ℝ) := by
    norm_num [ceSignedSpmRT21200P0072Lo, ceSignedSpmRT21200P0072Hi, SignedSpmRT21200P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT21200P0072Bound x h'
  norm_num [SignedSpmRT21200P0072Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT21200CoverD0B0P004 : ∀ x ∈ Icc ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpmRT21200CoverD0B0P004L064 SignedSpmRT21200CoverD0B0P004L065) (cover_union SignedSpmRT21200CoverD0B0P004L066 SignedSpmRT21200CoverD0B0P004L067)) (cover_union (cover_union SignedSpmRT21200CoverD0B0P004L068 SignedSpmRT21200CoverD0B0P004L069) (cover_union SignedSpmRT21200CoverD0B0P004L070 (cover_union SignedSpmRT21200CoverD0B0P004L071 SignedSpmRT21200CoverD0B0P004L072))))
#print axioms SignedSpmRT21200CoverD0B0P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200Cover

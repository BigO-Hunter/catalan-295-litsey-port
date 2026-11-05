module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0072
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT1116CoverD0B0P004L064 : ∀ x ∈ Icc ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ) ((((462635749 : ℚ) / 464000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0064Lo : ℝ) (ceSignedSpmRT1116P0064Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0064Lo, ceSignedSpmRT1116P0064Hi, SignedSpmRT1116P0064Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0064Bound x h'
  norm_num [SignedSpmRT1116P0064Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L065 : ∀ x ∈ Icc ((((462635749 : ℚ) / 464000000) : ℚ) : ℝ) ((((1851443247 : ℚ) / 1856000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0065Lo : ℝ) (ceSignedSpmRT1116P0065Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0065Lo, ceSignedSpmRT1116P0065Hi, SignedSpmRT1116P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0065Bound x h'
  norm_num [SignedSpmRT1116P0065Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L066 : ∀ x ∈ Icc ((((1851443247 : ℚ) / 1856000000) : ℚ) : ℝ) ((((740757349 : ℚ) / 742400000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0066Lo : ℝ) (ceSignedSpmRT1116P0066Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0066Lo, ceSignedSpmRT1116P0066Hi, SignedSpmRT1116P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0066Bound x h'
  norm_num [SignedSpmRT1116P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L067 : ∀ x ∈ Icc ((((740757349 : ℚ) / 742400000) : ℚ) : ℝ) ((((926171749 : ℚ) / 928000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0067Lo : ℝ) (ceSignedSpmRT1116P0067Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0067Lo, ceSignedSpmRT1116P0067Hi, SignedSpmRT1116P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0067Bound x h'
  norm_num [SignedSpmRT1116P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L068 : ∀ x ∈ Icc ((((926171749 : ℚ) / 928000000) : ℚ) : ℝ) ((((3705587247 : ℚ) / 3712000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0068Lo : ℝ) (ceSignedSpmRT1116P0068Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0068Lo, ceSignedSpmRT1116P0068Hi, SignedSpmRT1116P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0068Bound x h'
  norm_num [SignedSpmRT1116P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L069 : ∀ x ∈ Icc ((((3705587247 : ℚ) / 3712000000) : ℚ) : ℝ) ((((1853243749 : ℚ) / 1856000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0069Lo : ℝ) (ceSignedSpmRT1116P0069Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0069Lo, ceSignedSpmRT1116P0069Hi, SignedSpmRT1116P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0069Bound x h'
  norm_num [SignedSpmRT1116P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L070 : ∀ x ∈ Icc ((((1853243749 : ℚ) / 1856000000) : ℚ) : ℝ) ((((3707387749 : ℚ) / 3712000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0070Lo : ℝ) (ceSignedSpmRT1116P0070Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0070Lo, ceSignedSpmRT1116P0070Hi, SignedSpmRT1116P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0070Bound x h'
  norm_num [SignedSpmRT1116P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L071 : ∀ x ∈ Icc ((((3707387749 : ℚ) / 3712000000) : ℚ) : ℝ) ((((7415675749 : ℚ) / 7424000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0071Lo : ℝ) (ceSignedSpmRT1116P0071Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0071Lo, ceSignedSpmRT1116P0071Hi, SignedSpmRT1116P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0071Bound x h'
  norm_num [SignedSpmRT1116P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P004L072 : ∀ x ∈ Icc ((((7415675749 : ℚ) / 7424000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0072Lo : ℝ) (ceSignedSpmRT1116P0072Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0072Lo, ceSignedSpmRT1116P0072Hi, SignedSpmRT1116P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0072Bound x h'
  norm_num [SignedSpmRT1116P0072Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT1116CoverD0B0P004 : ∀ x ∈ Icc ((((369928549 : ℚ) / 371200000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P004L064 SignedSpmRT1116CoverD0B0P004L065) (cover_union SignedSpmRT1116CoverD0B0P004L066 SignedSpmRT1116CoverD0B0P004L067)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P004L068 SignedSpmRT1116CoverD0B0P004L069) (cover_union SignedSpmRT1116CoverD0B0P004L070 (cover_union SignedSpmRT1116CoverD0B0P004L071 SignedSpmRT1116CoverD0B0P004L072))))
#print axioms SignedSpmRT1116CoverD0B0P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover

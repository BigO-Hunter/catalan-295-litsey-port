module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0087
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD0B1P004L064 : ∀ x ∈ Icc ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ) ((((915713 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0082Lo : ℝ) (ceSignedSpT1P0082Hi : ℝ) := by
    norm_num [ceSignedSpT1P0082Lo, ceSignedSpT1P0082Hi, SignedSpT1P0082Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0082Bound x h'
  norm_num [SignedSpT1P0082Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P004L065 : ∀ x ∈ Icc ((((915713 : ℚ) / 917504) : ℚ) : ℝ) ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0083Lo : ℝ) (ceSignedSpT1P0083Hi : ℝ) := by
    norm_num [ceSignedSpT1P0083Lo, ceSignedSpT1P0083Hi, SignedSpT1P0083Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0083Bound x h'
  norm_num [SignedSpT1P0083Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P004L066 : ∀ x ∈ Icc ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ) ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0084Lo : ℝ) (ceSignedSpT1P0084Hi : ℝ) := by
    norm_num [ceSignedSpT1P0084Lo, ceSignedSpT1P0084Hi, SignedSpT1P0084Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0084Bound x h'
  norm_num [SignedSpT1P0084Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P004L067 : ∀ x ∈ Icc ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ) ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0085Lo : ℝ) (ceSignedSpT1P0085Hi : ℝ) := by
    norm_num [ceSignedSpT1P0085Lo, ceSignedSpT1P0085Hi, SignedSpT1P0085Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0085Bound x h'
  norm_num [SignedSpT1P0085Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P004L068 : ∀ x ∈ Icc ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ) ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0086Lo : ℝ) (ceSignedSpT1P0086Hi : ℝ) := by
    norm_num [ceSignedSpT1P0086Lo, ceSignedSpT1P0086Hi, SignedSpT1P0086Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0086Bound x h'
  norm_num [SignedSpT1P0086Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P004L069 : ∀ x ∈ Icc ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0087Lo : ℝ) (ceSignedSpT1P0087Hi : ℝ) := by
    norm_num [ceSignedSpT1P0087Lo, ceSignedSpT1P0087Hi, SignedSpT1P0087Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0087Bound x h'
  norm_num [SignedSpT1P0087Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD0B1P004 : ∀ x ∈ Icc ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT1CoverD0B1P004L064 (cover_union SignedSpT1CoverD0B1P004L065 SignedSpT1CoverD0B1P004L066)) (cover_union SignedSpT1CoverD0B1P004L067 (cover_union SignedSpT1CoverD0B1P004L068 SignedSpT1CoverD0B1P004L069)))
#print axioms SignedSpT1CoverD0B1P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0087
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B1P004L064 : ∀ x ∈ Icc ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ) ((((915713 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0082Lo : ℝ) (ceSignedSpT0P0082Hi : ℝ) := by
    norm_num [ceSignedSpT0P0082Lo, ceSignedSpT0P0082Hi, SignedSpT0P0082Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0082Bound x h'
  norm_num [SignedSpT0P0082Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P004L065 : ∀ x ∈ Icc ((((915713 : ℚ) / 917504) : ℚ) : ℝ) ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0083Lo : ℝ) (ceSignedSpT0P0083Hi : ℝ) := by
    norm_num [ceSignedSpT0P0083Lo, ceSignedSpT0P0083Hi, SignedSpT0P0083Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0083Bound x h'
  norm_num [SignedSpT0P0083Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P004L066 : ∀ x ∈ Icc ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ) ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0084Lo : ℝ) (ceSignedSpT0P0084Hi : ℝ) := by
    norm_num [ceSignedSpT0P0084Lo, ceSignedSpT0P0084Hi, SignedSpT0P0084Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0084Bound x h'
  norm_num [SignedSpT0P0084Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P004L067 : ∀ x ∈ Icc ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ) ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0085Lo : ℝ) (ceSignedSpT0P0085Hi : ℝ) := by
    norm_num [ceSignedSpT0P0085Lo, ceSignedSpT0P0085Hi, SignedSpT0P0085Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0085Bound x h'
  norm_num [SignedSpT0P0085Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P004L068 : ∀ x ∈ Icc ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ) ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0086Lo : ℝ) (ceSignedSpT0P0086Hi : ℝ) := by
    norm_num [ceSignedSpT0P0086Lo, ceSignedSpT0P0086Hi, SignedSpT0P0086Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0086Bound x h'
  norm_num [SignedSpT0P0086Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P004L069 : ∀ x ∈ Icc ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0087Lo : ℝ) (ceSignedSpT0P0087Hi : ℝ) := by
    norm_num [ceSignedSpT0P0087Lo, ceSignedSpT0P0087Hi, SignedSpT0P0087Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0087Bound x h'
  norm_num [SignedSpT0P0087Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B1P004 : ∀ x ∈ Icc ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT0CoverD0B1P004L064 (cover_union SignedSpT0CoverD0B1P004L065 SignedSpT0CoverD0B1P004L066)) (cover_union SignedSpT0CoverD0B1P004L067 (cover_union SignedSpT0CoverD0B1P004L068 SignedSpT0CoverD0B1P004L069)))
#print axioms SignedSpT0CoverD0B1P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

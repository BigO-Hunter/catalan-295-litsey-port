module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0087
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0089
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B1P004L064 : ∀ x ∈ Icc ((((457409 : ℚ) / 458752) : ℚ) : ℝ) ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0082Lo : ℝ) (ceSignedSpT2P0082Hi : ℝ) := by
    norm_num [ceSignedSpT2P0082Lo, ceSignedSpT2P0082Hi, SignedSpT2P0082Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0082Bound x h'
  norm_num [SignedSpT2P0082Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L065 : ∀ x ∈ Icc ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ) ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0083Lo : ℝ) (ceSignedSpT2P0083Hi : ℝ) := by
    norm_num [ceSignedSpT2P0083Lo, ceSignedSpT2P0083Hi, SignedSpT2P0083Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0083Bound x h'
  norm_num [SignedSpT2P0083Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L066 : ∀ x ∈ Icc ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ) ((((915713 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0084Lo : ℝ) (ceSignedSpT2P0084Hi : ℝ) := by
    norm_num [ceSignedSpT2P0084Lo, ceSignedSpT2P0084Hi, SignedSpT2P0084Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0084Bound x h'
  norm_num [SignedSpT2P0084Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L067 : ∀ x ∈ Icc ((((915713 : ℚ) / 917504) : ℚ) : ℝ) ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0085Lo : ℝ) (ceSignedSpT2P0085Hi : ℝ) := by
    norm_num [ceSignedSpT2P0085Lo, ceSignedSpT2P0085Hi, SignedSpT2P0085Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0085Bound x h'
  norm_num [SignedSpT2P0085Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L068 : ∀ x ∈ Icc ((((3663747 : ℚ) / 3670016) : ℚ) : ℝ) ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0086Lo : ℝ) (ceSignedSpT2P0086Hi : ℝ) := by
    norm_num [ceSignedSpT2P0086Lo, ceSignedSpT2P0086Hi, SignedSpT2P0086Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0086Bound x h'
  norm_num [SignedSpT2P0086Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L069 : ∀ x ∈ Icc ((((1832321 : ℚ) / 1835008) : ℚ) : ℝ) ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0087Lo : ℝ) (ceSignedSpT2P0087Hi : ℝ) := by
    norm_num [ceSignedSpT2P0087Lo, ceSignedSpT2P0087Hi, SignedSpT2P0087Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0087Bound x h'
  norm_num [SignedSpT2P0087Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L070 : ∀ x ∈ Icc ((((3665537 : ℚ) / 3670016) : ℚ) : ℝ) ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0088Lo : ℝ) (ceSignedSpT2P0088Hi : ℝ) := by
    norm_num [ceSignedSpT2P0088Lo, ceSignedSpT2P0088Hi, SignedSpT2P0088Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0088Bound x h'
  norm_num [SignedSpT2P0088Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P004L071 : ∀ x ∈ Icc ((((7331969 : ℚ) / 7340032) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0089Lo : ℝ) (ceSignedSpT2P0089Hi : ℝ) := by
    norm_num [ceSignedSpT2P0089Lo, ceSignedSpT2P0089Hi, SignedSpT2P0089Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0089Bound x h'
  norm_num [SignedSpT2P0089Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B1P004 : ∀ x ∈ Icc ((((457409 : ℚ) / 458752) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P004L064 SignedSpT2CoverD0B1P004L065) (cover_union SignedSpT2CoverD0B1P004L066 SignedSpT2CoverD0B1P004L067)) (cover_union (cover_union SignedSpT2CoverD0B1P004L068 SignedSpT2CoverD0B1P004L069) (cover_union SignedSpT2CoverD0B1P004L070 SignedSpT2CoverD0B1P004L071)))
#print axioms SignedSpT2CoverD0B1P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

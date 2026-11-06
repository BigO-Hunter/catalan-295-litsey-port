module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0081
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B1P003L048 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((64577 : ℚ) / 65536) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0066Lo : ℝ) (ceSignedSpT2P0066Hi : ℝ) := by
    norm_num [ceSignedSpT2P0066Lo, ceSignedSpT2P0066Hi, SignedSpT2P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0066Bound x h'
  norm_num [SignedSpT2P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L049 : ∀ x ∈ Icc ((((64577 : ℚ) / 65536) : ℚ) : ℝ) ((((226467 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0067Lo : ℝ) (ceSignedSpT2P0067Hi : ℝ) := by
    norm_num [ceSignedSpT2P0067Lo, ceSignedSpT2P0067Hi, SignedSpT2P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0067Bound x h'
  norm_num [SignedSpT2P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L050 : ∀ x ∈ Icc ((((226467 : ℚ) / 229376) : ℚ) : ℝ) ((((1812631 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0068Lo : ℝ) (ceSignedSpT2P0068Hi : ℝ) := by
    norm_num [ceSignedSpT2P0068Lo, ceSignedSpT2P0068Hi, SignedSpT2P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0068Bound x h'
  norm_num [SignedSpT2P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L051 : ∀ x ∈ Icc ((((1812631 : ℚ) / 1835008) : ℚ) : ℝ) ((((906763 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0069Lo : ℝ) (ceSignedSpT2P0069Hi : ℝ) := by
    norm_num [ceSignedSpT2P0069Lo, ceSignedSpT2P0069Hi, SignedSpT2P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0069Bound x h'
  norm_num [SignedSpT2P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L052 : ∀ x ∈ Icc ((((906763 : ℚ) / 917504) : ℚ) : ℝ) ((((259203 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0070Lo : ℝ) (ceSignedSpT2P0070Hi : ℝ) := by
    norm_num [ceSignedSpT2P0070Lo, ceSignedSpT2P0070Hi, SignedSpT2P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0070Bound x h'
  norm_num [SignedSpT2P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L053 : ∀ x ∈ Icc ((((259203 : ℚ) / 262144) : ℚ) : ℝ) ((((453829 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0071Lo : ℝ) (ceSignedSpT2P0071Hi : ℝ) := by
    norm_num [ceSignedSpT2P0071Lo, ceSignedSpT2P0071Hi, SignedSpT2P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0071Bound x h'
  norm_num [SignedSpT2P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L054 : ∀ x ∈ Icc ((((453829 : ℚ) / 458752) : ℚ) : ℝ) ((((908553 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0072Lo : ℝ) (ceSignedSpT2P0072Hi : ℝ) := by
    norm_num [ceSignedSpT2P0072Lo, ceSignedSpT2P0072Hi, SignedSpT2P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0072Bound x h'
  norm_num [SignedSpT2P0072Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L055 : ∀ x ∈ Icc ((((908553 : ℚ) / 917504) : ℚ) : ℝ) ((((113681 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0073Lo : ℝ) (ceSignedSpT2P0073Hi : ℝ) := by
    norm_num [ceSignedSpT2P0073Lo, ceSignedSpT2P0073Hi, SignedSpT2P0073Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0073Bound x h'
  norm_num [SignedSpT2P0073Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L056 : ∀ x ∈ Icc ((((113681 : ℚ) / 114688) : ℚ) : ℝ) ((((130049 : ℚ) / 131072) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0074Lo : ℝ) (ceSignedSpT2P0074Hi : ℝ) := by
    norm_num [ceSignedSpT2P0074Lo, ceSignedSpT2P0074Hi, SignedSpT2P0074Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0074Bound x h'
  norm_num [SignedSpT2P0074Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L057 : ∀ x ∈ Icc ((((130049 : ℚ) / 131072) : ℚ) : ℝ) ((((455619 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0075Lo : ℝ) (ceSignedSpT2P0075Hi : ℝ) := by
    norm_num [ceSignedSpT2P0075Lo, ceSignedSpT2P0075Hi, SignedSpT2P0075Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0075Bound x h'
  norm_num [SignedSpT2P0075Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L058 : ∀ x ∈ Icc ((((455619 : ℚ) / 458752) : ℚ) : ℝ) ((((912133 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0076Lo : ℝ) (ceSignedSpT2P0076Hi : ℝ) := by
    norm_num [ceSignedSpT2P0076Lo, ceSignedSpT2P0076Hi, SignedSpT2P0076Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0076Bound x h'
  norm_num [SignedSpT2P0076Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L059 : ∀ x ∈ Icc ((((912133 : ℚ) / 917504) : ℚ) : ℝ) ((((228257 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0077Lo : ℝ) (ceSignedSpT2P0077Hi : ℝ) := by
    norm_num [ceSignedSpT2P0077Lo, ceSignedSpT2P0077Hi, SignedSpT2P0077Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0077Bound x h'
  norm_num [SignedSpT2P0077Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L060 : ∀ x ∈ Icc ((((228257 : ℚ) / 229376) : ℚ) : ℝ) ((((260993 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0078Lo : ℝ) (ceSignedSpT2P0078Hi : ℝ) := by
    norm_num [ceSignedSpT2P0078Lo, ceSignedSpT2P0078Hi, SignedSpT2P0078Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0078Bound x h'
  norm_num [SignedSpT2P0078Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L061 : ∀ x ∈ Icc ((((260993 : ℚ) / 262144) : ℚ) : ℝ) ((((913923 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0079Lo : ℝ) (ceSignedSpT2P0079Hi : ℝ) := by
    norm_num [ceSignedSpT2P0079Lo, ceSignedSpT2P0079Hi, SignedSpT2P0079Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0079Bound x h'
  norm_num [SignedSpT2P0079Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L062 : ∀ x ∈ Icc ((((913923 : ℚ) / 917504) : ℚ) : ℝ) ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0080Lo : ℝ) (ceSignedSpT2P0080Hi : ℝ) := by
    norm_num [ceSignedSpT2P0080Lo, ceSignedSpT2P0080Hi, SignedSpT2P0080Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0080Bound x h'
  norm_num [SignedSpT2P0080Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P003L063 : ∀ x ∈ Icc ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ) ((((457409 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0081Lo : ℝ) (ceSignedSpT2P0081Hi : ℝ) := by
    norm_num [ceSignedSpT2P0081Lo, ceSignedSpT2P0081Hi, SignedSpT2P0081Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0081Bound x h'
  norm_num [SignedSpT2P0081Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B1P003 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((457409 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P003L048 SignedSpT2CoverD0B1P003L049) (cover_union SignedSpT2CoverD0B1P003L050 SignedSpT2CoverD0B1P003L051)) (cover_union (cover_union SignedSpT2CoverD0B1P003L052 SignedSpT2CoverD0B1P003L053) (cover_union SignedSpT2CoverD0B1P003L054 SignedSpT2CoverD0B1P003L055))) (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P003L056 SignedSpT2CoverD0B1P003L057) (cover_union SignedSpT2CoverD0B1P003L058 SignedSpT2CoverD0B1P003L059)) (cover_union (cover_union SignedSpT2CoverD0B1P003L060 SignedSpT2CoverD0B1P003L061) (cover_union SignedSpT2CoverD0B1P003L062 SignedSpT2CoverD0B1P003L063))))
#print axioms SignedSpT2CoverD0B1P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

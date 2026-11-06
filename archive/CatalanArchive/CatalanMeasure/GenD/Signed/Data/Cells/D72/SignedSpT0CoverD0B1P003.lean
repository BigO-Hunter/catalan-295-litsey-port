module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0081
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B1P003L048 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((64577 : ℚ) / 65536) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0066Lo : ℝ) (ceSignedSpT0P0066Hi : ℝ) := by
    norm_num [ceSignedSpT0P0066Lo, ceSignedSpT0P0066Hi, SignedSpT0P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0066Bound x h'
  norm_num [SignedSpT0P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L049 : ∀ x ∈ Icc ((((64577 : ℚ) / 65536) : ℚ) : ℝ) ((((226467 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0067Lo : ℝ) (ceSignedSpT0P0067Hi : ℝ) := by
    norm_num [ceSignedSpT0P0067Lo, ceSignedSpT0P0067Hi, SignedSpT0P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0067Bound x h'
  norm_num [SignedSpT0P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L050 : ∀ x ∈ Icc ((((226467 : ℚ) / 229376) : ℚ) : ℝ) ((((259203 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0068Lo : ℝ) (ceSignedSpT0P0068Hi : ℝ) := by
    norm_num [ceSignedSpT0P0068Lo, ceSignedSpT0P0068Hi, SignedSpT0P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0068Bound x h'
  norm_num [SignedSpT0P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L051 : ∀ x ∈ Icc ((((259203 : ℚ) / 262144) : ℚ) : ℝ) ((((453829 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0069Lo : ℝ) (ceSignedSpT0P0069Hi : ℝ) := by
    norm_num [ceSignedSpT0P0069Lo, ceSignedSpT0P0069Hi, SignedSpT0P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0069Bound x h'
  norm_num [SignedSpT0P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L052 : ∀ x ∈ Icc ((((453829 : ℚ) / 458752) : ℚ) : ℝ) ((((908553 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0070Lo : ℝ) (ceSignedSpT0P0070Hi : ℝ) := by
    norm_num [ceSignedSpT0P0070Lo, ceSignedSpT0P0070Hi, SignedSpT0P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0070Bound x h'
  norm_num [SignedSpT0P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L053 : ∀ x ∈ Icc ((((908553 : ℚ) / 917504) : ℚ) : ℝ) ((((113681 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0071Lo : ℝ) (ceSignedSpT0P0071Hi : ℝ) := by
    norm_num [ceSignedSpT0P0071Lo, ceSignedSpT0P0071Hi, SignedSpT0P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0071Bound x h'
  norm_num [SignedSpT0P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L054 : ∀ x ∈ Icc ((((113681 : ℚ) / 114688) : ℚ) : ℝ) ((((130049 : ℚ) / 131072) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0072Lo : ℝ) (ceSignedSpT0P0072Hi : ℝ) := by
    norm_num [ceSignedSpT0P0072Lo, ceSignedSpT0P0072Hi, SignedSpT0P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0072Bound x h'
  norm_num [SignedSpT0P0072Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L055 : ∀ x ∈ Icc ((((130049 : ℚ) / 131072) : ℚ) : ℝ) ((((455619 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0073Lo : ℝ) (ceSignedSpT0P0073Hi : ℝ) := by
    norm_num [ceSignedSpT0P0073Lo, ceSignedSpT0P0073Hi, SignedSpT0P0073Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0073Bound x h'
  norm_num [SignedSpT0P0073Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L056 : ∀ x ∈ Icc ((((455619 : ℚ) / 458752) : ℚ) : ℝ) ((((912133 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0074Lo : ℝ) (ceSignedSpT0P0074Hi : ℝ) := by
    norm_num [ceSignedSpT0P0074Lo, ceSignedSpT0P0074Hi, SignedSpT0P0074Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0074Bound x h'
  norm_num [SignedSpT0P0074Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L057 : ∀ x ∈ Icc ((((912133 : ℚ) / 917504) : ℚ) : ℝ) ((((228257 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0075Lo : ℝ) (ceSignedSpT0P0075Hi : ℝ) := by
    norm_num [ceSignedSpT0P0075Lo, ceSignedSpT0P0075Hi, SignedSpT0P0075Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0075Bound x h'
  norm_num [SignedSpT0P0075Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L058 : ∀ x ∈ Icc ((((228257 : ℚ) / 229376) : ℚ) : ℝ) ((((260993 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0076Lo : ℝ) (ceSignedSpT0P0076Hi : ℝ) := by
    norm_num [ceSignedSpT0P0076Lo, ceSignedSpT0P0076Hi, SignedSpT0P0076Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0076Bound x h'
  norm_num [SignedSpT0P0076Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L059 : ∀ x ∈ Icc ((((260993 : ℚ) / 262144) : ℚ) : ℝ) ((((913923 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0077Lo : ℝ) (ceSignedSpT0P0077Hi : ℝ) := by
    norm_num [ceSignedSpT0P0077Lo, ceSignedSpT0P0077Hi, SignedSpT0P0077Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0077Bound x h'
  norm_num [SignedSpT0P0077Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L060 : ∀ x ∈ Icc ((((913923 : ℚ) / 917504) : ℚ) : ℝ) ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0078Lo : ℝ) (ceSignedSpT0P0078Hi : ℝ) := by
    norm_num [ceSignedSpT0P0078Lo, ceSignedSpT0P0078Hi, SignedSpT0P0078Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0078Bound x h'
  norm_num [SignedSpT0P0078Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L061 : ∀ x ∈ Icc ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ) ((((457409 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0079Lo : ℝ) (ceSignedSpT0P0079Hi : ℝ) := by
    norm_num [ceSignedSpT0P0079Lo, ceSignedSpT0P0079Hi, SignedSpT0P0079Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0079Bound x h'
  norm_num [SignedSpT0P0079Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L062 : ∀ x ∈ Icc ((((457409 : ℚ) / 458752) : ℚ) : ℝ) ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0080Lo : ℝ) (ceSignedSpT0P0080Hi : ℝ) := by
    norm_num [ceSignedSpT0P0080Lo, ceSignedSpT0P0080Hi, SignedSpT0P0080Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0080Bound x h'
  norm_num [SignedSpT0P0080Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P003L063 : ∀ x ∈ Icc ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ) ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0081Lo : ℝ) (ceSignedSpT0P0081Hi : ℝ) := by
    norm_num [ceSignedSpT0P0081Lo, ceSignedSpT0P0081Hi, SignedSpT0P0081Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0081Bound x h'
  norm_num [SignedSpT0P0081Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B1P003 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P003L048 SignedSpT0CoverD0B1P003L049) (cover_union SignedSpT0CoverD0B1P003L050 SignedSpT0CoverD0B1P003L051)) (cover_union (cover_union SignedSpT0CoverD0B1P003L052 SignedSpT0CoverD0B1P003L053) (cover_union SignedSpT0CoverD0B1P003L054 SignedSpT0CoverD0B1P003L055))) (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P003L056 SignedSpT0CoverD0B1P003L057) (cover_union SignedSpT0CoverD0B1P003L058 SignedSpT0CoverD0B1P003L059)) (cover_union (cover_union SignedSpT0CoverD0B1P003L060 SignedSpT0CoverD0B1P003L061) (cover_union SignedSpT0CoverD0B1P003L062 SignedSpT0CoverD0B1P003L063))))
#print axioms SignedSpT0CoverD0B1P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

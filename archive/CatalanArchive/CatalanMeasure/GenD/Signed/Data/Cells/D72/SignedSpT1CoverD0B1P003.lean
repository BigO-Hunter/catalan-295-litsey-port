module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0081
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD0B1P003L048 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((64577 : ℚ) / 65536) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0066Lo : ℝ) (ceSignedSpT1P0066Hi : ℝ) := by
    norm_num [ceSignedSpT1P0066Lo, ceSignedSpT1P0066Hi, SignedSpT1P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0066Bound x h'
  norm_num [SignedSpT1P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L049 : ∀ x ∈ Icc ((((64577 : ℚ) / 65536) : ℚ) : ℝ) ((((226467 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0067Lo : ℝ) (ceSignedSpT1P0067Hi : ℝ) := by
    norm_num [ceSignedSpT1P0067Lo, ceSignedSpT1P0067Hi, SignedSpT1P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0067Bound x h'
  norm_num [SignedSpT1P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L050 : ∀ x ∈ Icc ((((226467 : ℚ) / 229376) : ℚ) : ℝ) ((((259203 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0068Lo : ℝ) (ceSignedSpT1P0068Hi : ℝ) := by
    norm_num [ceSignedSpT1P0068Lo, ceSignedSpT1P0068Hi, SignedSpT1P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0068Bound x h'
  norm_num [SignedSpT1P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L051 : ∀ x ∈ Icc ((((259203 : ℚ) / 262144) : ℚ) : ℝ) ((((453829 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0069Lo : ℝ) (ceSignedSpT1P0069Hi : ℝ) := by
    norm_num [ceSignedSpT1P0069Lo, ceSignedSpT1P0069Hi, SignedSpT1P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0069Bound x h'
  norm_num [SignedSpT1P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L052 : ∀ x ∈ Icc ((((453829 : ℚ) / 458752) : ℚ) : ℝ) ((((908553 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0070Lo : ℝ) (ceSignedSpT1P0070Hi : ℝ) := by
    norm_num [ceSignedSpT1P0070Lo, ceSignedSpT1P0070Hi, SignedSpT1P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0070Bound x h'
  norm_num [SignedSpT1P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L053 : ∀ x ∈ Icc ((((908553 : ℚ) / 917504) : ℚ) : ℝ) ((((113681 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0071Lo : ℝ) (ceSignedSpT1P0071Hi : ℝ) := by
    norm_num [ceSignedSpT1P0071Lo, ceSignedSpT1P0071Hi, SignedSpT1P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0071Bound x h'
  norm_num [SignedSpT1P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L054 : ∀ x ∈ Icc ((((113681 : ℚ) / 114688) : ℚ) : ℝ) ((((130049 : ℚ) / 131072) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0072Lo : ℝ) (ceSignedSpT1P0072Hi : ℝ) := by
    norm_num [ceSignedSpT1P0072Lo, ceSignedSpT1P0072Hi, SignedSpT1P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0072Bound x h'
  norm_num [SignedSpT1P0072Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L055 : ∀ x ∈ Icc ((((130049 : ℚ) / 131072) : ℚ) : ℝ) ((((455619 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0073Lo : ℝ) (ceSignedSpT1P0073Hi : ℝ) := by
    norm_num [ceSignedSpT1P0073Lo, ceSignedSpT1P0073Hi, SignedSpT1P0073Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0073Bound x h'
  norm_num [SignedSpT1P0073Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L056 : ∀ x ∈ Icc ((((455619 : ℚ) / 458752) : ℚ) : ℝ) ((((912133 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0074Lo : ℝ) (ceSignedSpT1P0074Hi : ℝ) := by
    norm_num [ceSignedSpT1P0074Lo, ceSignedSpT1P0074Hi, SignedSpT1P0074Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0074Bound x h'
  norm_num [SignedSpT1P0074Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L057 : ∀ x ∈ Icc ((((912133 : ℚ) / 917504) : ℚ) : ℝ) ((((228257 : ℚ) / 229376) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0075Lo : ℝ) (ceSignedSpT1P0075Hi : ℝ) := by
    norm_num [ceSignedSpT1P0075Lo, ceSignedSpT1P0075Hi, SignedSpT1P0075Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0075Bound x h'
  norm_num [SignedSpT1P0075Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L058 : ∀ x ∈ Icc ((((228257 : ℚ) / 229376) : ℚ) : ℝ) ((((260993 : ℚ) / 262144) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0076Lo : ℝ) (ceSignedSpT1P0076Hi : ℝ) := by
    norm_num [ceSignedSpT1P0076Lo, ceSignedSpT1P0076Hi, SignedSpT1P0076Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0076Bound x h'
  norm_num [SignedSpT1P0076Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L059 : ∀ x ∈ Icc ((((260993 : ℚ) / 262144) : ℚ) : ℝ) ((((913923 : ℚ) / 917504) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0077Lo : ℝ) (ceSignedSpT1P0077Hi : ℝ) := by
    norm_num [ceSignedSpT1P0077Lo, ceSignedSpT1P0077Hi, SignedSpT1P0077Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0077Bound x h'
  norm_num [SignedSpT1P0077Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L060 : ∀ x ∈ Icc ((((913923 : ℚ) / 917504) : ℚ) : ℝ) ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0078Lo : ℝ) (ceSignedSpT1P0078Hi : ℝ) := by
    norm_num [ceSignedSpT1P0078Lo, ceSignedSpT1P0078Hi, SignedSpT1P0078Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0078Bound x h'
  norm_num [SignedSpT1P0078Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L061 : ∀ x ∈ Icc ((((1828741 : ℚ) / 1835008) : ℚ) : ℝ) ((((457409 : ℚ) / 458752) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0079Lo : ℝ) (ceSignedSpT1P0079Hi : ℝ) := by
    norm_num [ceSignedSpT1P0079Lo, ceSignedSpT1P0079Hi, SignedSpT1P0079Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0079Bound x h'
  norm_num [SignedSpT1P0079Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L062 : ∀ x ∈ Icc ((((457409 : ℚ) / 458752) : ℚ) : ℝ) ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0080Lo : ℝ) (ceSignedSpT1P0080Hi : ℝ) := by
    norm_num [ceSignedSpT1P0080Lo, ceSignedSpT1P0080Hi, SignedSpT1P0080Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0080Bound x h'
  norm_num [SignedSpT1P0080Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P003L063 : ∀ x ∈ Icc ((((1830531 : ℚ) / 1835008) : ℚ) : ℝ) ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0081Lo : ℝ) (ceSignedSpT1P0081Hi : ℝ) := by
    norm_num [ceSignedSpT1P0081Lo, ceSignedSpT1P0081Hi, SignedSpT1P0081Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0081Bound x h'
  norm_num [SignedSpT1P0081Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD0B1P003 : ∀ x ∈ Icc ((((56393 : ℚ) / 57344) : ℚ) : ℝ) ((((3661957 : ℚ) / 3670016) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD0B1P003L048 SignedSpT1CoverD0B1P003L049) (cover_union SignedSpT1CoverD0B1P003L050 SignedSpT1CoverD0B1P003L051)) (cover_union (cover_union SignedSpT1CoverD0B1P003L052 SignedSpT1CoverD0B1P003L053) (cover_union SignedSpT1CoverD0B1P003L054 SignedSpT1CoverD0B1P003L055))) (cover_union (cover_union (cover_union SignedSpT1CoverD0B1P003L056 SignedSpT1CoverD0B1P003L057) (cover_union SignedSpT1CoverD0B1P003L058 SignedSpT1CoverD0B1P003L059)) (cover_union (cover_union SignedSpT1CoverD0B1P003L060 SignedSpT1CoverD0B1P003L061) (cover_union SignedSpT1CoverD0B1P003L062 SignedSpT1CoverD0B1P003L063))))
#print axioms SignedSpT1CoverD0B1P003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

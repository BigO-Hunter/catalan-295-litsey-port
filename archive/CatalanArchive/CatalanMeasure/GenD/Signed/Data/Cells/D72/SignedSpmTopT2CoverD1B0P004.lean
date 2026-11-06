module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0080
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P004L064 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0065Lo : ℝ) (ceSignedSpmTopT2P0065Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0065Lo, ceSignedSpmTopT2P0065Hi, SignedSpmTopT2P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0065Bound x h'
  norm_num [SignedSpmTopT2P0065Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L065 : ∀ x ∈ Icc ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0066Lo : ℝ) (ceSignedSpmTopT2P0066Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0066Lo, ceSignedSpmTopT2P0066Hi, SignedSpmTopT2P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0066Bound x h'
  norm_num [SignedSpmTopT2P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L066 : ∀ x ∈ Icc ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0067Lo : ℝ) (ceSignedSpmTopT2P0067Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0067Lo, ceSignedSpmTopT2P0067Hi, SignedSpmTopT2P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0067Bound x h'
  norm_num [SignedSpmTopT2P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L067 : ∀ x ∈ Icc ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0068Lo : ℝ) (ceSignedSpmTopT2P0068Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0068Lo, ceSignedSpmTopT2P0068Hi, SignedSpmTopT2P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0068Bound x h'
  norm_num [SignedSpmTopT2P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L068 : ∀ x ∈ Icc ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0069Lo : ℝ) (ceSignedSpmTopT2P0069Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0069Lo, ceSignedSpmTopT2P0069Hi, SignedSpmTopT2P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0069Bound x h'
  norm_num [SignedSpmTopT2P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L069 : ∀ x ∈ Icc ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0070Lo : ℝ) (ceSignedSpmTopT2P0070Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0070Lo, ceSignedSpmTopT2P0070Hi, SignedSpmTopT2P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0070Bound x h'
  norm_num [SignedSpmTopT2P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L070 : ∀ x ∈ Icc ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0071Lo : ℝ) (ceSignedSpmTopT2P0071Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0071Lo, ceSignedSpmTopT2P0071Hi, SignedSpmTopT2P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0071Bound x h'
  norm_num [SignedSpmTopT2P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L071 : ∀ x ∈ Icc ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0072Lo : ℝ) (ceSignedSpmTopT2P0072Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0072Lo, ceSignedSpmTopT2P0072Hi, SignedSpmTopT2P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0072Bound x h'
  norm_num [SignedSpmTopT2P0072Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L072 : ∀ x ∈ Icc ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0073Lo : ℝ) (ceSignedSpmTopT2P0073Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0073Lo, ceSignedSpmTopT2P0073Hi, SignedSpmTopT2P0073Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0073Bound x h'
  norm_num [SignedSpmTopT2P0073Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L073 : ∀ x ∈ Icc ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0074Lo : ℝ) (ceSignedSpmTopT2P0074Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0074Lo, ceSignedSpmTopT2P0074Hi, SignedSpmTopT2P0074Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0074Bound x h'
  norm_num [SignedSpmTopT2P0074Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L074 : ∀ x ∈ Icc ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0075Lo : ℝ) (ceSignedSpmTopT2P0075Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0075Lo, ceSignedSpmTopT2P0075Hi, SignedSpmTopT2P0075Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0075Bound x h'
  norm_num [SignedSpmTopT2P0075Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L075 : ∀ x ∈ Icc ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0076Lo : ℝ) (ceSignedSpmTopT2P0076Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0076Lo, ceSignedSpmTopT2P0076Hi, SignedSpmTopT2P0076Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0076Bound x h'
  norm_num [SignedSpmTopT2P0076Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L076 : ∀ x ∈ Icc ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0077Lo : ℝ) (ceSignedSpmTopT2P0077Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0077Lo, ceSignedSpmTopT2P0077Hi, SignedSpmTopT2P0077Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0077Bound x h'
  norm_num [SignedSpmTopT2P0077Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L077 : ∀ x ∈ Icc ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0078Lo : ℝ) (ceSignedSpmTopT2P0078Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0078Lo, ceSignedSpmTopT2P0078Hi, SignedSpmTopT2P0078Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0078Bound x h'
  norm_num [SignedSpmTopT2P0078Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L078 : ∀ x ∈ Icc ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0079Lo : ℝ) (ceSignedSpmTopT2P0079Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0079Lo, ceSignedSpmTopT2P0079Hi, SignedSpmTopT2P0079Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0079Bound x h'
  norm_num [SignedSpmTopT2P0079Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P004L079 : ∀ x ∈ Icc ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0080Lo : ℝ) (ceSignedSpmTopT2P0080Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0080Lo, ceSignedSpmTopT2P0080Hi, SignedSpmTopT2P0080Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0080Bound x h'
  norm_num [SignedSpmTopT2P0080Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P004 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P004L064 SignedSpmTopT2CoverD1B0P004L065) (cover_union SignedSpmTopT2CoverD1B0P004L066 SignedSpmTopT2CoverD1B0P004L067)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P004L068 SignedSpmTopT2CoverD1B0P004L069) (cover_union SignedSpmTopT2CoverD1B0P004L070 SignedSpmTopT2CoverD1B0P004L071))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P004L072 SignedSpmTopT2CoverD1B0P004L073) (cover_union SignedSpmTopT2CoverD1B0P004L074 SignedSpmTopT2CoverD1B0P004L075)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P004L076 SignedSpmTopT2CoverD1B0P004L077) (cover_union SignedSpmTopT2CoverD1B0P004L078 SignedSpmTopT2CoverD1B0P004L079))))
#print axioms SignedSpmTopT2CoverD1B0P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover

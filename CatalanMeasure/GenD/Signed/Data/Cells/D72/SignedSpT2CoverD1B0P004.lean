module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0154
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0155
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0156
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0157
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0158
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0159
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0160
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0161
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0162
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0163
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0164
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0165
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0166
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0167
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0169
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P004L064 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0154Lo : ℝ) (ceSignedSpT2P0154Hi : ℝ) := by
    norm_num [ceSignedSpT2P0154Lo, ceSignedSpT2P0154Hi, SignedSpT2P0154Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0154Bound x h'
  norm_num [SignedSpT2P0154Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L065 : ∀ x ∈ Icc ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0155Lo : ℝ) (ceSignedSpT2P0155Hi : ℝ) := by
    norm_num [ceSignedSpT2P0155Lo, ceSignedSpT2P0155Hi, SignedSpT2P0155Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0155Bound x h'
  norm_num [SignedSpT2P0155Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L066 : ∀ x ∈ Icc ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0156Lo : ℝ) (ceSignedSpT2P0156Hi : ℝ) := by
    norm_num [ceSignedSpT2P0156Lo, ceSignedSpT2P0156Hi, SignedSpT2P0156Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0156Bound x h'
  norm_num [SignedSpT2P0156Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L067 : ∀ x ∈ Icc ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0157Lo : ℝ) (ceSignedSpT2P0157Hi : ℝ) := by
    norm_num [ceSignedSpT2P0157Lo, ceSignedSpT2P0157Hi, SignedSpT2P0157Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0157Bound x h'
  norm_num [SignedSpT2P0157Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L068 : ∀ x ∈ Icc ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0158Lo : ℝ) (ceSignedSpT2P0158Hi : ℝ) := by
    norm_num [ceSignedSpT2P0158Lo, ceSignedSpT2P0158Hi, SignedSpT2P0158Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0158Bound x h'
  norm_num [SignedSpT2P0158Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L069 : ∀ x ∈ Icc ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0159Lo : ℝ) (ceSignedSpT2P0159Hi : ℝ) := by
    norm_num [ceSignedSpT2P0159Lo, ceSignedSpT2P0159Hi, SignedSpT2P0159Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0159Bound x h'
  norm_num [SignedSpT2P0159Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L070 : ∀ x ∈ Icc ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0160Lo : ℝ) (ceSignedSpT2P0160Hi : ℝ) := by
    norm_num [ceSignedSpT2P0160Lo, ceSignedSpT2P0160Hi, SignedSpT2P0160Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0160Bound x h'
  norm_num [SignedSpT2P0160Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L071 : ∀ x ∈ Icc ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0161Lo : ℝ) (ceSignedSpT2P0161Hi : ℝ) := by
    norm_num [ceSignedSpT2P0161Lo, ceSignedSpT2P0161Hi, SignedSpT2P0161Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0161Bound x h'
  norm_num [SignedSpT2P0161Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L072 : ∀ x ∈ Icc ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0162Lo : ℝ) (ceSignedSpT2P0162Hi : ℝ) := by
    norm_num [ceSignedSpT2P0162Lo, ceSignedSpT2P0162Hi, SignedSpT2P0162Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0162Bound x h'
  norm_num [SignedSpT2P0162Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L073 : ∀ x ∈ Icc ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0163Lo : ℝ) (ceSignedSpT2P0163Hi : ℝ) := by
    norm_num [ceSignedSpT2P0163Lo, ceSignedSpT2P0163Hi, SignedSpT2P0163Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0163Bound x h'
  norm_num [SignedSpT2P0163Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L074 : ∀ x ∈ Icc ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0164Lo : ℝ) (ceSignedSpT2P0164Hi : ℝ) := by
    norm_num [ceSignedSpT2P0164Lo, ceSignedSpT2P0164Hi, SignedSpT2P0164Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0164Bound x h'
  norm_num [SignedSpT2P0164Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L075 : ∀ x ∈ Icc ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0165Lo : ℝ) (ceSignedSpT2P0165Hi : ℝ) := by
    norm_num [ceSignedSpT2P0165Lo, ceSignedSpT2P0165Hi, SignedSpT2P0165Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0165Bound x h'
  norm_num [SignedSpT2P0165Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L076 : ∀ x ∈ Icc ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0166Lo : ℝ) (ceSignedSpT2P0166Hi : ℝ) := by
    norm_num [ceSignedSpT2P0166Lo, ceSignedSpT2P0166Hi, SignedSpT2P0166Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0166Bound x h'
  norm_num [SignedSpT2P0166Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L077 : ∀ x ∈ Icc ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0167Lo : ℝ) (ceSignedSpT2P0167Hi : ℝ) := by
    norm_num [ceSignedSpT2P0167Lo, ceSignedSpT2P0167Hi, SignedSpT2P0167Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0167Bound x h'
  norm_num [SignedSpT2P0167Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L078 : ∀ x ∈ Icc ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0168Lo : ℝ) (ceSignedSpT2P0168Hi : ℝ) := by
    norm_num [ceSignedSpT2P0168Lo, ceSignedSpT2P0168Hi, SignedSpT2P0168Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0168Bound x h'
  norm_num [SignedSpT2P0168Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P004L079 : ∀ x ∈ Icc ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0169Lo : ℝ) (ceSignedSpT2P0169Hi : ℝ) := by
    norm_num [ceSignedSpT2P0169Lo, ceSignedSpT2P0169Hi, SignedSpT2P0169Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0169Bound x h'
  norm_num [SignedSpT2P0169Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P004 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P004L064 SignedSpT2CoverD1B0P004L065) (cover_union SignedSpT2CoverD1B0P004L066 SignedSpT2CoverD1B0P004L067)) (cover_union (cover_union SignedSpT2CoverD1B0P004L068 SignedSpT2CoverD1B0P004L069) (cover_union SignedSpT2CoverD1B0P004L070 SignedSpT2CoverD1B0P004L071))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P004L072 SignedSpT2CoverD1B0P004L073) (cover_union SignedSpT2CoverD1B0P004L074 SignedSpT2CoverD1B0P004L075)) (cover_union (cover_union SignedSpT2CoverD1B0P004L076 SignedSpT2CoverD1B0P004L077) (cover_union SignedSpT2CoverD1B0P004L078 SignedSpT2CoverD1B0P004L079))))
#print axioms SignedSpT2CoverD1B0P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0071
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0079
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0080
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P004L064 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0065Lo : ℝ) (ceSignedSpmTopT1P0065Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0065Lo, ceSignedSpmTopT1P0065Hi, SignedSpmTopT1P0065Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0065Bound x h'
  norm_num [SignedSpmTopT1P0065Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L065 : ∀ x ∈ Icc ((((9007198180990977 : ℚ) / 9007199254740992) : ℚ) : ℝ) ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0066Lo : ℝ) (ceSignedSpmTopT1P0066Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0066Lo, ceSignedSpmTopT1P0066Hi, SignedSpmTopT1P0066Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0066Bound x h'
  norm_num [SignedSpmTopT1P0066Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L066 : ∀ x ∈ Icc ((((72057586521669639 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0067Lo : ℝ) (ceSignedSpmTopT1P0067Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0067Lo, ceSignedSpmTopT1P0067Hi, SignedSpmTopT1P0067Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0067Bound x h'
  norm_num [SignedSpmTopT1P0067Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L067 : ∀ x ∈ Icc ((((36028793797705731 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0068Lo : ℝ) (ceSignedSpmTopT1P0068Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0068Lo, ceSignedSpmTopT1P0068Hi, SignedSpmTopT1P0068Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0068Bound x h'
  norm_num [SignedSpmTopT1P0068Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L068 : ∀ x ∈ Icc ((((72057588669153285 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0069Lo : ℝ) (ceSignedSpmTopT1P0069Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0069Lo, ceSignedSpmTopT1P0069Hi, SignedSpmTopT1P0069Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0069Bound x h'
  norm_num [SignedSpmTopT1P0069Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L069 : ∀ x ∈ Icc ((((144115178412048393 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0070Lo : ℝ) (ceSignedSpmTopT1P0070Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0070Lo, ceSignedSpmTopT1P0070Hi, SignedSpmTopT1P0070Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0070Bound x h'
  norm_num [SignedSpmTopT1P0070Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L070 : ∀ x ∈ Icc ((((18014397435723777 : ℚ) / 18014398509481984) : ℚ) : ℝ) ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0071Lo : ℝ) (ceSignedSpmTopT1P0071Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0071Lo, ceSignedSpmTopT1P0071Hi, SignedSpmTopT1P0071Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0071Bound x h'
  norm_num [SignedSpmTopT1P0071Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L071 : ∀ x ∈ Icc ((((144115180559532039 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0072Lo : ℝ) (ceSignedSpmTopT1P0072Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0072Lo, ceSignedSpmTopT1P0072Hi, SignedSpmTopT1P0072Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0072Bound x h'
  norm_num [SignedSpmTopT1P0072Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L072 : ∀ x ∈ Icc ((((72057590816636931 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0073Lo : ℝ) (ceSignedSpmTopT1P0073Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0073Lo, ceSignedSpmTopT1P0073Hi, SignedSpmTopT1P0073Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0073Bound x h'
  norm_num [SignedSpmTopT1P0073Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L073 : ∀ x ∈ Icc ((((144115182707015685 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0074Lo : ℝ) (ceSignedSpmTopT1P0074Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0074Lo, ceSignedSpmTopT1P0074Hi, SignedSpmTopT1P0074Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0074Bound x h'
  norm_num [SignedSpmTopT1P0074Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L074 : ∀ x ∈ Icc ((((288230366487773193 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0075Lo : ℝ) (ceSignedSpmTopT1P0075Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0075Lo, ceSignedSpmTopT1P0075Hi, SignedSpmTopT1P0075Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0075Bound x h'
  norm_num [SignedSpmTopT1P0075Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L075 : ∀ x ∈ Icc ((((36028795945189377 : ℚ) / 36028797018963968) : ℚ) : ℝ) ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0076Lo : ℝ) (ceSignedSpmTopT1P0076Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0076Lo, ceSignedSpmTopT1P0076Hi, SignedSpmTopT1P0076Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0076Bound x h'
  norm_num [SignedSpmTopT1P0076Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L076 : ∀ x ∈ Icc ((((288230368635256839 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0077Lo : ℝ) (ceSignedSpmTopT1P0077Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0077Lo, ceSignedSpmTopT1P0077Hi, SignedSpmTopT1P0077Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0077Bound x h'
  norm_num [SignedSpmTopT1P0077Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L077 : ∀ x ∈ Icc ((((144115184854499331 : ℚ) / 144115188075855872) : ℚ) : ℝ) ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0078Lo : ℝ) (ceSignedSpmTopT1P0078Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0078Lo, ceSignedSpmTopT1P0078Hi, SignedSpmTopT1P0078Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0078Bound x h'
  norm_num [SignedSpmTopT1P0078Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L078 : ∀ x ∈ Icc ((((288230370782740485 : ℚ) / 288230376151711744) : ℚ) : ℝ) ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0079Lo : ℝ) (ceSignedSpmTopT1P0079Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0079Lo, ceSignedSpmTopT1P0079Hi, SignedSpmTopT1P0079Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0079Bound x h'
  norm_num [SignedSpmTopT1P0079Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P004L079 : ∀ x ∈ Icc ((((576460742639222793 : ℚ) / 576460752303423488) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0080Lo : ℝ) (ceSignedSpmTopT1P0080Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0080Lo, ceSignedSpmTopT1P0080Hi, SignedSpmTopT1P0080Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0080Bound x h'
  norm_num [SignedSpmTopT1P0080Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P004 : ∀ x ∈ Icc ((((72057584374185993 : ℚ) / 72057594037927936) : ℚ) : ℝ) ((((72057592964120577 : ℚ) / 72057594037927936) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P004L064 SignedSpmTopT1CoverD1B0P004L065) (cover_union SignedSpmTopT1CoverD1B0P004L066 SignedSpmTopT1CoverD1B0P004L067)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P004L068 SignedSpmTopT1CoverD1B0P004L069) (cover_union SignedSpmTopT1CoverD1B0P004L070 SignedSpmTopT1CoverD1B0P004L071))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P004L072 SignedSpmTopT1CoverD1B0P004L073) (cover_union SignedSpmTopT1CoverD1B0P004L074 SignedSpmTopT1CoverD1B0P004L075)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P004L076 SignedSpmTopT1CoverD1B0P004L077) (cover_union SignedSpmTopT1CoverD1B0P004L078 SignedSpmTopT1CoverD1B0P004L079))))
#print axioms SignedSpmTopT1CoverD1B0P004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover

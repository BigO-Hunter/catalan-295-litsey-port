module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0031
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT01200CoverD0B0P001L016 : ∀ x ∈ Icc ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ) ((((258589 : ℚ) / 1160000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0016Lo : ℝ) (ceSignedSpmRT01200P0016Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0016Lo, ceSignedSpmRT01200P0016Hi, SignedSpmRT01200P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0016Bound x h'
  norm_num [SignedSpmRT01200P0016Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L017 : ∀ x ∈ Icc ((((258589 : ℚ) / 1160000) : ℚ) : ℝ) ((((13829701 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0017Lo : ℝ) (ceSignedSpmRT01200P0017Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0017Lo, ceSignedSpmRT01200P0017Hi, SignedSpmRT01200P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0017Bound x h'
  norm_num [SignedSpmRT01200P0017Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L018 : ∀ x ∈ Icc ((((13829701 : ℚ) / 58000000) : ℚ) : ℝ) ((((460311 : ℚ) / 1812500) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0018Lo : ℝ) (ceSignedSpmRT01200P0018Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0018Lo, ceSignedSpmRT01200P0018Hi, SignedSpmRT01200P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0018Bound x h'
  norm_num [SignedSpmRT01200P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L019 : ∀ x ∈ Icc ((((460311 : ℚ) / 1812500) : ℚ) : ℝ) ((((15630203 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0019Lo : ℝ) (ceSignedSpmRT01200P0019Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0019Lo, ceSignedSpmRT01200P0019Hi, SignedSpmRT01200P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0019Bound x h'
  norm_num [SignedSpmRT01200P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L020 : ∀ x ∈ Icc ((((15630203 : ℚ) / 58000000) : ℚ) : ℝ) ((((8265227 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0020Lo : ℝ) (ceSignedSpmRT01200P0020Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0020Lo, ceSignedSpmRT01200P0020Hi, SignedSpmRT01200P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0020Bound x h'
  norm_num [SignedSpmRT01200P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L021 : ∀ x ∈ Icc ((((8265227 : ℚ) / 29000000) : ℚ) : ℝ) ((((3486141 : ℚ) / 11600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0021Lo : ℝ) (ceSignedSpmRT01200P0021Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0021Lo, ceSignedSpmRT01200P0021Hi, SignedSpmRT01200P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0021Bound x h'
  norm_num [SignedSpmRT01200P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L022 : ∀ x ∈ Icc ((((3486141 : ℚ) / 11600000) : ℚ) : ℝ) ((((4582739 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0022Lo : ℝ) (ceSignedSpmRT01200P0022Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0022Lo, ceSignedSpmRT01200P0022Hi, SignedSpmRT01200P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0022Bound x h'
  norm_num [SignedSpmRT01200P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L023 : ∀ x ∈ Icc ((((4582739 : ℚ) / 14500000) : ℚ) : ℝ) ((((10065729 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0023Lo : ℝ) (ceSignedSpmRT01200P0023Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0023Lo, ceSignedSpmRT01200P0023Hi, SignedSpmRT01200P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0023Bound x h'
  norm_num [SignedSpmRT01200P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L024 : ∀ x ∈ Icc ((((10065729 : ℚ) / 29000000) : ℚ) : ℝ) ((((548299 : ℚ) / 1450000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0024Lo : ℝ) (ceSignedSpmRT01200P0024Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0024Lo, ceSignedSpmRT01200P0024Hi, SignedSpmRT01200P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0024Bound x h'
  norm_num [SignedSpmRT01200P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L025 : ∀ x ∈ Icc ((((548299 : ℚ) / 1450000) : ℚ) : ℝ) ((((11866231 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0025Lo : ℝ) (ceSignedSpmRT01200P0025Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0025Lo, ceSignedSpmRT01200P0025Hi, SignedSpmRT01200P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0025Bound x h'
  norm_num [SignedSpmRT01200P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L026 : ∀ x ∈ Icc ((((11866231 : ℚ) / 29000000) : ℚ) : ℝ) ((((6383241 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0026Lo : ℝ) (ceSignedSpmRT01200P0026Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0026Lo, ceSignedSpmRT01200P0026Hi, SignedSpmRT01200P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0026Bound x h'
  norm_num [SignedSpmRT01200P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L027 : ∀ x ∈ Icc ((((6383241 : ℚ) / 14500000) : ℚ) : ℝ) ((((13666733 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0027Lo : ℝ) (ceSignedSpmRT01200P0027Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0027Lo, ceSignedSpmRT01200P0027Hi, SignedSpmRT01200P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0027Bound x h'
  norm_num [SignedSpmRT01200P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L028 : ∀ x ∈ Icc ((((13666733 : ℚ) / 29000000) : ℚ) : ℝ) ((((3093447 : ℚ) / 5800000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0028Lo : ℝ) (ceSignedSpmRT01200P0028Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0028Lo, ceSignedSpmRT01200P0028Hi, SignedSpmRT01200P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0028Bound x h'
  norm_num [SignedSpmRT01200P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L029 : ∀ x ∈ Icc ((((3093447 : ℚ) / 5800000) : ℚ) : ℝ) ((((17267737 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0029Lo : ℝ) (ceSignedSpmRT01200P0029Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0029Lo, ceSignedSpmRT01200P0029Hi, SignedSpmRT01200P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0029Bound x h'
  norm_num [SignedSpmRT01200P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L030 : ∀ x ∈ Icc ((((17267737 : ℚ) / 29000000) : ℚ) : ℝ) ((((19068239 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0030Lo : ℝ) (ceSignedSpmRT01200P0030Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0030Lo, ceSignedSpmRT01200P0030Hi, SignedSpmRT01200P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0030Bound x h'
  norm_num [SignedSpmRT01200P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverD0B0P001L031 : ∀ x ∈ Icc ((((19068239 : ℚ) / 29000000) : ℚ) : ℝ) ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0031Lo : ℝ) (ceSignedSpmRT01200P0031Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0031Lo, ceSignedSpmRT01200P0031Hi, SignedSpmRT01200P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0031Bound x h'
  norm_num [SignedSpmRT01200P0031Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT01200CoverD0B0P001 : ∀ x ∈ Icc ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ) ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT01200CoverD0B0P001L016 SignedSpmRT01200CoverD0B0P001L017) (cover_union SignedSpmRT01200CoverD0B0P001L018 SignedSpmRT01200CoverD0B0P001L019)) (cover_union (cover_union SignedSpmRT01200CoverD0B0P001L020 SignedSpmRT01200CoverD0B0P001L021) (cover_union SignedSpmRT01200CoverD0B0P001L022 SignedSpmRT01200CoverD0B0P001L023))) (cover_union (cover_union (cover_union SignedSpmRT01200CoverD0B0P001L024 SignedSpmRT01200CoverD0B0P001L025) (cover_union SignedSpmRT01200CoverD0B0P001L026 SignedSpmRT01200CoverD0B0P001L027)) (cover_union (cover_union SignedSpmRT01200CoverD0B0P001L028 SignedSpmRT01200CoverD0B0P001L029) (cover_union SignedSpmRT01200CoverD0B0P001L030 SignedSpmRT01200CoverD0B0P001L031))))
#print axioms SignedSpmRT01200CoverD0B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover

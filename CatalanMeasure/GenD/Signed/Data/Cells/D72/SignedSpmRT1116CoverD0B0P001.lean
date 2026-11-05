module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0031
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT1116CoverD0B0P001L016 : ∀ x ∈ Icc ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ) ((((258589 : ℚ) / 1160000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0016Lo : ℝ) (ceSignedSpmRT1116P0016Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0016Lo, ceSignedSpmRT1116P0016Hi, SignedSpmRT1116P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0016Bound x h'
  norm_num [SignedSpmRT1116P0016Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L017 : ∀ x ∈ Icc ((((258589 : ℚ) / 1160000) : ℚ) : ℝ) ((((13829701 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0017Lo : ℝ) (ceSignedSpmRT1116P0017Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0017Lo, ceSignedSpmRT1116P0017Hi, SignedSpmRT1116P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0017Bound x h'
  norm_num [SignedSpmRT1116P0017Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L018 : ∀ x ∈ Icc ((((13829701 : ℚ) / 58000000) : ℚ) : ℝ) ((((460311 : ℚ) / 1812500) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0018Lo : ℝ) (ceSignedSpmRT1116P0018Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0018Lo, ceSignedSpmRT1116P0018Hi, SignedSpmRT1116P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0018Bound x h'
  norm_num [SignedSpmRT1116P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L019 : ∀ x ∈ Icc ((((460311 : ℚ) / 1812500) : ℚ) : ℝ) ((((15630203 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0019Lo : ℝ) (ceSignedSpmRT1116P0019Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0019Lo, ceSignedSpmRT1116P0019Hi, SignedSpmRT1116P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0019Bound x h'
  norm_num [SignedSpmRT1116P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L020 : ∀ x ∈ Icc ((((15630203 : ℚ) / 58000000) : ℚ) : ℝ) ((((8265227 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0020Lo : ℝ) (ceSignedSpmRT1116P0020Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0020Lo, ceSignedSpmRT1116P0020Hi, SignedSpmRT1116P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0020Bound x h'
  norm_num [SignedSpmRT1116P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L021 : ∀ x ∈ Icc ((((8265227 : ℚ) / 29000000) : ℚ) : ℝ) ((((3486141 : ℚ) / 11600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0021Lo : ℝ) (ceSignedSpmRT1116P0021Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0021Lo, ceSignedSpmRT1116P0021Hi, SignedSpmRT1116P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0021Bound x h'
  norm_num [SignedSpmRT1116P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L022 : ∀ x ∈ Icc ((((3486141 : ℚ) / 11600000) : ℚ) : ℝ) ((((4582739 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0022Lo : ℝ) (ceSignedSpmRT1116P0022Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0022Lo, ceSignedSpmRT1116P0022Hi, SignedSpmRT1116P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0022Bound x h'
  norm_num [SignedSpmRT1116P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L023 : ∀ x ∈ Icc ((((4582739 : ℚ) / 14500000) : ℚ) : ℝ) ((((10065729 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0023Lo : ℝ) (ceSignedSpmRT1116P0023Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0023Lo, ceSignedSpmRT1116P0023Hi, SignedSpmRT1116P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0023Bound x h'
  norm_num [SignedSpmRT1116P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L024 : ∀ x ∈ Icc ((((10065729 : ℚ) / 29000000) : ℚ) : ℝ) ((((548299 : ℚ) / 1450000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0024Lo : ℝ) (ceSignedSpmRT1116P0024Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0024Lo, ceSignedSpmRT1116P0024Hi, SignedSpmRT1116P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0024Bound x h'
  norm_num [SignedSpmRT1116P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L025 : ∀ x ∈ Icc ((((548299 : ℚ) / 1450000) : ℚ) : ℝ) ((((11866231 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0025Lo : ℝ) (ceSignedSpmRT1116P0025Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0025Lo, ceSignedSpmRT1116P0025Hi, SignedSpmRT1116P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0025Bound x h'
  norm_num [SignedSpmRT1116P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L026 : ∀ x ∈ Icc ((((11866231 : ℚ) / 29000000) : ℚ) : ℝ) ((((6383241 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0026Lo : ℝ) (ceSignedSpmRT1116P0026Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0026Lo, ceSignedSpmRT1116P0026Hi, SignedSpmRT1116P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0026Bound x h'
  norm_num [SignedSpmRT1116P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L027 : ∀ x ∈ Icc ((((6383241 : ℚ) / 14500000) : ℚ) : ℝ) ((((13666733 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0027Lo : ℝ) (ceSignedSpmRT1116P0027Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0027Lo, ceSignedSpmRT1116P0027Hi, SignedSpmRT1116P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0027Bound x h'
  norm_num [SignedSpmRT1116P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L028 : ∀ x ∈ Icc ((((13666733 : ℚ) / 29000000) : ℚ) : ℝ) ((((3093447 : ℚ) / 5800000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0028Lo : ℝ) (ceSignedSpmRT1116P0028Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0028Lo, ceSignedSpmRT1116P0028Hi, SignedSpmRT1116P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0028Bound x h'
  norm_num [SignedSpmRT1116P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L029 : ∀ x ∈ Icc ((((3093447 : ℚ) / 5800000) : ℚ) : ℝ) ((((17267737 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0029Lo : ℝ) (ceSignedSpmRT1116P0029Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0029Lo, ceSignedSpmRT1116P0029Hi, SignedSpmRT1116P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0029Bound x h'
  norm_num [SignedSpmRT1116P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L030 : ∀ x ∈ Icc ((((17267737 : ℚ) / 29000000) : ℚ) : ℝ) ((((19068239 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0030Lo : ℝ) (ceSignedSpmRT1116P0030Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0030Lo, ceSignedSpmRT1116P0030Hi, SignedSpmRT1116P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0030Bound x h'
  norm_num [SignedSpmRT1116P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P001L031 : ∀ x ∈ Icc ((((19068239 : ℚ) / 29000000) : ℚ) : ℝ) ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0031Lo : ℝ) (ceSignedSpmRT1116P0031Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0031Lo, ceSignedSpmRT1116P0031Hi, SignedSpmRT1116P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0031Bound x h'
  norm_num [SignedSpmRT1116P0031Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT1116CoverD0B0P001 : ∀ x ∈ Icc ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ) ((((1996849 : ℚ) / 2900000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P001L016 SignedSpmRT1116CoverD0B0P001L017) (cover_union SignedSpmRT1116CoverD0B0P001L018 SignedSpmRT1116CoverD0B0P001L019)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P001L020 SignedSpmRT1116CoverD0B0P001L021) (cover_union SignedSpmRT1116CoverD0B0P001L022 SignedSpmRT1116CoverD0B0P001L023))) (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P001L024 SignedSpmRT1116CoverD0B0P001L025) (cover_union SignedSpmRT1116CoverD0B0P001L026 SignedSpmRT1116CoverD0B0P001L027)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P001L028 SignedSpmRT1116CoverD0B0P001L029) (cover_union SignedSpmRT1116CoverD0B0P001L030 SignedSpmRT1116CoverD0B0P001L031))))
#print axioms SignedSpmRT1116CoverD0B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover

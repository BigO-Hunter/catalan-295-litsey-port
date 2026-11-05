module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0032
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P001L016 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0017Lo : ℝ) (ceSignedSpmTopT1P0017Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0017Lo, ceSignedSpmTopT1P0017Hi, SignedSpmTopT1P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0017Bound x h'
  norm_num [SignedSpmTopT1P0017Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L017 : ∀ x ∈ Icc ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0018Lo : ℝ) (ceSignedSpmTopT1P0018Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0018Lo, ceSignedSpmTopT1P0018Hi, SignedSpmTopT1P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0018Bound x h'
  norm_num [SignedSpmTopT1P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L018 : ∀ x ∈ Icc ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0019Lo : ℝ) (ceSignedSpmTopT1P0019Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0019Lo, ceSignedSpmTopT1P0019Hi, SignedSpmTopT1P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0019Bound x h'
  norm_num [SignedSpmTopT1P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L019 : ∀ x ∈ Icc ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0020Lo : ℝ) (ceSignedSpmTopT1P0020Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0020Lo, ceSignedSpmTopT1P0020Hi, SignedSpmTopT1P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0020Bound x h'
  norm_num [SignedSpmTopT1P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L020 : ∀ x ∈ Icc ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0021Lo : ℝ) (ceSignedSpmTopT1P0021Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0021Lo, ceSignedSpmTopT1P0021Hi, SignedSpmTopT1P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0021Bound x h'
  norm_num [SignedSpmTopT1P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L021 : ∀ x ∈ Icc ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0022Lo : ℝ) (ceSignedSpmTopT1P0022Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0022Lo, ceSignedSpmTopT1P0022Hi, SignedSpmTopT1P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0022Bound x h'
  norm_num [SignedSpmTopT1P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L022 : ∀ x ∈ Icc ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0023Lo : ℝ) (ceSignedSpmTopT1P0023Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0023Lo, ceSignedSpmTopT1P0023Hi, SignedSpmTopT1P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0023Bound x h'
  norm_num [SignedSpmTopT1P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L023 : ∀ x ∈ Icc ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0024Lo : ℝ) (ceSignedSpmTopT1P0024Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0024Lo, ceSignedSpmTopT1P0024Hi, SignedSpmTopT1P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0024Bound x h'
  norm_num [SignedSpmTopT1P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L024 : ∀ x ∈ Icc ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0025Lo : ℝ) (ceSignedSpmTopT1P0025Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0025Lo, ceSignedSpmTopT1P0025Hi, SignedSpmTopT1P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0025Bound x h'
  norm_num [SignedSpmTopT1P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L025 : ∀ x ∈ Icc ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0026Lo : ℝ) (ceSignedSpmTopT1P0026Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0026Lo, ceSignedSpmTopT1P0026Hi, SignedSpmTopT1P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0026Bound x h'
  norm_num [SignedSpmTopT1P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L026 : ∀ x ∈ Icc ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0027Lo : ℝ) (ceSignedSpmTopT1P0027Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0027Lo, ceSignedSpmTopT1P0027Hi, SignedSpmTopT1P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0027Bound x h'
  norm_num [SignedSpmTopT1P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L027 : ∀ x ∈ Icc ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0028Lo : ℝ) (ceSignedSpmTopT1P0028Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0028Lo, ceSignedSpmTopT1P0028Hi, SignedSpmTopT1P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0028Bound x h'
  norm_num [SignedSpmTopT1P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L028 : ∀ x ∈ Icc ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0029Lo : ℝ) (ceSignedSpmTopT1P0029Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0029Lo, ceSignedSpmTopT1P0029Hi, SignedSpmTopT1P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0029Bound x h'
  norm_num [SignedSpmTopT1P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L029 : ∀ x ∈ Icc ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0030Lo : ℝ) (ceSignedSpmTopT1P0030Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0030Lo, ceSignedSpmTopT1P0030Hi, SignedSpmTopT1P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0030Bound x h'
  norm_num [SignedSpmTopT1P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L030 : ∀ x ∈ Icc ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0031Lo : ℝ) (ceSignedSpmTopT1P0031Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0031Lo, ceSignedSpmTopT1P0031Hi, SignedSpmTopT1P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0031Bound x h'
  norm_num [SignedSpmTopT1P0031Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P001L031 : ∀ x ∈ Icc ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0032Lo : ℝ) (ceSignedSpmTopT1P0032Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0032Lo, ceSignedSpmTopT1P0032Hi, SignedSpmTopT1P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0032Bound x h'
  norm_num [SignedSpmTopT1P0032Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P001 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P001L016 SignedSpmTopT1CoverD1B0P001L017) (cover_union SignedSpmTopT1CoverD1B0P001L018 SignedSpmTopT1CoverD1B0P001L019)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P001L020 SignedSpmTopT1CoverD1B0P001L021) (cover_union SignedSpmTopT1CoverD1B0P001L022 SignedSpmTopT1CoverD1B0P001L023))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P001L024 SignedSpmTopT1CoverD1B0P001L025) (cover_union SignedSpmTopT1CoverD1B0P001L026 SignedSpmTopT1CoverD1B0P001L027)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P001L028 SignedSpmTopT1CoverD1B0P001L029) (cover_union SignedSpmTopT1CoverD1B0P001L030 SignedSpmTopT1CoverD1B0P001L031))))
#print axioms SignedSpmTopT1CoverD1B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover

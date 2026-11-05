module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0111
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0119
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P001L016 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0104Lo : ℝ) (ceSignedSpT0P0104Hi : ℝ) := by
    norm_num [ceSignedSpT0P0104Lo, ceSignedSpT0P0104Hi, SignedSpT0P0104Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0104Bound x h'
  norm_num [SignedSpT0P0104Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L017 : ∀ x ∈ Icc ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0105Lo : ℝ) (ceSignedSpT0P0105Hi : ℝ) := by
    norm_num [ceSignedSpT0P0105Lo, ceSignedSpT0P0105Hi, SignedSpT0P0105Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0105Bound x h'
  norm_num [SignedSpT0P0105Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L018 : ∀ x ∈ Icc ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0106Lo : ℝ) (ceSignedSpT0P0106Hi : ℝ) := by
    norm_num [ceSignedSpT0P0106Lo, ceSignedSpT0P0106Hi, SignedSpT0P0106Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0106Bound x h'
  norm_num [SignedSpT0P0106Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L019 : ∀ x ∈ Icc ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0107Lo : ℝ) (ceSignedSpT0P0107Hi : ℝ) := by
    norm_num [ceSignedSpT0P0107Lo, ceSignedSpT0P0107Hi, SignedSpT0P0107Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0107Bound x h'
  norm_num [SignedSpT0P0107Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L020 : ∀ x ∈ Icc ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0108Lo : ℝ) (ceSignedSpT0P0108Hi : ℝ) := by
    norm_num [ceSignedSpT0P0108Lo, ceSignedSpT0P0108Hi, SignedSpT0P0108Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0108Bound x h'
  norm_num [SignedSpT0P0108Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L021 : ∀ x ∈ Icc ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0109Lo : ℝ) (ceSignedSpT0P0109Hi : ℝ) := by
    norm_num [ceSignedSpT0P0109Lo, ceSignedSpT0P0109Hi, SignedSpT0P0109Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0109Bound x h'
  norm_num [SignedSpT0P0109Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L022 : ∀ x ∈ Icc ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0110Lo : ℝ) (ceSignedSpT0P0110Hi : ℝ) := by
    norm_num [ceSignedSpT0P0110Lo, ceSignedSpT0P0110Hi, SignedSpT0P0110Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0110Bound x h'
  norm_num [SignedSpT0P0110Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L023 : ∀ x ∈ Icc ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0111Lo : ℝ) (ceSignedSpT0P0111Hi : ℝ) := by
    norm_num [ceSignedSpT0P0111Lo, ceSignedSpT0P0111Hi, SignedSpT0P0111Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0111Bound x h'
  norm_num [SignedSpT0P0111Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L024 : ∀ x ∈ Icc ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0112Lo : ℝ) (ceSignedSpT0P0112Hi : ℝ) := by
    norm_num [ceSignedSpT0P0112Lo, ceSignedSpT0P0112Hi, SignedSpT0P0112Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0112Bound x h'
  norm_num [SignedSpT0P0112Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L025 : ∀ x ∈ Icc ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0113Lo : ℝ) (ceSignedSpT0P0113Hi : ℝ) := by
    norm_num [ceSignedSpT0P0113Lo, ceSignedSpT0P0113Hi, SignedSpT0P0113Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0113Bound x h'
  norm_num [SignedSpT0P0113Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L026 : ∀ x ∈ Icc ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0114Lo : ℝ) (ceSignedSpT0P0114Hi : ℝ) := by
    norm_num [ceSignedSpT0P0114Lo, ceSignedSpT0P0114Hi, SignedSpT0P0114Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0114Bound x h'
  norm_num [SignedSpT0P0114Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L027 : ∀ x ∈ Icc ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0115Lo : ℝ) (ceSignedSpT0P0115Hi : ℝ) := by
    norm_num [ceSignedSpT0P0115Lo, ceSignedSpT0P0115Hi, SignedSpT0P0115Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0115Bound x h'
  norm_num [SignedSpT0P0115Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L028 : ∀ x ∈ Icc ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0116Lo : ℝ) (ceSignedSpT0P0116Hi : ℝ) := by
    norm_num [ceSignedSpT0P0116Lo, ceSignedSpT0P0116Hi, SignedSpT0P0116Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0116Bound x h'
  norm_num [SignedSpT0P0116Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L029 : ∀ x ∈ Icc ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0117Lo : ℝ) (ceSignedSpT0P0117Hi : ℝ) := by
    norm_num [ceSignedSpT0P0117Lo, ceSignedSpT0P0117Hi, SignedSpT0P0117Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0117Bound x h'
  norm_num [SignedSpT0P0117Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L030 : ∀ x ∈ Icc ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0118Lo : ℝ) (ceSignedSpT0P0118Hi : ℝ) := by
    norm_num [ceSignedSpT0P0118Lo, ceSignedSpT0P0118Hi, SignedSpT0P0118Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0118Bound x h'
  norm_num [SignedSpT0P0118Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P001L031 : ∀ x ∈ Icc ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0119Lo : ℝ) (ceSignedSpT0P0119Hi : ℝ) := by
    norm_num [ceSignedSpT0P0119Lo, ceSignedSpT0P0119Hi, SignedSpT0P0119Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0119Bound x h'
  norm_num [SignedSpT0P0119Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P001 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P001L016 SignedSpT0CoverD1B0P001L017) (cover_union SignedSpT0CoverD1B0P001L018 SignedSpT0CoverD1B0P001L019)) (cover_union (cover_union SignedSpT0CoverD1B0P001L020 SignedSpT0CoverD1B0P001L021) (cover_union SignedSpT0CoverD1B0P001L022 SignedSpT0CoverD1B0P001L023))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P001L024 SignedSpT0CoverD1B0P001L025) (cover_union SignedSpT0CoverD1B0P001L026 SignedSpT0CoverD1B0P001L027)) (cover_union (cover_union SignedSpT0CoverD1B0P001L028 SignedSpT0CoverD1B0P001L029) (cover_union SignedSpT0CoverD1B0P001L030 SignedSpT0CoverD1B0P001L031))))
#print axioms SignedSpT0CoverD1B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

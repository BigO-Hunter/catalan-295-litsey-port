module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0111
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0119
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0121
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P001L016 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0106Lo : ℝ) (ceSignedSpT2P0106Hi : ℝ) := by
    norm_num [ceSignedSpT2P0106Lo, ceSignedSpT2P0106Hi, SignedSpT2P0106Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0106Bound x h'
  norm_num [SignedSpT2P0106Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L017 : ∀ x ∈ Icc ((((35181150863331 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0107Lo : ℝ) (ceSignedSpT2P0107Hi : ℝ) := by
    norm_num [ceSignedSpT2P0107Lo, ceSignedSpT2P0107Hi, SignedSpT2P0107Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0107Bound x h'
  norm_num [SignedSpT2P0107Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L018 : ∀ x ∈ Icc ((((70363375468485 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0108Lo : ℝ) (ceSignedSpT2P0108Hi : ℝ) := by
    norm_num [ceSignedSpT2P0108Lo, ceSignedSpT2P0108Hi, SignedSpT2P0108Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0108Bound x h'
  norm_num [SignedSpT2P0108Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L019 : ∀ x ∈ Icc ((((140727824678793 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0109Lo : ℝ) (ceSignedSpT2P0109Hi : ℝ) := by
    norm_num [ceSignedSpT2P0109Lo, ceSignedSpT2P0109Hi, SignedSpT2P0109Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0109Bound x h'
  norm_num [SignedSpT2P0109Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L020 : ∀ x ∈ Icc ((((17591112302577 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0110Lo : ℝ) (ceSignedSpT2P0110Hi : ℝ) := by
    norm_num [ceSignedSpT2P0110Lo, ceSignedSpT2P0110Hi, SignedSpT2P0110Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0110Bound x h'
  norm_num [SignedSpT2P0110Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L021 : ∀ x ∈ Icc ((((140729972162439 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0111Lo : ℝ) (ceSignedSpT2P0111Hi : ℝ) := by
    norm_num [ceSignedSpT2P0111Lo, ceSignedSpT2P0111Hi, SignedSpT2P0111Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0111Bound x h'
  norm_num [SignedSpT2P0111Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L022 : ∀ x ∈ Icc ((((70365522952131 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0112Lo : ℝ) (ceSignedSpT2P0112Hi : ℝ) := by
    norm_num [ceSignedSpT2P0112Lo, ceSignedSpT2P0112Hi, SignedSpT2P0112Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0112Bound x h'
  norm_num [SignedSpT2P0112Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L023 : ∀ x ∈ Icc ((((140732119646085 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0113Lo : ℝ) (ceSignedSpT2P0113Hi : ℝ) := by
    norm_num [ceSignedSpT2P0113Lo, ceSignedSpT2P0113Hi, SignedSpT2P0113Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0113Bound x h'
  norm_num [SignedSpT2P0113Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L024 : ∀ x ∈ Icc ((((281465313033993 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0114Lo : ℝ) (ceSignedSpT2P0114Hi : ℝ) := by
    norm_num [ceSignedSpT2P0114Lo, ceSignedSpT2P0114Hi, SignedSpT2P0114Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0114Bound x h'
  norm_num [SignedSpT2P0114Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L025 : ∀ x ∈ Icc ((((35183298346977 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0115Lo : ℝ) (ceSignedSpT2P0115Hi : ℝ) := by
    norm_num [ceSignedSpT2P0115Lo, ceSignedSpT2P0115Hi, SignedSpT2P0115Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0115Bound x h'
  norm_num [SignedSpT2P0115Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L026 : ∀ x ∈ Icc ((((281467460517639 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0116Lo : ℝ) (ceSignedSpT2P0116Hi : ℝ) := by
    norm_num [ceSignedSpT2P0116Lo, ceSignedSpT2P0116Hi, SignedSpT2P0116Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0116Bound x h'
  norm_num [SignedSpT2P0116Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L027 : ∀ x ∈ Icc ((((140734267129731 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0117Lo : ℝ) (ceSignedSpT2P0117Hi : ℝ) := by
    norm_num [ceSignedSpT2P0117Lo, ceSignedSpT2P0117Hi, SignedSpT2P0117Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0117Bound x h'
  norm_num [SignedSpT2P0117Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L028 : ∀ x ∈ Icc ((((281469608001285 : ℚ) / 281474976710656) : ℚ) : ℝ) ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0118Lo : ℝ) (ceSignedSpT2P0118Hi : ℝ) := by
    norm_num [ceSignedSpT2P0118Lo, ceSignedSpT2P0118Hi, SignedSpT2P0118Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0118Bound x h'
  norm_num [SignedSpT2P0118Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L029 : ∀ x ∈ Icc ((((562940289744393 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0119Lo : ℝ) (ceSignedSpT2P0119Hi : ℝ) := by
    norm_num [ceSignedSpT2P0119Lo, ceSignedSpT2P0119Hi, SignedSpT2P0119Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0119Bound x h'
  norm_num [SignedSpT2P0119Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L030 : ∀ x ∈ Icc ((((70367670435777 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0120Lo : ℝ) (ceSignedSpT2P0120Hi : ℝ) := by
    norm_num [ceSignedSpT2P0120Lo, ceSignedSpT2P0120Hi, SignedSpT2P0120Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0120Bound x h'
  norm_num [SignedSpT2P0120Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P001L031 : ∀ x ∈ Icc ((((562942437228039 : ℚ) / 562949953421312) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0121Lo : ℝ) (ceSignedSpT2P0121Hi : ℝ) := by
    norm_num [ceSignedSpT2P0121Lo, ceSignedSpT2P0121Hi, SignedSpT2P0121Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0121Bound x h'
  norm_num [SignedSpT2P0121Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P001 : ∀ x ∈ Icc ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((281471755484931 : ℚ) / 281474976710656) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P001L016 SignedSpT2CoverD1B0P001L017) (cover_union SignedSpT2CoverD1B0P001L018 SignedSpT2CoverD1B0P001L019)) (cover_union (cover_union SignedSpT2CoverD1B0P001L020 SignedSpT2CoverD1B0P001L021) (cover_union SignedSpT2CoverD1B0P001L022 SignedSpT2CoverD1B0P001L023))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P001L024 SignedSpT2CoverD1B0P001L025) (cover_union SignedSpT2CoverD1B0P001L026 SignedSpT2CoverD1B0P001L027)) (cover_union (cover_union SignedSpT2CoverD1B0P001L028 SignedSpT2CoverD1B0P001L029) (cover_union SignedSpT2CoverD1B0P001L030 SignedSpT2CoverD1B0P001L031))))
#print axioms SignedSpT2CoverD1B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

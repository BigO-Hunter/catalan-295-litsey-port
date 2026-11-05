module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0119
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0128
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0113Lo : ℝ) (ceSignedSpmTopT0P0113Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0113Lo, ceSignedSpmTopT0P0113Hi, SignedSpmTopT0P0113Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0113Bound x h'
  norm_num [SignedSpmTopT0P0113Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0114Lo : ℝ) (ceSignedSpmTopT0P0114Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0114Lo, ceSignedSpmTopT0P0114Hi, SignedSpmTopT0P0114Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0114Bound x h'
  norm_num [SignedSpmTopT0P0114Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0115Lo : ℝ) (ceSignedSpmTopT0P0115Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0115Lo, ceSignedSpmTopT0P0115Hi, SignedSpmTopT0P0115Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0115Bound x h'
  norm_num [SignedSpmTopT0P0115Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0116Lo : ℝ) (ceSignedSpmTopT0P0116Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0116Lo, ceSignedSpmTopT0P0116Hi, SignedSpmTopT0P0116Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0116Bound x h'
  norm_num [SignedSpmTopT0P0116Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0117Lo : ℝ) (ceSignedSpmTopT0P0117Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0117Lo, ceSignedSpmTopT0P0117Hi, SignedSpmTopT0P0117Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0117Bound x h'
  norm_num [SignedSpmTopT0P0117Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0118Lo : ℝ) (ceSignedSpmTopT0P0118Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0118Lo, ceSignedSpmTopT0P0118Hi, SignedSpmTopT0P0118Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0118Bound x h'
  norm_num [SignedSpmTopT0P0118Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0119Lo : ℝ) (ceSignedSpmTopT0P0119Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0119Lo, ceSignedSpmTopT0P0119Hi, SignedSpmTopT0P0119Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0119Bound x h'
  norm_num [SignedSpmTopT0P0119Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0120Lo : ℝ) (ceSignedSpmTopT0P0120Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0120Lo, ceSignedSpmTopT0P0120Hi, SignedSpmTopT0P0120Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0120Bound x h'
  norm_num [SignedSpmTopT0P0120Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0121Lo : ℝ) (ceSignedSpmTopT0P0121Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0121Lo, ceSignedSpmTopT0P0121Hi, SignedSpmTopT0P0121Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0121Bound x h'
  norm_num [SignedSpmTopT0P0121Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0122Lo : ℝ) (ceSignedSpmTopT0P0122Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0122Lo, ceSignedSpmTopT0P0122Hi, SignedSpmTopT0P0122Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0122Bound x h'
  norm_num [SignedSpmTopT0P0122Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0123Lo : ℝ) (ceSignedSpmTopT0P0123Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0123Lo, ceSignedSpmTopT0P0123Hi, SignedSpmTopT0P0123Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0123Bound x h'
  norm_num [SignedSpmTopT0P0123Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0124Lo : ℝ) (ceSignedSpmTopT0P0124Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0124Lo, ceSignedSpmTopT0P0124Hi, SignedSpmTopT0P0124Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0124Bound x h'
  norm_num [SignedSpmTopT0P0124Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0125Lo : ℝ) (ceSignedSpmTopT0P0125Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0125Lo, ceSignedSpmTopT0P0125Hi, SignedSpmTopT0P0125Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0125Bound x h'
  norm_num [SignedSpmTopT0P0125Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0126Lo : ℝ) (ceSignedSpmTopT0P0126Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0126Lo, ceSignedSpmTopT0P0126Hi, SignedSpmTopT0P0126Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0126Bound x h'
  norm_num [SignedSpmTopT0P0126Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0127Lo : ℝ) (ceSignedSpmTopT0P0127Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0127Lo, ceSignedSpmTopT0P0127Hi, SignedSpmTopT0P0127Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0127Bound x h'
  norm_num [SignedSpmTopT0P0127Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0128Lo : ℝ) (ceSignedSpmTopT0P0128Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0128Lo, ceSignedSpmTopT0P0128Hi, SignedSpmTopT0P0128Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0128Bound x h'
  norm_num [SignedSpmTopT0P0128Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT0CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P007L112 SignedSpmTopT0CoverD1B0P007L113) (cover_union SignedSpmTopT0CoverD1B0P007L114 SignedSpmTopT0CoverD1B0P007L115)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P007L116 SignedSpmTopT0CoverD1B0P007L117) (cover_union SignedSpmTopT0CoverD1B0P007L118 SignedSpmTopT0CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P007L120 SignedSpmTopT0CoverD1B0P007L121) (cover_union SignedSpmTopT0CoverD1B0P007L122 SignedSpmTopT0CoverD1B0P007L123)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P007L124 SignedSpmTopT0CoverD1B0P007L125) (cover_union SignedSpmTopT0CoverD1B0P007L126 SignedSpmTopT0CoverD1B0P007L127))))
#print axioms SignedSpmTopT0CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

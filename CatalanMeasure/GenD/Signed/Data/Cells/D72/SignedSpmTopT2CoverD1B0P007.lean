module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0119
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0128
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0113Lo : ℝ) (ceSignedSpmTopT2P0113Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0113Lo, ceSignedSpmTopT2P0113Hi, SignedSpmTopT2P0113Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0113Bound x h'
  norm_num [SignedSpmTopT2P0113Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0114Lo : ℝ) (ceSignedSpmTopT2P0114Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0114Lo, ceSignedSpmTopT2P0114Hi, SignedSpmTopT2P0114Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0114Bound x h'
  norm_num [SignedSpmTopT2P0114Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0115Lo : ℝ) (ceSignedSpmTopT2P0115Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0115Lo, ceSignedSpmTopT2P0115Hi, SignedSpmTopT2P0115Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0115Bound x h'
  norm_num [SignedSpmTopT2P0115Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0116Lo : ℝ) (ceSignedSpmTopT2P0116Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0116Lo, ceSignedSpmTopT2P0116Hi, SignedSpmTopT2P0116Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0116Bound x h'
  norm_num [SignedSpmTopT2P0116Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0117Lo : ℝ) (ceSignedSpmTopT2P0117Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0117Lo, ceSignedSpmTopT2P0117Hi, SignedSpmTopT2P0117Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0117Bound x h'
  norm_num [SignedSpmTopT2P0117Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0118Lo : ℝ) (ceSignedSpmTopT2P0118Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0118Lo, ceSignedSpmTopT2P0118Hi, SignedSpmTopT2P0118Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0118Bound x h'
  norm_num [SignedSpmTopT2P0118Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0119Lo : ℝ) (ceSignedSpmTopT2P0119Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0119Lo, ceSignedSpmTopT2P0119Hi, SignedSpmTopT2P0119Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0119Bound x h'
  norm_num [SignedSpmTopT2P0119Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0120Lo : ℝ) (ceSignedSpmTopT2P0120Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0120Lo, ceSignedSpmTopT2P0120Hi, SignedSpmTopT2P0120Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0120Bound x h'
  norm_num [SignedSpmTopT2P0120Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0121Lo : ℝ) (ceSignedSpmTopT2P0121Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0121Lo, ceSignedSpmTopT2P0121Hi, SignedSpmTopT2P0121Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0121Bound x h'
  norm_num [SignedSpmTopT2P0121Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0122Lo : ℝ) (ceSignedSpmTopT2P0122Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0122Lo, ceSignedSpmTopT2P0122Hi, SignedSpmTopT2P0122Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0122Bound x h'
  norm_num [SignedSpmTopT2P0122Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0123Lo : ℝ) (ceSignedSpmTopT2P0123Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0123Lo, ceSignedSpmTopT2P0123Hi, SignedSpmTopT2P0123Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0123Bound x h'
  norm_num [SignedSpmTopT2P0123Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0124Lo : ℝ) (ceSignedSpmTopT2P0124Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0124Lo, ceSignedSpmTopT2P0124Hi, SignedSpmTopT2P0124Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0124Bound x h'
  norm_num [SignedSpmTopT2P0124Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0125Lo : ℝ) (ceSignedSpmTopT2P0125Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0125Lo, ceSignedSpmTopT2P0125Hi, SignedSpmTopT2P0125Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0125Bound x h'
  norm_num [SignedSpmTopT2P0125Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0126Lo : ℝ) (ceSignedSpmTopT2P0126Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0126Lo, ceSignedSpmTopT2P0126Hi, SignedSpmTopT2P0126Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0126Bound x h'
  norm_num [SignedSpmTopT2P0126Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0127Lo : ℝ) (ceSignedSpmTopT2P0127Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0127Lo, ceSignedSpmTopT2P0127Hi, SignedSpmTopT2P0127Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0127Bound x h'
  norm_num [SignedSpmTopT2P0127Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0128Lo : ℝ) (ceSignedSpmTopT2P0128Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0128Lo, ceSignedSpmTopT2P0128Hi, SignedSpmTopT2P0128Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0128Bound x h'
  norm_num [SignedSpmTopT2P0128Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P007L112 SignedSpmTopT2CoverD1B0P007L113) (cover_union SignedSpmTopT2CoverD1B0P007L114 SignedSpmTopT2CoverD1B0P007L115)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P007L116 SignedSpmTopT2CoverD1B0P007L117) (cover_union SignedSpmTopT2CoverD1B0P007L118 SignedSpmTopT2CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P007L120 SignedSpmTopT2CoverD1B0P007L121) (cover_union SignedSpmTopT2CoverD1B0P007L122 SignedSpmTopT2CoverD1B0P007L123)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P007L124 SignedSpmTopT2CoverD1B0P007L125) (cover_union SignedSpmTopT2CoverD1B0P007L126 SignedSpmTopT2CoverD1B0P007L127))))
#print axioms SignedSpmTopT2CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover

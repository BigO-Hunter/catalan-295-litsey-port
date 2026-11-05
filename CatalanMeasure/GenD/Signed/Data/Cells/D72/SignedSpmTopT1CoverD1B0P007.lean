module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0119
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0127
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0128
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0113Lo : ℝ) (ceSignedSpmTopT1P0113Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0113Lo, ceSignedSpmTopT1P0113Hi, SignedSpmTopT1P0113Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0113Bound x h'
  norm_num [SignedSpmTopT1P0113Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0114Lo : ℝ) (ceSignedSpmTopT1P0114Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0114Lo, ceSignedSpmTopT1P0114Hi, SignedSpmTopT1P0114Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0114Bound x h'
  norm_num [SignedSpmTopT1P0114Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0115Lo : ℝ) (ceSignedSpmTopT1P0115Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0115Lo, ceSignedSpmTopT1P0115Hi, SignedSpmTopT1P0115Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0115Bound x h'
  norm_num [SignedSpmTopT1P0115Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0116Lo : ℝ) (ceSignedSpmTopT1P0116Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0116Lo, ceSignedSpmTopT1P0116Hi, SignedSpmTopT1P0116Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0116Bound x h'
  norm_num [SignedSpmTopT1P0116Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0117Lo : ℝ) (ceSignedSpmTopT1P0117Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0117Lo, ceSignedSpmTopT1P0117Hi, SignedSpmTopT1P0117Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0117Bound x h'
  norm_num [SignedSpmTopT1P0117Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0118Lo : ℝ) (ceSignedSpmTopT1P0118Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0118Lo, ceSignedSpmTopT1P0118Hi, SignedSpmTopT1P0118Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0118Bound x h'
  norm_num [SignedSpmTopT1P0118Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0119Lo : ℝ) (ceSignedSpmTopT1P0119Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0119Lo, ceSignedSpmTopT1P0119Hi, SignedSpmTopT1P0119Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0119Bound x h'
  norm_num [SignedSpmTopT1P0119Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0120Lo : ℝ) (ceSignedSpmTopT1P0120Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0120Lo, ceSignedSpmTopT1P0120Hi, SignedSpmTopT1P0120Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0120Bound x h'
  norm_num [SignedSpmTopT1P0120Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0121Lo : ℝ) (ceSignedSpmTopT1P0121Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0121Lo, ceSignedSpmTopT1P0121Hi, SignedSpmTopT1P0121Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0121Bound x h'
  norm_num [SignedSpmTopT1P0121Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0122Lo : ℝ) (ceSignedSpmTopT1P0122Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0122Lo, ceSignedSpmTopT1P0122Hi, SignedSpmTopT1P0122Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0122Bound x h'
  norm_num [SignedSpmTopT1P0122Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0123Lo : ℝ) (ceSignedSpmTopT1P0123Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0123Lo, ceSignedSpmTopT1P0123Hi, SignedSpmTopT1P0123Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0123Bound x h'
  norm_num [SignedSpmTopT1P0123Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0124Lo : ℝ) (ceSignedSpmTopT1P0124Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0124Lo, ceSignedSpmTopT1P0124Hi, SignedSpmTopT1P0124Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0124Bound x h'
  norm_num [SignedSpmTopT1P0124Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0125Lo : ℝ) (ceSignedSpmTopT1P0125Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0125Lo, ceSignedSpmTopT1P0125Hi, SignedSpmTopT1P0125Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0125Bound x h'
  norm_num [SignedSpmTopT1P0125Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0126Lo : ℝ) (ceSignedSpmTopT1P0126Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0126Lo, ceSignedSpmTopT1P0126Hi, SignedSpmTopT1P0126Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0126Bound x h'
  norm_num [SignedSpmTopT1P0126Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0127Lo : ℝ) (ceSignedSpmTopT1P0127Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0127Lo, ceSignedSpmTopT1P0127Hi, SignedSpmTopT1P0127Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0127Bound x h'
  norm_num [SignedSpmTopT1P0127Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT1CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0128Lo : ℝ) (ceSignedSpmTopT1P0128Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0128Lo, ceSignedSpmTopT1P0128Hi, SignedSpmTopT1P0128Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0128Bound x h'
  norm_num [SignedSpmTopT1P0128Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-57030279665533 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P007L112 SignedSpmTopT1CoverD1B0P007L113) (cover_union SignedSpmTopT1CoverD1B0P007L114 SignedSpmTopT1CoverD1B0P007L115)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P007L116 SignedSpmTopT1CoverD1B0P007L117) (cover_union SignedSpmTopT1CoverD1B0P007L118 SignedSpmTopT1CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpmTopT1CoverD1B0P007L120 SignedSpmTopT1CoverD1B0P007L121) (cover_union SignedSpmTopT1CoverD1B0P007L122 SignedSpmTopT1CoverD1B0P007L123)) (cover_union (cover_union SignedSpmTopT1CoverD1B0P007L124 SignedSpmTopT1CoverD1B0P007L125) (cover_union SignedSpmTopT1CoverD1B0P007L126 SignedSpmTopT1CoverD1B0P007L127))))
#print axioms SignedSpmTopT1CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover

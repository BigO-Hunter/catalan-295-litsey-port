module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0200
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0201
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0207
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0215
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0200Lo : ℝ) (ceSignedSpT1P0200Hi : ℝ) := by
    norm_num [ceSignedSpT1P0200Lo, ceSignedSpT1P0200Hi, SignedSpT1P0200Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0200Bound x h'
  norm_num [SignedSpT1P0200Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0201Lo : ℝ) (ceSignedSpT1P0201Hi : ℝ) := by
    norm_num [ceSignedSpT1P0201Lo, ceSignedSpT1P0201Hi, SignedSpT1P0201Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0201Bound x h'
  norm_num [SignedSpT1P0201Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0202Lo : ℝ) (ceSignedSpT1P0202Hi : ℝ) := by
    norm_num [ceSignedSpT1P0202Lo, ceSignedSpT1P0202Hi, SignedSpT1P0202Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0202Bound x h'
  norm_num [SignedSpT1P0202Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0203Lo : ℝ) (ceSignedSpT1P0203Hi : ℝ) := by
    norm_num [ceSignedSpT1P0203Lo, ceSignedSpT1P0203Hi, SignedSpT1P0203Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0203Bound x h'
  norm_num [SignedSpT1P0203Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0204Lo : ℝ) (ceSignedSpT1P0204Hi : ℝ) := by
    norm_num [ceSignedSpT1P0204Lo, ceSignedSpT1P0204Hi, SignedSpT1P0204Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0204Bound x h'
  norm_num [SignedSpT1P0204Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0205Lo : ℝ) (ceSignedSpT1P0205Hi : ℝ) := by
    norm_num [ceSignedSpT1P0205Lo, ceSignedSpT1P0205Hi, SignedSpT1P0205Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0205Bound x h'
  norm_num [SignedSpT1P0205Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0206Lo : ℝ) (ceSignedSpT1P0206Hi : ℝ) := by
    norm_num [ceSignedSpT1P0206Lo, ceSignedSpT1P0206Hi, SignedSpT1P0206Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0206Bound x h'
  norm_num [SignedSpT1P0206Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0207Lo : ℝ) (ceSignedSpT1P0207Hi : ℝ) := by
    norm_num [ceSignedSpT1P0207Lo, ceSignedSpT1P0207Hi, SignedSpT1P0207Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0207Bound x h'
  norm_num [SignedSpT1P0207Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0208Lo : ℝ) (ceSignedSpT1P0208Hi : ℝ) := by
    norm_num [ceSignedSpT1P0208Lo, ceSignedSpT1P0208Hi, SignedSpT1P0208Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0208Bound x h'
  norm_num [SignedSpT1P0208Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0209Lo : ℝ) (ceSignedSpT1P0209Hi : ℝ) := by
    norm_num [ceSignedSpT1P0209Lo, ceSignedSpT1P0209Hi, SignedSpT1P0209Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0209Bound x h'
  norm_num [SignedSpT1P0209Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0210Lo : ℝ) (ceSignedSpT1P0210Hi : ℝ) := by
    norm_num [ceSignedSpT1P0210Lo, ceSignedSpT1P0210Hi, SignedSpT1P0210Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0210Bound x h'
  norm_num [SignedSpT1P0210Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0211Lo : ℝ) (ceSignedSpT1P0211Hi : ℝ) := by
    norm_num [ceSignedSpT1P0211Lo, ceSignedSpT1P0211Hi, SignedSpT1P0211Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0211Bound x h'
  norm_num [SignedSpT1P0211Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0212Lo : ℝ) (ceSignedSpT1P0212Hi : ℝ) := by
    norm_num [ceSignedSpT1P0212Lo, ceSignedSpT1P0212Hi, SignedSpT1P0212Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0212Bound x h'
  norm_num [SignedSpT1P0212Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0213Lo : ℝ) (ceSignedSpT1P0213Hi : ℝ) := by
    norm_num [ceSignedSpT1P0213Lo, ceSignedSpT1P0213Hi, SignedSpT1P0213Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0213Bound x h'
  norm_num [SignedSpT1P0213Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0214Lo : ℝ) (ceSignedSpT1P0214Hi : ℝ) := by
    norm_num [ceSignedSpT1P0214Lo, ceSignedSpT1P0214Hi, SignedSpT1P0214Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0214Bound x h'
  norm_num [SignedSpT1P0214Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0215Lo : ℝ) (ceSignedSpT1P0215Hi : ℝ) := by
    norm_num [ceSignedSpT1P0215Lo, ceSignedSpT1P0215Hi, SignedSpT1P0215Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0215Bound x h'
  norm_num [SignedSpT1P0215Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P007L112 SignedSpT1CoverD1B0P007L113) (cover_union SignedSpT1CoverD1B0P007L114 SignedSpT1CoverD1B0P007L115)) (cover_union (cover_union SignedSpT1CoverD1B0P007L116 SignedSpT1CoverD1B0P007L117) (cover_union SignedSpT1CoverD1B0P007L118 SignedSpT1CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P007L120 SignedSpT1CoverD1B0P007L121) (cover_union SignedSpT1CoverD1B0P007L122 SignedSpT1CoverD1B0P007L123)) (cover_union (cover_union SignedSpT1CoverD1B0P007L124 SignedSpT1CoverD1B0P007L125) (cover_union SignedSpT1CoverD1B0P007L126 SignedSpT1CoverD1B0P007L127))))
#print axioms SignedSpT1CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

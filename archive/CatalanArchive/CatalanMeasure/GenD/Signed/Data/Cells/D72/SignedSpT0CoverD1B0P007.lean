module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0200
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0201
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0207
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0215
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0200Lo : ℝ) (ceSignedSpT0P0200Hi : ℝ) := by
    norm_num [ceSignedSpT0P0200Lo, ceSignedSpT0P0200Hi, SignedSpT0P0200Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0200Bound x h'
  norm_num [SignedSpT0P0200Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0201Lo : ℝ) (ceSignedSpT0P0201Hi : ℝ) := by
    norm_num [ceSignedSpT0P0201Lo, ceSignedSpT0P0201Hi, SignedSpT0P0201Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0201Bound x h'
  norm_num [SignedSpT0P0201Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0202Lo : ℝ) (ceSignedSpT0P0202Hi : ℝ) := by
    norm_num [ceSignedSpT0P0202Lo, ceSignedSpT0P0202Hi, SignedSpT0P0202Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0202Bound x h'
  norm_num [SignedSpT0P0202Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0203Lo : ℝ) (ceSignedSpT0P0203Hi : ℝ) := by
    norm_num [ceSignedSpT0P0203Lo, ceSignedSpT0P0203Hi, SignedSpT0P0203Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0203Bound x h'
  norm_num [SignedSpT0P0203Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0204Lo : ℝ) (ceSignedSpT0P0204Hi : ℝ) := by
    norm_num [ceSignedSpT0P0204Lo, ceSignedSpT0P0204Hi, SignedSpT0P0204Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0204Bound x h'
  norm_num [SignedSpT0P0204Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0205Lo : ℝ) (ceSignedSpT0P0205Hi : ℝ) := by
    norm_num [ceSignedSpT0P0205Lo, ceSignedSpT0P0205Hi, SignedSpT0P0205Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0205Bound x h'
  norm_num [SignedSpT0P0205Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0206Lo : ℝ) (ceSignedSpT0P0206Hi : ℝ) := by
    norm_num [ceSignedSpT0P0206Lo, ceSignedSpT0P0206Hi, SignedSpT0P0206Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0206Bound x h'
  norm_num [SignedSpT0P0206Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0207Lo : ℝ) (ceSignedSpT0P0207Hi : ℝ) := by
    norm_num [ceSignedSpT0P0207Lo, ceSignedSpT0P0207Hi, SignedSpT0P0207Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0207Bound x h'
  norm_num [SignedSpT0P0207Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0208Lo : ℝ) (ceSignedSpT0P0208Hi : ℝ) := by
    norm_num [ceSignedSpT0P0208Lo, ceSignedSpT0P0208Hi, SignedSpT0P0208Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0208Bound x h'
  norm_num [SignedSpT0P0208Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0209Lo : ℝ) (ceSignedSpT0P0209Hi : ℝ) := by
    norm_num [ceSignedSpT0P0209Lo, ceSignedSpT0P0209Hi, SignedSpT0P0209Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0209Bound x h'
  norm_num [SignedSpT0P0209Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0210Lo : ℝ) (ceSignedSpT0P0210Hi : ℝ) := by
    norm_num [ceSignedSpT0P0210Lo, ceSignedSpT0P0210Hi, SignedSpT0P0210Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0210Bound x h'
  norm_num [SignedSpT0P0210Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0211Lo : ℝ) (ceSignedSpT0P0211Hi : ℝ) := by
    norm_num [ceSignedSpT0P0211Lo, ceSignedSpT0P0211Hi, SignedSpT0P0211Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0211Bound x h'
  norm_num [SignedSpT0P0211Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0212Lo : ℝ) (ceSignedSpT0P0212Hi : ℝ) := by
    norm_num [ceSignedSpT0P0212Lo, ceSignedSpT0P0212Hi, SignedSpT0P0212Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0212Bound x h'
  norm_num [SignedSpT0P0212Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0213Lo : ℝ) (ceSignedSpT0P0213Hi : ℝ) := by
    norm_num [ceSignedSpT0P0213Lo, ceSignedSpT0P0213Hi, SignedSpT0P0213Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0213Bound x h'
  norm_num [SignedSpT0P0213Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0214Lo : ℝ) (ceSignedSpT0P0214Hi : ℝ) := by
    norm_num [ceSignedSpT0P0214Lo, ceSignedSpT0P0214Hi, SignedSpT0P0214Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0214Bound x h'
  norm_num [SignedSpT0P0214Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0215Lo : ℝ) (ceSignedSpT0P0215Hi : ℝ) := by
    norm_num [ceSignedSpT0P0215Lo, ceSignedSpT0P0215Hi, SignedSpT0P0215Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0215Bound x h'
  norm_num [SignedSpT0P0215Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P007L112 SignedSpT0CoverD1B0P007L113) (cover_union SignedSpT0CoverD1B0P007L114 SignedSpT0CoverD1B0P007L115)) (cover_union (cover_union SignedSpT0CoverD1B0P007L116 SignedSpT0CoverD1B0P007L117) (cover_union SignedSpT0CoverD1B0P007L118 SignedSpT0CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P007L120 SignedSpT0CoverD1B0P007L121) (cover_union SignedSpT0CoverD1B0P007L122 SignedSpT0CoverD1B0P007L123)) (cover_union (cover_union SignedSpT0CoverD1B0P007L124 SignedSpT0CoverD1B0P007L125) (cover_union SignedSpT0CoverD1B0P007L126 SignedSpT0CoverD1B0P007L127))))
#print axioms SignedSpT0CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

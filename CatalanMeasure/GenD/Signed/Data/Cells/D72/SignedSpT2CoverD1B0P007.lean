module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0207
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0215
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0217
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P007L112 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0202Lo : ℝ) (ceSignedSpT2P0202Hi : ℝ) := by
    norm_num [ceSignedSpT2P0202Lo, ceSignedSpT2P0202Hi, SignedSpT2P0202Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0202Bound x h'
  norm_num [SignedSpT2P0202Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L113 : ∀ x ∈ Icc ((((36893488142016839685 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0203Lo : ℝ) (ceSignedSpT2P0203Hi : ℝ) := by
    norm_num [ceSignedSpT2P0203Lo, ceSignedSpT2P0203Hi, SignedSpT2P0203Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0203Bound x h'
  norm_num [SignedSpT2P0203Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L114 : ∀ x ∈ Icc ((((73786976285107421193 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0204Lo : ℝ) (ceSignedSpT2P0204Hi : ℝ) := by
    norm_num [ceSignedSpT2P0204Lo, ceSignedSpT2P0204Hi, SignedSpT2P0204Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0204Bound x h'
  norm_num [SignedSpT2P0204Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L115 : ∀ x ∈ Icc ((((9223372035772645377 : ℚ) / 9223372036854775808) : ℚ) : ℝ) ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0205Lo : ℝ) (ceSignedSpT2P0205Hi : ℝ) := by
    norm_num [ceSignedSpT2P0205Lo, ceSignedSpT2P0205Hi, SignedSpT2P0205Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0205Bound x h'
  norm_num [SignedSpT2P0205Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L116 : ∀ x ∈ Icc ((((73786976287254904839 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0206Lo : ℝ) (ceSignedSpT2P0206Hi : ℝ) := by
    norm_num [ceSignedSpT2P0206Lo, ceSignedSpT2P0206Hi, SignedSpT2P0206Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0206Bound x h'
  norm_num [SignedSpT2P0206Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L117 : ∀ x ∈ Icc ((((36893488144164323331 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0207Lo : ℝ) (ceSignedSpT2P0207Hi : ℝ) := by
    norm_num [ceSignedSpT2P0207Lo, ceSignedSpT2P0207Hi, SignedSpT2P0207Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0207Bound x h'
  norm_num [SignedSpT2P0207Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L118 : ∀ x ∈ Icc ((((73786976289402388485 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0208Lo : ℝ) (ceSignedSpT2P0208Hi : ℝ) := by
    norm_num [ceSignedSpT2P0208Lo, ceSignedSpT2P0208Hi, SignedSpT2P0208Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0208Bound x h'
  norm_num [SignedSpT2P0208Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L119 : ∀ x ∈ Icc ((((147573952579878518793 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0209Lo : ℝ) (ceSignedSpT2P0209Hi : ℝ) := by
    norm_num [ceSignedSpT2P0209Lo, ceSignedSpT2P0209Hi, SignedSpT2P0209Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0209Bound x h'
  norm_num [SignedSpT2P0209Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L120 : ∀ x ∈ Icc ((((18446744072619032577 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0210Lo : ℝ) (ceSignedSpT2P0210Hi : ℝ) := by
    norm_num [ceSignedSpT2P0210Lo, ceSignedSpT2P0210Hi, SignedSpT2P0210Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0210Bound x h'
  norm_num [SignedSpT2P0210Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L121 : ∀ x ∈ Icc ((((147573952582026002439 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0211Lo : ℝ) (ceSignedSpT2P0211Hi : ℝ) := by
    norm_num [ceSignedSpT2P0211Lo, ceSignedSpT2P0211Hi, SignedSpT2P0211Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0211Bound x h'
  norm_num [SignedSpT2P0211Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L122 : ∀ x ∈ Icc ((((73786976291549872131 : ℚ) / 73786976294838206464) : ℚ) : ℝ) ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0212Lo : ℝ) (ceSignedSpT2P0212Hi : ℝ) := by
    norm_num [ceSignedSpT2P0212Lo, ceSignedSpT2P0212Hi, SignedSpT2P0212Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0212Bound x h'
  norm_num [SignedSpT2P0212Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L123 : ∀ x ∈ Icc ((((147573952584173486085 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0213Lo : ℝ) (ceSignedSpT2P0213Hi : ℝ) := by
    norm_num [ceSignedSpT2P0213Lo, ceSignedSpT2P0213Hi, SignedSpT2P0213Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0213Bound x h'
  norm_num [SignedSpT2P0213Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L124 : ∀ x ∈ Icc ((((295147905169420713993 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0214Lo : ℝ) (ceSignedSpT2P0214Hi : ℝ) := by
    norm_num [ceSignedSpT2P0214Lo, ceSignedSpT2P0214Hi, SignedSpT2P0214Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0214Bound x h'
  norm_num [SignedSpT2P0214Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L125 : ∀ x ∈ Icc ((((36893488146311806977 : ℚ) / 36893488147419103232) : ℚ) : ℝ) ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0215Lo : ℝ) (ceSignedSpT2P0215Hi : ℝ) := by
    norm_num [ceSignedSpT2P0215Lo, ceSignedSpT2P0215Hi, SignedSpT2P0215Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0215Bound x h'
  norm_num [SignedSpT2P0215Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L126 : ∀ x ∈ Icc ((((295147905171568197639 : ℚ) / 295147905179352825856) : ℚ) : ℝ) ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0216Lo : ℝ) (ceSignedSpT2P0216Hi : ℝ) := by
    norm_num [ceSignedSpT2P0216Lo, ceSignedSpT2P0216Hi, SignedSpT2P0216Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0216Bound x h'
  norm_num [SignedSpT2P0216Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P007L127 : ∀ x ∈ Icc ((((147573952586320969731 : ℚ) / 147573952589676412928) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0217Lo : ℝ) (ceSignedSpT2P0217Hi : ℝ) := by
    norm_num [ceSignedSpT2P0217Lo, ceSignedSpT2P0217Hi, SignedSpT2P0217Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0217Bound x h'
  norm_num [SignedSpT2P0217Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P007 : ∀ x ∈ Icc ((((18446744070471548931 : ℚ) / 18446744073709551616) : ℚ) : ℝ) ((((295147905173715681285 : ℚ) / 295147905179352825856) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P007L112 SignedSpT2CoverD1B0P007L113) (cover_union SignedSpT2CoverD1B0P007L114 SignedSpT2CoverD1B0P007L115)) (cover_union (cover_union SignedSpT2CoverD1B0P007L116 SignedSpT2CoverD1B0P007L117) (cover_union SignedSpT2CoverD1B0P007L118 SignedSpT2CoverD1B0P007L119))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P007L120 SignedSpT2CoverD1B0P007L121) (cover_union SignedSpT2CoverD1B0P007L122 SignedSpT2CoverD1B0P007L123)) (cover_union (cover_union SignedSpT2CoverD1B0P007L124 SignedSpT2CoverD1B0P007L125) (cover_union SignedSpT2CoverD1B0P007L126 SignedSpT2CoverD1B0P007L127))))
#print axioms SignedSpT2CoverD1B0P007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

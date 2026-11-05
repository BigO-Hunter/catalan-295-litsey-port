module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0P0033
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT0CoverD0B1P000L000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((15231 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0018Lo : ℝ) (ceSignedSpT0P0018Hi : ℝ) := by
    norm_num [ceSignedSpT0P0018Lo, ceSignedSpT0P0018Hi, SignedSpT0P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0018Bound x h'
  norm_num [SignedSpT0P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L001 : ∀ x ∈ Icc ((((15231 : ℚ) / 114688) : ℚ) : ℝ) ((((8063 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0019Lo : ℝ) (ceSignedSpT0P0019Hi : ℝ) := by
    norm_num [ceSignedSpT0P0019Lo, ceSignedSpT0P0019Hi, SignedSpT0P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0019Bound x h'
  norm_num [SignedSpT0P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L002 : ∀ x ∈ Icc ((((8063 : ℚ) / 57344) : ℚ) : ℝ) ((((17021 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0020Lo : ℝ) (ceSignedSpT0P0020Hi : ℝ) := by
    norm_num [ceSignedSpT0P0020Lo, ceSignedSpT0P0020Hi, SignedSpT0P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0020Bound x h'
  norm_num [SignedSpT0P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L003 : ∀ x ∈ Icc ((((17021 : ℚ) / 114688) : ℚ) : ℝ) ((((4479 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0021Lo : ℝ) (ceSignedSpT0P0021Hi : ℝ) := by
    norm_num [ceSignedSpT0P0021Lo, ceSignedSpT0P0021Hi, SignedSpT0P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0021Bound x h'
  norm_num [SignedSpT0P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L004 : ∀ x ∈ Icc ((((4479 : ℚ) / 28672) : ℚ) : ℝ) ((((18811 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0022Lo : ℝ) (ceSignedSpT0P0022Hi : ℝ) := by
    norm_num [ceSignedSpT0P0022Lo, ceSignedSpT0P0022Hi, SignedSpT0P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0022Bound x h'
  norm_num [SignedSpT0P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L005 : ∀ x ∈ Icc ((((18811 : ℚ) / 114688) : ℚ) : ℝ) ((((9853 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0023Lo : ℝ) (ceSignedSpT0P0023Hi : ℝ) := by
    norm_num [ceSignedSpT0P0023Lo, ceSignedSpT0P0023Hi, SignedSpT0P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0023Bound x h'
  norm_num [SignedSpT0P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L006 : ∀ x ∈ Icc ((((9853 : ℚ) / 57344) : ℚ) : ℝ) ((((2943 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0024Lo : ℝ) (ceSignedSpT0P0024Hi : ℝ) := by
    norm_num [ceSignedSpT0P0024Lo, ceSignedSpT0P0024Hi, SignedSpT0P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0024Bound x h'
  norm_num [SignedSpT0P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L007 : ∀ x ∈ Icc ((((2943 : ℚ) / 16384) : ℚ) : ℝ) ((((2687 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0025Lo : ℝ) (ceSignedSpT0P0025Hi : ℝ) := by
    norm_num [ceSignedSpT0P0025Lo, ceSignedSpT0P0025Hi, SignedSpT0P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0025Bound x h'
  norm_num [SignedSpT0P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L008 : ∀ x ∈ Icc ((((2687 : ℚ) / 14336) : ℚ) : ℝ) ((((22391 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0026Lo : ℝ) (ceSignedSpT0P0026Hi : ℝ) := by
    norm_num [ceSignedSpT0P0026Lo, ceSignedSpT0P0026Hi, SignedSpT0P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0026Bound x h'
  norm_num [SignedSpT0P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L009 : ∀ x ∈ Icc ((((22391 : ℚ) / 114688) : ℚ) : ℝ) ((((11643 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0027Lo : ℝ) (ceSignedSpT0P0027Hi : ℝ) := by
    norm_num [ceSignedSpT0P0027Lo, ceSignedSpT0P0027Hi, SignedSpT0P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0027Bound x h'
  norm_num [SignedSpT0P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L010 : ∀ x ∈ Icc ((((11643 : ℚ) / 57344) : ℚ) : ℝ) ((((6269 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0028Lo : ℝ) (ceSignedSpT0P0028Hi : ℝ) := by
    norm_num [ceSignedSpT0P0028Lo, ceSignedSpT0P0028Hi, SignedSpT0P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0028Bound x h'
  norm_num [SignedSpT0P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L011 : ∀ x ∈ Icc ((((6269 : ℚ) / 28672) : ℚ) : ℝ) ((((1919 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0029Lo : ℝ) (ceSignedSpT0P0029Hi : ℝ) := by
    norm_num [ceSignedSpT0P0029Lo, ceSignedSpT0P0029Hi, SignedSpT0P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0029Bound x h'
  norm_num [SignedSpT0P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L012 : ∀ x ∈ Icc ((((1919 : ℚ) / 8192) : ℚ) : ℝ) ((((1791 : ℚ) / 7168) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0030Lo : ℝ) (ceSignedSpT0P0030Hi : ℝ) := by
    norm_num [ceSignedSpT0P0030Lo, ceSignedSpT0P0030Hi, SignedSpT0P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0030Bound x h'
  norm_num [SignedSpT0P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L013 : ∀ x ∈ Icc ((((1791 : ℚ) / 7168) : ℚ) : ℝ) ((((15223 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0031Lo : ℝ) (ceSignedSpT0P0031Hi : ℝ) := by
    norm_num [ceSignedSpT0P0031Lo, ceSignedSpT0P0031Hi, SignedSpT0P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0031Bound x h'
  norm_num [SignedSpT0P0031Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L014 : ∀ x ∈ Icc ((((15223 : ℚ) / 57344) : ℚ) : ℝ) ((((8059 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0032Lo : ℝ) (ceSignedSpT0P0032Hi : ℝ) := by
    norm_num [ceSignedSpT0P0032Lo, ceSignedSpT0P0032Hi, SignedSpT0P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0032Bound x h'
  norm_num [SignedSpT0P0032Literal.q2] at h ⊢
  exact h

private theorem SignedSpT0CoverD0B1P000L015 : ∀ x ∈ Icc ((((8059 : ℚ) / 28672) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT0P0033Lo : ℝ) (ceSignedSpT0P0033Hi : ℝ) := by
    norm_num [ceSignedSpT0P0033Lo, ceSignedSpT0P0033Hi, SignedSpT0P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT0P0033Bound x h'
  norm_num [SignedSpT0P0033Literal.q2] at h ⊢
  exact h

theorem SignedSpT0CoverD0B1P000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P000L000 SignedSpT0CoverD0B1P000L001) (cover_union SignedSpT0CoverD0B1P000L002 SignedSpT0CoverD0B1P000L003)) (cover_union (cover_union SignedSpT0CoverD0B1P000L004 SignedSpT0CoverD0B1P000L005) (cover_union SignedSpT0CoverD0B1P000L006 SignedSpT0CoverD0B1P000L007))) (cover_union (cover_union (cover_union SignedSpT0CoverD0B1P000L008 SignedSpT0CoverD0B1P000L009) (cover_union SignedSpT0CoverD0B1P000L010 SignedSpT0CoverD0B1P000L011)) (cover_union (cover_union SignedSpT0CoverD0B1P000L012 SignedSpT0CoverD0B1P000L013) (cover_union SignedSpT0CoverD0B1P000L014 SignedSpT0CoverD0B1P000L015))))
#print axioms SignedSpT0CoverD0B1P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

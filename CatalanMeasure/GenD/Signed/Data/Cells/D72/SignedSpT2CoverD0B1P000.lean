module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0033
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD0B1P000L000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((15231 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0018Lo : ℝ) (ceSignedSpT2P0018Hi : ℝ) := by
    norm_num [ceSignedSpT2P0018Lo, ceSignedSpT2P0018Hi, SignedSpT2P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0018Bound x h'
  norm_num [SignedSpT2P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L001 : ∀ x ∈ Icc ((((15231 : ℚ) / 114688) : ℚ) : ℝ) ((((8063 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0019Lo : ℝ) (ceSignedSpT2P0019Hi : ℝ) := by
    norm_num [ceSignedSpT2P0019Lo, ceSignedSpT2P0019Hi, SignedSpT2P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0019Bound x h'
  norm_num [SignedSpT2P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L002 : ∀ x ∈ Icc ((((8063 : ℚ) / 57344) : ℚ) : ℝ) ((((17021 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0020Lo : ℝ) (ceSignedSpT2P0020Hi : ℝ) := by
    norm_num [ceSignedSpT2P0020Lo, ceSignedSpT2P0020Hi, SignedSpT2P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0020Bound x h'
  norm_num [SignedSpT2P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L003 : ∀ x ∈ Icc ((((17021 : ℚ) / 114688) : ℚ) : ℝ) ((((4479 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0021Lo : ℝ) (ceSignedSpT2P0021Hi : ℝ) := by
    norm_num [ceSignedSpT2P0021Lo, ceSignedSpT2P0021Hi, SignedSpT2P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0021Bound x h'
  norm_num [SignedSpT2P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L004 : ∀ x ∈ Icc ((((4479 : ℚ) / 28672) : ℚ) : ℝ) ((((18811 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0022Lo : ℝ) (ceSignedSpT2P0022Hi : ℝ) := by
    norm_num [ceSignedSpT2P0022Lo, ceSignedSpT2P0022Hi, SignedSpT2P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0022Bound x h'
  norm_num [SignedSpT2P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L005 : ∀ x ∈ Icc ((((18811 : ℚ) / 114688) : ℚ) : ℝ) ((((9853 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0023Lo : ℝ) (ceSignedSpT2P0023Hi : ℝ) := by
    norm_num [ceSignedSpT2P0023Lo, ceSignedSpT2P0023Hi, SignedSpT2P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0023Bound x h'
  norm_num [SignedSpT2P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L006 : ∀ x ∈ Icc ((((9853 : ℚ) / 57344) : ℚ) : ℝ) ((((2943 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0024Lo : ℝ) (ceSignedSpT2P0024Hi : ℝ) := by
    norm_num [ceSignedSpT2P0024Lo, ceSignedSpT2P0024Hi, SignedSpT2P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0024Bound x h'
  norm_num [SignedSpT2P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L007 : ∀ x ∈ Icc ((((2943 : ℚ) / 16384) : ℚ) : ℝ) ((((2687 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0025Lo : ℝ) (ceSignedSpT2P0025Hi : ℝ) := by
    norm_num [ceSignedSpT2P0025Lo, ceSignedSpT2P0025Hi, SignedSpT2P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0025Bound x h'
  norm_num [SignedSpT2P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L008 : ∀ x ∈ Icc ((((2687 : ℚ) / 14336) : ℚ) : ℝ) ((((22391 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0026Lo : ℝ) (ceSignedSpT2P0026Hi : ℝ) := by
    norm_num [ceSignedSpT2P0026Lo, ceSignedSpT2P0026Hi, SignedSpT2P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0026Bound x h'
  norm_num [SignedSpT2P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L009 : ∀ x ∈ Icc ((((22391 : ℚ) / 114688) : ℚ) : ℝ) ((((11643 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0027Lo : ℝ) (ceSignedSpT2P0027Hi : ℝ) := by
    norm_num [ceSignedSpT2P0027Lo, ceSignedSpT2P0027Hi, SignedSpT2P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0027Bound x h'
  norm_num [SignedSpT2P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L010 : ∀ x ∈ Icc ((((11643 : ℚ) / 57344) : ℚ) : ℝ) ((((6269 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0028Lo : ℝ) (ceSignedSpT2P0028Hi : ℝ) := by
    norm_num [ceSignedSpT2P0028Lo, ceSignedSpT2P0028Hi, SignedSpT2P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0028Bound x h'
  norm_num [SignedSpT2P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L011 : ∀ x ∈ Icc ((((6269 : ℚ) / 28672) : ℚ) : ℝ) ((((1919 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0029Lo : ℝ) (ceSignedSpT2P0029Hi : ℝ) := by
    norm_num [ceSignedSpT2P0029Lo, ceSignedSpT2P0029Hi, SignedSpT2P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0029Bound x h'
  norm_num [SignedSpT2P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L012 : ∀ x ∈ Icc ((((1919 : ℚ) / 8192) : ℚ) : ℝ) ((((1791 : ℚ) / 7168) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0030Lo : ℝ) (ceSignedSpT2P0030Hi : ℝ) := by
    norm_num [ceSignedSpT2P0030Lo, ceSignedSpT2P0030Hi, SignedSpT2P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0030Bound x h'
  norm_num [SignedSpT2P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L013 : ∀ x ∈ Icc ((((1791 : ℚ) / 7168) : ℚ) : ℝ) ((((15223 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0031Lo : ℝ) (ceSignedSpT2P0031Hi : ℝ) := by
    norm_num [ceSignedSpT2P0031Lo, ceSignedSpT2P0031Hi, SignedSpT2P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0031Bound x h'
  norm_num [SignedSpT2P0031Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L014 : ∀ x ∈ Icc ((((15223 : ℚ) / 57344) : ℚ) : ℝ) ((((8059 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0032Lo : ℝ) (ceSignedSpT2P0032Hi : ℝ) := by
    norm_num [ceSignedSpT2P0032Lo, ceSignedSpT2P0032Hi, SignedSpT2P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0032Bound x h'
  norm_num [SignedSpT2P0032Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD0B1P000L015 : ∀ x ∈ Icc ((((8059 : ℚ) / 28672) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0033Lo : ℝ) (ceSignedSpT2P0033Hi : ℝ) := by
    norm_num [ceSignedSpT2P0033Lo, ceSignedSpT2P0033Hi, SignedSpT2P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0033Bound x h'
  norm_num [SignedSpT2P0033Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD0B1P000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P000L000 SignedSpT2CoverD0B1P000L001) (cover_union SignedSpT2CoverD0B1P000L002 SignedSpT2CoverD0B1P000L003)) (cover_union (cover_union SignedSpT2CoverD0B1P000L004 SignedSpT2CoverD0B1P000L005) (cover_union SignedSpT2CoverD0B1P000L006 SignedSpT2CoverD0B1P000L007))) (cover_union (cover_union (cover_union SignedSpT2CoverD0B1P000L008 SignedSpT2CoverD0B1P000L009) (cover_union SignedSpT2CoverD0B1P000L010 SignedSpT2CoverD0B1P000L011)) (cover_union (cover_union SignedSpT2CoverD0B1P000L012 SignedSpT2CoverD0B1P000L013) (cover_union SignedSpT2CoverD0B1P000L014 SignedSpT2CoverD0B1P000L015))))
#print axioms SignedSpT2CoverD0B1P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

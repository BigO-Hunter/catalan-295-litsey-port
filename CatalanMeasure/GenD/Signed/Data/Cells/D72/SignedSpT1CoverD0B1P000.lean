module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0033
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD0B1P000L000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((15231 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0018Lo : ℝ) (ceSignedSpT1P0018Hi : ℝ) := by
    norm_num [ceSignedSpT1P0018Lo, ceSignedSpT1P0018Hi, SignedSpT1P0018Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0018Bound x h'
  norm_num [SignedSpT1P0018Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L001 : ∀ x ∈ Icc ((((15231 : ℚ) / 114688) : ℚ) : ℝ) ((((8063 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0019Lo : ℝ) (ceSignedSpT1P0019Hi : ℝ) := by
    norm_num [ceSignedSpT1P0019Lo, ceSignedSpT1P0019Hi, SignedSpT1P0019Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0019Bound x h'
  norm_num [SignedSpT1P0019Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L002 : ∀ x ∈ Icc ((((8063 : ℚ) / 57344) : ℚ) : ℝ) ((((17021 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0020Lo : ℝ) (ceSignedSpT1P0020Hi : ℝ) := by
    norm_num [ceSignedSpT1P0020Lo, ceSignedSpT1P0020Hi, SignedSpT1P0020Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0020Bound x h'
  norm_num [SignedSpT1P0020Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L003 : ∀ x ∈ Icc ((((17021 : ℚ) / 114688) : ℚ) : ℝ) ((((4479 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0021Lo : ℝ) (ceSignedSpT1P0021Hi : ℝ) := by
    norm_num [ceSignedSpT1P0021Lo, ceSignedSpT1P0021Hi, SignedSpT1P0021Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0021Bound x h'
  norm_num [SignedSpT1P0021Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L004 : ∀ x ∈ Icc ((((4479 : ℚ) / 28672) : ℚ) : ℝ) ((((18811 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0022Lo : ℝ) (ceSignedSpT1P0022Hi : ℝ) := by
    norm_num [ceSignedSpT1P0022Lo, ceSignedSpT1P0022Hi, SignedSpT1P0022Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0022Bound x h'
  norm_num [SignedSpT1P0022Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L005 : ∀ x ∈ Icc ((((18811 : ℚ) / 114688) : ℚ) : ℝ) ((((9853 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0023Lo : ℝ) (ceSignedSpT1P0023Hi : ℝ) := by
    norm_num [ceSignedSpT1P0023Lo, ceSignedSpT1P0023Hi, SignedSpT1P0023Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0023Bound x h'
  norm_num [SignedSpT1P0023Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L006 : ∀ x ∈ Icc ((((9853 : ℚ) / 57344) : ℚ) : ℝ) ((((2943 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0024Lo : ℝ) (ceSignedSpT1P0024Hi : ℝ) := by
    norm_num [ceSignedSpT1P0024Lo, ceSignedSpT1P0024Hi, SignedSpT1P0024Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0024Bound x h'
  norm_num [SignedSpT1P0024Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L007 : ∀ x ∈ Icc ((((2943 : ℚ) / 16384) : ℚ) : ℝ) ((((2687 : ℚ) / 14336) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0025Lo : ℝ) (ceSignedSpT1P0025Hi : ℝ) := by
    norm_num [ceSignedSpT1P0025Lo, ceSignedSpT1P0025Hi, SignedSpT1P0025Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0025Bound x h'
  norm_num [SignedSpT1P0025Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L008 : ∀ x ∈ Icc ((((2687 : ℚ) / 14336) : ℚ) : ℝ) ((((22391 : ℚ) / 114688) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0026Lo : ℝ) (ceSignedSpT1P0026Hi : ℝ) := by
    norm_num [ceSignedSpT1P0026Lo, ceSignedSpT1P0026Hi, SignedSpT1P0026Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0026Bound x h'
  norm_num [SignedSpT1P0026Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L009 : ∀ x ∈ Icc ((((22391 : ℚ) / 114688) : ℚ) : ℝ) ((((11643 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0027Lo : ℝ) (ceSignedSpT1P0027Hi : ℝ) := by
    norm_num [ceSignedSpT1P0027Lo, ceSignedSpT1P0027Hi, SignedSpT1P0027Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0027Bound x h'
  norm_num [SignedSpT1P0027Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L010 : ∀ x ∈ Icc ((((11643 : ℚ) / 57344) : ℚ) : ℝ) ((((6269 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0028Lo : ℝ) (ceSignedSpT1P0028Hi : ℝ) := by
    norm_num [ceSignedSpT1P0028Lo, ceSignedSpT1P0028Hi, SignedSpT1P0028Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0028Bound x h'
  norm_num [SignedSpT1P0028Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L011 : ∀ x ∈ Icc ((((6269 : ℚ) / 28672) : ℚ) : ℝ) ((((1919 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0029Lo : ℝ) (ceSignedSpT1P0029Hi : ℝ) := by
    norm_num [ceSignedSpT1P0029Lo, ceSignedSpT1P0029Hi, SignedSpT1P0029Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0029Bound x h'
  norm_num [SignedSpT1P0029Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L012 : ∀ x ∈ Icc ((((1919 : ℚ) / 8192) : ℚ) : ℝ) ((((1791 : ℚ) / 7168) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0030Lo : ℝ) (ceSignedSpT1P0030Hi : ℝ) := by
    norm_num [ceSignedSpT1P0030Lo, ceSignedSpT1P0030Hi, SignedSpT1P0030Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0030Bound x h'
  norm_num [SignedSpT1P0030Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L013 : ∀ x ∈ Icc ((((1791 : ℚ) / 7168) : ℚ) : ℝ) ((((15223 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0031Lo : ℝ) (ceSignedSpT1P0031Hi : ℝ) := by
    norm_num [ceSignedSpT1P0031Lo, ceSignedSpT1P0031Hi, SignedSpT1P0031Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0031Bound x h'
  norm_num [SignedSpT1P0031Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L014 : ∀ x ∈ Icc ((((15223 : ℚ) / 57344) : ℚ) : ℝ) ((((8059 : ℚ) / 28672) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0032Lo : ℝ) (ceSignedSpT1P0032Hi : ℝ) := by
    norm_num [ceSignedSpT1P0032Lo, ceSignedSpT1P0032Hi, SignedSpT1P0032Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0032Bound x h'
  norm_num [SignedSpT1P0032Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B1P000L015 : ∀ x ∈ Icc ((((8059 : ℚ) / 28672) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0033Lo : ℝ) (ceSignedSpT1P0033Hi : ℝ) := by
    norm_num [ceSignedSpT1P0033Lo, ceSignedSpT1P0033Hi, SignedSpT1P0033Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0033Bound x h'
  norm_num [SignedSpT1P0033Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD0B1P000 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((17013 : ℚ) / 57344) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD0B1P000L000 SignedSpT1CoverD0B1P000L001) (cover_union SignedSpT1CoverD0B1P000L002 SignedSpT1CoverD0B1P000L003)) (cover_union (cover_union SignedSpT1CoverD0B1P000L004 SignedSpT1CoverD0B1P000L005) (cover_union SignedSpT1CoverD0B1P000L006 SignedSpT1CoverD0B1P000L007))) (cover_union (cover_union (cover_union SignedSpT1CoverD0B1P000L008 SignedSpT1CoverD0B1P000L009) (cover_union SignedSpT1CoverD0B1P000L010 SignedSpT1CoverD0B1P000L011)) (cover_union (cover_union SignedSpT1CoverD0B1P000L012 SignedSpT1CoverD0B1P000L013) (cover_union SignedSpT1CoverD0B1P000L014 SignedSpT1CoverD0B1P000L015))))
#print axioms SignedSpT1CoverD0B1P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

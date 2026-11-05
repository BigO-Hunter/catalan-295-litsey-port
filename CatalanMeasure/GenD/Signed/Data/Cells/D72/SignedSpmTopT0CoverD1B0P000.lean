module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0016
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverD1B0P000L000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0001Lo : ℝ) (ceSignedSpmTopT0P0001Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0001Lo, ceSignedSpmTopT0P0001Hi, SignedSpmTopT0P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0001Bound x h'
  norm_num [SignedSpmTopT0P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L001 : ∀ x ∈ Icc ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0002Lo : ℝ) (ceSignedSpmTopT0P0002Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0002Lo, ceSignedSpmTopT0P0002Hi, SignedSpmTopT0P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0002Bound x h'
  norm_num [SignedSpmTopT0P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L002 : ∀ x ∈ Icc ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0003Lo : ℝ) (ceSignedSpmTopT0P0003Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0003Lo, ceSignedSpmTopT0P0003Hi, SignedSpmTopT0P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0003Bound x h'
  norm_num [SignedSpmTopT0P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L003 : ∀ x ∈ Icc ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0004Lo : ℝ) (ceSignedSpmTopT0P0004Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0004Lo, ceSignedSpmTopT0P0004Hi, SignedSpmTopT0P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0004Bound x h'
  norm_num [SignedSpmTopT0P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L004 : ∀ x ∈ Icc ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0005Lo : ℝ) (ceSignedSpmTopT0P0005Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0005Lo, ceSignedSpmTopT0P0005Hi, SignedSpmTopT0P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0005Bound x h'
  norm_num [SignedSpmTopT0P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L005 : ∀ x ∈ Icc ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0006Lo : ℝ) (ceSignedSpmTopT0P0006Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0006Lo, ceSignedSpmTopT0P0006Hi, SignedSpmTopT0P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0006Bound x h'
  norm_num [SignedSpmTopT0P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L006 : ∀ x ∈ Icc ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0007Lo : ℝ) (ceSignedSpmTopT0P0007Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0007Lo, ceSignedSpmTopT0P0007Hi, SignedSpmTopT0P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0007Bound x h'
  norm_num [SignedSpmTopT0P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L007 : ∀ x ∈ Icc ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0008Lo : ℝ) (ceSignedSpmTopT0P0008Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0008Lo, ceSignedSpmTopT0P0008Hi, SignedSpmTopT0P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0008Bound x h'
  norm_num [SignedSpmTopT0P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L008 : ∀ x ∈ Icc ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0009Lo : ℝ) (ceSignedSpmTopT0P0009Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0009Lo, ceSignedSpmTopT0P0009Hi, SignedSpmTopT0P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0009Bound x h'
  norm_num [SignedSpmTopT0P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L009 : ∀ x ∈ Icc ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0010Lo : ℝ) (ceSignedSpmTopT0P0010Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0010Lo, ceSignedSpmTopT0P0010Hi, SignedSpmTopT0P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0010Bound x h'
  norm_num [SignedSpmTopT0P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L010 : ∀ x ∈ Icc ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0011Lo : ℝ) (ceSignedSpmTopT0P0011Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0011Lo, ceSignedSpmTopT0P0011Hi, SignedSpmTopT0P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0011Bound x h'
  norm_num [SignedSpmTopT0P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L011 : ∀ x ∈ Icc ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0012Lo : ℝ) (ceSignedSpmTopT0P0012Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0012Lo, ceSignedSpmTopT0P0012Hi, SignedSpmTopT0P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0012Bound x h'
  norm_num [SignedSpmTopT0P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L012 : ∀ x ∈ Icc ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0013Lo : ℝ) (ceSignedSpmTopT0P0013Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0013Lo, ceSignedSpmTopT0P0013Hi, SignedSpmTopT0P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0013Bound x h'
  norm_num [SignedSpmTopT0P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L013 : ∀ x ∈ Icc ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0014Lo : ℝ) (ceSignedSpmTopT0P0014Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0014Lo, ceSignedSpmTopT0P0014Hi, SignedSpmTopT0P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0014Bound x h'
  norm_num [SignedSpmTopT0P0014Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L014 : ∀ x ∈ Icc ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0015Lo : ℝ) (ceSignedSpmTopT0P0015Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0015Lo, ceSignedSpmTopT0P0015Hi, SignedSpmTopT0P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0015Bound x h'
  norm_num [SignedSpmTopT0P0015Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT0CoverD1B0P000L015 : ∀ x ∈ Icc ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0016Lo : ℝ) (ceSignedSpmTopT0P0016Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0016Lo, ceSignedSpmTopT0P0016Hi, SignedSpmTopT0P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0016Bound x h'
  norm_num [SignedSpmTopT0P0016Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT0CoverD1B0P000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P000L000 SignedSpmTopT0CoverD1B0P000L001) (cover_union SignedSpmTopT0CoverD1B0P000L002 SignedSpmTopT0CoverD1B0P000L003)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P000L004 SignedSpmTopT0CoverD1B0P000L005) (cover_union SignedSpmTopT0CoverD1B0P000L006 SignedSpmTopT0CoverD1B0P000L007))) (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P000L008 SignedSpmTopT0CoverD1B0P000L009) (cover_union SignedSpmTopT0CoverD1B0P000L010 SignedSpmTopT0CoverD1B0P000L011)) (cover_union (cover_union SignedSpmTopT0CoverD1B0P000L012 SignedSpmTopT0CoverD1B0P000L013) (cover_union SignedSpmTopT0CoverD1B0P000L014 SignedSpmTopT0CoverD1B0P000L015))))
#print axioms SignedSpmTopT0CoverD1B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2P0016
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT2CoverD1B0P000L000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0001Lo : ℝ) (ceSignedSpmTopT2P0001Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0001Lo, ceSignedSpmTopT2P0001Hi, SignedSpmTopT2P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0001Bound x h'
  norm_num [SignedSpmTopT2P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L001 : ∀ x ∈ Icc ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0002Lo : ℝ) (ceSignedSpmTopT2P0002Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0002Lo, ceSignedSpmTopT2P0002Hi, SignedSpmTopT2P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0002Bound x h'
  norm_num [SignedSpmTopT2P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L002 : ∀ x ∈ Icc ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0003Lo : ℝ) (ceSignedSpmTopT2P0003Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0003Lo, ceSignedSpmTopT2P0003Hi, SignedSpmTopT2P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0003Bound x h'
  norm_num [SignedSpmTopT2P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L003 : ∀ x ∈ Icc ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0004Lo : ℝ) (ceSignedSpmTopT2P0004Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0004Lo, ceSignedSpmTopT2P0004Hi, SignedSpmTopT2P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0004Bound x h'
  norm_num [SignedSpmTopT2P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L004 : ∀ x ∈ Icc ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0005Lo : ℝ) (ceSignedSpmTopT2P0005Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0005Lo, ceSignedSpmTopT2P0005Hi, SignedSpmTopT2P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0005Bound x h'
  norm_num [SignedSpmTopT2P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L005 : ∀ x ∈ Icc ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0006Lo : ℝ) (ceSignedSpmTopT2P0006Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0006Lo, ceSignedSpmTopT2P0006Hi, SignedSpmTopT2P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0006Bound x h'
  norm_num [SignedSpmTopT2P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L006 : ∀ x ∈ Icc ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0007Lo : ℝ) (ceSignedSpmTopT2P0007Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0007Lo, ceSignedSpmTopT2P0007Hi, SignedSpmTopT2P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0007Bound x h'
  norm_num [SignedSpmTopT2P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L007 : ∀ x ∈ Icc ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0008Lo : ℝ) (ceSignedSpmTopT2P0008Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0008Lo, ceSignedSpmTopT2P0008Hi, SignedSpmTopT2P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0008Bound x h'
  norm_num [SignedSpmTopT2P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L008 : ∀ x ∈ Icc ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0009Lo : ℝ) (ceSignedSpmTopT2P0009Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0009Lo, ceSignedSpmTopT2P0009Hi, SignedSpmTopT2P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0009Bound x h'
  norm_num [SignedSpmTopT2P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L009 : ∀ x ∈ Icc ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0010Lo : ℝ) (ceSignedSpmTopT2P0010Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0010Lo, ceSignedSpmTopT2P0010Hi, SignedSpmTopT2P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0010Bound x h'
  norm_num [SignedSpmTopT2P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L010 : ∀ x ∈ Icc ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0011Lo : ℝ) (ceSignedSpmTopT2P0011Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0011Lo, ceSignedSpmTopT2P0011Hi, SignedSpmTopT2P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0011Bound x h'
  norm_num [SignedSpmTopT2P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L011 : ∀ x ∈ Icc ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0012Lo : ℝ) (ceSignedSpmTopT2P0012Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0012Lo, ceSignedSpmTopT2P0012Hi, SignedSpmTopT2P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0012Bound x h'
  norm_num [SignedSpmTopT2P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L012 : ∀ x ∈ Icc ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0013Lo : ℝ) (ceSignedSpmTopT2P0013Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0013Lo, ceSignedSpmTopT2P0013Hi, SignedSpmTopT2P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0013Bound x h'
  norm_num [SignedSpmTopT2P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L013 : ∀ x ∈ Icc ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0014Lo : ℝ) (ceSignedSpmTopT2P0014Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0014Lo, ceSignedSpmTopT2P0014Hi, SignedSpmTopT2P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0014Bound x h'
  norm_num [SignedSpmTopT2P0014Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L014 : ∀ x ∈ Icc ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0015Lo : ℝ) (ceSignedSpmTopT2P0015Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0015Lo, ceSignedSpmTopT2P0015Hi, SignedSpmTopT2P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0015Bound x h'
  norm_num [SignedSpmTopT2P0015Literal.q2] at h ⊢
  exact h

private theorem SignedSpmTopT2CoverD1B0P000L015 : ∀ x ∈ Icc ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT2P0016Lo : ℝ) (ceSignedSpmTopT2P0016Hi : ℝ) := by
    norm_num [ceSignedSpmTopT2P0016Lo, ceSignedSpmTopT2P0016Hi, SignedSpmTopT2P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT2P0016Bound x h'
  norm_num [SignedSpmTopT2P0016Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT2CoverD1B0P000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P000L000 SignedSpmTopT2CoverD1B0P000L001) (cover_union SignedSpmTopT2CoverD1B0P000L002 SignedSpmTopT2CoverD1B0P000L003)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P000L004 SignedSpmTopT2CoverD1B0P000L005) (cover_union SignedSpmTopT2CoverD1B0P000L006 SignedSpmTopT2CoverD1B0P000L007))) (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P000L008 SignedSpmTopT2CoverD1B0P000L009) (cover_union SignedSpmTopT2CoverD1B0P000L010 SignedSpmTopT2CoverD1B0P000L011)) (cover_union (cover_union SignedSpmTopT2CoverD1B0P000L012 SignedSpmTopT2CoverD1B0P000L013) (cover_union SignedSpmTopT2CoverD1B0P000L014 SignedSpmTopT2CoverD1B0P000L015))))
#print axioms SignedSpmTopT2CoverD1B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover

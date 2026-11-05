module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0095
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0103
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD1B0P000L000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0088Lo : ℝ) (ceSignedSpT1P0088Hi : ℝ) := by
    norm_num [ceSignedSpT1P0088Lo, ceSignedSpT1P0088Hi, SignedSpT1P0088Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0088Bound x h'
  norm_num [SignedSpT1P0088Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L001 : ∀ x ∈ Icc ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0089Lo : ℝ) (ceSignedSpT1P0089Hi : ℝ) := by
    norm_num [ceSignedSpT1P0089Lo, ceSignedSpT1P0089Hi, SignedSpT1P0089Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0089Bound x h'
  norm_num [SignedSpT1P0089Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L002 : ∀ x ∈ Icc ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0090Lo : ℝ) (ceSignedSpT1P0090Hi : ℝ) := by
    norm_num [ceSignedSpT1P0090Lo, ceSignedSpT1P0090Hi, SignedSpT1P0090Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0090Bound x h'
  norm_num [SignedSpT1P0090Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L003 : ∀ x ∈ Icc ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0091Lo : ℝ) (ceSignedSpT1P0091Hi : ℝ) := by
    norm_num [ceSignedSpT1P0091Lo, ceSignedSpT1P0091Hi, SignedSpT1P0091Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0091Bound x h'
  norm_num [SignedSpT1P0091Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L004 : ∀ x ∈ Icc ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0092Lo : ℝ) (ceSignedSpT1P0092Hi : ℝ) := by
    norm_num [ceSignedSpT1P0092Lo, ceSignedSpT1P0092Hi, SignedSpT1P0092Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0092Bound x h'
  norm_num [SignedSpT1P0092Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L005 : ∀ x ∈ Icc ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0093Lo : ℝ) (ceSignedSpT1P0093Hi : ℝ) := by
    norm_num [ceSignedSpT1P0093Lo, ceSignedSpT1P0093Hi, SignedSpT1P0093Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0093Bound x h'
  norm_num [SignedSpT1P0093Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L006 : ∀ x ∈ Icc ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0094Lo : ℝ) (ceSignedSpT1P0094Hi : ℝ) := by
    norm_num [ceSignedSpT1P0094Lo, ceSignedSpT1P0094Hi, SignedSpT1P0094Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0094Bound x h'
  norm_num [SignedSpT1P0094Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L007 : ∀ x ∈ Icc ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0095Lo : ℝ) (ceSignedSpT1P0095Hi : ℝ) := by
    norm_num [ceSignedSpT1P0095Lo, ceSignedSpT1P0095Hi, SignedSpT1P0095Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0095Bound x h'
  norm_num [SignedSpT1P0095Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L008 : ∀ x ∈ Icc ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0096Lo : ℝ) (ceSignedSpT1P0096Hi : ℝ) := by
    norm_num [ceSignedSpT1P0096Lo, ceSignedSpT1P0096Hi, SignedSpT1P0096Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0096Bound x h'
  norm_num [SignedSpT1P0096Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L009 : ∀ x ∈ Icc ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0097Lo : ℝ) (ceSignedSpT1P0097Hi : ℝ) := by
    norm_num [ceSignedSpT1P0097Lo, ceSignedSpT1P0097Hi, SignedSpT1P0097Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0097Bound x h'
  norm_num [SignedSpT1P0097Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L010 : ∀ x ∈ Icc ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0098Lo : ℝ) (ceSignedSpT1P0098Hi : ℝ) := by
    norm_num [ceSignedSpT1P0098Lo, ceSignedSpT1P0098Hi, SignedSpT1P0098Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0098Bound x h'
  norm_num [SignedSpT1P0098Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L011 : ∀ x ∈ Icc ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0099Lo : ℝ) (ceSignedSpT1P0099Hi : ℝ) := by
    norm_num [ceSignedSpT1P0099Lo, ceSignedSpT1P0099Hi, SignedSpT1P0099Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0099Bound x h'
  norm_num [SignedSpT1P0099Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L012 : ∀ x ∈ Icc ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0100Lo : ℝ) (ceSignedSpT1P0100Hi : ℝ) := by
    norm_num [ceSignedSpT1P0100Lo, ceSignedSpT1P0100Hi, SignedSpT1P0100Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0100Bound x h'
  norm_num [SignedSpT1P0100Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L013 : ∀ x ∈ Icc ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0101Lo : ℝ) (ceSignedSpT1P0101Hi : ℝ) := by
    norm_num [ceSignedSpT1P0101Lo, ceSignedSpT1P0101Hi, SignedSpT1P0101Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0101Bound x h'
  norm_num [SignedSpT1P0101Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L014 : ∀ x ∈ Icc ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0102Lo : ℝ) (ceSignedSpT1P0102Hi : ℝ) := by
    norm_num [ceSignedSpT1P0102Lo, ceSignedSpT1P0102Hi, SignedSpT1P0102Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0102Bound x h'
  norm_num [SignedSpT1P0102Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD1B0P000L015 : ∀ x ∈ Icc ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0103Lo : ℝ) (ceSignedSpT1P0103Hi : ℝ) := by
    norm_num [ceSignedSpT1P0103Lo, ceSignedSpT1P0103Hi, SignedSpT1P0103Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0103Bound x h'
  norm_num [SignedSpT1P0103Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD1B0P000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P000L000 SignedSpT1CoverD1B0P000L001) (cover_union SignedSpT1CoverD1B0P000L002 SignedSpT1CoverD1B0P000L003)) (cover_union (cover_union SignedSpT1CoverD1B0P000L004 SignedSpT1CoverD1B0P000L005) (cover_union SignedSpT1CoverD1B0P000L006 SignedSpT1CoverD1B0P000L007))) (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P000L008 SignedSpT1CoverD1B0P000L009) (cover_union SignedSpT1CoverD1B0P000L010 SignedSpT1CoverD1B0P000L011)) (cover_union (cover_union SignedSpT1CoverD1B0P000L012 SignedSpT1CoverD1B0P000L013) (cover_union SignedSpT1CoverD1B0P000L014 SignedSpT1CoverD1B0P000L015))))
#print axioms SignedSpT1CoverD1B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

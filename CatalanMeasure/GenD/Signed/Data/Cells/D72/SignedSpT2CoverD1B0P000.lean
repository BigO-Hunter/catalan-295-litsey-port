module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0095
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0103
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2P0105
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT2CoverD1B0P000L000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0090Lo : ℝ) (ceSignedSpT2P0090Hi : ℝ) := by
    norm_num [ceSignedSpT2P0090Lo, ceSignedSpT2P0090Hi, SignedSpT2P0090Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0090Bound x h'
  norm_num [SignedSpT2P0090Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L001 : ∀ x ∈ Icc ((((8788576829439 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0091Lo : ℝ) (ceSignedSpT2P0091Hi : ℝ) := by
    norm_num [ceSignedSpT2P0091Lo, ceSignedSpT2P0091Hi, SignedSpT2P0091Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0091Bound x h'
  norm_num [SignedSpT2P0091Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L002 : ∀ x ∈ Icc ((((4394825285631 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0092Lo : ℝ) (ceSignedSpT2P0092Hi : ℝ) := by
    norm_num [ceSignedSpT2P0092Lo, ceSignedSpT2P0092Hi, SignedSpT2P0092Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0092Bound x h'
  norm_num [SignedSpT2P0092Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L003 : ∀ x ∈ Icc ((((8790724313085 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0093Lo : ℝ) (ceSignedSpT2P0093Hi : ℝ) := by
    norm_num [ceSignedSpT2P0093Lo, ceSignedSpT2P0093Hi, SignedSpT2P0093Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0093Bound x h'
  norm_num [SignedSpT2P0093Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L004 : ∀ x ∈ Icc ((((17582522367993 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0094Lo : ℝ) (ceSignedSpT2P0094Hi : ℝ) := by
    norm_num [ceSignedSpT2P0094Lo, ceSignedSpT2P0094Hi, SignedSpT2P0094Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0094Bound x h'
  norm_num [SignedSpT2P0094Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L005 : ∀ x ∈ Icc ((((2197949513727 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0095Lo : ℝ) (ceSignedSpT2P0095Hi : ℝ) := by
    norm_num [ceSignedSpT2P0095Lo, ceSignedSpT2P0095Hi, SignedSpT2P0095Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0095Bound x h'
  norm_num [SignedSpT2P0095Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L006 : ∀ x ∈ Icc ((((17584669851639 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0096Lo : ℝ) (ceSignedSpT2P0096Hi : ℝ) := by
    norm_num [ceSignedSpT2P0096Lo, ceSignedSpT2P0096Hi, SignedSpT2P0096Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0096Bound x h'
  norm_num [SignedSpT2P0096Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L007 : ∀ x ∈ Icc ((((8792871796731 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0097Lo : ℝ) (ceSignedSpT2P0097Hi : ℝ) := by
    norm_num [ceSignedSpT2P0097Lo, ceSignedSpT2P0097Hi, SignedSpT2P0097Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0097Bound x h'
  norm_num [SignedSpT2P0097Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L008 : ∀ x ∈ Icc ((((17586817335285 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0098Lo : ℝ) (ceSignedSpT2P0098Hi : ℝ) := by
    norm_num [ceSignedSpT2P0098Lo, ceSignedSpT2P0098Hi, SignedSpT2P0098Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0098Bound x h'
  norm_num [SignedSpT2P0098Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L009 : ∀ x ∈ Icc ((((35174708412393 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0099Lo : ℝ) (ceSignedSpT2P0099Hi : ℝ) := by
    norm_num [ceSignedSpT2P0099Lo, ceSignedSpT2P0099Hi, SignedSpT2P0099Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0099Bound x h'
  norm_num [SignedSpT2P0099Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L010 : ∀ x ∈ Icc ((((4396972769277 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0100Lo : ℝ) (ceSignedSpT2P0100Hi : ℝ) := by
    norm_num [ceSignedSpT2P0100Lo, ceSignedSpT2P0100Hi, SignedSpT2P0100Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0100Bound x h'
  norm_num [SignedSpT2P0100Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L011 : ∀ x ∈ Icc ((((35176855896039 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0101Lo : ℝ) (ceSignedSpT2P0101Hi : ℝ) := by
    norm_num [ceSignedSpT2P0101Lo, ceSignedSpT2P0101Hi, SignedSpT2P0101Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0101Bound x h'
  norm_num [SignedSpT2P0101Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L012 : ∀ x ∈ Icc ((((17588964818931 : ℚ) / 17592186044416) : ℚ) : ℝ) ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0102Lo : ℝ) (ceSignedSpT2P0102Hi : ℝ) := by
    norm_num [ceSignedSpT2P0102Lo, ceSignedSpT2P0102Hi, SignedSpT2P0102Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0102Bound x h'
  norm_num [SignedSpT2P0102Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L013 : ∀ x ∈ Icc ((((35179003379685 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0103Lo : ℝ) (ceSignedSpT2P0103Hi : ℝ) := by
    norm_num [ceSignedSpT2P0103Lo, ceSignedSpT2P0103Hi, SignedSpT2P0103Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0103Bound x h'
  norm_num [SignedSpT2P0103Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L014 : ∀ x ∈ Icc ((((70359080501193 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0104Lo : ℝ) (ceSignedSpT2P0104Hi : ℝ) := by
    norm_num [ceSignedSpT2P0104Lo, ceSignedSpT2P0104Hi, SignedSpT2P0104Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0104Bound x h'
  norm_num [SignedSpT2P0104Literal.q2] at h ⊢
  exact h

private theorem SignedSpT2CoverD1B0P000L015 : ∀ x ∈ Icc ((((8795019280377 : ℚ) / 8796093022208) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT2P0105Lo : ℝ) (ceSignedSpT2P0105Hi : ℝ) := by
    norm_num [ceSignedSpT2P0105Lo, ceSignedSpT2P0105Hi, SignedSpT2P0105Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT2P0105Bound x h'
  norm_num [SignedSpT2P0105Literal.q2] at h ⊢
  exact h

theorem SignedSpT2CoverD1B0P000 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((70361227984839 : ℚ) / 70368744177664) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P000L000 SignedSpT2CoverD1B0P000L001) (cover_union SignedSpT2CoverD1B0P000L002 SignedSpT2CoverD1B0P000L003)) (cover_union (cover_union SignedSpT2CoverD1B0P000L004 SignedSpT2CoverD1B0P000L005) (cover_union SignedSpT2CoverD1B0P000L006 SignedSpT2CoverD1B0P000L007))) (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P000L008 SignedSpT2CoverD1B0P000L009) (cover_union SignedSpT2CoverD1B0P000L010 SignedSpT2CoverD1B0P000L011)) (cover_union (cover_union SignedSpT2CoverD1B0P000L012 SignedSpT2CoverD1B0P000L013) (cover_union SignedSpT2CoverD1B0P000L014 SignedSpT2CoverD1B0P000L015))))
#print axioms SignedSpT2CoverD1B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

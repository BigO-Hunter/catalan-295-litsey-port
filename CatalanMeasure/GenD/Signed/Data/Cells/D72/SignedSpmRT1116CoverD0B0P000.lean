module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116P0015
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT1116CoverD0B0P000L000 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((23810019 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0000Lo : ℝ) (ceSignedSpmRT1116P0000Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0000Lo, ceSignedSpmRT1116P0000Hi, SignedSpmRT1116P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0000Bound x h'
  norm_num [SignedSpmRT1116P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L001 : ∀ x ∈ Icc ((((23810019 : ℚ) / 232000000) : ℚ) : ℝ) ((((2471027 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0001Lo : ℝ) (ceSignedSpmRT1116P0001Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0001Lo, ceSignedSpmRT1116P0001Hi, SignedSpmRT1116P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0001Bound x h'
  norm_num [SignedSpmRT1116P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L002 : ∀ x ∈ Icc ((((2471027 : ℚ) / 23200000) : ℚ) : ℝ) ((((25610521 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0002Lo : ℝ) (ceSignedSpmRT1116P0002Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0002Lo, ceSignedSpmRT1116P0002Hi, SignedSpmRT1116P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0002Bound x h'
  norm_num [SignedSpmRT1116P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L003 : ∀ x ∈ Icc ((((25610521 : ℚ) / 232000000) : ℚ) : ℝ) ((((6627693 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0003Lo : ℝ) (ceSignedSpmRT1116P0003Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0003Lo, ceSignedSpmRT1116P0003Hi, SignedSpmRT1116P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0003Bound x h'
  norm_num [SignedSpmRT1116P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L004 : ∀ x ∈ Icc ((((6627693 : ℚ) / 58000000) : ℚ) : ℝ) ((((27411023 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0004Lo : ℝ) (ceSignedSpmRT1116P0004Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0004Lo, ceSignedSpmRT1116P0004Hi, SignedSpmRT1116P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0004Bound x h'
  norm_num [SignedSpmRT1116P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L005 : ∀ x ∈ Icc ((((27411023 : ℚ) / 232000000) : ℚ) : ℝ) ((((14155637 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0005Lo : ℝ) (ceSignedSpmRT1116P0005Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0005Lo, ceSignedSpmRT1116P0005Hi, SignedSpmRT1116P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0005Bound x h'
  norm_num [SignedSpmRT1116P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L006 : ∀ x ∈ Icc ((((14155637 : ℚ) / 116000000) : ℚ) : ℝ) ((((940993 : ℚ) / 7250000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0006Lo : ℝ) (ceSignedSpmRT1116P0006Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0006Lo, ceSignedSpmRT1116P0006Hi, SignedSpmRT1116P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0006Bound x h'
  norm_num [SignedSpmRT1116P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L007 : ∀ x ∈ Icc ((((940993 : ℚ) / 7250000) : ℚ) : ℝ) ((((15956139 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0007Lo : ℝ) (ceSignedSpmRT1116P0007Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0007Lo, ceSignedSpmRT1116P0007Hi, SignedSpmRT1116P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0007Bound x h'
  norm_num [SignedSpmRT1116P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L008 : ∀ x ∈ Icc ((((15956139 : ℚ) / 116000000) : ℚ) : ℝ) ((((1685639 : ℚ) / 11600000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0008Lo : ℝ) (ceSignedSpmRT1116P0008Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0008Lo, ceSignedSpmRT1116P0008Hi, SignedSpmRT1116P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0008Bound x h'
  norm_num [SignedSpmRT1116P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L009 : ∀ x ∈ Icc ((((1685639 : ℚ) / 11600000) : ℚ) : ℝ) ((((17756641 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0009Lo : ℝ) (ceSignedSpmRT1116P0009Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0009Lo, ceSignedSpmRT1116P0009Hi, SignedSpmRT1116P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0009Bound x h'
  norm_num [SignedSpmRT1116P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L010 : ∀ x ∈ Icc ((((17756641 : ℚ) / 116000000) : ℚ) : ℝ) ((((4664223 : ℚ) / 29000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0010Lo : ℝ) (ceSignedSpmRT1116P0010Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0010Lo, ceSignedSpmRT1116P0010Hi, SignedSpmRT1116P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0010Bound x h'
  norm_num [SignedSpmRT1116P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L011 : ∀ x ∈ Icc ((((4664223 : ℚ) / 29000000) : ℚ) : ℝ) ((((19557143 : ℚ) / 116000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0011Lo : ℝ) (ceSignedSpmRT1116P0011Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0011Lo, ceSignedSpmRT1116P0011Hi, SignedSpmRT1116P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0011Bound x h'
  norm_num [SignedSpmRT1116P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L012 : ∀ x ∈ Icc ((((19557143 : ℚ) / 116000000) : ℚ) : ℝ) ((((10228697 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0012Lo : ℝ) (ceSignedSpmRT1116P0012Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0012Lo, ceSignedSpmRT1116P0012Hi, SignedSpmRT1116P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0012Bound x h'
  norm_num [SignedSpmRT1116P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L013 : ∀ x ∈ Icc ((((10228697 : ℚ) / 58000000) : ℚ) : ℝ) ((((4271529 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0013Lo : ℝ) (ceSignedSpmRT1116P0013Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0013Lo, ceSignedSpmRT1116P0013Hi, SignedSpmRT1116P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0013Bound x h'
  norm_num [SignedSpmRT1116P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L014 : ∀ x ∈ Icc ((((4271529 : ℚ) / 23200000) : ℚ) : ℝ) ((((2782237 : ℚ) / 14500000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0014Lo : ℝ) (ceSignedSpmRT1116P0014Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0014Lo, ceSignedSpmRT1116P0014Hi, SignedSpmRT1116P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0014Bound x h'
  norm_num [SignedSpmRT1116P0014Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT1116CoverD0B0P000L015 : ∀ x ∈ Icc ((((2782237 : ℚ) / 14500000) : ℚ) : ℝ) ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT1116P0015Lo : ℝ) (ceSignedSpmRT1116P0015Hi : ℝ) := by
    norm_num [ceSignedSpmRT1116P0015Lo, ceSignedSpmRT1116P0015Hi, SignedSpmRT1116P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT1116P0015Bound x h'
  norm_num [SignedSpmRT1116P0015Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT1116CoverD0B0P000 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((12029199 : ℚ) / 58000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P000L000 SignedSpmRT1116CoverD0B0P000L001) (cover_union SignedSpmRT1116CoverD0B0P000L002 SignedSpmRT1116CoverD0B0P000L003)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P000L004 SignedSpmRT1116CoverD0B0P000L005) (cover_union SignedSpmRT1116CoverD0B0P000L006 SignedSpmRT1116CoverD0B0P000L007))) (cover_union (cover_union (cover_union SignedSpmRT1116CoverD0B0P000L008 SignedSpmRT1116CoverD0B0P000L009) (cover_union SignedSpmRT1116CoverD0B0P000L010 SignedSpmRT1116CoverD0B0P000L011)) (cover_union (cover_union SignedSpmRT1116CoverD0B0P000L012 SignedSpmRT1116CoverD0B0P000L013) (cover_union SignedSpmRT1116CoverD0B0P000L014 SignedSpmRT1116CoverD0B0P000L015))))
#print axioms SignedSpmRT1116CoverD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover

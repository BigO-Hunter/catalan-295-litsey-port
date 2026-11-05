module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0CoverD1B0P009
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  SignedSpmTopT0CoverD0B0P000
#print axioms region0B0

theorem region1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpmTopT0CoverD1B0P000 SignedSpmTopT0CoverD1B0P001) (cover_union SignedSpmTopT0CoverD1B0P002 (cover_union SignedSpmTopT0CoverD1B0P003 SignedSpmTopT0CoverD1B0P004))) (cover_union (cover_union SignedSpmTopT0CoverD1B0P005 SignedSpmTopT0CoverD1B0P006) (cover_union SignedSpmTopT0CoverD1B0P007 (cover_union SignedSpmTopT0CoverD1B0P008 SignedSpmTopT0CoverD1B0P009))))
#print axioms region1B0

theorem named0B0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region0B0 x hx hd
#print axioms named0B0

theorem named1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ ((((-28450269804527 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region1B0 x hx hd
#print axioms named1B0

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

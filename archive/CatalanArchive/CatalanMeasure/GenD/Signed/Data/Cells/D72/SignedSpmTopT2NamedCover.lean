module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2CoverD1B0P009
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-3144710066661 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  SignedSpmTopT2CoverD0B0P000
#print axioms region0B0

theorem region1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT2Fq (poleF ceSignedSpmTopT2Fq.poles) 0 x + lfieldTower ceSignedSpmTopT2Ts 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpmTopT2CoverD1B0P000 SignedSpmTopT2CoverD1B0P001) (cover_union SignedSpmTopT2CoverD1B0P002 (cover_union SignedSpmTopT2CoverD1B0P003 SignedSpmTopT2CoverD1B0P004))) (cover_union (cover_union SignedSpmTopT2CoverD1B0P005 SignedSpmTopT2CoverD1B0P006) (cover_union SignedSpmTopT2CoverD1B0P007 (cover_union SignedSpmTopT2CoverD1B0P008 SignedSpmTopT2CoverD1B0P009))))
#print axioms region1B0

theorem named0B0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ ((((-3144710066661 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region0B0 x hx hd
#print axioms named0B0

theorem named1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ ((((-28388289945869 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region1B0 x hx hd
#print axioms named1B0

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT2Cover

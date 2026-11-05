module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverD0B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverD0B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverD0B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116CoverD0B0P004
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpmRT1116CoverD0B0P000 SignedSpmRT1116CoverD0B0P001) (cover_union SignedSpmRT1116CoverD0B0P002 (cover_union SignedSpmRT1116CoverD0B0P003 SignedSpmRT1116CoverD0B0P004)))
#print axioms region0B0

theorem named0B0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x ≤ ((((-5754975790293 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region0B0 x hx hd
#print axioms named0B0

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover

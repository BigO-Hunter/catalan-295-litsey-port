module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverD0B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverD0B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverD0B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200CoverD0B0P004
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT21200Fq (poleF ceSignedSpmRT21200Fq.poles) 0 x + lfieldTower ceSignedSpmRT21200Ts 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpmRT21200CoverD0B0P000 SignedSpmRT21200CoverD0B0P001) (cover_union SignedSpmRT21200CoverD0B0P002 (cover_union SignedSpmRT21200CoverD0B0P003 SignedSpmRT21200CoverD0B0P004)))
#print axioms region0B0

theorem named0B0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((999 : ℚ) / 1000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 200)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 200)).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ ((((-2879621665765 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  rw [← namedValue x]
  exact region0B0 x hx hd
#print axioms named0B0

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT21200Cover

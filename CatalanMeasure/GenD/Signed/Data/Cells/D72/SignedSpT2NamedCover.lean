module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B1P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B1P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B1P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B1P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD0B1P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverD1B0P009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2CoverBridge
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2ZeroPlain (poleF ceSignedSpT2ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-411093350182344919644072899367097800940090430121886826095904761297540575273695 : ℚ) / 50659039041325835497812305941300959685805618291217746767262693003461994217472) : ℚ) : ℝ) :=
  (cover_union SignedSpT2CoverD0B0P000 SignedSpT2CoverD0B0P001)
#print axioms region0B0

theorem region0B1 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-8922433729115 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT2CoverD0B1P000 SignedSpT2CoverD0B1P001) (cover_union SignedSpT2CoverD0B1P002 (cover_union SignedSpT2CoverD0B1P003 SignedSpT2CoverD0B1P004)))
#print axioms region0B1

theorem region1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x ≤ ((((-80473702253875 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpT2CoverD1B0P000 SignedSpT2CoverD1B0P001) (cover_union SignedSpT2CoverD1B0P002 (cover_union SignedSpT2CoverD1B0P003 SignedSpT2CoverD1B0P004))) (cover_union (cover_union SignedSpT2CoverD1B0P005 SignedSpT2CoverD1B0P006) (cover_union SignedSpT2CoverD1B0P007 (cover_union SignedSpT2CoverD1B0P008 SignedSpT2CoverD1B0P009))))
#print axioms region1B0

theorem before : ∀ x ∈ Ioc (ceSignedSpT2End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ (ceSignedSpT2ZeroCap : ℝ) := beforeOf region0B0 region0B1
theorem after : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x ≤ (ceSignedSpT2End01Target : ℝ) := afterOf region1B0
#print axioms before
#print axioms after

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

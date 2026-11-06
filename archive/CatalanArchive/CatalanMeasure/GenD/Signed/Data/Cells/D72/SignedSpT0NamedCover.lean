module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B1P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B1P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B1P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B1P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD0B1P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverD1B0P009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0CoverBridge
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0ZeroPlain (poleF ceSignedSpT0ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-102988191598820542775105217547844767057059176941991823714562039501040002768079 : ℚ) / 12664759760331458874453076485325239921451404572804436691815673250865498554368) : ℚ) : ℝ) :=
  (cover_union SignedSpT0CoverD0B0P000 SignedSpT0CoverD0B0P001)
#print axioms region0B0

theorem region0B1 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-8941086631679 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT0CoverD0B1P000 SignedSpT0CoverD0B1P001) (cover_union SignedSpT0CoverD0B1P002 (cover_union SignedSpT0CoverD0B1P003 SignedSpT0CoverD0B1P004)))
#print axioms region0B1

theorem region1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT0Fq (poleF ceSignedSpT0Fq.poles) 0 x + lfieldTower ceSignedSpT0Ts 0 x ≤ ((((-80641578376951 : ℚ) / 9895604649984) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpT0CoverD1B0P000 SignedSpT0CoverD1B0P001) (cover_union SignedSpT0CoverD1B0P002 (cover_union SignedSpT0CoverD1B0P003 SignedSpT0CoverD1B0P004))) (cover_union (cover_union SignedSpT0CoverD1B0P005 SignedSpT0CoverD1B0P006) (cover_union SignedSpT0CoverD1B0P007 (cover_union SignedSpT0CoverD1B0P008 SignedSpT0CoverD1B0P009))))
#print axioms region1B0

theorem before : ∀ x ∈ Ioc (ceSignedSpT0End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ (ceSignedSpT0ZeroCap : ℝ) := beforeOf region0B0 region0B1
theorem after : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x ≤ (ceSignedSpT0End01Target : ℝ) := afterOf region1B0
#print axioms before
#print axioms after

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Cover

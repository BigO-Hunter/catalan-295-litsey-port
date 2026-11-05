module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B1P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B1P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B1P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B1P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD0B1P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverD1B0P009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1CoverBridge
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem region0B0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) :=
  (cover_union SignedSpT1CoverD0B0P000 SignedSpT1CoverD0B0P001)
#print axioms region0B0

theorem region0B1 : ∀ x ∈ Icc ((((1 : ℚ) / 8) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-4477501371827 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union (cover_union SignedSpT1CoverD0B1P000 SignedSpT1CoverD0B1P001) (cover_union SignedSpT1CoverD0B1P002 (cover_union SignedSpT1CoverD0B1P003 SignedSpT1CoverD0B1P004)))
#print axioms region0B1

theorem region1B0 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1Fq (poleF ceSignedSpT1Fq.poles) 0 x + lfieldTower ceSignedSpT1Ts 0 x ≤ ((((-40383411692363 : ℚ) / 4947802324992) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union SignedSpT1CoverD1B0P000 SignedSpT1CoverD1B0P001) (cover_union SignedSpT1CoverD1B0P002 (cover_union SignedSpT1CoverD1B0P003 SignedSpT1CoverD1B0P004))) (cover_union (cover_union SignedSpT1CoverD1B0P005 SignedSpT1CoverD1B0P006) (cover_union SignedSpT1CoverD1B0P007 (cover_union SignedSpT1CoverD1B0P008 SignedSpT1CoverD1B0P009))))
#print axioms region1B0

theorem before : ∀ x ∈ Ioc (ceSignedSpT1End00Hi : ℝ) (1023/1024 : ℝ),
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x ≤ (ceSignedSpT1ZeroCap : ℝ) := beforeOf region0B0 region0B1
theorem after : ∀ x ∈ Ico (1023/1024 : ℝ) 1,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x ≤ (ceSignedSpT1End01Target : ℝ) := afterOf region1B0
#print axioms before
#print axioms after

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

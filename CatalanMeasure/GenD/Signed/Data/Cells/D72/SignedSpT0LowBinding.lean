module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev terms := dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn
abbrev zeroC : ℚ := endC ceSignedSpT0End00FullFq ceSignedSpT0End00FullTs ceSignedSpT0End00Site
abbrev zeroE : ℚ := ceSignedSpT0ZeroCap - ceSignedSpT0ZeroPlainCap

theorem lowPlainCheck : fieldNFCheck ceSignedSpT0End00FullFq ceSignedSpT0ZeroPlain = true := by decide +kernel
theorem lowFieldCheck : fieldNFCheck ceSignedSpT0ZeroInputFq CatalanMeasure.GenD.Signed.Data.Trial72.T0.spFq = true := by decide +kernel
theorem lowRawTermsCheck : laurentNF ceSignedSpT0Ts = laurentNF terms := by decide +kernel
theorem lowTermsEq (x : ℝ) : lfieldTower ceSignedSpT0ZeroInputTs 0 x = lfieldTower terms 0 x := by
  change lfieldTower (D72.pruneZeroLogs (laurentClean ceSignedSpT0Ts)) 0 x = _
  rw [D72.pruneZeroLogs_sound, laurentClean_sound, ← laurentNF_sound ceSignedSpT0Ts x,
    lowRawTermsCheck, laurentNF_sound terms x]
#print axioms lowPlainCheck
#print axioms lowFieldCheck
#print axioms lowRawTermsCheck
#print axioms lowTermsEq
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT0Endpoints

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev terms := dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn
abbrev zeroC : ℚ := endC ceSignedSpT2End00FullFq ceSignedSpT2End00FullTs ceSignedSpT2End00Site
abbrev zeroE : ℚ := ceSignedSpT2ZeroCap - ceSignedSpT2ZeroPlainCap

theorem lowPlainCheck : fieldNFCheck ceSignedSpT2End00FullFq ceSignedSpT2ZeroPlain = true := by decide +kernel
theorem lowFieldCheck : fieldNFCheck ceSignedSpT2ZeroInputFq CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq = true := by decide +kernel
theorem lowRawTermsCheck : laurentNF ceSignedSpT2Ts = laurentNF terms := by decide +kernel
theorem lowTermsEq (x : ℝ) : lfieldTower ceSignedSpT2ZeroInputTs 0 x = lfieldTower terms 0 x := by
  change lfieldTower (D72.pruneZeroLogs (laurentClean ceSignedSpT2Ts)) 0 x = _
  rw [D72.pruneZeroLogs_sound, laurentClean_sound, ← laurentNF_sound ceSignedSpT2Ts x,
    lowRawTermsCheck, laurentNF_sound terms x]
#print axioms lowPlainCheck
#print axioms lowFieldCheck
#print axioms lowRawTermsCheck
#print axioms lowTermsEq
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Endpoints

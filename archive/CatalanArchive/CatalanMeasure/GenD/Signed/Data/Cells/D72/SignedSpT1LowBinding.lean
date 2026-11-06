module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1ZeroTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroSeriesPoint
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Fields
public import CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Assembly
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

abbrev terms := dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn
abbrev zeroC : ℚ := endC ceSignedSpT1End00FullFq ceSignedSpT1End00FullTs ceSignedSpT1End00Site
abbrev zeroE : ℚ := ceSignedSpT1ZeroCap - ceSignedSpT1ZeroPlainCap

theorem lowPlainCheck : fieldNFCheck ceSignedSpT1End00FullFq ceSignedSpT1ZeroPlain = true := by decide +kernel
theorem lowFieldCheck : fieldNFCheck ceSignedSpT1ZeroInputFq CatalanMeasure.GenD.Signed.Data.Trial72.T1.spFq = true := by decide +kernel
theorem lowRawTermsCheck : laurentNF ceSignedSpT1Ts = laurentNF terms := by decide +kernel
theorem lowTermsEq (x : ℝ) : lfieldTower ceSignedSpT1ZeroInputTs 0 x = lfieldTower terms 0 x := by
  change lfieldTower (D72.pruneZeroLogs (laurentClean ceSignedSpT1Ts)) 0 x = _
  rw [D72.pruneZeroLogs_sound, laurentClean_sound, ← laurentNF_sound ceSignedSpT1Ts x,
    lowRawTermsCheck, laurentNF_sound terms x]
#print axioms lowPlainCheck
#print axioms lowFieldCheck
#print axioms lowRawTermsCheck
#print axioms lowTermsEq
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Endpoints

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem rawField : fieldNFCheck ceSignedSpT2Fq CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq = true := by decide +kernel
theorem rawTerms : laurentNF ceSignedSpT2Ts = laurentNF (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) := by decide +kernel
theorem namedValue (x : ℝ) : fieldTower ceSignedSpT2Fq (poleF ceSignedSpT2Fq.poles) 0 x + lfieldTower ceSignedSpT2Ts 0 x = fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.spFq.poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 x := by
  rw [fieldNFCheck_sound rawField x, ← laurentNF_sound ceSignedSpT2Ts x, rawTerms, laurentNF_sound (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) x]
#print axioms rawField
#print axioms rawTerms
#print axioms namedValue

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT2Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0FieldBinding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem rawField : fieldNFCheck ceSignedSpmTopT0Fq (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) = true := by decide +kernel
theorem rawTerms : laurentNF ceSignedSpmTopT0Ts = laurentNF (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) := by decide +kernel
theorem namedValue (x : ℝ) : fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x = fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x := by
  rw [fieldNFCheck_sound rawField x, ← laurentNF_sound ceSignedSpmTopT0Ts x, rawTerms, laurentNF_sound (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) x]
#print axioms rawField
#print axioms rawTerms
#print axioms namedValue

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Fields
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1FieldBinding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem rawField : fieldNFCheck ceSignedSpmRT1116Fq (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)) = true := by decide +kernel
theorem rawTerms : laurentNF ceSignedSpmRT1116Ts = laurentNF (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) := by decide +kernel
theorem namedValue (x : ℝ) : fieldTower ceSignedSpmRT1116Fq (poleF ceSignedSpmRT1116Fq.poles) 0 x + lfieldTower ceSignedSpmRT1116Ts 0 x = fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 x := by
  rw [fieldNFCheck_sound rawField x, ← laurentNF_sound ceSignedSpmRT1116Ts x, rawTerms, laurentNF_sound (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) x]
#print axioms rawField
#print axioms rawTerms
#print axioms namedValue

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT1116Cover

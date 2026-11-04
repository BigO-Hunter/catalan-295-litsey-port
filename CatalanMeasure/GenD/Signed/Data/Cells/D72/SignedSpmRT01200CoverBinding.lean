module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0FieldBinding
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


theorem rawField : fieldNFCheck ceSignedSpmRT01200Fq (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt ((1 : ℚ) / 200)) = true := by decide +kernel
theorem rawTerms : laurentNF ceSignedSpmRT01200Ts = laurentNF (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) := by decide +kernel
theorem namedValue (x : ℝ) : fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x = fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt ((1 : ℚ) / 200)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt ((1 : ℚ) / 200)).poles) 0 x + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 x := by
  rw [fieldNFCheck_sound rawField x, ← laurentNF_sound ceSignedSpmRT01200Ts x, rawTerms, laurentNF_sound (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) x]
#print axioms rawField
#print axioms rawTerms
#print axioms namedValue

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover

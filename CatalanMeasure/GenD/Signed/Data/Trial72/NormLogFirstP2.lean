module
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Representative declaration17 from the actual firstP log chunks.
This is the largest estimated-operation two-row chunk (300 log terms),
not a zero-residue row or a substituted transcendental-log bound.
Source norm-firstP.json SHA256 1dacd71c343af63a5d5f051d1a4199783b909d41bc8b585ecf1043db61d82217. -/
-- kcost: 12.0552s estimated: 120552 rational operations, 32400 series iterations; max input114bits.
theorem nlFirstP17 : logUpperOK
    (((ReferenceData.firstPData.tail.drop 34).take 2).flatMap (CatalanMeasure.CellCert.rowTerms ReferenceData.firstPData.tail))
    (129977196269059 / 1152921504606846976 : ℚ) = true := by decide +kernel
end
end CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2.nlFirstP17

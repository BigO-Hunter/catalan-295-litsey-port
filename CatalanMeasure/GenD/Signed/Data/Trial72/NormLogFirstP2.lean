module
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
public import CatalanMeasure.GenD.Cert.WLogSpec
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! C24: two one-row declarations over the SAME frozen two-row norm input,
shared checked WLog node tables, adaptive series/cutoff, per-term dyadic rounding.
The final upper bound is the identical rational cap used in baseline3be23a2b.
No complete norm claim; this is the directed representative before norm bulk. -/
def rows17 := (ReferenceData.firstPData.tail.drop 34).take 2
def terms34 := (rows17.take 1).flatMap (CatalanMeasure.CellCert.rowTerms ReferenceData.firstPData.tail)
def terms35 := (rows17.drop 1).flatMap (CatalanMeasure.CellCert.rowTerms ReferenceData.firstPData.tail)
-- kcost: 1.2680s estimated: 12680 rational operations;150input terms, one outer row; shared nodes checked once.
theorem nlFirstP34W : logUpperWOK terms34 (25027465317729/1152921504606846976:ℚ) = true := by decide +kernel
-- kcost: 1.2728s estimated: 12728 rational operations;150input terms, one outer row; shared nodes checked once.
theorem nlFirstP35W : logUpperWOK terms35 (26237350933331/288230376151711744:ℚ) = true := by decide +kernel

theorem nlFirstP17 :
    ((((ReferenceData.firstPData.tail.drop 34).take 2).flatMap
      (CatalanMeasure.CellCert.rowTerms ReferenceData.firstPData.tail)).map LogTerm.val).sum ≤
        ((129977196269059/1152921504606846976:ℚ) : ℝ) := by
  have h0 := logUpperW_le nlFirstP34W
  have h1 := logUpperW_le nlFirstP35W
  change pairRowsValue ReferenceData.firstPData.tail (rows17.take 1) ≤ ((25027465317729/1152921504606846976:ℚ) : ℝ) at h0
  change pairRowsValue ReferenceData.firstPData.tail (rows17.drop 1) ≤ ((26237350933331/288230376151711744:ℚ) : ℝ) at h1
  have hs := pairRowsValue_split ReferenceData.firstPData.tail rows17 1
  have hc : (25027465317729/1152921504606846976:ℚ)+(26237350933331/288230376151711744:ℚ) ≤ (129977196269059/1152921504606846976:ℚ) := by decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr hc
  push_cast at hr
  change pairRowsValue ReferenceData.firstPData.tail rows17 ≤ ((129977196269059/1152921504606846976:ℚ) : ℝ)
  linarith only [h0,h1,hs,hr]
end
end CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2
#print axioms CatalanMeasure.WLog.lnChk_all
#print axioms CatalanMeasure.WLog.atChk_all
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2.nlFirstP34W
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2.nlFirstP35W
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormLogFirstP2.nlFirstP17

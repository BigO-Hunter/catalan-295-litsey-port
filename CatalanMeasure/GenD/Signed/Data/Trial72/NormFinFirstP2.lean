module
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NormFinFirstP2
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Representative four-tail Horner chunk14: maximum exact-result
height9580bits in this raw firstP table.
Source norm-firstP.json SHA256 1dacd71c343af63a5d5f051d1a4199783b909d41bc8b585ecf1043db61d82217. -/
-- kcost: 0.5784s estimated: 5784 rational operations and 640 Horner steps; GCD/large-integer cost additional.
theorem nfFirstP14 :
    (((ReferenceData.firstPData.tail.drop 56).take 4).map (nCross NormData.firstPInt)).sum ≤
      (263100062482284957 / 1152921504606846976 : ℚ) := by decide +kernel
end
end CatalanMeasure.GenD.Signed.Data.Trial72.NormFinFirstP2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NormFinFirstP2.nfFirstP14

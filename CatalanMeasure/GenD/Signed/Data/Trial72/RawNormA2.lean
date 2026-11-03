module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2Log09

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < A2LogUBs.length,
    logUpperWOK (((A2Tail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A2Tail))
      (A2LogUBs.getD j 0) = true := by
  intro j hj
  change j < 20 at hj
  interval_cases j
  · exact RawNormA2Log00.row0
  · exact RawNormA2Log00.row1
  · exact RawNormA2Log01.row2
  · exact RawNormA2Log01.row3
  · exact RawNormA2Log02.row4
  · exact RawNormA2Log02.row5
  · exact RawNormA2Log03.row6
  · exact RawNormA2Log03.row7
  · exact RawNormA2Log04.row8
  · exact RawNormA2Log04.row9
  · exact RawNormA2Log05.row10
  · exact RawNormA2Log05.row11
  · exact RawNormA2Log06.row12
  · exact RawNormA2Log06.row13
  · exact RawNormA2Log07.row14
  · exact RawNormA2Log07.row15
  · exact RawNormA2Log08.row16
  · exact RawNormA2Log08.row17
  · exact RawNormA2Log09.row18
  · exact RawNormA2Log09.row19

theorem log_bound : ((pairTerms A2Tail).map LogTerm.val).sum ≤ (A2LogUBs.sum : ℝ) :=
  pair_le_of_row_chunk_bounds A2Tail 1 A2LogUBs (by decide +kernel)
    (fun j hj => logUpperW_le (logs_ok j hj))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA2.log_bound

module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1Log09

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < A1LogUBs.length,
    logUpperWOK (((A1Tail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A1Tail))
      (A1LogUBs.getD j 0) = true := by
  intro j hj
  change j < 20 at hj
  interval_cases j
  · exact RawNormA1Log00.row0
  · exact RawNormA1Log00.row1
  · exact RawNormA1Log01.row2
  · exact RawNormA1Log01.row3
  · exact RawNormA1Log02.row4
  · exact RawNormA1Log02.row5
  · exact RawNormA1Log03.row6
  · exact RawNormA1Log03.row7
  · exact RawNormA1Log04.row8
  · exact RawNormA1Log04.row9
  · exact RawNormA1Log05.row10
  · exact RawNormA1Log05.row11
  · exact RawNormA1Log06.row12
  · exact RawNormA1Log06.row13
  · exact RawNormA1Log07.row14
  · exact RawNormA1Log07.row15
  · exact RawNormA1Log08.row16
  · exact RawNormA1Log08.row17
  · exact RawNormA1Log09.row18
  · exact RawNormA1Log09.row19

theorem log_bound : ((pairTerms A1Tail).map LogTerm.val).sum ≤ (A1LogUBs.sum : ℝ) :=
  pair_le_of_row_chunk_bounds A1Tail 1 A1LogUBs (by decide +kernel)
    (fun j hj => logUpperW_le (logs_ok j hj))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA1.log_bound

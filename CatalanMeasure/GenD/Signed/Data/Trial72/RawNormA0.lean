module

public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log00
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log01
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log02
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log03
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log04
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log05
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log06
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log07
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log08
public import CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0Log09

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open RawNormBounds
theorem logs_ok : ∀ j < A0LogUBs.length,
    logUpperWOK (((A0Tail.drop (1 * j)).take 1).flatMap (CatalanMeasure.CellCert.rowTerms A0Tail))
      (A0LogUBs.getD j 0) = true := by
  intro j hj
  change j < 20 at hj
  interval_cases j
  · exact RawNormA0Log00.row0
  · exact RawNormA0Log00.row1
  · exact RawNormA0Log01.row2
  · exact RawNormA0Log01.row3
  · exact RawNormA0Log02.row4
  · exact RawNormA0Log02.row5
  · exact RawNormA0Log03.row6
  · exact RawNormA0Log03.row7
  · exact RawNormA0Log04.row8
  · exact RawNormA0Log04.row9
  · exact RawNormA0Log05.row10
  · exact RawNormA0Log05.row11
  · exact RawNormA0Log06.row12
  · exact RawNormA0Log06.row13
  · exact RawNormA0Log07.row14
  · exact RawNormA0Log07.row15
  · exact RawNormA0Log08.row16
  · exact RawNormA0Log08.row17
  · exact RawNormA0Log09.row18
  · exact RawNormA0Log09.row19

theorem log_bound : ((pairTerms A0Tail).map LogTerm.val).sum ≤ (A0LogUBs.sum : ℝ) :=
  pair_le_of_row_chunk_bounds A0Tail 1 A0LogUBs (by decide +kernel)
    (fun j hj => logUpperW_le (logs_ok j hj))

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RawNormA0.log_bound

module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColMisc
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColBr
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCells
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColPack
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal1
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal2
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal3
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal4
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal5
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal6
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: assembly only (generic column terminal theorem applied to the checked instance facts)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCap
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColInst CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
open CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep CatalanMeasure.GenD.Signed.RouteI.Maxima.ColMisc CatalanMeasure.GenD.Signed.RouteI.Maxima.ColBr CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCells CatalanMeasure.GenD.Signed.RouteI.Maxima.ColPack
theorem vals_all : ∀ l∈keepLsY,evLe (colSpecW C Vc V 0).ev (midQ l) (MY - 1/2^28)=true := by
  intro l hl
  simp only [keepLsY,List.mem_append] at hl
  rcases hl with ((((((h0) | h1) | h2) | h3) | h4) | h5) | h6
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal0.valsC0 l h0
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal1.valsC1 l h1
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal2.valsC2 l h2
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal3.valsC3 l h3
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal4.valsC4 l h4
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal5.valsC5 l h5
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.ColVal6.valsC6 l h6
/-- Terminal statement, the same type as `column_sup_S` (PositiveCert/YCover.lean) for the copied data. -/
theorem xmAvoidY : ∀ s∈Set.Ioo (0 : ℝ) 1,colFieldS C Vc V s≤(MY : ℝ) :=
  col_cap_terminal C Vc V MY tailsV V_nonzero (by norm_num [C]) (by norm_num [C])
    csY scaleY fsY cellsY vsY LsY keepLsY y_hcs y_hcsl y_hc0 y_hscale y_hfs leavesY zY y_hleq y_hZeq
    y_hlv y_hlvl y_hleaves y_hpack y_hcells y_hvl y_hchain y_hsum y_hbr y_hord y_hpos y_hkeep vals_all
    y_hok y_hL
#print axioms xmAvoidY
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCap

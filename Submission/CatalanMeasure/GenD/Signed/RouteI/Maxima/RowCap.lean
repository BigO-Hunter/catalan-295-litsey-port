module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowMisc
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBr
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCells
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowPack
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBound
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal0
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal1
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal2
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal3
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal4
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal5
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal6
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal7
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal8
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal9
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: assembly only (generic terminal theorem applied to the checked instance facts)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCap
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
open CatalanMeasure.GenD.Signed.RouteI.Maxima.RowMisc CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBr CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCells CatalanMeasure.GenD.Signed.RouteI.Maxima.RowPack CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBound
theorem vals_all : ∀ l∈keepLsX,evLe (rowSpecW R Pc Vc P V 0).ev (midQ l) (MX - 1/2^28)=true := by
  intro l hl
  simp only [keepLsX,List.mem_append] at hl
  rcases hl with (((((((((h0) | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal0.valsC0 l h0
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal1.valsC1 l h1
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal2.valsC2 l h2
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal3.valsC3 l h3
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal4.valsC4 l h4
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal5.valsC5 l h5
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal6.valsC6 l h6
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal7.valsC7 l h7
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal8.valsC8 l h8
  · exact CatalanMeasure.GenD.Signed.RouteI.Maxima.RowVal9.valsC9 l h9
/-- Terminal statement, the same type as `row_sup_S` for the copied data. -/
theorem xmAvoidX : ∀ x∈Set.Ico (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1,rowFieldS R Pc Vc P V x≤(MX : ℝ) :=
  row_cap_terminal R Pc Vc P V MX tailsP tailsV P_nonzero V_nonzero (by norm_num [R]) (by norm_num [R])
    csX scaleX fsX cellsX vsX LsX keepLsX x_hcs x_hcsl x_hc0 x_hscale x_hfs leavesX zX x_hleq x_hZeq
    x_hlv x_hlvl x_hleaves x_hpack x_hcells x_hvl x_hchain x_hsum x_hbr x_hord x_hkeep vals_all
    x_bound x_hok x_hL
#print axioms xmAvoidX
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCap

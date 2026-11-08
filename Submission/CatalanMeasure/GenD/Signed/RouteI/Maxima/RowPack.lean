module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: packed identity of fullNum vs scale*reduced*cancel at base 2*(max mass+1), degree<=467; one declaration, balanced evaluation tree for the reduced polynomial
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowPack
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst
theorem x_hpack : PackOK zX (buildPT 8 (leavesX.map PoleTree.leaf)) csX scaleX fsX := by decide +kernel -- kcost: 3.4 s (standalone 5 Nov)
#print axioms x_hpack
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowPack

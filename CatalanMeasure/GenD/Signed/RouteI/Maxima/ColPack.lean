module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColData
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: packed identity fullNum = scale*reduced*cancel at base 2*(max mass+1), degree<=313; one declaration (X: 3.4 s at degree 465)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColPack
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.ColInst
theorem y_hpack : PackOK zY (buildPT 8 (leavesY.map PoleTree.leaf)) csY scaleY fsY := by decide +kernel -- kcost: 1.6 s (standalone 6 Nov)
#print axioms y_hpack
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColPack

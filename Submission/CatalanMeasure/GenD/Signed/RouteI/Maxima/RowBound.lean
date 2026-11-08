module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: one evLe goal at x=-1 (RealValueChunk rowBoundary 3.97 s)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBound
open CatalanMeasure.CellCert CatalanMeasure.GenD.D58.Cert590
theorem x_bound : evLe (rowSpecW R Pc Vc P V 0).ev (-1) (MX - 1/2^28) = true := by decide +kernel
#print axioms x_bound
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowBound

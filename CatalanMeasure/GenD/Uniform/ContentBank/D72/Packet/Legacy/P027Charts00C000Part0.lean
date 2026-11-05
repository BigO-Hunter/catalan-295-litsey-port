module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Part0Sub0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Part0Sub1
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Part0Sub2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Part0Sub3
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Part0Sub4
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C000
theorem part0 : kerOK basis.matrix 89 87 ((chart.ker).take 5) chart.rows = true := by
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part0s0) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part0s1) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part0s2) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part0s3) ?_
  simpa only [List.drop_drop] using part0s4

end C000
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027

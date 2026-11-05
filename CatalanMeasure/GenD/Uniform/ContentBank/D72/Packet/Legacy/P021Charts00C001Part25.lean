module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Part25Sub0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Part25Sub1
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Part25Sub2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Part25Sub3
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Part25Sub4
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C001
theorem part25 : kerOK basis.matrix 90 87 ((chart.ker.drop 25).take 5) chart.rows = true := by
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part25s0) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part25s1) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part25s2) ?_
  refine kerOK_join (i := 1) (by simpa only [List.drop_drop] using part25s3) ?_
  simpa only [List.drop_drop] using part25s4

end C001
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

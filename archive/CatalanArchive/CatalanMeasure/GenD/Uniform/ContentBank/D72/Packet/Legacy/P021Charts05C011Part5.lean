module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C011
theorem part5 : kerOK basis.matrix 90 87 ((chart.ker.drop 5).take 5) chart.rows = true := by decide +kernel

end C011
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

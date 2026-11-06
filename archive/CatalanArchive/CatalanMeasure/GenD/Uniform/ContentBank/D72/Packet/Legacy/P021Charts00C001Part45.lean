module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00C001Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C001
theorem part45 : kerOK basis.matrix 90 87 ((chart.ker.drop 45).take 5) chart.rows = true := by decide +kernel

end C001
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

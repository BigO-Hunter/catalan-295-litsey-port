module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts01C002Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C002
-- kcost: 4.6458 s provisional model for 7743 first-product units.
theorem part58 : kerOK basis.matrix 89 87 (chart.ker.drop 58) chart.rows = true := by decide +kernel

end C002
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027

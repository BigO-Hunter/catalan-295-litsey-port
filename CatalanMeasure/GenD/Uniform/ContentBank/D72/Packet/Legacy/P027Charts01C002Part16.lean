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
-- kcost: 9.2916 s provisional model for 15486 first-product units.
theorem part16 : kerOK basis.matrix 89 87 ((chart.ker.drop 16).take 2) chart.rows = true := by decide +kernel

end C002
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027

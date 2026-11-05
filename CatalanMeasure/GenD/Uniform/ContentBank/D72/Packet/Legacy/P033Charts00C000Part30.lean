module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts00C000Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C000
-- kcost: 23.4900 s provisional model for 39150 first-product units.
theorem part30 : kerOK basis.matrix 90 87 ((chart.ker.drop 30).take 5) chart.rows = true := by decide +kernel

end C000
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033

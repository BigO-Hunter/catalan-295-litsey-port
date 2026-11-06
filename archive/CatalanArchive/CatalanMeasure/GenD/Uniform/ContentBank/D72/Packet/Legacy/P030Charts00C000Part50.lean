module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts00C000Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C000
-- kcost: 24.8400 s provisional model for 41400 first-product units.
theorem part50 : kerOK basis.matrix 92 90 ((chart.ker.drop 50).take 5) chart.rows = true := by decide +kernel

end C000
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030

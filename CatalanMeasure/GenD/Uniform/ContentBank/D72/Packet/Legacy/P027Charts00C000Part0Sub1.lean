module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027Charts00C000Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C000
-- kcost: 4.6458 s provisional model for 7743 first-product units.
theorem part0s1 : kerOK basis.matrix 89 87 ((((chart.ker).take 5).drop 1).take 1) chart.rows = true := by decide +kernel

end C000
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P027

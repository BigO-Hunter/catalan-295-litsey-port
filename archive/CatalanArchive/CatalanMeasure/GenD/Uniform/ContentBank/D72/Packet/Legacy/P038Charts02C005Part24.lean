module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts02C005Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C005
-- kcost: 9.9360 s provisional model for 16560 first-product units.
theorem part24 : kerOK basis.matrix 92 90 ((chart.ker.drop 24).take 2) chart.rows = true := by decide +kernel

end C005
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038

module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032
open CatalanMeasure.GenD.Uniform.W.Prof


-- kcost: 13.8624 s model; 23104 original product units.
#time theorem headRows09 : ((List.range' 72 4).all headRowOK) = true :=
  by decide +kernel
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032

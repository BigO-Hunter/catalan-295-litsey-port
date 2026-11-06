module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof


-- kcost: 36.3312 s model; 60552 original product units.
#time theorem headRows04 : ((List.range' 32 8).all headRowOK) = true :=
  by decide +kernel
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

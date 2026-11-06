module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
open CatalanMeasure.GenD.Uniform.W.Prof


-- kcost: 9.7200 s model; 16200 original product units.
#time theorem headRows11 : ((List.range' 88 2).all headRowOK) = true :=
  by decide +kernel
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030

module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Base

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033
open CatalanMeasure.GenD.Uniform.W.Prof


-- kcost: 31.7898 s model; 52983 original product units.
#time theorem headRows10 : ((List.range' 80 7).all headRowOK) = true :=
  by decide +kernel
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033

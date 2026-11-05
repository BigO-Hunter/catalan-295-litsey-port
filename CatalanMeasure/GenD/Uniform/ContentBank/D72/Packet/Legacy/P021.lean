module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts00
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts03
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts04
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Head

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

#time def packet : Packet := { input.packet with charts := [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart, C011.chart] }
-- kcost: 395.1018 s provisional ×3 model; 658503 original head product units.
#time theorem headChecked : packet.checkHead = true := inputHeadChecked
#time theorem checked : packet.check = true := by
  apply Packet.check_of_parts headChecked
  intro c hc
  change c ∈ [C000.chart, C001.chart, C002.chart, C003.chart, C004.chart, C005.chart, C006.chart, C007.chart, C008.chart, C009.chart, C010.chart, C011.chart] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact C000.checked
  · exact C001.checked
  · exact C002.checked
  · exact C003.checked
  · exact C004.checked
  · exact C005.checked
  · exact C006.checked
  · exact C007.checked
  · exact C008.checked
  · exact C009.checked
  · exact C010.checked
  · exact C011.checked
#time theorem sound : packet.Sound := Packet.check_sound checked
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

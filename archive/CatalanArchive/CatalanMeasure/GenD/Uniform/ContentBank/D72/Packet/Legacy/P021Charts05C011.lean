module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part5
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part15
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part25
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part35
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part45
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part50
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts05C011Part55
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C011

theorem checked : chart.check 90 87 basis.matrix = true := by
  simp only [Chart.check, Bool.and_eq_true]
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part0) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part5) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part10) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part15) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part20) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part25) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part30) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part35) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part40) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part45) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part50) ?_
  simpa only [List.drop_drop] using part55

end C011
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

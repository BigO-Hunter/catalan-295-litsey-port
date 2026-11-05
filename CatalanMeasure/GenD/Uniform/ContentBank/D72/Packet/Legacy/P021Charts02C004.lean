module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part5
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part15
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts02C004Part25
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C004
theorem checked : chart.check 90 87 basis.matrix = true := by
  simp only [Chart.check, Bool.and_eq_true]
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part0) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part5) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part10) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part15) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part20) ?_
  simpa only [List.drop_drop] using part25

end C004
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

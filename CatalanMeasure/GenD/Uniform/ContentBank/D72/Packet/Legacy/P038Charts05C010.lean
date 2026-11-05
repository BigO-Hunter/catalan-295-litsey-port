module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part26
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part28
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038Charts05C010Part30
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C010
theorem checked : chart.check 92 90 basis.matrix = true := by
  simp only [Chart.check, Bool.and_eq_true]
  refine ⟨⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part0) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part2) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part4) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part6) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part8) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part10) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part12) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part14) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part16) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part18) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part20) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part22) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part24) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part26) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part28) ?_
  simpa only [List.drop_drop] using part30

end C010
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P038

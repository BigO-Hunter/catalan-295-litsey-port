module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part26
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part28
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part32
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part34
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part36
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part38
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part42
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part44
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part46
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts01C003Part48
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C003
theorem checked : chart.check 100 76 basis.matrix = true := by
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
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part30) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part32) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part34) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part36) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part38) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part40) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part42) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part44) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part46) ?_
  simpa only [List.drop_drop] using part48

end C003
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032

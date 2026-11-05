module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part26
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part28
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part32
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part34
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part36
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part38
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part42
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part44
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part46
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part48
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032Charts00C000Part50
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C000
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
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part48) ?_
  simpa only [List.drop_drop] using part50

end C000
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P032

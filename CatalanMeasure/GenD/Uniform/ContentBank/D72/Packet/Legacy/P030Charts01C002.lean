module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part26
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part28
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part32
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part34
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part36
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part38
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part42
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part44
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part46
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part48
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part50
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part52
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part54
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part56
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part58
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts01C002Part60
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C002
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
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part50) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part52) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part54) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part56) ?_
  refine kerOK_join (i := 2) (by simpa only [List.drop_drop] using part58) ?_
  simpa only [List.drop_drop] using part60

end C002
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030

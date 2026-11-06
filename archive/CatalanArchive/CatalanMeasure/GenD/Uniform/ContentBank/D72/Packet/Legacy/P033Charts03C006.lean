module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part26
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part28
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part32
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part34
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part36
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part38
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part42
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part44
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part46
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part48
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part50
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part52
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part54
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033Charts03C006Part56
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C006
theorem checked : chart.check 90 87 basis.matrix = true := by
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
  simpa only [List.drop_drop] using part56

end C006
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P033

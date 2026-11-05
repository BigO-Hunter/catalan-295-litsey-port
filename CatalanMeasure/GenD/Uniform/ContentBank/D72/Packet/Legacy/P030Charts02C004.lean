module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part2
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part4
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part6
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part8
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part12
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part14
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part16
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part18
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part22
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part24
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030Charts02C004Part26
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C004
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
  simpa only [List.drop_drop] using part26

end C004
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P030

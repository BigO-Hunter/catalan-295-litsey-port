module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.GraphChartInd
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part50
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part60
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part70
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C002Part80
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C002
theorem checked : chart.check 90 87 basis.matrix = true := by
  simp only [Chart.check, Bool.and_eq_true]
  -- kcost: 87 list constructors for length; the 90-row scratch control took 10 ms.
  have hdim : (chart.ker.length + chart.r == 87) = true := by decide +kernel
  -- kcost: 174 finite role comparisons, with at most 30276 list visits.
  have hrole : graph.roleCheck roles = true := by decide +kernel
  refine ⟨⟨hdim, graphChart_indOK graph chartRows roles hrole⟩, ?_⟩
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part0) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part10) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part20) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part30) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part40) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part50) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part60) ?_
  refine kerOK_join (i := 10) (by simpa only [List.drop_drop] using part70) ?_
  simpa only [List.drop_drop] using part80

end C002
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

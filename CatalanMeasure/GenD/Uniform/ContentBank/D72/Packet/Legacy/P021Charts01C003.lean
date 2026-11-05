module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.GraphChartInd
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.ChartParts
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Data
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part0
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part5
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part10
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part15
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part20
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part25
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part30
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part35
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part40
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part45
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part50
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part55
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part60
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part65
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part70
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part75
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part80
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021Charts01C003Part85
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-! Exact D72 finite packet; checked by the original Packet.check. -/
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021
open CatalanMeasure.GenD.Uniform.W.Prof

namespace C003
theorem checked : chart.check 90 87 basis.matrix = true := by
  simp only [Chart.check, Bool.and_eq_true]
  -- kcost: 87 list constructors for length; the 90-row scratch control took 10 ms.
  have hdim : (chart.ker.length + chart.r == 87) = true := by decide +kernel
  -- kcost: 174 finite role comparisons, with at most 30276 list visits.
  have hrole : graph.roleCheck roles = true := by decide +kernel
  refine ⟨⟨hdim, graphChart_indOK graph chartRows roles hrole⟩, ?_⟩
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
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part55) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part60) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part65) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part70) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part75) ?_
  refine kerOK_join (i := 5) (by simpa only [List.drop_drop] using part80) ?_
  simpa only [List.drop_drop] using part85

end C003
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Packet.Legacy.P021

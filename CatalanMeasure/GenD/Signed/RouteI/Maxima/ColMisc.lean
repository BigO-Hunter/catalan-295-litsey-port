module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColData
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: structural decide checks (leaves 77, poles 77, Z 160); X measured 62 s for 153 leaves
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColMisc
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.ColInst CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.ColGenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
theorem y_hcs : csY≠[] := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hcsl : csY.length≤512 := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hc0 : csY.getD 0 0≠0 := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hscale : 0<scaleY := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hfs : ∀ f∈fsY,SafeFactor f := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hlv : 0<(colLeavesOf C V).length := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hlvl : (colLeavesOf C V).length≤256 := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hleaves : ∀ r∈colLeavesOf C V,0<r.D ∧ 0<r.E ∧ SafePole r := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hleq : colLeavesOf C V=leavesY := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hZeq : colZ Vc=zY := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hok : ∀ q∈colPolesP C V false false,PoleOK q := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hL : 2*uBnd Vc+(poleBoundC (1/2^50) (colPolesP C V false false) : Rat)≤2^50 := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hchain : chainOK 0 1 (cellsY.map ratCell)=true := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hvl : vsY.length=cellsY.length := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hsum : vsY.sum=LsY.length := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hord : adj LsY=true := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem y_hpos : ∀ l∈LsY,dI≤l := by decide +kernel -- kcost: structural checks, 33.5 s total for the module, hleq dominates (standalone 6 Nov)
#print axioms y_hcs
#print axioms y_hcsl
#print axioms y_hc0
#print axioms y_hscale
#print axioms y_hfs
#print axioms y_hlv
#print axioms y_hlvl
#print axioms y_hleaves
#print axioms y_hleq
#print axioms y_hZeq
#print axioms y_hok
#print axioms y_hL
#print axioms y_hchain
#print axioms y_hvl
#print axioms y_hsum
#print axioms y_hord
#print axioms y_hpos
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColMisc

module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RowData
public import Submission.CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: structural decide checks (leaves 153, poles 153, Z 160); measured 4.0 s total
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RowMisc
open CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.GenD.Signed.RouteI.Maxima.RowInst CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericB CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
theorem x_hcs : csX≠[] := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hcsl : csX.length≤512 := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hc0 : csX.getD 0 0≠0 := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hscale : 0<scaleX := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hfs : ∀ f∈fsX,SafeFactor f := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hlv : 0<(leavesOf R P V).length := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hlvl : (leavesOf R P V).length≤256 := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hleaves : ∀ r∈leavesOf R P V,0<r.D ∧ 0<r.E ∧ SafePole r := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hleq : leavesOf R P V=leavesX := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hZeq : rowZ Pc Vc=zX := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hok : ∀ q∈rowPolesP R P V false false,PoleOK q := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hL : 4*uBnd Pc+pBnd Vc+(poleBoundC (1/2^50) (rowPolesP R P V false false) : Rat)≤2^50 := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hchain : chainOK (-1) 1 (cellsX.map ratCell)=true := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hvl : vsX.length=cellsX.length := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hsum : vsX.sum=LsX.length := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
theorem x_hord : adj LsX=true := by decide +kernel -- kcost: structural checks, 36.5 s total for the module, hleq dominates (standalone 6 Nov)
#print axioms x_hcs
#print axioms x_hcsl
#print axioms x_hc0
#print axioms x_hscale
#print axioms x_hfs
#print axioms x_hlv
#print axioms x_hlvl
#print axioms x_hleaves
#print axioms x_hleq
#print axioms x_hZeq
#print axioms x_hok
#print axioms x_hL
#print axioms x_hchain
#print axioms x_hvl
#print axioms x_hsum
#print axioms x_hord
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RowMisc

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedScDeltaT2Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedScDeltaT2BindingLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedScDeltaT2BindingLiteral
set_option profiler true
theorem ceSignedScDeltaT2Field : fieldNFCheck CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (fqAdd CatalanMeasure.GenD.Signed.Data.Trial72.T0.scFq ceSignedScDeltaT2Fq) = true := by decide +kernel
theorem ceSignedScDeltaT2Identity (x : ℝ) :
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.scFq.poles) 0 x =
      fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.scFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.scFq.poles) 0 x + fieldTower ceSignedScDeltaT2Fq (poleF ceSignedScDeltaT2Fq.poles) 0 x := by
  rw [fieldNFCheck_sound ceSignedScDeltaT2Field x,fieldTower_add]
#print axioms ceSignedScDeltaT2Field
#print axioms ceSignedScDeltaT2Identity

end CatalanMeasure.GenD.Signed.Data.Cells

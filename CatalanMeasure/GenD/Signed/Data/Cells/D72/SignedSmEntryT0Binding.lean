module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSmEntryT0Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Fields
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSmEntryT0BindingLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSmEntryT0BindingLiteral
set_option profiler true
theorem ceSignedSmEntryT0FieldCheck : fieldNFCheck ceSignedSmEntryT0Fq CatalanMeasure.GenD.Signed.Data.Trial72.T0.smFq = true := by decide +kernel
theorem ceSignedSmEntryT0FieldEq (x : ℝ) :
    fieldTower ceSignedSmEntryT0Fq (poleF ceSignedSmEntryT0Fq.poles) 0 x =
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.smFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.smFq.poles) 0 x :=
  fieldNFCheck_sound ceSignedSmEntryT0FieldCheck x
#print axioms ceSignedSmEntryT0FieldCheck
#print axioms ceSignedSmEntryT0FieldEq

end CatalanMeasure.GenD.Signed.Data.Cells

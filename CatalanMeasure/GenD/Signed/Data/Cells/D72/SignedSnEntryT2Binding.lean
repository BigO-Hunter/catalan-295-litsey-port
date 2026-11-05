module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSnEntryT2BindingLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSnEntryT2BindingLiteral
set_option profiler true
theorem ceSignedSnEntryT2FieldCheck : fieldNFCheck ceSignedSnEntryT2Fq CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq = true := by decide +kernel
theorem ceSignedSnEntryT2FieldEq (x : ℝ) :
    fieldTower ceSignedSnEntryT2Fq (poleF ceSignedSnEntryT2Fq.poles) 0 x =
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq.poles) 0 x :=
  fieldNFCheck_sound ceSignedSnEntryT2FieldCheck x
#print axioms ceSignedSnEntryT2FieldCheck
#print axioms ceSignedSnEntryT2FieldEq

end CatalanMeasure.GenD.Signed.Data.Cells

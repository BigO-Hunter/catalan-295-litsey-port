module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Literal
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Fields
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace SignedSnEntryT1BindingLiteral
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end SignedSnEntryT1BindingLiteral
set_option profiler true
theorem ceSignedSnEntryT1FieldCheck : fieldNFCheck ceSignedSnEntryT1Fq CatalanMeasure.GenD.Signed.Data.Trial72.T1.snFq = true := by decide +kernel
theorem ceSignedSnEntryT1FieldEq (x : ℝ) :
    fieldTower ceSignedSnEntryT1Fq (poleF ceSignedSnEntryT1Fq.poles) 0 x =
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.snFq.poles) 0 x :=
  fieldNFCheck_sound ceSignedSnEntryT1FieldCheck x
#print axioms ceSignedSnEntryT1FieldCheck
#print axioms ceSignedSnEntryT1FieldEq

end CatalanMeasure.GenD.Signed.Data.Cells

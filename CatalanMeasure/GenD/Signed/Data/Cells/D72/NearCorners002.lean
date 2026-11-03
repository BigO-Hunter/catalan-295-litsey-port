module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearBinding002
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Fields
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2FieldBinding
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearCorners002
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearCorners002
namespace D72.NearCorners002
open CatalanMeasure.GenD.Signed.Data.Trial
def delta0 : FieldQ := ⟨d2LitsNearCorners002.q2listC (raw_ints% []), [], mkPolesC (d2LitsNearCorners002.q2listC (raw_ints% []))⟩
-- kcost: frozen Near corner normal-form equality; only constant-coefficient logs differ, pole/Laurent data unchanged.
theorem corner0Check : fieldNFCheck (fqAdd NearBinding002.literalField delta0) (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (0) 1 (0))) = true := by decide +kernel
theorem corner0Value (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (0) 1 (0))) x = fval NearBinding002.literalField x + fval delta0 x := by
  have h := fieldNFCheck_sound corner0Check x
  change fval (fqAdd NearBinding002.literalField delta0) x = fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (0) 1 (0))) x at h
  rw [fval_add] at h
  exact h.symm
-- kcost: exact finite Laurent equality; same frozen qF/qFn for every corner.
theorem corner0Terms : laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) = laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) := by decide +kernel
#print axioms corner0Check
#print axioms corner0Value
#print axioms corner0Terms
def delta1 : FieldQ := ⟨d2LitsNearCorners002.q2listC (raw_ints% []), [(d2LitsNearCorners002.q2listC (raw_ints% [-1, 55, -3]), (d2LitsNearCorners002.q2 (-1) 1 (0))), (d2LitsNearCorners002.q2listC (raw_ints% [-1, 55, -3]), (d2LitsNearCorners002.q2 (1) 1 (0)))], mkPolesC (d2LitsNearCorners002.q2listC (raw_ints% []))⟩
-- kcost: frozen Near corner normal-form equality; only constant-coefficient logs differ, pole/Laurent data unchanged.
theorem corner1Check : fieldNFCheck (fqAdd NearBinding002.literalField delta1) (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (1) 25 (-3))) = true := by decide +kernel
theorem corner1Value (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (1) 25 (-3))) x = fval NearBinding002.literalField x + fval delta1 x := by
  have h := fieldNFCheck_sound corner1Check x
  change fval (fqAdd NearBinding002.literalField delta1) x = fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 25 (-3)) (d2LitsNearCorners002.q2 (1) 25 (-3))) x at h
  rw [fval_add] at h
  exact h.symm
-- kcost: exact finite Laurent equality; same frozen qF/qFn for every corner.
theorem corner1Terms : laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) = laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) := by decide +kernel
#print axioms corner1Check
#print axioms corner1Value
#print axioms corner1Terms
def delta2 : FieldQ := ⟨d2LitsNearCorners002.q2listC (raw_ints% []), [(d2LitsNearCorners002.q2listC (raw_ints% [23, 25, -5]), (d2LitsNearCorners002.q2 (-1) 1 (0)))], mkPolesC (d2LitsNearCorners002.q2listC (raw_ints% []))⟩
-- kcost: frozen Near corner normal-form equality; only constant-coefficient logs differ, pole/Laurent data unchanged.
theorem corner2Check : fieldNFCheck (fqAdd NearBinding002.literalField delta2) (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (0) 1 (0))) = true := by decide +kernel
theorem corner2Value (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (0) 1 (0))) x = fval NearBinding002.literalField x + fval delta2 x := by
  have h := fieldNFCheck_sound corner2Check x
  change fval (fqAdd NearBinding002.literalField delta2) x = fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (0) 1 (0))) x at h
  rw [fval_add] at h
  exact h.symm
-- kcost: exact finite Laurent equality; same frozen qF/qFn for every corner.
theorem corner2Terms : laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) = laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) := by decide +kernel
#print axioms corner2Check
#print axioms corner2Value
#print axioms corner2Terms
def delta3 : FieldQ := ⟨d2LitsNearCorners002.q2listC (raw_ints% []), [(d2LitsNearCorners002.q2listC (raw_ints% [3, 275, -5]), (d2LitsNearCorners002.q2 (-1) 1 (0))), (d2LitsNearCorners002.q2listC (raw_ints% [-5, 11, -4]), (d2LitsNearCorners002.q2 (1) 1 (0)))], mkPolesC (d2LitsNearCorners002.q2listC (raw_ints% []))⟩
-- kcost: frozen Near corner normal-form equality; only constant-coefficient logs differ, pole/Laurent data unchanged.
theorem corner3Check : fieldNFCheck (fqAdd NearBinding002.literalField delta3) (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (1) 1 (-4))) = true := by decide +kernel
theorem corner3Value (x : ℝ) : fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (1) 1 (-4))) x = fval NearBinding002.literalField x + fval delta3 x := by
  have h := fieldNFCheck_sound corner3Check x
  change fval (fqAdd NearBinding002.literalField delta3) x = fval (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt (d2LitsNearCorners002.q2 (1) 1 (-4)) (d2LitsNearCorners002.q2 (1) 1 (-4))) x at h
  rw [fval_add] at h
  exact h.symm
-- kcost: exact finite Laurent equality; same frozen qF/qFn for every corner.
theorem corner3Terms : laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) = laurentNF (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) := by decide +kernel
#print axioms corner3Check
#print axioms corner3Value
#print axioms corner3Terms
end D72.NearCorners002
end CatalanMeasure.GenD.Signed.Data.Cells

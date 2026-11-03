module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsConstantsGate
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsConstantsGate
namespace D72.StandaloneConstantsGate
open CatalanMeasure.GenD.Signed.Data.Consts.EvalKappa
open CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
open D72.StandaloneAdapter
set_option profiler true
set_option profiler.threshold 0
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic0 : encT firstPData.tail = some (-43019117843867337, 273) := by decide +kernel
def iv0 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (-21509558921933805) 1 (-55)), (d2LitsConstantsGate.q2 (-5377389730483383) 1 (-53)))
theorem enclosed0 : Encl (tailT firstPData) iv0 := by
  change Encl (tConstE firstPData.tail) iv0
  have h := encl_tConst firstPData.tail
  rw [basic0] at h
  have he : ivOf (some (-43019117843867337, 273)) = iv0 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic1 : encS firstVData.tail = some (-284934103039664982, 276) := by decide +kernel
def iv1 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (-142467051519832629) 1 (-55)), (d2LitsConstantsGate.q2 (-142467051519832353) 1 (-55)))
theorem enclosed1 : Encl (tailS firstVData) iv1 := by
  change Encl (sConstE firstVData.tail) iv1
  have h := encl_sConst firstVData.tail
  rw [basic1] at h
  have he : ivOf (some (-284934103039664982, 276)) = iv1 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic2 : encT firstVData.tail = some (-216453495415139385, 273) := by decide +kernel
def iv2 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (-108226747707569829) 1 (-55)), (d2LitsConstantsGate.q2 (-27056686926892389) 1 (-53)))
theorem enclosed2 : Encl (tailT firstVData) iv2 := by
  change Encl (tConstE firstVData.tail) iv2
  have h := encl_tConst firstVData.tail
  rw [basic2] at h
  have he : ivOf (some (-216453495415139385, 273)) = iv2 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic3 : encT secondPData.tail = some (-374182068496652202, 281) := by decide +kernel
def iv3 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (-374182068496652483) 1 (-56)), (d2LitsConstantsGate.q2 (-374182068496651921) 1 (-56)))
theorem enclosed3 : Encl (tailT secondPData) iv3 := by
  change Encl (tConstE secondPData.tail) iv3
  have h := encl_tConst secondPData.tail
  rw [basic3] at h
  have he : ivOf (some (-374182068496652202, 281)) = iv3 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic4 : encS secondVData.tail = some (219958300254890109, 319) := by decide +kernel
def iv4 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (109979150127444895) 1 (-55)), (d2LitsConstantsGate.q2 (54989575063722607) 1 (-54)))
theorem enclosed4 : Encl (tailS secondVData) iv4 := by
  change Encl (sConstE secondVData.tail) iv4
  have h := encl_sConst secondVData.tail
  rw [basic4] at h
  have he : ivOf (some (219958300254890109, 319)) = iv4 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:75pole terms,estimated10500integer steps atP56; one independent declaration.
theorem basic5 : encT secondVData.tail = some (605944718502765539, 290) := by decide +kernel
def iv5 : Option (ℚ × ℚ) := some ((d2LitsConstantsGate.q2 (605944718502765249) 1 (-56)), (d2LitsConstantsGate.q2 (605944718502765829) 1 (-56)))
theorem enclosed5 : Encl (tailT secondVData) iv5 := by
  change Encl (tConstE secondVData.tail) iv5
  have h := encl_tConst secondVData.tail
  rw [basic5] at h
  have he : ivOf (some (605944718502765539, 290)) = iv5 := by decide +kernel
  rw [he] at h
  exact h
-- kcost:<50rational operations; six basic enclosures shared by all five expressions.
theorem firstRowCheck : lin3 0 (d2LitsConstantsGate.q2 (-1) 1 (2)) (d2LitsConstantsGate.q2 (-1) 1 (0)) 0 iv0 iv1 iv1 (d2LitsConstantsGate.q2 (228505287207567849) 1 (-55)) = true := by decide +kernel
theorem firstRowUpper : rowK firstPData firstVData ≤ (((d2LitsConstantsGate.q2 (228505287207567849) 1 (-55)):ℚ):ℝ) := by
  have h := lin3_sound enclosed0 enclosed1 enclosed1 firstRowCheck
  norm_num [d2LitsConstantsGate.q2, rowK, columnK, residualK] at h ⊢
  linarith
-- kcost:<50rational operations; six basic enclosures shared by all five expressions.
theorem firstColCheck : lin3 0 (d2LitsConstantsGate.q2 (1) 1 (1)) (d2LitsConstantsGate.q2 (0) 1 (0)) 0 iv2 iv2 iv2 (d2LitsConstantsGate.q2 (-27056686926892389) 1 (-52)) = true := by decide +kernel
theorem firstColUpper : columnK firstVData ≤ (((d2LitsConstantsGate.q2 (-27056686926892389) 1 (-52)):ℚ):ℝ) := by
  have h := lin3_sound enclosed2 enclosed2 enclosed2 firstColCheck
  norm_num [d2LitsConstantsGate.q2, rowK, columnK, residualK] at h ⊢
  linarith
-- kcost:<50rational operations; six basic enclosures shared by all five expressions.
theorem refRowCheck : lin3 0 (d2LitsConstantsGate.q2 (-1) 1 (2)) (d2LitsConstantsGate.q2 (-1) 1 (0)) 0 iv3 iv4 iv4 (d2LitsConstantsGate.q2 (638384986865860071) 1 (-55)) = true := by decide +kernel
theorem refRowUpper : rowK secondPData secondVData ≤ (((d2LitsConstantsGate.q2 (638384986865860071) 1 (-55)):ℚ):ℝ) := by
  have h := lin3_sound enclosed3 enclosed4 enclosed4 refRowCheck
  norm_num [d2LitsConstantsGate.q2, rowK, columnK, residualK] at h ⊢
  linarith
-- kcost:<50rational operations; six basic enclosures shared by all five expressions.
theorem refColCheck : lin3 0 (d2LitsConstantsGate.q2 (1) 1 (1)) (d2LitsConstantsGate.q2 (0) 1 (0)) 0 iv5 iv5 iv5 (d2LitsConstantsGate.q2 (605944718502765829) 1 (-55)) = true := by decide +kernel
theorem refColUpper : columnK secondVData ≤ (((d2LitsConstantsGate.q2 (605944718502765829) 1 (-55)):ℚ):ℝ) := by
  have h := lin3_sound enclosed5 enclosed5 enclosed5 refColCheck
  norm_num [d2LitsConstantsGate.q2, rowK, columnK, residualK] at h ⊢
  linarith
-- kcost:<50rational operations; six basic enclosures shared by all five expressions.
theorem residualCheck : lin3 0 (d2LitsConstantsGate.q2 (-1) 1 (1)) (d2LitsConstantsGate.q2 (0) 1 (0)) 0 iv3 iv3 iv3 (d2LitsConstantsGate.q2 (374182068496652483) 1 (-55)) = true := by decide +kernel
theorem residualUpper : residualK secondPData ≤ (((d2LitsConstantsGate.q2 (374182068496652483) 1 (-55)):ℚ):ℝ) := by
  have h := lin3_sound enclosed3 enclosed3 enclosed3 residualCheck
  norm_num [d2LitsConstantsGate.q2, rowK, columnK, residualK] at h ⊢
  linarith
#print axioms basic0
#print axioms enclosed0
#print axioms basic1
#print axioms enclosed1
#print axioms basic2
#print axioms enclosed2
#print axioms basic3
#print axioms enclosed3
#print axioms basic4
#print axioms enclosed4
#print axioms basic5
#print axioms enclosed5
#print axioms firstRowCheck
#print axioms firstRowUpper
#print axioms firstColCheck
#print axioms firstColUpper
#print axioms refRowCheck
#print axioms refRowUpper
#print axioms refColCheck
#print axioms refColUpper
#print axioms residualCheck
#print axioms residualUpper
end D72.StandaloneConstantsGate
end CatalanMeasure.GenD.Signed.Data.Cells

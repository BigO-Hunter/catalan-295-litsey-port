module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers053
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover003
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-1652047289650462095660639 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P0Lo : ℝ) (d2NearProduction020P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P0Lo, d2NearProduction020P0Hi, d2NearProduction020P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P0Literal.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-826023662533127717731261 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P1Lo : ℝ) (d2NearProduction020P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P1Lo, d2NearProduction020P1Hi, d2NearProduction020P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P1Literal.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-7528663614085909507115363 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P2Lo : ℝ) (d2NearProduction020P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P2Lo, d2NearProduction020P2Hi, d2NearProduction020P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P2Literal.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-15057330549193853703019759 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P3Lo : ℝ) (d2NearProduction020P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P3Lo, d2NearProduction020P3Hi, d2NearProduction020P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P3Literal.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-7528666104776415628404497 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P4Lo : ℝ) (d2NearProduction020P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P4Lo, d2NearProduction020P4Hi, d2NearProduction020P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P4Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-7528666519847157749784749 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P5Lo : ℝ) (d2NearProduction020P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P5Lo, d2NearProduction020P5Hi, d2NearProduction020P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P5Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-15057333454755557163989713 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P6Lo : ℝ) (d2NearProduction020P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P6Lo, d2NearProduction020P6Hi, d2NearProduction020P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P6Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-1882166707785475370815529 : ℚ) / 1360041547066457821544448) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction020P7Lo : ℝ) (d2NearProduction020P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction020P7Lo, d2NearProduction020P7Hi, d2NearProduction020P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction020P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction020P7Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-15057333766047332120942695 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction021P0Lo : ℝ) (d2NearProduction021P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction021P0Lo, d2NearProduction021P0Hi, d2NearProduction021P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction021P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction021P0Literal.q2])
theorem envelope9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((262143 : ℚ) / 262144) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-29408855113142477075705 : ℚ) / 21250649172913403461632) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction021P1Lo : ℝ) (d2NearProduction021P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction021P1Lo, d2NearProduction021P1Hi, d2NearProduction021P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction021P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction021P1Literal.q2])
theorem envelope10 (x : ℝ) (hx : x ∈ Icc ((((262143 : ℚ) / 262144) : ℚ) : ℝ) ((((524287 : ℚ) / 524288) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-7528666921934859612493751 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction021P2Lo : ℝ) (d2NearProduction021P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction021P2Lo, d2NearProduction021P2Hi, d2NearProduction021P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction021P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction021P2Literal.q2])
theorem envelope11 (x : ℝ) (hx : x ∈ Icc ((((524287 : ℚ) / 524288) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) ≤ ((((-3764333467452616362038809 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction021P3Lo : ℝ) (d2NearProduction021P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction021P3Lo, d2NearProduction021P3Hi, d2NearProduction021P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction021P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction021P3Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners003.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners003.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners003.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + ((0 : ℝ)) := by
  have hf : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x = fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta0 x := by
    convert D72.NearCorners003.corner0Value x using 1 <;> norm_num [d2LitsNearCorners003.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = lfieldTower D72.NearBinding003.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) D72.NearCorners003.corner0Terms x).trans (D72.NearBinding003.termsValue x).symm
  calc
    _ = (fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta0 x) + lfieldTower D72.NearBinding003.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + ((0 : ℝ)) := by rw [delta0Value]; ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-751264128269 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-751264128269 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner0Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-751264128269 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-751264128269 : ℚ) / 549755813888) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
  intro p hp
  simp only [corner0Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner0Piece0
  · exact corner0Piece1
#print axioms corner0Domain0Cover
#print axioms corner0Domain0
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((262143 : ℚ) / 262144) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope9 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece10 (x : ℝ) (hx : x ∈ Icc ((((262143 : ℚ) / 262144) : ℚ) : ℝ) ((((524287 : ℚ) / 524288) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope10 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece11 (x : ℝ) (hx : x ∈ Icc ((((524287 : ℚ) / 524288) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope11 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((262143 : ℚ) / 262144)), (((262143 : ℚ) / 262144), ((524287 : ℚ) / 524288)), (((524287 : ℚ) / 524288), ((1 : ℚ) / 1))]
theorem corner0Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner0Domain1Pieces = true := by decide +kernel
theorem corner0Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-6847276500341 : ℚ) / 4947802324992) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner0Domain1Pieces (by decide +kernel) corner0Domain1Cover
  intro p hp
  simp only [corner0Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner0Piece2
  · exact corner0Piece3
  · exact corner0Piece4
  · exact corner0Piece5
  · exact corner0Piece6
  · exact corner0Piece7
  · exact corner0Piece8
  · exact corner0Piece9
  · exact corner0Piece10
  · exact corner0Piece11
#print axioms corner0Domain1Cover
#print axioms corner0Domain1
theorem delta1Check : fieldNFCheck D72.NearCorners003.delta1 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners003.delta1 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners003.delta1 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x = fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta1 x := by
    convert D72.NearCorners003.corner1Value x using 1 <;> norm_num [d2LitsNearCorners003.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = lfieldTower D72.NearBinding003.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) D72.NearCorners003.corner1Terms x).trans (D72.NearBinding003.termsValue x).symm
  calc
    _ = (fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta1 x) + lfieldTower D72.NearBinding003.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta1Value]; ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer403Lo : ℝ) (d2WiderTransfer403Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer403Lo, d2WiderTransfer403Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer403Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2093397711619402323551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer403Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer403C0, d2WiderTransfer403S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1652047289650462095660639 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2093397711619402323551 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer405Lo : ℝ) (d2WiderTransfer405Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer405Lo, d2WiderTransfer405Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer405Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046716563706371062717 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer405Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer405C0, d2WiderTransfer405S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-826023662533127717731261 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046716563706371062717 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner1Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-187578040361 : ℚ) / 137438953472) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
  intro p hp
  simp only [corner1Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner1Piece0
  · exact corner1Piece1
#print axioms corner1Domain0Cover
#print axioms corner1Domain0
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer407Lo : ℝ) (d2WiderTransfer407Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer407Lo, d2WiderTransfer407Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer407Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047085633747164758283 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer407Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer407C0, d2WiderTransfer407S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528663614085909507115363 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047085633747164758283 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer409Lo : ℝ) (d2WiderTransfer409Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer409Lo, d2WiderTransfer409Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer409Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094540269942628270903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer409Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer409C0, d2WiderTransfer409S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057330549193853703019759 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094540269942628270903 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer411Lo : ℝ) (d2WiderTransfer411Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer411Lo, d2WiderTransfer411Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer411Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047362377136733790409 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer411Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer411C0, d2WiderTransfer411S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666104776415628404497 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047362377136733790409 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer413Lo : ℝ) (d2WiderTransfer413Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer413Lo, d2WiderTransfer413Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer413Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047408496108080610437 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer413Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer413C0, d2WiderTransfer413S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666519847157749784749 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047408496108080610437 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer415Lo : ℝ) (d2WiderTransfer415Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer415Lo, d2WiderTransfer415Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer415Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094863110131901712009 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer415Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer415C0, d2WiderTransfer415S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057333454755557163989713 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094863110131901712009 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer417Lo : ℝ) (d2WiderTransfer417Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer417Lo, d2WiderTransfer417Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer417Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((261860771103234971425 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer417Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer417C0, d2WiderTransfer417S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1882166707785475370815529 : ℚ) / 1360041547066457821544448) : ℚ) : ℝ) + ((((261860771103234971425 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer419Lo : ℝ) (d2WiderTransfer419Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer419Lo, d2WiderTransfer419Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer419Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094897698106896929007 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer419Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer419C0, d2WiderTransfer419S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057333766047332120942695 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094897698106896929007 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((262143 : ℚ) / 262144) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer421Lo : ℝ) (d2WiderTransfer421Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer421Lo, d2WiderTransfer421Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer421Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4091608325646313841 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer421Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer421C0, d2WiderTransfer421S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-29408855113142477075705 : ℚ) / 21250649172913403461632) : ℚ) : ℝ) + ((((4091608325646313841 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece10 (x : ℝ) (hx : x ∈ Icc ((((262143 : ℚ) / 262144) : ℚ) : ℝ) ((((524287 : ℚ) / 524288) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer423Lo : ℝ) (d2WiderTransfer423Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer423Lo, d2WiderTransfer423Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer423Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047453172519398689215 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer423Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer423C0, d2WiderTransfer423S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666921934859612493751 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047453172519398689215 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece11 (x : ℝ) (hx : x ∈ Icc ((((524287 : ℚ) / 524288) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer425Lo : ℝ) (d2WiderTransfer425Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer425Lo, d2WiderTransfer425Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer425Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((523727306835983321489 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer425Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer425C0, d2WiderTransfer425S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-3764333467452616362038809 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) + ((((523727306835983321489 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((262143 : ℚ) / 262144)), (((262143 : ℚ) / 262144), ((524287 : ℚ) / 524288)), (((524287 : ℚ) / 524288), ((1 : ℚ) / 1))]
theorem corner1Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner1Domain1Pieces = true := by decide +kernel
theorem corner1Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-1709677199729 : ℚ) / 1236950581248) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner1Domain1Pieces (by decide +kernel) corner1Domain1Cover
  intro p hp
  simp only [corner1Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner1Piece2
  · exact corner1Piece3
  · exact corner1Piece4
  · exact corner1Piece5
  · exact corner1Piece6
  · exact corner1Piece7
  · exact corner1Piece8
  · exact corner1Piece9
  · exact corner1Piece10
  · exact corner1Piece11
#print axioms corner1Domain1Cover
#print axioms corner1Domain1
theorem delta2Check : fieldNFCheck D72.NearCorners003.delta2 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners003.delta2 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners003.delta2 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  have hf : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x = fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta2 x := by
    convert D72.NearCorners003.corner2Value x using 1 <;> norm_num [d2LitsNearCorners003.q2]
  have ht : lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x = lfieldTower D72.NearBinding003.literalTerms 0 x :=
    (laurent_eq_of_nf (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) D72.NearCorners003.corner2Terms x).trans (D72.NearBinding003.termsValue x).symm
  calc
    _ = (fval D72.NearBinding003.literalField x + fval D72.NearCorners003.delta2 x) + lfieldTower D72.NearBinding003.literalTerms 0 x :=
      congrArg₂ (fun u v : ℝ => u + v) hf ht
    _ = (fval D72.NearBinding003.literalField x + lfieldTower D72.NearBinding003.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by rw [delta2Value]; ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer404Lo : ℝ) (d2WiderTransfer404Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer404Lo, d2WiderTransfer404Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer404Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2093397292705472140895 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer404Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer404C0, d2WiderTransfer404S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1652047289650462095660639 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) + ((((2093397292705472140895 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer406Lo : ℝ) (d2WiderTransfer406Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer406Lo, d2WiderTransfer406Hi, d2LitsNearWiderTransfers050.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer406Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046716354249405971389 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer406Cap, d2LitsNearWiderTransfers050.q2, d2WiderTransfer406C0, d2WiderTransfer406S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-826023662533127717731261 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046716354249405971389 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner2Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-1500624323269 : ℚ) / 1099511627776) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
  intro p hp
  simp only [corner2Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner2Piece0
  · exact corner2Piece1
#print axioms corner2Domain0Cover
#print axioms corner2Domain0
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer408Lo : ℝ) (d2WiderTransfer408Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer408Lo, d2WiderTransfer408Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer408Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047085424290199666955 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer408Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer408C0, d2WiderTransfer408S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528663614085909507115363 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047085424290199666955 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer410Lo : ℝ) (d2WiderTransfer410Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer410Lo, d2WiderTransfer410Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer410Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094539851028698088247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer410Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer410C0, d2WiderTransfer410S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057330549193853703019759 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094539851028698088247 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer412Lo : ℝ) (d2WiderTransfer412Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer412Lo, d2WiderTransfer412Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer412Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047362167679768699081 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer412Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer412C0, d2WiderTransfer412S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666104776415628404497 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047362167679768699081 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer414Lo : ℝ) (d2WiderTransfer414Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer414Lo, d2WiderTransfer414Hi, d2LitsNearWiderTransfers051.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer414Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047408286651115519109 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer414Cap, d2LitsNearWiderTransfers051.q2, d2WiderTransfer414C0, d2WiderTransfer414S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666519847157749784749 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047408286651115519109 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer416Lo : ℝ) (d2WiderTransfer416Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer416Lo, d2WiderTransfer416Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer416Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094862691217971529353 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer416Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer416C0, d2WiderTransfer416S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057333454755557163989713 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094862691217971529353 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer418Lo : ℝ) (d2WiderTransfer418Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer418Lo, d2WiderTransfer418Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer418Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((261860718738993698593 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer418Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer418C0, d2WiderTransfer418S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-1882166707785475370815529 : ℚ) / 1360041547066457821544448) : ℚ) : ℝ) + ((((261860718738993698593 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer420Lo : ℝ) (d2WiderTransfer420Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer420Lo, d2WiderTransfer420Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer420Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2094897279192966746351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer420Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer420C0, d2WiderTransfer420S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-15057333766047332120942695 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2094897279192966746351 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((262143 : ℚ) / 262144) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer422Lo : ℝ) (d2WiderTransfer422Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer422Lo, d2WiderTransfer422Hi, d2LitsNearWiderTransfers052.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer422Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((4091607507455043953 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer422Cap, d2LitsNearWiderTransfers052.q2, d2WiderTransfer422C0, d2WiderTransfer422S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-29408855113142477075705 : ℚ) / 21250649172913403461632) : ℚ) : ℝ) + ((((4091607507455043953 : ℚ) / 2361183241434822606848) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece10 (x : ℝ) (hx : x ∈ Icc ((((262143 : ℚ) / 262144) : ℚ) : ℝ) ((((524287 : ℚ) / 524288) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope10 x hx
  have hxT : x ∈ Icc (d2WiderTransfer424Lo : ℝ) (d2WiderTransfer424Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer424Lo, d2WiderTransfer424Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer424Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1047452963062433597887 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer424Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer424C0, d2WiderTransfer424S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-7528666921934859612493751 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1047452963062433597887 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece11 (x : ℝ) (hx : x ∈ Icc ((((524287 : ℚ) / 524288) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope11 x hx
  have hxT : x ∈ Icc (d2WiderTransfer426Lo : ℝ) (d2WiderTransfer426Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer426Lo, d2WiderTransfer426Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢ <;> exact hx
  have hD := d2WiderTransfer426Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((523727202107500775825 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    norm_num [d2WiderTransfer426Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer426C0, d2WiderTransfer426S0, add_comm] at hD ⊢ <;> exact hD
  have hcap : ((((-3764333467452616362038809 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) + ((((523727202107500775825 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((262143 : ℚ) / 262144)), (((262143 : ℚ) / 262144), ((524287 : ℚ) / 524288)), (((524287 : ℚ) / 524288), ((1 : ℚ) / 1))]
theorem corner2Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner2Domain1Pieces = true := by decide +kernel
theorem corner2Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x ≤ ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T0.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qFn))) 0 x) ((((-13677417601261 : ℚ) / 9895604649984) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner2Domain1Pieces (by decide +kernel) corner2Domain1Cover
  intro p hp
  simp only [corner2Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner2Piece2
  · exact corner2Piece3
  · exact corner2Piece4
  · exact corner2Piece5
  · exact corner2Piece6
  · exact corner2Piece7
  · exact corner2Piece8
  · exact corner2Piece9
  · exact corner2Piece10
  · exact corner2Piece11
#print axioms corner2Domain1Cover
#print axioms corner2Domain1
end D72.NearCornerCover003
end CatalanMeasure.GenD.Signed.Data.Cells

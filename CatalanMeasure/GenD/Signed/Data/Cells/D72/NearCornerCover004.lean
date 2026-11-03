module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers055
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers057
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover004
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-833273084816547567786957 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P0Lo : ℝ) (d2NearProduction022P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P0Lo, d2NearProduction022P0Hi, d2NearProduction022P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P0Literal.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-833273306165255941548729 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P1Lo : ℝ) (d2NearProduction022P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P1Lo, d2NearProduction022P1Hi, d2NearProduction022P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P1Literal.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-7593948605524285668963629 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P2Lo : ℝ) (d2NearProduction022P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P2Lo, d2NearProduction022P2Hi, d2NearProduction022P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P2Literal.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-15187938723824004947790229 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P3Lo : ℝ) (d2NearProduction022P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P3Lo, d2NearProduction022P3Hi, d2NearProduction022P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P3Literal.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-15187959478311224370155671 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P4Lo : ℝ) (d2NearProduction022P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P4Lo, d2NearProduction022P4Hi, d2NearProduction022P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P4Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-7593984927539888702330981 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P5Lo : ℝ) (d2NearProduction022P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P5Lo, d2NearProduction022P5Hi, d2NearProduction022P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P5Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-15187975043345298209914573 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P6Lo : ℝ) (d2NearProduction022P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P6Lo, d2NearProduction022P6Hi, d2NearProduction022P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P6Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-7593988818724185370798037 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction022P7Lo : ℝ) (d2NearProduction022P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction022P7Lo, d2NearProduction022P7Hi, d2NearProduction022P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction022P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction022P7Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) ≤ ((((-949248764470728235123981 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction023P0Lo : ℝ) (d2NearProduction023P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction023P0Lo, d2NearProduction023P0Hi, d2NearProduction023P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction023P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction023P0Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners004.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners004.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners004.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) + ((0 : ℝ)) := by
  rw [D72.NearCorners004.corner0Value, delta0Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) x, D72.NearCorners004.corner0Terms, laurentNF_sound, ← D72.NearBinding004.termsValue x]
  ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-11841522741 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-11841522741 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner0Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-11841522741 : ℚ) / 8589934592) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-11841522741 : ℚ) / 8589934592) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
  intro p hp
  simp only [corner0Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner0Piece0
  · exact corner0Piece1
#print axioms corner0Domain0Cover
#print axioms corner0Domain0
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((1 : ℚ) / 1))]
theorem corner0Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner0Domain1Pieces = true := by decide +kernel
theorem corner0Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((0 : ℚ) / 1) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-107915881949 : ℚ) / 77309411328) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner0Domain1Pieces (by decide +kernel) corner0Domain1Cover
  intro p hp
  simp only [corner0Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner0Piece2
  · exact corner0Piece3
  · exact corner0Piece4
  · exact corner0Piece5
  · exact corner0Piece6
  · exact corner0Piece7
  · exact corner0Piece8
#print axioms corner0Domain1Cover
#print axioms corner0Domain1
theorem delta1Check : fieldNFCheck D72.NearCorners004.delta1 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners004.delta1 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners004.delta1 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners004.corner1Value, delta1Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) x, D72.NearCorners004.corner1Terms, laurentNF_sound, ← D72.NearBinding004.termsValue x]
  ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer427Lo : ℝ) (d2WiderTransfer427Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer427Lo, d2WiderTransfer427Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer427Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046698974472468061133 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer427Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer427C0, d2WiderTransfer427S0] using hD
  have hcap : ((((-833273084816547567786957 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046698974472468061133 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer431Lo : ℝ) (d2WiderTransfer431Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer431Lo, d2WiderTransfer431Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer431Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046920323180841822905 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer431Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer431C0, d2WiderTransfer431S0] using hD
  have hcap : ((((-833273306165255941548729 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046920323180841822905 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner1Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-756905488599 : ℚ) / 549755813888) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
  intro p hp
  simp only [corner1Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner1Piece0
  · exact corner1Piece1
#print axioms corner1Domain0Cover
#print axioms corner1Domain0
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer435Lo : ℝ) (d2WiderTransfer435Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer435Lo, d2WiderTransfer435Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer435Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1051533698690763017477 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer435Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer435C0, d2WiderTransfer435S0] using hD
  have hcap : ((((-7593948605524285668963629 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1051533698690763017477 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer439Lo : ℝ) (d2WiderTransfer439Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer439Lo, d2WiderTransfer439Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer439Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2107679927985260464173 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer439Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer439C0, d2WiderTransfer439S0] using hD
  have hcap : ((((-15187938723824004947790229 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2107679927985260464173 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer443Lo : ℝ) (d2WiderTransfer443Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer443Lo, d2WiderTransfer443Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer443Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2109985982120751838111 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer443Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer443C0, d2WiderTransfer443S0] using hD
  have hcap : ((((-15187959478311224370155671 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2109985982120751838111 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer447Lo : ℝ) (d2WiderTransfer447Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer447Lo, d2WiderTransfer447Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer447Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1055569478202211169405 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer447Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer447C0, d2WiderTransfer447S0] using hD
  have hcap : ((((-7593984927539888702330981 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1055569478202211169405 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer451Lo : ℝ) (d2WiderTransfer451Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer451Lo, d2WiderTransfer451Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer451Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2111715430351178477989 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer451Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer451C0, d2WiderTransfer451S0] using hD
  have hcap : ((((-15187975043345298209914573 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2111715430351178477989 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer455Lo : ℝ) (d2WiderTransfer455Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer455Lo, d2WiderTransfer455Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer455Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1056001832012952110189 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer455Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer455C0, d2WiderTransfer455S0] using hD
  have hcap : ((((-7593988818724185370798037 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1056001832012952110189 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer459Lo : ℝ) (d2WiderTransfer459Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer459Lo, d2WiderTransfer459Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer459Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((132018243468848322021 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer459Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer459C0, d2WiderTransfer459S0] using hD
  have hcap : ((((-949248764470728235123981 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((132018243468848322021 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((1 : ℚ) / 1))]
theorem corner1Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner1Domain1Pieces = true := by decide +kernel
theorem corner1Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-6898048743311 : ℚ) / 4947802324992) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner1Domain1Pieces (by decide +kernel) corner1Domain1Cover
  intro p hp
  simp only [corner1Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner1Piece2
  · exact corner1Piece3
  · exact corner1Piece4
  · exact corner1Piece5
  · exact corner1Piece6
  · exact corner1Piece7
  · exact corner1Piece8
#print axioms corner1Domain1Cover
#print axioms corner1Domain1
theorem delta2Check : fieldNFCheck D72.NearCorners004.delta2 (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners004.delta2 x = ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners004.delta2 x = fval (fqSum [logFQ ((1 : ℚ) / 400) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) + (((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners004.corner2Value, delta2Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) x, D72.NearCorners004.corner2Terms, laurentNF_sound, ← D72.NearBinding004.termsValue x]
  ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer428Lo : ℝ) (d2WiderTransfer428Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer428Lo, d2WiderTransfer428Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer428Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046698765015502969805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer428Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer428C0, d2WiderTransfer428S0] using hD
  have hcap : ((((-833273084816547567786957 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046698765015502969805 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer432Lo : ℝ) (d2WiderTransfer432Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer432Lo, d2WiderTransfer432Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer432Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1046920113723876731577 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer432Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer432C0, d2WiderTransfer432S0] using hD
  have hcap : ((((-833273306165255941548729 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((1046920113723876731577 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner2Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1513810977579 : ℚ) / 1099511627776) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
  intro p hp
  simp only [corner2Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner2Piece0
  · exact corner2Piece1
#print axioms corner2Domain0Cover
#print axioms corner2Domain0
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer436Lo : ℝ) (d2WiderTransfer436Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer436Lo, d2WiderTransfer436Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer436Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1051533489233797926149 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer436Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer436C0, d2WiderTransfer436S0] using hD
  have hcap : ((((-7593948605524285668963629 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1051533489233797926149 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer440Lo : ℝ) (d2WiderTransfer440Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer440Lo, d2WiderTransfer440Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer440Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2107679509071330281517 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer440Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer440C0, d2WiderTransfer440S0] using hD
  have hcap : ((((-15187938723824004947790229 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2107679509071330281517 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer444Lo : ℝ) (d2WiderTransfer444Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer444Lo, d2WiderTransfer444Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer444Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2109985563206821655455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer444Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer444C0, d2WiderTransfer444S0] using hD
  have hcap : ((((-15187959478311224370155671 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2109985563206821655455 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer448Lo : ℝ) (d2WiderTransfer448Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer448Lo, d2WiderTransfer448Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer448Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1055569268745246078077 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer448Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer448C0, d2WiderTransfer448S0] using hD
  have hcap : ((((-7593984927539888702330981 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1055569268745246078077 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer452Lo : ℝ) (d2WiderTransfer452Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer452Lo, d2WiderTransfer452Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer452Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((2111715011437248295333 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer452Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer452C0, d2WiderTransfer452S0] using hD
  have hcap : ((((-15187975043345298209914573 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((2111715011437248295333 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer456Lo : ℝ) (d2WiderTransfer456Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer456Lo, d2WiderTransfer456Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer456Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1056001622555987018861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer456Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer456C0, d2WiderTransfer456S0] using hD
  have hcap : ((((-7593988818724185370798037 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((1056001622555987018861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer460Lo : ℝ) (d2WiderTransfer460Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer460Lo, d2WiderTransfer460Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer460Bound x hxT
  have hd : ((((1 : ℚ) / 400) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((132018217286727685605 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer460Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer460C0, d2WiderTransfer460S0] using hD
  have hcap : ((((-949248764470728235123981 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((132018217286727685605 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((1 : ℚ) / 1))]
theorem corner2Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner2Domain1Pieces = true := by decide +kernel
theorem corner2Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-13796097490051 : ℚ) / 9895604649984) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner2Domain1Pieces (by decide +kernel) corner2Domain1Cover
  intro p hp
  simp only [corner2Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner2Piece2
  · exact corner2Piece3
  · exact corner2Piece4
  · exact corner2Piece5
  · exact corner2Piece6
  · exact corner2Piece7
  · exact corner2Piece8
#print axioms corner2Domain1Cover
#print axioms corner2Domain1
theorem delta3Check : fieldNFCheck D72.NearCorners004.delta3 (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta3Value (x : ℝ) : fval D72.NearCorners004.delta3 x = ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta3Check x
  change fval D72.NearCorners004.delta3 x = fval (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner3Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) + (((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners004.corner3Value, delta3Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) x, D72.NearCorners004.corner3Terms, laurentNF_sound, ← D72.NearBinding004.termsValue x]
  ring
theorem corner3Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer429Lo : ℝ) (d2WiderTransfer429Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer429Lo, d2WiderTransfer429Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer429Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13083733079409200880589 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer429Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer429C0, d2WiderTransfer429S0] using hD
  have hcap : ((((-833273084816547567786957 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((13083733079409200880589 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer433Lo : ℝ) (d2WiderTransfer433Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer433Lo, d2WiderTransfer433Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer433Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13083954428117574642361 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer433Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer433C0, d2WiderTransfer433S0] using hD
  have hcap : ((((-833273306165255941548729 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((13083954428117574642361 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner3Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner3Domain0Pieces = true := by decide +kernel
theorem corner3Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1491915739711 : ℚ) / 1099511627776) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner3Domain0Pieces (by decide +kernel) corner3Domain0Cover
  intro p hp
  simp only [corner3Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner3Piece0
  · exact corner3Piece1
#print axioms corner3Domain0Cover
#print axioms corner3Domain0
theorem corner3Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer437Lo : ℝ) (d2WiderTransfer437Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer437Lo, d2WiderTransfer437Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer437Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13088567803627495836933 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer437Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer437C0, d2WiderTransfer437S0] using hD
  have hcap : ((((-7593948605524285668963629 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13088567803627495836933 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer441Lo : ℝ) (d2WiderTransfer441Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer441Lo, d2WiderTransfer441Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer441Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26181748137858726103085 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer441Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer441C0, d2WiderTransfer441S0] using hD
  have hcap : ((((-15187938723824004947790229 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26181748137858726103085 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer445Lo : ℝ) (d2WiderTransfer445Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer445Lo, d2WiderTransfer445Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer445Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26184054191994217477023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer445Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer445C0, d2WiderTransfer445S0] using hD
  have hcap : ((((-15187959478311224370155671 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26184054191994217477023 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer449Lo : ℝ) (d2WiderTransfer449Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer449Lo, d2WiderTransfer449Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer449Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13092603583138943988861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer449Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer449C0, d2WiderTransfer449S0] using hD
  have hcap : ((((-7593984927539888702330981 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13092603583138943988861 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer453Lo : ℝ) (d2WiderTransfer453Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer453Lo, d2WiderTransfer453Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer453Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26185783640224644116901 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer453Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer453C0, d2WiderTransfer453S0] using hD
  have hcap : ((((-15187975043345298209914573 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26185783640224644116901 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer457Lo : ℝ) (d2WiderTransfer457Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer457Lo, d2WiderTransfer457Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer457Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13093035936949684929645 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer457Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer457C0, d2WiderTransfer457S0] using hD
  have hcap : ((((-7593988818724185370798037 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13093035936949684929645 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer461Lo : ℝ) (d2WiderTransfer461Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer461Lo, d2WiderTransfer461Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer461Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1636647506585939924453 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer461Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer461C0, d2WiderTransfer461S0] using hD
  have hcap : ((((-949248764470728235123981 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((1636647506585939924453 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((1 : ℚ) / 1))]
theorem corner3Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner3Domain1Pieces = true := by decide +kernel
theorem corner3Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-13599040349239 : ℚ) / 9895604649984) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner3Domain1Pieces (by decide +kernel) corner3Domain1Cover
  intro p hp
  simp only [corner3Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner3Piece2
  · exact corner3Piece3
  · exact corner3Piece4
  · exact corner3Piece5
  · exact corner3Piece6
  · exact corner3Piece7
  · exact corner3Piece8
#print axioms corner3Domain1Cover
#print axioms corner3Domain1
theorem delta4Check : fieldNFCheck D72.NearCorners004.delta4 (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta4Value (x : ℝ) : fval D72.NearCorners004.delta4 x = ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta4Check x
  change fval D72.NearCorners004.delta4 x = fval (fqSum [logFQ ((1 : ℚ) / 32) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner4Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x = (fval D72.NearBinding004.literalField x + lfieldTower D72.NearBinding004.literalTerms 0 x) + (((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners004.corner4Value, delta4Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) x, D72.NearCorners004.corner4Terms, laurentNF_sound, ← D72.NearBinding004.termsValue x]
  ring
theorem corner4Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer430Lo : ℝ) (d2WiderTransfer430Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer430Lo, d2WiderTransfer430Hi, d2LitsNearWiderTransfers053.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer430Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13083733277321293880269 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer430Cap, d2LitsNearWiderTransfers053.q2, d2WiderTransfer430C0, d2WiderTransfer430S0] using hD
  have hcap : ((((-833273084816547567786957 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((13083733277321293880269 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer434Lo : ℝ) (d2WiderTransfer434Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer434Lo, d2WiderTransfer434Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer434Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13083954626029667642041 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer434Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer434C0, d2WiderTransfer434S0] using hD
  have hcap : ((((-833273306165255941548729 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) + ((((13083954626029667642041 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner4Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner4Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner4Domain0Pieces = true := by decide +kernel
theorem corner4Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-1491915739351 : ℚ) / 1099511627776) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner4Domain0Pieces (by decide +kernel) corner4Domain0Cover
  intro p hp
  simp only [corner4Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner4Piece0
  · exact corner4Piece1
#print axioms corner4Domain0Cover
#print axioms corner4Domain0
theorem corner4Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer438Lo : ℝ) (d2WiderTransfer438Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer438Lo, d2WiderTransfer438Hi, d2LitsNearWiderTransfers054.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer438Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13088568001539588836613 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer438Cap, d2LitsNearWiderTransfers054.q2, d2WiderTransfer438C0, d2WiderTransfer438S0] using hD
  have hcap : ((((-7593948605524285668963629 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13088568001539588836613 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer442Lo : ℝ) (d2WiderTransfer442Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer442Lo, d2WiderTransfer442Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer442Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26181748533682912102445 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer442Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer442C0, d2WiderTransfer442S0] using hD
  have hcap : ((((-15187938723824004947790229 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26181748533682912102445 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer446Lo : ℝ) (d2WiderTransfer446Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer446Lo, d2WiderTransfer446Hi, d2LitsNearWiderTransfers055.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer446Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26184054587818403476383 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer446Cap, d2LitsNearWiderTransfers055.q2, d2WiderTransfer446C0, d2WiderTransfer446S0] using hD
  have hcap : ((((-15187959478311224370155671 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26184054587818403476383 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer450Lo : ℝ) (d2WiderTransfer450Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer450Lo, d2WiderTransfer450Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer450Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13092603781051036988541 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer450Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer450C0, d2WiderTransfer450S0] using hD
  have hcap : ((((-7593984927539888702330981 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13092603781051036988541 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer454Lo : ℝ) (d2WiderTransfer454Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer454Lo, d2WiderTransfer454Hi, d2LitsNearWiderTransfers056.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer454Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((26185784036048830116261 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer454Cap, d2LitsNearWiderTransfers056.q2, d2WiderTransfer454C0, d2WiderTransfer454S0] using hD
  have hcap : ((((-15187975043345298209914573 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((26185784036048830116261 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer458Lo : ℝ) (d2WiderTransfer458Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer458Lo, d2WiderTransfer458Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer458Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((13093036134861777929325 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer458Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer458C0, d2WiderTransfer458S0] using hD
  have hcap : ((((-7593988818724185370798037 : ℚ) / 5440166188265831286177792) : ℚ) : ℝ) + ((((13093036134861777929325 : ℚ) / 604462909807314587353088) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner4Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner4Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer462Lo : ℝ) (d2WiderTransfer462Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer462Lo, d2WiderTransfer462Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer462Bound x hxT
  have hd : ((((1 : ℚ) / 32) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1636647531324951549413 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer462Cap, d2LitsNearWiderTransfers057.q2, d2WiderTransfer462C0, d2WiderTransfer462S0] using hD
  have hcap : ((((-949248764470728235123981 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((1636647531324951549413 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner4Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((1 : ℚ) / 1))]
theorem corner4Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner4Domain1Pieces = true := by decide +kernel
theorem corner4Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x ≤ ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T1.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qFn))) 0 x) ((((-13599040345999 : ℚ) / 9895604649984) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner4Domain1Pieces (by decide +kernel) corner4Domain1Cover
  intro p hp
  simp only [corner4Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner4Piece2
  · exact corner4Piece3
  · exact corner4Piece4
  · exact corner4Piece5
  · exact corner4Piece6
  · exact corner4Piece7
  · exact corner4Piece8
#print axioms corner4Domain1Cover
#print axioms corner4Domain1
end D72.NearCornerCover004
end CatalanMeasure.GenD.Signed.Data.Cells

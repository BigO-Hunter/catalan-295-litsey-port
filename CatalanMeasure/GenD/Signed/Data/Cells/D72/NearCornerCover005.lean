module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearCorners005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearProduction025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearWiderTransfers061
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.NearCornerCover005
theorem envelope0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-405327941281399689500751 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P0Lo : ℝ) (d2NearProduction024P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P0Lo, d2NearProduction024P0Hi, d2NearProduction024P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P0Literal.q2])
theorem envelope1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-202664021550902770715583 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P1Lo : ℝ) (d2NearProduction024P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P1Lo, d2NearProduction024P1Hi, d2NearProduction024P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P1Literal.q2])
theorem envelope2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780780608478229595051933 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P2Lo : ℝ) (d2NearProduction024P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P2Lo, d2NearProduction024P2Hi, d2NearProduction024P2Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P2Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P2Literal.q2])
theorem envelope3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780818800231628516125871 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P3Lo : ℝ) (d2NearProduction024P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P3Lo, d2NearProduction024P3Hi, d2NearProduction024P3Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P3Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P3Literal.q2])
theorem envelope4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780837894359870384702069 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P4Lo : ℝ) (d2NearProduction024P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P4Lo, d2NearProduction024P4Hi, d2NearProduction024P4Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P4Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P4Literal.q2])
theorem envelope5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-923802965061683698527991 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P5Lo : ℝ) (d2NearProduction024P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P5Lo, d2NearProduction024P5Hi, d2NearProduction024P5Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P5Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P5Literal.q2])
theorem envelope6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780852214191218317280261 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P6Lo : ℝ) (d2NearProduction024P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P6Lo, d2NearProduction024P6Hi, d2NearProduction024P6Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P6Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P6Literal.q2])
theorem envelope7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780854600766045046427243 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction024P7Lo : ℝ) (d2NearProduction024P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction024P7Lo, d2NearProduction024P7Hi, d2NearProduction024P7Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction024P7Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction024P7Literal.q2])
theorem envelope8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-14780855794046630322239581 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction025P0Lo : ℝ) (d2NearProduction025P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction025P0Lo, d2NearProduction025P0Hi, d2NearProduction025P0Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction025P0Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction025P0Literal.q2])
theorem envelope9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) ≤ ((((-3695214246830665896295963 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2NearProduction025P1Lo : ℝ) (d2NearProduction025P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2NearProduction025P1Lo, d2NearProduction025P1Hi, d2NearProduction025P1Literal.q2] at hx ⊢
    exact hx
  have hb := d2NearProduction025P1Bound x hxC
  exact hb.trans (by norm_num [d2NearProduction025P1Literal.q2])
theorem delta0Check : fieldNFCheck D72.NearCorners005.delta0 (fqSum []) = true := by decide +kernel
theorem delta0Value (x : ℝ) : fval D72.NearCorners005.delta0 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta0Check x
  change fval D72.NearCorners005.delta0 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner0Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) + ((0 : ℝ)) := by
  rw [D72.NearCorners005.corner0Value, delta0Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners005.corner0Terms, laurentNF_sound, ← D72.NearBinding005.termsValue x]
  ring
theorem corner0Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1474574460067 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope0 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1474574460067 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope1 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner0Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner0Domain0Pieces = true := by decide +kernel
theorem corner0Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-1474574460067 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-1474574460067 : ℚ) / 1099511627776) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner0Domain0Pieces (by decide +kernel) corner0Domain0Cover
  intro p hp
  simp only [corner0Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner0Piece0
  · exact corner0Piece1
#print axioms corner0Domain0Cover
#print axioms corner0Domain0
theorem corner0Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope2 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope3 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope4 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope5 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope6 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope7 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope8 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
theorem corner0Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  rw [corner0Identity]
  have h := envelope9 x hx
  rw [add_zero]
  exact h.trans (by norm_num)
def corner0Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((1 : ℚ) / 1))]
theorem corner0Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner0Domain1Pieces = true := by decide +kernel
theorem corner0Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-13442968832443 : ℚ) / 9895604649984) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner0Domain1Pieces (by decide +kernel) corner0Domain1Cover
  intro p hp
  simp only [corner0Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner0Piece2
  · exact corner0Piece3
  · exact corner0Piece4
  · exact corner0Piece5
  · exact corner0Piece6
  · exact corner0Piece7
  · exact corner0Piece8
  · exact corner0Piece9
#print axioms corner0Domain1Cover
#print axioms corner0Domain1
theorem delta1Check : fieldNFCheck D72.NearCorners005.delta1 (fqSum []) = true := by decide +kernel
theorem delta1Value (x : ℝ) : fval D72.NearCorners005.delta1 x = (0 : ℝ) := by
  have h := fieldNFCheck_sound delta1Check x
  change fval D72.NearCorners005.delta1 x = fval (fqSum []) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner1Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) + ((0 : ℝ)) := by
  rw [D72.NearCorners005.corner1Value, delta1Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners005.corner1Terms, laurentNF_sound, ← D72.NearBinding005.termsValue x]
  ring
theorem corner1Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer463Lo : ℝ) (d2WiderTransfer463Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer463Lo, d2WiderTransfer463Hi, d2LitsNearWiderTransfers057.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer463Bound x hxT
  have hd : (0 : ℝ) ≤ ((((241850313660495 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer463Cap, d2LitsNearWiderTransfers057.q2] using hD
  have hcap : ((((-405327941281399689500751 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((241850313660495 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer466Lo : ℝ) (d2WiderTransfer466Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer466Lo, d2WiderTransfer466Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer466Bound x hxT
  have hd : (0 : ℝ) ≤ ((((51031128082795455 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer466Cap, d2LitsNearWiderTransfers058.q2] using hD
  have hcap : ((((-202664021550902770715583 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((51031128082795455 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner1Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner1Domain0Pieces = true := by decide +kernel
theorem corner1Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-46080451857 : ℚ) / 34359738368) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner1Domain0Pieces (by decide +kernel) corner1Domain0Cover
  intro p hp
  simp only [corner1Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner1Piece0
  · exact corner1Piece1
#print axioms corner1Domain0Cover
#print axioms corner1Domain0
theorem corner1Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer469Lo : ℝ) (d2WiderTransfer469Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer469Lo, d2WiderTransfer469Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer469Bound x hxT
  have hd : (0 : ℝ) ≤ ((((8896859962917361653 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer469Cap, d2LitsNearWiderTransfers058.q2] using hD
  have hcap : ((((-14780780608478229595051933 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((8896859962917361653 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer472Lo : ℝ) (d2WiderTransfer472Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer472Lo, d2WiderTransfer472Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer472Bound x hxT
  have hd : (0 : ℝ) ≤ ((((13140388118353036535 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer472Cap, d2LitsNearWiderTransfers059.q2] using hD
  have hcap : ((((-14780818800231628516125871 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((13140388118353036535 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer475Lo : ℝ) (d2WiderTransfer475Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer475Lo, d2WiderTransfer475Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer475Bound x hxT
  have hd : (0 : ℝ) ≤ ((((15261957923005100557 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer475Cap, d2LitsNearWiderTransfers059.q2] using hD
  have hcap : ((((-14780837894359870384702069 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((15261957923005100557 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer478Lo : ℝ) (d2WiderTransfer478Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer478Lo, d2WiderTransfer478Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer478Bound x hxT
  have hd : (0 : ℝ) ≤ ((((1020168391498872575 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer478Cap, d2LitsNearWiderTransfers059.q2] using hD
  have hcap : ((((-923802965061683698527991 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((1020168391498872575 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer481Lo : ℝ) (d2WiderTransfer481Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer481Lo, d2WiderTransfer481Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer481Bound x hxT
  have hd : (0 : ℝ) ≤ ((((16853050294997609245 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer481Cap, d2LitsNearWiderTransfers060.q2] using hD
  have hcap : ((((-14780852214191218317280261 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((16853050294997609245 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer484Lo : ℝ) (d2WiderTransfer484Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer484Lo, d2WiderTransfer484Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer484Bound x hxT
  have hd : (0 : ℝ) ≤ ((((17118225275745292243 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer484Cap, d2LitsNearWiderTransfers060.q2] using hD
  have hcap : ((((-14780854600766045046427243 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((17118225275745292243 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer487Lo : ℝ) (d2WiderTransfer487Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer487Lo, d2WiderTransfer487Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer487Bound x hxT
  have hd : (0 : ℝ) ≤ ((((17250812007442604725 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer487Cap, d2LitsNearWiderTransfers060.q2] using hD
  have hcap : ((((-14780855794046630322239581 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((17250812007442604725 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner1Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  rw [corner1Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer490Lo : ℝ) (d2WiderTransfer490Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer490Lo, d2WiderTransfer490Hi, d2LitsNearWiderTransfers061.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer490Bound x hxT
  have hd : (0 : ℝ) ≤ ((((4345849558340177411 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer490Cap, d2LitsNearWiderTransfers061.q2] using hD
  have hcap : ((((-3695214246830665896295963 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) + ((((4345849558340177411 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner1Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((1 : ℚ) / 1))]
theorem corner1Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner1Domain1Pieces = true := by decide +kernel
theorem corner1Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 200) ((1 : ℚ) / 200)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-420092775833 : ℚ) / 309237645312) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner1Domain1Pieces (by decide +kernel) corner1Domain1Cover
  intro p hp
  simp only [corner1Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner1Piece2
  · exact corner1Piece3
  · exact corner1Piece4
  · exact corner1Piece5
  · exact corner1Piece6
  · exact corner1Piece7
  · exact corner1Piece8
  · exact corner1Piece9
#print axioms corner1Domain1Cover
#print axioms corner1Domain1
theorem delta2Check : fieldNFCheck D72.NearCorners005.delta2 (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta2Value (x : ℝ) : fval D72.NearCorners005.delta2 x = ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta2Check x
  change fval D72.NearCorners005.delta2 x = fval (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner2Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) + (((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners005.corner2Value, delta2Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners005.corner2Terms, laurentNF_sound, ← D72.NearBinding005.termsValue x]
  ring
theorem corner2Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer464Lo : ℝ) (d2WiderTransfer464Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer464Lo, d2WiderTransfer464Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer464Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((6018517399047162615887 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer464Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer464C0, d2WiderTransfer464S0] using hD
  have hcap : ((((-405327941281399689500751 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((6018517399047162615887 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer467Lo : ℝ) (d2WiderTransfer467Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer467Lo, d2WiderTransfer467Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer467Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3009309609726507273151 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer467Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer467C0, d2WiderTransfer467S0] using hD
  have hcap : ((((-202664021550902770715583 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((3009309609726507273151 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner2Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner2Domain0Pieces = true := by decide +kernel
theorem corner2Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-363169805389 : ℚ) / 274877906944) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner2Domain0Pieces (by decide +kernel) corner2Domain0Cover
  intro p hp
  simp only [corner2Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner2Piece0
  · exact corner2Piece1
#print axioms corner2Domain0Cover
#print axioms corner2Domain0
theorem corner2Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer470Lo : ℝ) (d2WiderTransfer470Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer470Lo, d2WiderTransfer470Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer470Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24082965488750313183221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer470Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer470C0, d2WiderTransfer470S0] using hD
  have hcap : ((((-14780780608478229595051933 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24082965488750313183221 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer473Lo : ℝ) (d2WiderTransfer473Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer473Lo, d2WiderTransfer473Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer473Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24087209016905748858103 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer473Cap, d2LitsNearWiderTransfers059.q2, d2WiderTransfer473C0, d2WiderTransfer473S0] using hD
  have hcap : ((((-14780818800231628516125871 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24087209016905748858103 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer476Lo : ℝ) (d2WiderTransfer476Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer476Lo, d2WiderTransfer476Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer476Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24089330586710400922125 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer476Cap, d2LitsNearWiderTransfers059.q2, d2WiderTransfer476C0, d2WiderTransfer476S0] using hD
  have hcap : ((((-14780837894359870384702069 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24089330586710400922125 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer479Lo : ℝ) (d2WiderTransfer479Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer479Lo, d2WiderTransfer479Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer479Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1505649457690711111423 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer479Cap, d2LitsNearWiderTransfers059.q2, d2WiderTransfer479C0, d2WiderTransfer479S0] using hD
  have hcap : ((((-923802965061683698527991 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((1505649457690711111423 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer482Lo : ℝ) (d2WiderTransfer482Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer482Lo, d2WiderTransfer482Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer482Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24090921679082393430813 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer482Cap, d2LitsNearWiderTransfers060.q2, d2WiderTransfer482C0, d2WiderTransfer482S0] using hD
  have hcap : ((((-14780852214191218317280261 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24090921679082393430813 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer485Lo : ℝ) (d2WiderTransfer485Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer485Lo, d2WiderTransfer485Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer485Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24091186854063141113811 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer485Cap, d2LitsNearWiderTransfers060.q2, d2WiderTransfer485C0, d2WiderTransfer485S0] using hD
  have hcap : ((((-14780854600766045046427243 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24091186854063141113811 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer488Lo : ℝ) (d2WiderTransfer488Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer488Lo, d2WiderTransfer488Hi, d2LitsNearWiderTransfers061.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer488Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24091319440794838426293 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer488Cap, d2LitsNearWiderTransfers061.q2, d2WiderTransfer488C0, d2WiderTransfer488S0] using hD
  have hcap : ((((-14780855794046630322239581 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24091319440794838426293 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner2Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner2Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer491Lo : ℝ) (d2WiderTransfer491Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer491Lo, d2WiderTransfer491Hi, d2LitsNearWiderTransfers061.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer491Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((6022863006755189132803 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer491Cap, d2LitsNearWiderTransfers061.q2, d2WiderTransfer491C0, d2WiderTransfer491S0] using hD
  have hcap : ((((-3695214246830665896295963 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) + ((((6022863006755189132803 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner2Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((1 : ℚ) / 1))]
theorem corner2Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner2Domain1Pieces = true := by decide +kernel
theorem corner2Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((0 : ℚ) / 1)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-3311477921461 : ℚ) / 2473901162496) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner2Domain1Pieces (by decide +kernel) corner2Domain1Cover
  intro p hp
  simp only [corner2Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner2Piece2
  · exact corner2Piece3
  · exact corner2Piece4
  · exact corner2Piece5
  · exact corner2Piece6
  · exact corner2Piece7
  · exact corner2Piece8
  · exact corner2Piece9
#print axioms corner2Domain1Cover
#print axioms corner2Domain1
theorem delta3Check : fieldNFCheck D72.NearCorners005.delta3 (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) = true := by decide +kernel
theorem delta3Value (x : ℝ) : fval D72.NearCorners005.delta3 x = ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| := by
  have h := fieldNFCheck_sound delta3Check x
  change fval D72.NearCorners005.delta3 x = fval (fqSum [logFQ ((23 : ℚ) / 800) ((-1 : ℚ) / 1)]) x at h
  rw [h]
  simp [fval_sum, fval_log]
theorem corner3Identity (x : ℝ) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x = (fval D72.NearBinding005.literalField x + lfieldTower D72.NearBinding005.literalTerms 0 x) + (((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)|) := by
  rw [D72.NearCorners005.corner3Value, delta3Value, ← laurentNF_sound (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) x, D72.NearCorners005.corner3Terms, laurentNF_sound, ← D72.NearBinding005.termsValue x]
  ring
theorem corner3Piece0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope0 x hx
  have hxT : x ∈ Icc (d2WiderTransfer465Lo : ℝ) (d2WiderTransfer465Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer465Lo, d2WiderTransfer465Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer465Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((6018517216528232405071 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer465Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer465C0, d2WiderTransfer465S0] using hD
  have hcap : ((((-405327941281399689500751 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) + ((((6018517216528232405071 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece1 (x : ℝ) (hx : x ∈ Icc ((((16760439 : ℚ) / 16777216) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope1 x hx
  have hxT : x ∈ Icc (d2WiderTransfer468Lo : ℝ) (d2WiderTransfer468Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer468Lo, d2WiderTransfer468Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer468Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((3009309518467042167743 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer468Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer468C0, d2WiderTransfer468S0] using hD
  have hcap : ((((-202664021550902770715583 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) + ((((3009309518467042167743 : ℚ) / 151115727451828646838272) : ℚ) : ℝ) = ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain0Pieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((16760439 : ℚ) / 16777216)), (((16760439 : ℚ) / 16777216), ((1023 : ℚ) / 1024))]
theorem corner3Domain0Cover : pieceCover ((1023 : ℚ) / 1024) ((999 : ℚ) / 1000) corner3Domain0Pieces = true := by decide +kernel
theorem corner3Domain0 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1023 : ℚ) / 1024) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-363169805555 : ℚ) / 274877906944) : ℚ) : ℝ) ((999 : ℚ) / 1000) corner3Domain0Pieces (by decide +kernel) corner3Domain0Cover
  intro p hp
  simp only [corner3Domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact corner3Piece0
  · exact corner3Piece1
#print axioms corner3Domain0Cover
#print axioms corner3Domain0
theorem corner3Piece2 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((2047 : ℚ) / 2048) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope2 x hx
  have hxT : x ∈ Icc (d2WiderTransfer471Lo : ℝ) (d2WiderTransfer471Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer471Lo, d2WiderTransfer471Hi, d2LitsNearWiderTransfers058.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer471Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24082964758674592339957 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer471Cap, d2LitsNearWiderTransfers058.q2, d2WiderTransfer471C0, d2WiderTransfer471S0] using hD
  have hcap : ((((-14780780608478229595051933 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24082964758674592339957 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece3 (x : ℝ) (hx : x ∈ Icc ((((2047 : ℚ) / 2048) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope3 x hx
  have hxT : x ∈ Icc (d2WiderTransfer474Lo : ℝ) (d2WiderTransfer474Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer474Lo, d2WiderTransfer474Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer474Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24087208286830028014839 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer474Cap, d2LitsNearWiderTransfers059.q2, d2WiderTransfer474C0, d2WiderTransfer474S0] using hD
  have hcap : ((((-14780818800231628516125871 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24087208286830028014839 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece4 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((8191 : ℚ) / 8192) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope4 x hx
  have hxT : x ∈ Icc (d2WiderTransfer477Lo : ℝ) (d2WiderTransfer477Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer477Lo, d2WiderTransfer477Hi, d2LitsNearWiderTransfers059.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer477Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24089329856634680078861 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer477Cap, d2LitsNearWiderTransfers059.q2, d2WiderTransfer477C0, d2WiderTransfer477S0] using hD
  have hcap : ((((-14780837894359870384702069 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24089329856634680078861 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece5 (x : ℝ) (hx : x ∈ Icc ((((8191 : ℚ) / 8192) : ℚ) : ℝ) ((((16383 : ℚ) / 16384) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope5 x hx
  have hxT : x ∈ Icc (d2WiderTransfer480Lo : ℝ) (d2WiderTransfer480Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer480Lo, d2WiderTransfer480Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer480Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((1505649412060978558719 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer480Cap, d2LitsNearWiderTransfers060.q2, d2WiderTransfer480C0, d2WiderTransfer480S0] using hD
  have hcap : ((((-923802965061683698527991 : ℚ) / 680020773533228910772224) : ℚ) : ℝ) + ((((1505649412060978558719 : ℚ) / 75557863725914323419136) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece6 (x : ℝ) (hx : x ∈ Icc ((((16383 : ℚ) / 16384) : ℚ) : ℝ) ((((32767 : ℚ) / 32768) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope6 x hx
  have hxT : x ∈ Icc (d2WiderTransfer483Lo : ℝ) (d2WiderTransfer483Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer483Lo, d2WiderTransfer483Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer483Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24090920949006672587549 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer483Cap, d2LitsNearWiderTransfers060.q2, d2WiderTransfer483C0, d2WiderTransfer483S0] using hD
  have hcap : ((((-14780852214191218317280261 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24090920949006672587549 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece7 (x : ℝ) (hx : x ∈ Icc ((((32767 : ℚ) / 32768) : ℚ) : ℝ) ((((65535 : ℚ) / 65536) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope7 x hx
  have hxT : x ∈ Icc (d2WiderTransfer486Lo : ℝ) (d2WiderTransfer486Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer486Lo, d2WiderTransfer486Hi, d2LitsNearWiderTransfers060.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer486Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24091186123987420270547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer486Cap, d2LitsNearWiderTransfers060.q2, d2WiderTransfer486C0, d2WiderTransfer486S0] using hD
  have hcap : ((((-14780854600766045046427243 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24091186123987420270547 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece8 (x : ℝ) (hx : x ∈ Icc ((((65535 : ℚ) / 65536) : ℚ) : ℝ) ((((131071 : ℚ) / 131072) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope8 x hx
  have hxT : x ∈ Icc (d2WiderTransfer489Lo : ℝ) (d2WiderTransfer489Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer489Lo, d2WiderTransfer489Hi, d2LitsNearWiderTransfers061.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer489Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((24091318710719117583029 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer489Cap, d2LitsNearWiderTransfers061.q2, d2WiderTransfer489C0, d2WiderTransfer489S0] using hD
  have hcap : ((((-14780855794046630322239581 : ℚ) / 10880332376531662572355584) : ℚ) : ℝ) + ((((24091318710719117583029 : ℚ) / 1208925819614629174706176) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
theorem corner3Piece9 (x : ℝ) (hx : x ∈ Icc ((((131071 : ℚ) / 131072) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) : fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  rw [corner3Identity]
  have h := envelope9 x hx
  have hxT : x ∈ Icc (d2WiderTransfer492Lo : ℝ) (d2WiderTransfer492Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2WiderTransfer492Lo, d2WiderTransfer492Hi, d2LitsNearWiderTransfers061.q2] at hx ⊢
    exact hx
  have hD := d2WiderTransfer492Bound x hxT
  have hd : ((((23 : ℚ) / 800) : ℚ) : ℝ) * Real.log |x - ((((-1 : ℚ) / 1) : ℚ) : ℝ)| ≤ ((((6022862824236258921987 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) := by
    simpa [d2WiderTransfer492Cap, d2LitsNearWiderTransfers061.q2, d2WiderTransfer492C0, d2WiderTransfer492S0] using hD
  have hcap : ((((-3695214246830665896295963 : ℚ) / 2720083094132915643088896) : ℚ) : ℝ) + ((((6022862824236258921987 : ℚ) / 302231454903657293676544) : ℚ) : ℝ) = ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by norm_num
  rw [← hcap]
  exact add_le_add h hd
def corner3Domain1Pieces : List (ℚ × ℚ) := [(((1023 : ℚ) / 1024), ((2047 : ℚ) / 2048)), (((2047 : ℚ) / 2048), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((8191 : ℚ) / 8192)), (((8191 : ℚ) / 8192), ((16383 : ℚ) / 16384)), (((16383 : ℚ) / 16384), ((32767 : ℚ) / 32768)), (((32767 : ℚ) / 32768), ((65535 : ℚ) / 65536)), (((65535 : ℚ) / 65536), ((131071 : ℚ) / 131072)), (((131071 : ℚ) / 131072), ((1 : ℚ) / 1))]
theorem corner3Domain1Cover : pieceCover ((1 : ℚ) / 1) ((1023 : ℚ) / 1024) corner3Domain1Pieces = true := by decide +kernel
theorem corner3Domain1 : ∀ x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x ≤ ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) := by
  apply pieceCover_bound ((1 : ℚ) / 1) (fun x : ℝ => fval (let f := (CatalanMeasure.GenD.Signed.Data.Trial72.T2.nearAt ((1 : ℚ) / 16) ((1 : ℚ) / 16)); { f with plogs := f.plogs.take (f.plogs.length - 2) }) x + lfieldTower (CatalanMeasure.Signed.FieldForm.scaleL (-1) (CatalanMeasure.Signed.FieldForm.reflL (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qF CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qFn))) 0 x) ((((-3311477922955 : ℚ) / 2473901162496) : ℚ) : ℝ) ((1023 : ℚ) / 1024) corner3Domain1Pieces (by decide +kernel) corner3Domain1Cover
  intro p hp
  simp only [corner3Domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact corner3Piece2
  · exact corner3Piece3
  · exact corner3Piece4
  · exact corner3Piece5
  · exact corner3Piece6
  · exact corner3Piece7
  · exact corner3Piece8
  · exact corner3Piece9
#print axioms corner3Domain1Cover
#print axioms corner3Domain1
end D72.NearCornerCover005
end CatalanMeasure.GenD.Signed.Data.Cells

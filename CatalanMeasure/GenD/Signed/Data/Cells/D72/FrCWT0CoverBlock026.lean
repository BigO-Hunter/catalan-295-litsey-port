module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0215

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0208 : ∀ x ∈ Icc ((((1 : ℚ) / 128) : ℚ) : ℝ) ((((5 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0208Lo = ((1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0208Hi = ((5 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0208Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0208Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0209 : ∀ x ∈ Icc ((((5 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0209Lo = ((5 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0209Hi = ((3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0209Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0209Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0210 : ∀ x ∈ Icc ((((3 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0210Lo = ((3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0210Hi = ((9 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0210Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0210Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0211 : ∀ x ∈ Icc ((((9 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0211Lo = ((9 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0211Hi = ((5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0211Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0211Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0212 : ∀ x ∈ Icc ((((5 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0212Lo = ((5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0212Hi = ((13 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0212Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0212Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0213 : ∀ x ∈ Icc ((((13 : ℚ) / 256) : ℚ) : ℝ) ((((7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0213Lo = ((13 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0213Hi = ((7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0213Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0213Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0214 : ∀ x ∈ Icc ((((7 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0214Lo = ((7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0214Hi = ((17 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0214Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0214Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0215 : ∀ x ∈ Icc ((((17 : ℚ) / 256) : ℚ) : ℝ) ((((9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0215Lo = ((17 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0215Hi = ((9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0215Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0215Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock026 : ∀ x ∈ Icc ((((1 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0208 liftFrCWT0P0209) (cover_union liftFrCWT0P0210 liftFrCWT0P0211)) (cover_union (cover_union liftFrCWT0P0212 liftFrCWT0P0213) (cover_union liftFrCWT0P0214 liftFrCWT0P0215)))
#print axioms FrCWT0CoverBlock026

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

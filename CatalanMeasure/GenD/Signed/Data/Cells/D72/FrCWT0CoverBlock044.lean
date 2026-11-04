module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0352
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0353
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0354
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0355
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0356
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0357
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0358
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0359

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0352 : ∀ x ∈ Icc ((((213 : ℚ) / 256) : ℚ) : ℝ) ((((107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0352Lo = ((213 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0352Hi = ((107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0352Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0352Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0353 : ∀ x ∈ Icc ((((107 : ℚ) / 128) : ℚ) : ℝ) ((((429 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0353Lo = ((107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0353Hi = ((429 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0353Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0353Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0354 : ∀ x ∈ Icc ((((429 : ℚ) / 512) : ℚ) : ℝ) ((((215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0354Lo = ((429 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0354Hi = ((215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0354Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0354Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0355 : ∀ x ∈ Icc ((((215 : ℚ) / 256) : ℚ) : ℝ) ((((433 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0355Lo = ((215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0355Hi = ((433 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0355Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0355Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0356 : ∀ x ∈ Icc ((((433 : ℚ) / 512) : ℚ) : ℝ) ((((217 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0356Lo = ((433 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0356Hi = ((217 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0356Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0356Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0357 : ∀ x ∈ Icc ((((217 : ℚ) / 256) : ℚ) : ℝ) ((((437 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0357Lo = ((217 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0357Hi = ((437 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0357Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0357Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0358 : ∀ x ∈ Icc ((((437 : ℚ) / 512) : ℚ) : ℝ) ((((875 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0358Lo = ((437 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0358Hi = ((875 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0358Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0358Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0359 : ∀ x ∈ Icc ((((875 : ℚ) / 1024) : ℚ) : ℝ) ((((219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0359Lo = ((875 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0359Hi = ((219 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0359Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0359Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock044 : ∀ x ∈ Icc ((((213 : ℚ) / 256) : ℚ) : ℝ) ((((219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0352 liftFrCWT0P0353) (cover_union liftFrCWT0P0354 liftFrCWT0P0355)) (cover_union (cover_union liftFrCWT0P0356 liftFrCWT0P0357) (cover_union liftFrCWT0P0358 liftFrCWT0P0359)))
#print axioms FrCWT0CoverBlock044

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

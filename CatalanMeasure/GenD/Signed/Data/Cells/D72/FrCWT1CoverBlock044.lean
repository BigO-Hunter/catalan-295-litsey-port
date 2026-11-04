module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0352
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0353
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0354
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0355
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0356
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0357
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0358
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0359

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0352 : ∀ x ∈ Icc ((((215 : ℚ) / 256) : ℚ) : ℝ) ((((433 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0352Lo = ((215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0352Hi = ((433 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0352Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0352Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0353 : ∀ x ∈ Icc ((((433 : ℚ) / 512) : ℚ) : ℝ) ((((217 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0353Lo = ((433 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0353Hi = ((217 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0353Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0353Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0354 : ∀ x ∈ Icc ((((217 : ℚ) / 256) : ℚ) : ℝ) ((((437 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0354Lo = ((217 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0354Hi = ((437 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0354Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0354Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0355 : ∀ x ∈ Icc ((((437 : ℚ) / 512) : ℚ) : ℝ) ((((875 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0355Lo = ((437 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0355Hi = ((875 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0355Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0355Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0356 : ∀ x ∈ Icc ((((875 : ℚ) / 1024) : ℚ) : ℝ) ((((219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0356Lo = ((875 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0356Hi = ((219 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0356Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0356Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0357 : ∀ x ∈ Icc ((((219 : ℚ) / 256) : ℚ) : ℝ) ((((439 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0357Lo = ((219 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0357Hi = ((439 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0357Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0357Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0358 : ∀ x ∈ Icc ((((439 : ℚ) / 512) : ℚ) : ℝ) ((((441 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0358Lo = ((439 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0358Hi = ((441 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0358Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0358Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0359 : ∀ x ∈ Icc ((((441 : ℚ) / 512) : ℚ) : ℝ) ((((883 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0359Lo = ((441 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0359Hi = ((883 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0359Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0359Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock044 : ∀ x ∈ Icc ((((215 : ℚ) / 256) : ℚ) : ℝ) ((((883 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0352 liftFrCWT1P0353) (cover_union liftFrCWT1P0354 liftFrCWT1P0355)) (cover_union (cover_union liftFrCWT1P0356 liftFrCWT1P0357) (cover_union liftFrCWT1P0358 liftFrCWT1P0359)))
#print axioms FrCWT1CoverBlock044

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

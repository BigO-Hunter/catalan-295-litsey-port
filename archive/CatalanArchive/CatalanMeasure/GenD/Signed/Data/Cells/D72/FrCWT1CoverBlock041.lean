module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0328
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0329
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0330
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0331
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0332
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0333
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0334
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0335

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0328 : ∀ x ∈ Icc ((((381 : ℚ) / 512) : ℚ) : ℝ) ((((385 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0328Lo = ((381 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0328Hi = ((385 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0328Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0328Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0329 : ∀ x ∈ Icc ((((385 : ℚ) / 512) : ℚ) : ℝ) ((((193 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0329Lo = ((385 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0329Hi = ((193 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0329Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0329Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0330 : ∀ x ∈ Icc ((((193 : ℚ) / 256) : ℚ) : ℝ) ((((97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0330Lo = ((193 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0330Hi = ((97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0330Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0330Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0331 : ∀ x ∈ Icc ((((97 : ℚ) / 128) : ℚ) : ℝ) ((((195 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0331Lo = ((97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0331Hi = ((195 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0331Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0331Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0332 : ∀ x ∈ Icc ((((195 : ℚ) / 256) : ℚ) : ℝ) ((((49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0332Lo = ((195 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0332Hi = ((49 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0332Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0332Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0333 : ∀ x ∈ Icc ((((49 : ℚ) / 64) : ℚ) : ℝ) ((((25 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0333Lo = ((49 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0333Hi = ((25 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0333Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0333Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0334 : ∀ x ∈ Icc ((((25 : ℚ) / 32) : ℚ) : ℝ) ((((201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0334Lo = ((25 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0334Hi = ((201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0334Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0334Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0335 : ∀ x ∈ Icc ((((201 : ℚ) / 256) : ℚ) : ℝ) ((((101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0335Lo = ((201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0335Hi = ((101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0335Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0335Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock041 : ∀ x ∈ Icc ((((381 : ℚ) / 512) : ℚ) : ℝ) ((((101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0328 liftFrCWT1P0329) (cover_union liftFrCWT1P0330 liftFrCWT1P0331)) (cover_union (cover_union liftFrCWT1P0332 liftFrCWT1P0333) (cover_union liftFrCWT1P0334 liftFrCWT1P0335)))
#print axioms FrCWT1CoverBlock041

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

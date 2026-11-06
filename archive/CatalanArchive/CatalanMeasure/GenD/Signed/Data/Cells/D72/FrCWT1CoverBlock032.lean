module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0256
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0257
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0258
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0259
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0260
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0261
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0262
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0263

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0256 : ∀ x ∈ Icc ((((49 : ℚ) / 128) : ℚ) : ℝ) ((((99 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0256Lo = ((49 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0256Hi = ((99 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0256Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0256Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0257 : ∀ x ∈ Icc ((((99 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0257Lo = ((99 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0257Hi = ((25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0257Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0257Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0258 : ∀ x ∈ Icc ((((25 : ℚ) / 64) : ℚ) : ℝ) ((((51 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0258Lo = ((25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0258Hi = ((51 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0258Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0258Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0259 : ∀ x ∈ Icc ((((51 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0259Lo = ((51 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0259Hi = ((13 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0259Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0259Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0260 : ∀ x ∈ Icc ((((13 : ℚ) / 32) : ℚ) : ℝ) ((((53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0260Lo = ((13 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0260Hi = ((53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0260Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0260Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0261 : ∀ x ∈ Icc ((((53 : ℚ) / 128) : ℚ) : ℝ) ((((107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0261Lo = ((53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0261Hi = ((107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0261Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0261Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0262 : ∀ x ∈ Icc ((((107 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0262Lo = ((107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0262Hi = ((27 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0262Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0262Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0263 : ∀ x ∈ Icc ((((27 : ℚ) / 64) : ℚ) : ℝ) ((((55 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0263Lo = ((27 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0263Hi = ((55 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0263Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0263Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock032 : ∀ x ∈ Icc ((((49 : ℚ) / 128) : ℚ) : ℝ) ((((55 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0256 liftFrCWT1P0257) (cover_union liftFrCWT1P0258 liftFrCWT1P0259)) (cover_union (cover_union liftFrCWT1P0260 liftFrCWT1P0261) (cover_union liftFrCWT1P0262 liftFrCWT1P0263)))
#print axioms FrCWT1CoverBlock032

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

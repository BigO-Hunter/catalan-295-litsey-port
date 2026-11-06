module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0288
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0289
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0290
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0291
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0292
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0293
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0294
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0295

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0288 : ∀ x ∈ Icc ((((73 : ℚ) / 128) : ℚ) : ℝ) ((((147 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0288Lo = ((73 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0288Hi = ((147 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0288Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0288Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0289 : ∀ x ∈ Icc ((((147 : ℚ) / 256) : ℚ) : ℝ) ((((37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0289Lo = ((147 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0289Hi = ((37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0289Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0289Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0290 : ∀ x ∈ Icc ((((37 : ℚ) / 64) : ℚ) : ℝ) ((((297 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0290Lo = ((37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0290Hi = ((297 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0290Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0290Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0291 : ∀ x ∈ Icc ((((297 : ℚ) / 512) : ℚ) : ℝ) ((((75 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0291Lo = ((297 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0291Hi = ((75 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0291Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0291Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0292 : ∀ x ∈ Icc ((((75 : ℚ) / 128) : ℚ) : ℝ) ((((151 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0292Lo = ((75 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0292Hi = ((151 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0292Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0292Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0293 : ∀ x ∈ Icc ((((151 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0293Lo = ((151 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0293Hi = ((19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0293Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0293Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0294 : ∀ x ∈ Icc ((((19 : ℚ) / 32) : ℚ) : ℝ) ((((77 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0294Lo = ((19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0294Hi = ((77 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0294Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0294Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0295 : ∀ x ∈ Icc ((((77 : ℚ) / 128) : ℚ) : ℝ) ((((309 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0295Lo = ((77 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0295Hi = ((309 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0295Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0295Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock036 : ∀ x ∈ Icc ((((73 : ℚ) / 128) : ℚ) : ℝ) ((((309 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0288 liftFrCWT1P0289) (cover_union liftFrCWT1P0290 liftFrCWT1P0291)) (cover_union (cover_union liftFrCWT1P0292 liftFrCWT1P0293) (cover_union liftFrCWT1P0294 liftFrCWT1P0295)))
#print axioms FrCWT1CoverBlock036

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

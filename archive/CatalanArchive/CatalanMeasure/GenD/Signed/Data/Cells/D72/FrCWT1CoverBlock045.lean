module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0360
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0361
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0362
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0363
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0364
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0365
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0366
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0367

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0360 : ∀ x ∈ Icc ((((883 : ℚ) / 1024) : ℚ) : ℝ) ((((221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0360Lo = ((883 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0360Hi = ((221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0360Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0360Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0361 : ∀ x ∈ Icc ((((221 : ℚ) / 256) : ℚ) : ℝ) ((((443 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0361Lo = ((221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0361Hi = ((443 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0361Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0361Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0362 : ∀ x ∈ Icc ((((443 : ℚ) / 512) : ℚ) : ℝ) ((((445 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0362Lo = ((443 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0362Hi = ((445 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0362Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0362Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0363 : ∀ x ∈ Icc ((((445 : ℚ) / 512) : ℚ) : ℝ) ((((891 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0363Lo = ((445 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0363Hi = ((891 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0363Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0363Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0364 : ∀ x ∈ Icc ((((891 : ℚ) / 1024) : ℚ) : ℝ) ((((223 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0364Lo = ((891 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0364Hi = ((223 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0364Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0364Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0365 : ∀ x ∈ Icc ((((223 : ℚ) / 256) : ℚ) : ℝ) ((((893 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0365Lo = ((223 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0365Hi = ((893 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0365Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0365Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0366 : ∀ x ∈ Icc ((((893 : ℚ) / 1024) : ℚ) : ℝ) ((((449 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0366Lo = ((893 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0366Hi = ((449 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0366Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0366Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0367 : ∀ x ∈ Icc ((((449 : ℚ) / 512) : ℚ) : ℝ) ((((225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0367Lo = ((449 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0367Hi = ((225 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0367Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0367Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock045 : ∀ x ∈ Icc ((((883 : ℚ) / 1024) : ℚ) : ℝ) ((((225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0360 liftFrCWT1P0361) (cover_union liftFrCWT1P0362 liftFrCWT1P0363)) (cover_union (cover_union liftFrCWT1P0364 liftFrCWT1P0365) (cover_union liftFrCWT1P0366 liftFrCWT1P0367)))
#print axioms FrCWT1CoverBlock045

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

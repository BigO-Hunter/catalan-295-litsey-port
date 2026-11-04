module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0272
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0273
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0274
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0275
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0276
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0277
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0278
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0279

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0272 : ∀ x ∈ Icc ((((61 : ℚ) / 128) : ℚ) : ℝ) ((((31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0272Lo = ((61 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0272Hi = ((31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0272Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0272Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0273 : ∀ x ∈ Icc ((((31 : ℚ) / 64) : ℚ) : ℝ) ((((125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0273Lo = ((31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0273Hi = ((125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0273Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0273Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0274 : ∀ x ∈ Icc ((((125 : ℚ) / 256) : ℚ) : ℝ) ((((255 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0274Lo = ((125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0274Hi = ((255 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0274Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0274Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0275 : ∀ x ∈ Icc ((((255 : ℚ) / 512) : ℚ) : ℝ) ((((1 : ℚ) / 2) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0275Lo = ((255 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0275Hi = ((1 : ℚ) / 2) := by decide +kernel
  have hcap : FrCWT1P0275Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0275Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0276 : ∀ x ∈ Icc ((((1 : ℚ) / 2) : ℚ) : ℝ) ((((129 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0276Lo = ((1 : ℚ) / 2) := by decide +kernel
  have hhi : ceFrCWT1P0276Hi = ((129 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0276Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0276Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0277 : ∀ x ∈ Icc ((((129 : ℚ) / 256) : ℚ) : ℝ) ((((131 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0277Lo = ((129 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0277Hi = ((131 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0277Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0277Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0278 : ∀ x ∈ Icc ((((131 : ℚ) / 256) : ℚ) : ℝ) ((((33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0278Lo = ((131 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0278Hi = ((33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0278Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0278Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0279 : ∀ x ∈ Icc ((((33 : ℚ) / 64) : ℚ) : ℝ) ((((17 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0279Lo = ((33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0279Hi = ((17 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0279Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0279Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock034 : ∀ x ∈ Icc ((((61 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0272 liftFrCWT1P0273) (cover_union liftFrCWT1P0274 liftFrCWT1P0275)) (cover_union (cover_union liftFrCWT1P0276 liftFrCWT1P0277) (cover_union liftFrCWT1P0278 liftFrCWT1P0279)))
#print axioms FrCWT1CoverBlock034

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

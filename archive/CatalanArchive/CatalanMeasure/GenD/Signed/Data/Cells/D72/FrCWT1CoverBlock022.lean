module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0183

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0176 : ∀ x ∈ Icc ((((-55 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0176Lo = ((-55 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0176Hi = ((-27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0176Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0176Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0177 : ∀ x ∈ Icc ((((-27 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0177Lo = ((-27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0177Hi = ((-51 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0177Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0177Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0178 : ∀ x ∈ Icc ((((-51 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0178Lo = ((-51 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0178Hi = ((-25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0178Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0178Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0179 : ∀ x ∈ Icc ((((-25 : ℚ) / 128) : ℚ) : ℝ) ((((-47 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0179Lo = ((-25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0179Hi = ((-47 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0179Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0179Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0180 : ∀ x ∈ Icc ((((-47 : ℚ) / 256) : ℚ) : ℝ) ((((-23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0180Lo = ((-47 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0180Hi = ((-23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0180Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0180Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0181 : ∀ x ∈ Icc ((((-23 : ℚ) / 128) : ℚ) : ℝ) ((((-43 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0181Lo = ((-23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0181Hi = ((-43 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0181Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0181Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0182 : ∀ x ∈ Icc ((((-43 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0182Lo = ((-43 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0182Hi = ((-21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0182Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0182Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0183 : ∀ x ∈ Icc ((((-21 : ℚ) / 128) : ℚ) : ℝ) ((((-39 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0183Lo = ((-21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0183Hi = ((-39 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0183Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0183Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock022 : ∀ x ∈ Icc ((((-55 : ℚ) / 256) : ℚ) : ℝ) ((((-39 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0176 liftFrCWT1P0177) (cover_union liftFrCWT1P0178 liftFrCWT1P0179)) (cover_union (cover_union liftFrCWT1P0180 liftFrCWT1P0181) (cover_union liftFrCWT1P0182 liftFrCWT1P0183)))
#print axioms FrCWT1CoverBlock022

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

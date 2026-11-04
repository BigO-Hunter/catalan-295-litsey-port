module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0233
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0238
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0239

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0232 : ∀ x ∈ Icc ((((27 : ℚ) / 128) : ℚ) : ℝ) ((((7 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0232Lo = ((27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0232Hi = ((7 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0232Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0232Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0233 : ∀ x ∈ Icc ((((7 : ℚ) / 32) : ℚ) : ℝ) ((((29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0233Lo = ((7 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0233Hi = ((29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0233Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0233Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0234 : ∀ x ∈ Icc ((((29 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0234Lo = ((29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0234Hi = ((15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0234Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0234Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0235 : ∀ x ∈ Icc ((((15 : ℚ) / 64) : ℚ) : ℝ) ((((31 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0235Lo = ((15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0235Hi = ((31 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0235Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0235Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0236 : ∀ x ∈ Icc ((((31 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0236Lo = ((31 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0236Hi = ((17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0236Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0236Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0237 : ∀ x ∈ Icc ((((17 : ℚ) / 64) : ℚ) : ℝ) ((((35 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0237Lo = ((17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0237Hi = ((35 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0237Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0237Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0238 : ∀ x ∈ Icc ((((35 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0238Lo = ((35 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0238Hi = ((9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0238Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0238Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0239 : ∀ x ∈ Icc ((((9 : ℚ) / 32) : ℚ) : ℝ) ((((73 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0239Lo = ((9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0239Hi = ((73 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0239Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0239Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock029 : ∀ x ∈ Icc ((((27 : ℚ) / 128) : ℚ) : ℝ) ((((73 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0232 liftFrCWT1P0233) (cover_union liftFrCWT1P0234 liftFrCWT1P0235)) (cover_union (cover_union liftFrCWT1P0236 liftFrCWT1P0237) (cover_union liftFrCWT1P0238 liftFrCWT1P0239)))
#print axioms FrCWT1CoverBlock029

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0248
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0249
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0250
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0251
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0252
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0253
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0254
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0255

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0248 : ∀ x ∈ Icc ((((85 : ℚ) / 256) : ℚ) : ℝ) ((((43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0248Lo = ((85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0248Hi = ((43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0248Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0248Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0249 : ∀ x ∈ Icc ((((43 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0249Lo = ((43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0249Hi = ((45 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0249Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0249Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0250 : ∀ x ∈ Icc ((((45 : ℚ) / 128) : ℚ) : ℝ) ((((91 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0250Lo = ((45 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0250Hi = ((91 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0250Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0250Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0251 : ∀ x ∈ Icc ((((91 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0251Lo = ((91 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0251Hi = ((23 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0251Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0251Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0252 : ∀ x ∈ Icc ((((23 : ℚ) / 64) : ℚ) : ℝ) ((((47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0252Lo = ((23 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0252Hi = ((47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0252Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0252Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0253 : ∀ x ∈ Icc ((((47 : ℚ) / 128) : ℚ) : ℝ) ((((95 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0253Lo = ((47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0253Hi = ((95 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0253Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0253Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0254 : ∀ x ∈ Icc ((((95 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0254Lo = ((95 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0254Hi = ((3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT1P0254Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0254Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0255 : ∀ x ∈ Icc ((((3 : ℚ) / 8) : ℚ) : ℝ) ((((49 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0255Lo = ((3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT1P0255Hi = ((49 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0255Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0255Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock031 : ∀ x ∈ Icc ((((85 : ℚ) / 256) : ℚ) : ℝ) ((((49 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0248 liftFrCWT1P0249) (cover_union liftFrCWT1P0250 liftFrCWT1P0251)) (cover_union (cover_union liftFrCWT1P0252 liftFrCWT1P0253) (cover_union liftFrCWT1P0254 liftFrCWT1P0255)))
#print axioms FrCWT1CoverBlock031

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

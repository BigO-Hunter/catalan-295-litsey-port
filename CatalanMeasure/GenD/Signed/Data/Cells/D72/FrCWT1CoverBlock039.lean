module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0312
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0313
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0314
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0315
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0316
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0317
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0318
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0319

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0312 : ∀ x ∈ Icc ((((347 : ℚ) / 512) : ℚ) : ℝ) ((((175 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0312Lo = ((347 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0312Hi = ((175 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0312Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0312Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0313 : ∀ x ∈ Icc ((((175 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0313Lo = ((175 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0313Hi = ((11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0313Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0313Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0314 : ∀ x ∈ Icc ((((11 : ℚ) / 16) : ℚ) : ℝ) ((((353 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0314Lo = ((11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0314Hi = ((353 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0314Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0314Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0315 : ∀ x ∈ Icc ((((353 : ℚ) / 512) : ℚ) : ℝ) ((((89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0315Lo = ((353 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0315Hi = ((89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0315Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0315Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0316 : ∀ x ∈ Icc ((((89 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0316Lo = ((89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0316Hi = ((45 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0316Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0316Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0317 : ∀ x ∈ Icc ((((45 : ℚ) / 64) : ℚ) : ℝ) ((((363 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0317Lo = ((45 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0317Hi = ((363 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0317Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0317Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0318 : ∀ x ∈ Icc ((((363 : ℚ) / 512) : ℚ) : ℝ) ((((91 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0318Lo = ((363 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0318Hi = ((91 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0318Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0318Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0319 : ∀ x ∈ Icc ((((91 : ℚ) / 128) : ℚ) : ℝ) ((((183 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0319Lo = ((91 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0319Hi = ((183 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0319Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0319Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock039 : ∀ x ∈ Icc ((((347 : ℚ) / 512) : ℚ) : ℝ) ((((183 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0312 liftFrCWT1P0313) (cover_union liftFrCWT1P0314 liftFrCWT1P0315)) (cover_union (cover_union liftFrCWT1P0316 liftFrCWT1P0317) (cover_union liftFrCWT1P0318 liftFrCWT1P0319)))
#print axioms FrCWT1CoverBlock039

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

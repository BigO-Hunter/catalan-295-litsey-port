module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0312
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0313
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0314
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0315
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0316
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0317
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0318
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0319

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0312 : ∀ x ∈ Icc ((((187 : ℚ) / 256) : ℚ) : ℝ) ((((47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0312Lo = ((187 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0312Hi = ((47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0312Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0312Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0313 : ∀ x ∈ Icc ((((47 : ℚ) / 64) : ℚ) : ℝ) ((((189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0313Lo = ((47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0313Hi = ((189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0313Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0313Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0314 : ∀ x ∈ Icc ((((189 : ℚ) / 256) : ℚ) : ℝ) ((((95 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0314Lo = ((189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0314Hi = ((95 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0314Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0314Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0315 : ∀ x ∈ Icc ((((95 : ℚ) / 128) : ℚ) : ℝ) ((((381 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0315Lo = ((95 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0315Hi = ((381 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0315Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0315Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0316 : ∀ x ∈ Icc ((((381 : ℚ) / 512) : ℚ) : ℝ) ((((385 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0316Lo = ((381 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0316Hi = ((385 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0316Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0316Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0317 : ∀ x ∈ Icc ((((385 : ℚ) / 512) : ℚ) : ℝ) ((((193 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0317Lo = ((385 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0317Hi = ((193 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0317Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0317Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0318 : ∀ x ∈ Icc ((((193 : ℚ) / 256) : ℚ) : ℝ) ((((97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0318Lo = ((193 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0318Hi = ((97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0318Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0318Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0319 : ∀ x ∈ Icc ((((97 : ℚ) / 128) : ℚ) : ℝ) ((((195 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0319Lo = ((97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0319Hi = ((195 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0319Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0319Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock039 : ∀ x ∈ Icc ((((187 : ℚ) / 256) : ℚ) : ℝ) ((((195 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0312 liftFrCWT2P0313) (cover_union liftFrCWT2P0314 liftFrCWT2P0315)) (cover_union (cover_union liftFrCWT2P0316 liftFrCWT2P0317) (cover_union liftFrCWT2P0318 liftFrCWT2P0319)))
#print axioms FrCWT2CoverBlock039

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

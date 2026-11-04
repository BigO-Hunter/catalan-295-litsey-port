module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0352
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0353
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0354
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0355
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0356
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0357
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0358
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0359

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0352 : ∀ x ∈ Icc ((((899 : ℚ) / 1024) : ℚ) : ℝ) ((((225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0352Lo = ((899 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0352Hi = ((225 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0352Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0352Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0353 : ∀ x ∈ Icc ((((225 : ℚ) / 256) : ℚ) : ℝ) ((((901 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0353Lo = ((225 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0353Hi = ((901 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0353Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0353Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0354 : ∀ x ∈ Icc ((((901 : ℚ) / 1024) : ℚ) : ℝ) ((((113 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0354Lo = ((901 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0354Hi = ((113 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0354Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0354Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0355 : ∀ x ∈ Icc ((((113 : ℚ) / 128) : ℚ) : ℝ) ((((227 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0355Lo = ((113 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0355Hi = ((227 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0355Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0355Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0356 : ∀ x ∈ Icc ((((227 : ℚ) / 256) : ℚ) : ℝ) ((((57 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0356Lo = ((227 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0356Hi = ((57 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0356Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0356Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0357 : ∀ x ∈ Icc ((((57 : ℚ) / 64) : ℚ) : ℝ) ((((115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0357Lo = ((57 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0357Hi = ((115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0357Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0357Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0358 : ∀ x ∈ Icc ((((115 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0358Lo = ((115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0358Hi = ((29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0358Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0358Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0359 : ∀ x ∈ Icc ((((29 : ℚ) / 32) : ℚ) : ℝ) ((((15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0359Lo = ((29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0359Hi = ((15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0359Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0359Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock044 : ∀ x ∈ Icc ((((899 : ℚ) / 1024) : ℚ) : ℝ) ((((15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0352 liftFrCWT2P0353) (cover_union liftFrCWT2P0354 liftFrCWT2P0355)) (cover_union (cover_union liftFrCWT2P0356 liftFrCWT2P0357) (cover_union liftFrCWT2P0358 liftFrCWT2P0359)))
#print axioms FrCWT2CoverBlock044

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0256
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0257
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0258
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0259
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0260
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0261
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0262
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0263

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0256 : ∀ x ∈ Icc ((((55 : ℚ) / 128) : ℚ) : ℝ) ((((111 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0256Lo = ((55 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0256Hi = ((111 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0256Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0256Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0257 : ∀ x ∈ Icc ((((111 : ℚ) / 256) : ℚ) : ℝ) ((((113 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0257Lo = ((111 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0257Hi = ((113 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0257Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0257Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0258 : ∀ x ∈ Icc ((((113 : ℚ) / 256) : ℚ) : ℝ) ((((57 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0258Lo = ((113 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0258Hi = ((57 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0258Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0258Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0259 : ∀ x ∈ Icc ((((57 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0259Lo = ((57 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0259Hi = ((29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0259Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0259Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0260 : ∀ x ∈ Icc ((((29 : ℚ) / 64) : ℚ) : ℝ) ((((117 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0260Lo = ((29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0260Hi = ((117 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0260Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0260Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0261 : ∀ x ∈ Icc ((((117 : ℚ) / 256) : ℚ) : ℝ) ((((59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0261Lo = ((117 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0261Hi = ((59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0261Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0261Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0262 : ∀ x ∈ Icc ((((59 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0262Lo = ((59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0262Hi = ((15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0262Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0262Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0263 : ∀ x ∈ Icc ((((15 : ℚ) / 32) : ℚ) : ℝ) ((((61 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0263Lo = ((15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0263Hi = ((61 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0263Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0263Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock032 : ∀ x ∈ Icc ((((55 : ℚ) / 128) : ℚ) : ℝ) ((((61 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0256 liftFrCWT2P0257) (cover_union liftFrCWT2P0258 liftFrCWT2P0259)) (cover_union (cover_union liftFrCWT2P0260 liftFrCWT2P0261) (cover_union liftFrCWT2P0262 liftFrCWT2P0263)))
#print axioms FrCWT2CoverBlock032

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0360
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0361

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0360 : ∀ x ∈ Icc ((((15 : ℚ) / 16) : ℚ) : ℝ) ((((31 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0360Lo = ((15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0360Hi = ((31 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0360Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0360Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0361 : ∀ x ∈ Icc ((((31 : ℚ) / 32) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0361Lo = ((31 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0361Hi = ((1 : ℚ) / 1) := by decide +kernel
  have hcap : FrCWT2P0361Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0361Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock045 : ∀ x ∈ Icc ((((15 : ℚ) / 16) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union liftFrCWT2P0360 liftFrCWT2P0361)
#print axioms FrCWT2CoverBlock045

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

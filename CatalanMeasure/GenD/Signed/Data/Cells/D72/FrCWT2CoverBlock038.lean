module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0304
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0305
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0306
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0307
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0308
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0309
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0310
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0311

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0304 : ∀ x ∈ Icc ((((353 : ℚ) / 512) : ℚ) : ℝ) ((((89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0304Lo = ((353 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0304Hi = ((89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0304Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0304Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0305 : ∀ x ∈ Icc ((((89 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0305Lo = ((89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0305Hi = ((45 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0305Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0305Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0306 : ∀ x ∈ Icc ((((45 : ℚ) / 64) : ℚ) : ℝ) ((((363 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0306Lo = ((45 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0306Hi = ((363 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0306Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0306Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0307 : ∀ x ∈ Icc ((((363 : ℚ) / 512) : ℚ) : ℝ) ((((91 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0307Lo = ((363 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0307Hi = ((91 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0307Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0307Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0308 : ∀ x ∈ Icc ((((91 : ℚ) / 128) : ℚ) : ℝ) ((((183 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0308Lo = ((91 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0308Hi = ((183 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0308Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0308Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0309 : ∀ x ∈ Icc ((((183 : ℚ) / 256) : ℚ) : ℝ) ((((369 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0309Lo = ((183 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0309Hi = ((369 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0309Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0309Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0310 : ∀ x ∈ Icc ((((369 : ℚ) / 512) : ℚ) : ℝ) ((((185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0310Lo = ((369 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0310Hi = ((185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0310Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0310Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0311 : ∀ x ∈ Icc ((((185 : ℚ) / 256) : ℚ) : ℝ) ((((187 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0311Lo = ((185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0311Hi = ((187 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0311Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0311Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock038 : ∀ x ∈ Icc ((((353 : ℚ) / 512) : ℚ) : ℝ) ((((187 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0304 liftFrCWT2P0305) (cover_union liftFrCWT2P0306 liftFrCWT2P0307)) (cover_union (cover_union liftFrCWT2P0308 liftFrCWT2P0309) (cover_union liftFrCWT2P0310 liftFrCWT2P0311)))
#print axioms FrCWT2CoverBlock038

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

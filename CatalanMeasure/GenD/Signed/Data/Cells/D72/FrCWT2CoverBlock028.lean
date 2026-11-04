module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0231

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0224 : ∀ x ∈ Icc ((((53 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0224Lo = ((53 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0224Hi = ((27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0224Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0224Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0225 : ∀ x ∈ Icc ((((27 : ℚ) / 128) : ℚ) : ℝ) ((((7 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0225Lo = ((27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0225Hi = ((7 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0225Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0225Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0226 : ∀ x ∈ Icc ((((7 : ℚ) / 32) : ℚ) : ℝ) ((((29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0226Lo = ((7 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0226Hi = ((29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0226Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0226Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0227 : ∀ x ∈ Icc ((((29 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0227Lo = ((29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0227Hi = ((15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0227Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0227Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0228 : ∀ x ∈ Icc ((((15 : ℚ) / 64) : ℚ) : ℝ) ((((31 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0228Lo = ((15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0228Hi = ((31 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0228Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0228Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0229 : ∀ x ∈ Icc ((((31 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0229Lo = ((31 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0229Hi = ((17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0229Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0229Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0230 : ∀ x ∈ Icc ((((17 : ℚ) / 64) : ℚ) : ℝ) ((((35 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0230Lo = ((17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0230Hi = ((35 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0230Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0230Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0231 : ∀ x ∈ Icc ((((35 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0231Lo = ((35 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0231Hi = ((9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0231Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0231Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock028 : ∀ x ∈ Icc ((((53 : ℚ) / 256) : ℚ) : ℝ) ((((9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0224 liftFrCWT2P0225) (cover_union liftFrCWT2P0226 liftFrCWT2P0227)) (cover_union (cover_union liftFrCWT2P0228 liftFrCWT2P0229) (cover_union liftFrCWT2P0230 liftFrCWT2P0231)))
#print axioms FrCWT2CoverBlock028

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

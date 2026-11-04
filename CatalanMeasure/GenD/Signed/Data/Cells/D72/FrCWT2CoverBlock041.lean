module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0328
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0329
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0330
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0331
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0332
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0333
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0334
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0335

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0328 : ∀ x ∈ Icc ((((415 : ℚ) / 512) : ℚ) : ℝ) ((((13 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0328Lo = ((415 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0328Hi = ((13 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0328Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0328Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0329 : ∀ x ∈ Icc ((((13 : ℚ) / 16) : ℚ) : ℝ) ((((209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0329Lo = ((13 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0329Hi = ((209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0329Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0329Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0330 : ∀ x ∈ Icc ((((209 : ℚ) / 256) : ℚ) : ℝ) ((((105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0330Lo = ((209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0330Hi = ((105 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0330Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0330Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0331 : ∀ x ∈ Icc ((((105 : ℚ) / 128) : ℚ) : ℝ) ((((421 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0331Lo = ((105 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0331Hi = ((421 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0331Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0331Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0332 : ∀ x ∈ Icc ((((421 : ℚ) / 512) : ℚ) : ℝ) ((((53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0332Lo = ((421 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0332Hi = ((53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0332Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0332Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0333 : ∀ x ∈ Icc ((((53 : ℚ) / 64) : ℚ) : ℝ) ((((849 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0333Lo = ((53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0333Hi = ((849 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0333Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0333Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0334 : ∀ x ∈ Icc ((((849 : ℚ) / 1024) : ℚ) : ℝ) ((((425 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0334Lo = ((849 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0334Hi = ((425 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0334Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0334Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0335 : ∀ x ∈ Icc ((((425 : ℚ) / 512) : ℚ) : ℝ) ((((213 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0335Lo = ((425 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0335Hi = ((213 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0335Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0335Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock041 : ∀ x ∈ Icc ((((415 : ℚ) / 512) : ℚ) : ℝ) ((((213 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0328 liftFrCWT2P0329) (cover_union liftFrCWT2P0330 liftFrCWT2P0331)) (cover_union (cover_union liftFrCWT2P0332 liftFrCWT2P0333) (cover_union liftFrCWT2P0334 liftFrCWT2P0335)))
#print axioms FrCWT2CoverBlock041

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0280
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0281
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0282
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0283
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0284
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0285
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0286
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0287

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0280 : ∀ x ∈ Icc ((((297 : ℚ) / 512) : ℚ) : ℝ) ((((75 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0280Lo = ((297 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0280Hi = ((75 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0280Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0280Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0281 : ∀ x ∈ Icc ((((75 : ℚ) / 128) : ℚ) : ℝ) ((((151 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0281Lo = ((75 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0281Hi = ((151 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0281Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0281Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0282 : ∀ x ∈ Icc ((((151 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0282Lo = ((151 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0282Hi = ((19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0282Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0282Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0283 : ∀ x ∈ Icc ((((19 : ℚ) / 32) : ℚ) : ℝ) ((((77 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0283Lo = ((19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0283Hi = ((77 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0283Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0283Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0284 : ∀ x ∈ Icc ((((77 : ℚ) / 128) : ℚ) : ℝ) ((((309 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0284Lo = ((77 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0284Hi = ((309 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0284Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0284Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0285 : ∀ x ∈ Icc ((((309 : ℚ) / 512) : ℚ) : ℝ) ((((155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0285Lo = ((309 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0285Hi = ((155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0285Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0285Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0286 : ∀ x ∈ Icc ((((155 : ℚ) / 256) : ℚ) : ℝ) ((((39 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0286Lo = ((155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0286Hi = ((39 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0286Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0286Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0287 : ∀ x ∈ Icc ((((39 : ℚ) / 64) : ℚ) : ℝ) ((((5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0287Lo = ((39 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0287Hi = ((5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT2P0287Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0287Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock035 : ∀ x ∈ Icc ((((297 : ℚ) / 512) : ℚ) : ℝ) ((((5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0280 liftFrCWT2P0281) (cover_union liftFrCWT2P0282 liftFrCWT2P0283)) (cover_union (cover_union liftFrCWT2P0284 liftFrCWT2P0285) (cover_union liftFrCWT2P0286 liftFrCWT2P0287)))
#print axioms FrCWT2CoverBlock035

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

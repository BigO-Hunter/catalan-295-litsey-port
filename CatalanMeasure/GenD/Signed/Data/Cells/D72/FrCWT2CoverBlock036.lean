module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0288
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0289
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0290
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0291
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0292
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0293
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0294
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0295

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0288 : ∀ x ∈ Icc ((((5 : ℚ) / 8) : ℚ) : ℝ) ((((81 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0288Lo = ((5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT2P0288Hi = ((81 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0288Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0288Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0289 : ∀ x ∈ Icc ((((81 : ℚ) / 128) : ℚ) : ℝ) ((((163 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0289Lo = ((81 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0289Hi = ((163 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0289Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0289Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0290 : ∀ x ∈ Icc ((((163 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0290Lo = ((163 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0290Hi = ((41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0290Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0290Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0291 : ∀ x ∈ Icc ((((41 : ℚ) / 64) : ℚ) : ℝ) ((((329 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0291Lo = ((41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0291Hi = ((329 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0291Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0291Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0292 : ∀ x ∈ Icc ((((329 : ℚ) / 512) : ℚ) : ℝ) ((((83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0292Lo = ((329 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0292Hi = ((83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0292Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0292Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0293 : ∀ x ∈ Icc ((((83 : ℚ) / 128) : ℚ) : ℝ) ((((167 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0293Lo = ((83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0293Hi = ((167 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0293Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0293Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0294 : ∀ x ∈ Icc ((((167 : ℚ) / 256) : ℚ) : ℝ) ((((335 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0294Lo = ((167 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0294Hi = ((335 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0294Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0294Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0295 : ∀ x ∈ Icc ((((335 : ℚ) / 512) : ℚ) : ℝ) ((((169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0295Lo = ((335 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0295Hi = ((169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0295Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0295Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock036 : ∀ x ∈ Icc ((((5 : ℚ) / 8) : ℚ) : ℝ) ((((169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0288 liftFrCWT2P0289) (cover_union liftFrCWT2P0290 liftFrCWT2P0291)) (cover_union (cover_union liftFrCWT2P0292 liftFrCWT2P0293) (cover_union liftFrCWT2P0294 liftFrCWT2P0295)))
#print axioms FrCWT2CoverBlock036

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

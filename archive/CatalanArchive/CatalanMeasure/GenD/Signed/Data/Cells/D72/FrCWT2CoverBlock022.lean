module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0183

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0176 : ∀ x ∈ Icc ((((-21 : ℚ) / 128) : ℚ) : ℝ) ((((-39 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0176Lo = ((-21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0176Hi = ((-39 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0176Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0176Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0177 : ∀ x ∈ Icc ((((-39 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0177Lo = ((-39 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0177Hi = ((-19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0177Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0177Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0178 : ∀ x ∈ Icc ((((-19 : ℚ) / 128) : ℚ) : ℝ) ((((-35 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0178Lo = ((-19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0178Hi = ((-35 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0178Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0178Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0179 : ∀ x ∈ Icc ((((-35 : ℚ) / 256) : ℚ) : ℝ) ((((-17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0179Lo = ((-35 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0179Hi = ((-17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0179Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0179Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0180 : ∀ x ∈ Icc ((((-17 : ℚ) / 128) : ℚ) : ℝ) ((((-31 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0180Lo = ((-17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0180Hi = ((-31 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0180Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0180Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0181 : ∀ x ∈ Icc ((((-31 : ℚ) / 256) : ℚ) : ℝ) ((((-15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0181Lo = ((-31 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0181Hi = ((-15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0181Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0181Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0182 : ∀ x ∈ Icc ((((-15 : ℚ) / 128) : ℚ) : ℝ) ((((-27 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0182Lo = ((-15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0182Hi = ((-27 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0182Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0182Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0183 : ∀ x ∈ Icc ((((-27 : ℚ) / 256) : ℚ) : ℝ) ((((-13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0183Lo = ((-27 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0183Hi = ((-13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0183Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0183Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock022 : ∀ x ∈ Icc ((((-21 : ℚ) / 128) : ℚ) : ℝ) ((((-13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0176 liftFrCWT2P0177) (cover_union liftFrCWT2P0178 liftFrCWT2P0179)) (cover_union (cover_union liftFrCWT2P0180 liftFrCWT2P0181) (cover_union liftFrCWT2P0182 liftFrCWT2P0183)))
#print axioms FrCWT2CoverBlock022

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

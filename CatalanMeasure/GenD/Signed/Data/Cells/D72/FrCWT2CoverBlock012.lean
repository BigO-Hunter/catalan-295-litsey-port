module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0103

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0096 : ∀ x ∈ Icc ((((-107 : ℚ) / 128) : ℚ) : ℝ) ((((-53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0096Lo = ((-107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0096Hi = ((-53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0096Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0096Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0097 : ∀ x ∈ Icc ((((-53 : ℚ) / 64) : ℚ) : ℝ) ((((-211 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0097Lo = ((-53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0097Hi = ((-211 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0097Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0097Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0098 : ∀ x ∈ Icc ((((-211 : ℚ) / 256) : ℚ) : ℝ) ((((-421 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0098Lo = ((-211 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0098Hi = ((-421 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0098Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0098Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0099 : ∀ x ∈ Icc ((((-421 : ℚ) / 512) : ℚ) : ℝ) ((((-209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0099Lo = ((-421 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0099Hi = ((-209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0099Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0099Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0100 : ∀ x ∈ Icc ((((-209 : ℚ) / 256) : ℚ) : ℝ) ((((-13 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0100Lo = ((-209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0100Hi = ((-13 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0100Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0100Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0101 : ∀ x ∈ Icc ((((-13 : ℚ) / 16) : ℚ) : ℝ) ((((-207 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0101Lo = ((-13 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0101Hi = ((-207 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0101Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0101Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0102 : ∀ x ∈ Icc ((((-207 : ℚ) / 256) : ℚ) : ℝ) ((((-51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0102Lo = ((-207 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0102Hi = ((-51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0102Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0102Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0103 : ∀ x ∈ Icc ((((-51 : ℚ) / 64) : ℚ) : ℝ) ((((-203 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0103Lo = ((-51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0103Hi = ((-203 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0103Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0103Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock012 : ∀ x ∈ Icc ((((-107 : ℚ) / 128) : ℚ) : ℝ) ((((-203 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0096 liftFrCWT2P0097) (cover_union liftFrCWT2P0098 liftFrCWT2P0099)) (cover_union (cover_union liftFrCWT2P0100 liftFrCWT2P0101) (cover_union liftFrCWT2P0102 liftFrCWT2P0103)))
#print axioms FrCWT2CoverBlock012

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

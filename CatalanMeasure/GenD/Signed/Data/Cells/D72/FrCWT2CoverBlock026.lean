module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0215

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0208 : ∀ x ∈ Icc ((((11 : ℚ) / 128) : ℚ) : ℝ) ((((25 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0208Lo = ((11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0208Hi = ((25 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0208Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0208Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0209 : ∀ x ∈ Icc ((((25 : ℚ) / 256) : ℚ) : ℝ) ((((13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0209Lo = ((25 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0209Hi = ((13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0209Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0209Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0210 : ∀ x ∈ Icc ((((13 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0210Lo = ((13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0210Hi = ((29 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0210Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0210Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0211 : ∀ x ∈ Icc ((((29 : ℚ) / 256) : ℚ) : ℝ) ((((15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0211Lo = ((29 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0211Hi = ((15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0211Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0211Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0212 : ∀ x ∈ Icc ((((15 : ℚ) / 128) : ℚ) : ℝ) ((((33 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0212Lo = ((15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0212Hi = ((33 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0212Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0212Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0213 : ∀ x ∈ Icc ((((33 : ℚ) / 256) : ℚ) : ℝ) ((((17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0213Lo = ((33 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0213Hi = ((17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0213Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0213Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0214 : ∀ x ∈ Icc ((((17 : ℚ) / 128) : ℚ) : ℝ) ((((37 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0214Lo = ((17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0214Hi = ((37 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0214Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0214Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0215 : ∀ x ∈ Icc ((((37 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0215Lo = ((37 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0215Hi = ((19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0215Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0215Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock026 : ∀ x ∈ Icc ((((11 : ℚ) / 128) : ℚ) : ℝ) ((((19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0208 liftFrCWT2P0209) (cover_union liftFrCWT2P0210 liftFrCWT2P0211)) (cover_union (cover_union liftFrCWT2P0212 liftFrCWT2P0213) (cover_union liftFrCWT2P0214 liftFrCWT2P0215)))
#print axioms FrCWT2CoverBlock026

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

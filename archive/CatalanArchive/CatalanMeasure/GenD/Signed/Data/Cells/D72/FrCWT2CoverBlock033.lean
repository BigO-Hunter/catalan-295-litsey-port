module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0264
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0265
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0266
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0267
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0268
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0269
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0270
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0271

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0264 : ∀ x ∈ Icc ((((61 : ℚ) / 128) : ℚ) : ℝ) ((((31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0264Lo = ((61 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0264Hi = ((31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0264Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0264Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0265 : ∀ x ∈ Icc ((((31 : ℚ) / 64) : ℚ) : ℝ) ((((125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0265Lo = ((31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0265Hi = ((125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0265Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0265Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0266 : ∀ x ∈ Icc ((((125 : ℚ) / 256) : ℚ) : ℝ) ((((127 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0266Lo = ((125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0266Hi = ((127 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0266Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0266Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0267 : ∀ x ∈ Icc ((((127 : ℚ) / 256) : ℚ) : ℝ) ((((129 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0267Lo = ((127 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0267Hi = ((129 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0267Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0267Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0268 : ∀ x ∈ Icc ((((129 : ℚ) / 256) : ℚ) : ℝ) ((((131 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0268Lo = ((129 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0268Hi = ((131 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0268Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0268Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0269 : ∀ x ∈ Icc ((((131 : ℚ) / 256) : ℚ) : ℝ) ((((33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0269Lo = ((131 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0269Hi = ((33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0269Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0269Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0270 : ∀ x ∈ Icc ((((33 : ℚ) / 64) : ℚ) : ℝ) ((((17 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0270Lo = ((33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0270Hi = ((17 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0270Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0270Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0271 : ∀ x ∈ Icc ((((17 : ℚ) / 32) : ℚ) : ℝ) ((((69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0271Lo = ((17 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0271Hi = ((69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0271Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0271Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock033 : ∀ x ∈ Icc ((((61 : ℚ) / 128) : ℚ) : ℝ) ((((69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0264 liftFrCWT2P0265) (cover_union liftFrCWT2P0266 liftFrCWT2P0267)) (cover_union (cover_union liftFrCWT2P0268 liftFrCWT2P0269) (cover_union liftFrCWT2P0270 liftFrCWT2P0271)))
#print axioms FrCWT2CoverBlock033

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

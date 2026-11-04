module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0272
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0273
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0274
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0275
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0276
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0277
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0278
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0279

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0272 : ∀ x ∈ Icc ((((69 : ℚ) / 128) : ℚ) : ℝ) ((((139 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0272Lo = ((69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0272Hi = ((139 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0272Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0272Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0273 : ∀ x ∈ Icc ((((139 : ℚ) / 256) : ℚ) : ℝ) ((((141 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0273Lo = ((139 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0273Hi = ((141 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0273Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0273Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0274 : ∀ x ∈ Icc ((((141 : ℚ) / 256) : ℚ) : ℝ) ((((71 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0274Lo = ((141 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0274Hi = ((71 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0274Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0274Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0275 : ∀ x ∈ Icc ((((71 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0275Lo = ((71 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0275Hi = ((9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0275Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0275Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0276 : ∀ x ∈ Icc ((((9 : ℚ) / 16) : ℚ) : ℝ) ((((73 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0276Lo = ((9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0276Hi = ((73 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0276Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0276Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0277 : ∀ x ∈ Icc ((((73 : ℚ) / 128) : ℚ) : ℝ) ((((147 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0277Lo = ((73 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0277Hi = ((147 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0277Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0277Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0278 : ∀ x ∈ Icc ((((147 : ℚ) / 256) : ℚ) : ℝ) ((((37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0278Lo = ((147 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0278Hi = ((37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0278Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0278Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0279 : ∀ x ∈ Icc ((((37 : ℚ) / 64) : ℚ) : ℝ) ((((297 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0279Lo = ((37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0279Hi = ((297 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0279Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0279Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock034 : ∀ x ∈ Icc ((((69 : ℚ) / 128) : ℚ) : ℝ) ((((297 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0272 liftFrCWT2P0273) (cover_union liftFrCWT2P0274 liftFrCWT2P0275)) (cover_union (cover_union liftFrCWT2P0276 liftFrCWT2P0277) (cover_union liftFrCWT2P0278 liftFrCWT2P0279)))
#print axioms FrCWT2CoverBlock034

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0240
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0241
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0242
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0243
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0244
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0245
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0246
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0247

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0240 : ∀ x ∈ Icc ((((21 : ℚ) / 64) : ℚ) : ℝ) ((((85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0240Lo = ((21 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0240Hi = ((85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0240Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0240Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0241 : ∀ x ∈ Icc ((((85 : ℚ) / 256) : ℚ) : ℝ) ((((43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0241Lo = ((85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0241Hi = ((43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0241Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0241Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0242 : ∀ x ∈ Icc ((((43 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0242Lo = ((43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0242Hi = ((45 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0242Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0242Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0243 : ∀ x ∈ Icc ((((45 : ℚ) / 128) : ℚ) : ℝ) ((((91 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0243Lo = ((45 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0243Hi = ((91 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0243Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0243Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0244 : ∀ x ∈ Icc ((((91 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0244Lo = ((91 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0244Hi = ((23 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0244Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0244Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0245 : ∀ x ∈ Icc ((((23 : ℚ) / 64) : ℚ) : ℝ) ((((47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0245Lo = ((23 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0245Hi = ((47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0245Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0245Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0246 : ∀ x ∈ Icc ((((47 : ℚ) / 128) : ℚ) : ℝ) ((((95 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0246Lo = ((47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0246Hi = ((95 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0246Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0246Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0247 : ∀ x ∈ Icc ((((95 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0247Lo = ((95 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0247Hi = ((3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT2P0247Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0247Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock030 : ∀ x ∈ Icc ((((21 : ℚ) / 64) : ℚ) : ℝ) ((((3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0240 liftFrCWT2P0241) (cover_union liftFrCWT2P0242 liftFrCWT2P0243)) (cover_union (cover_union liftFrCWT2P0244 liftFrCWT2P0245) (cover_union liftFrCWT2P0246 liftFrCWT2P0247)))
#print axioms FrCWT2CoverBlock030

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

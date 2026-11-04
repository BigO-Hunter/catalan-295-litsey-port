module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0248
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0249
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0250
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0251
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0252
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0253
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0254
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0255

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0248 : ∀ x ∈ Icc ((((3 : ℚ) / 8) : ℚ) : ℝ) ((((49 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0248Lo = ((3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT2P0248Hi = ((49 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0248Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0248Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0249 : ∀ x ∈ Icc ((((49 : ℚ) / 128) : ℚ) : ℝ) ((((99 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0249Lo = ((49 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0249Hi = ((99 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0249Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0249Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0250 : ∀ x ∈ Icc ((((99 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0250Lo = ((99 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0250Hi = ((25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0250Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0250Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0251 : ∀ x ∈ Icc ((((25 : ℚ) / 64) : ℚ) : ℝ) ((((13 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0251Lo = ((25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0251Hi = ((13 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0251Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0251Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0252 : ∀ x ∈ Icc ((((13 : ℚ) / 32) : ℚ) : ℝ) ((((53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0252Lo = ((13 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0252Hi = ((53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0252Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0252Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0253 : ∀ x ∈ Icc ((((53 : ℚ) / 128) : ℚ) : ℝ) ((((107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0253Lo = ((53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0253Hi = ((107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0253Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0253Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0254 : ∀ x ∈ Icc ((((107 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0254Lo = ((107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0254Hi = ((27 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0254Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0254Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0255 : ∀ x ∈ Icc ((((27 : ℚ) / 64) : ℚ) : ℝ) ((((55 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0255Lo = ((27 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0255Hi = ((55 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0255Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0255Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock031 : ∀ x ∈ Icc ((((3 : ℚ) / 8) : ℚ) : ℝ) ((((55 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0248 liftFrCWT2P0249) (cover_union liftFrCWT2P0250 liftFrCWT2P0251)) (cover_union (cover_union liftFrCWT2P0252 liftFrCWT2P0253) (cover_union liftFrCWT2P0254 liftFrCWT2P0255)))
#print axioms FrCWT2CoverBlock031

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

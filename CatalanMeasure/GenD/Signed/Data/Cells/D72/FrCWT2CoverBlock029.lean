module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0233
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0238
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0239

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0232 : ∀ x ∈ Icc ((((9 : ℚ) / 32) : ℚ) : ℝ) ((((73 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0232Lo = ((9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0232Hi = ((73 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0232Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0232Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0233 : ∀ x ∈ Icc ((((73 : ℚ) / 256) : ℚ) : ℝ) ((((37 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0233Lo = ((73 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0233Hi = ((37 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0233Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0233Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0234 : ∀ x ∈ Icc ((((37 : ℚ) / 128) : ℚ) : ℝ) ((((19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0234Lo = ((37 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0234Hi = ((19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0234Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0234Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0235 : ∀ x ∈ Icc ((((19 : ℚ) / 64) : ℚ) : ℝ) ((((77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0235Lo = ((19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0235Hi = ((77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0235Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0235Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0236 : ∀ x ∈ Icc ((((77 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0236Lo = ((77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0236Hi = ((5 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0236Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0236Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0237 : ∀ x ∈ Icc ((((5 : ℚ) / 16) : ℚ) : ℝ) ((((81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0237Lo = ((5 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0237Hi = ((81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0237Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0237Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0238 : ∀ x ∈ Icc ((((81 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0238Lo = ((81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0238Hi = ((41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0238Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0238Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0239 : ∀ x ∈ Icc ((((41 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0239Lo = ((41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0239Hi = ((21 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0239Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0239Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock029 : ∀ x ∈ Icc ((((9 : ℚ) / 32) : ℚ) : ℝ) ((((21 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0232 liftFrCWT2P0233) (cover_union liftFrCWT2P0234 liftFrCWT2P0235)) (cover_union (cover_union liftFrCWT2P0236 liftFrCWT2P0237) (cover_union liftFrCWT2P0238 liftFrCWT2P0239)))
#print axioms FrCWT2CoverBlock029

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

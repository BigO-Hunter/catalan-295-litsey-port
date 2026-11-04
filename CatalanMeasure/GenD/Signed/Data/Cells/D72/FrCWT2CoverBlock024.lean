module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0192
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0193
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0194
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0195
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0196
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0197
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0198
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0199

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0192 : ∀ x ∈ Icc ((((-5 : ℚ) / 128) : ℚ) : ℝ) ((((-7 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0192Lo = ((-5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0192Hi = ((-7 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0192Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0192Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0193 : ∀ x ∈ Icc ((((-7 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0193Lo = ((-7 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0193Hi = ((-3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0193Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0193Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0194 : ∀ x ∈ Icc ((((-3 : ℚ) / 128) : ℚ) : ℝ) ((((-3 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0194Lo = ((-3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0194Hi = ((-3 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0194Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0194Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0195 : ∀ x ∈ Icc ((((-3 : ℚ) / 256) : ℚ) : ℝ) ((((-1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0195Lo = ((-3 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0195Hi = ((-1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0195Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0195Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0196 : ∀ x ∈ Icc ((((-1 : ℚ) / 128) : ℚ) : ℝ) ((((1 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0196Lo = ((-1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0196Hi = ((1 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0196Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0196Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0197 : ∀ x ∈ Icc ((((1 : ℚ) / 256) : ℚ) : ℝ) ((((1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0197Lo = ((1 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0197Hi = ((1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0197Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0197Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0198 : ∀ x ∈ Icc ((((1 : ℚ) / 128) : ℚ) : ℝ) ((((5 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0198Lo = ((1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0198Hi = ((5 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0198Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0198Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0199 : ∀ x ∈ Icc ((((5 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0199Lo = ((5 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0199Hi = ((3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0199Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0199Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock024 : ∀ x ∈ Icc ((((-5 : ℚ) / 128) : ℚ) : ℝ) ((((3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0192 liftFrCWT2P0193) (cover_union liftFrCWT2P0194 liftFrCWT2P0195)) (cover_union (cover_union liftFrCWT2P0196 liftFrCWT2P0197) (cover_union liftFrCWT2P0198 liftFrCWT2P0199)))
#print axioms FrCWT2CoverBlock024

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

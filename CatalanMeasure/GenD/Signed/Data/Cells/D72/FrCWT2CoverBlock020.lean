module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0160
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0161
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0162
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0163
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0164
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0165
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0166
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0167

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0160 : ∀ x ∈ Icc ((((-39 : ℚ) / 128) : ℚ) : ℝ) ((((-77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0160Lo = ((-39 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0160Hi = ((-77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0160Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0160Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0161 : ∀ x ∈ Icc ((((-77 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0161Lo = ((-77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0161Hi = ((-19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0161Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0161Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0162 : ∀ x ∈ Icc ((((-19 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0162Lo = ((-19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0162Hi = ((-9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0162Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0162Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0163 : ∀ x ∈ Icc ((((-9 : ℚ) / 32) : ℚ) : ℝ) ((((-17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0163Lo = ((-9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0163Hi = ((-17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0163Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0163Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0164 : ∀ x ∈ Icc ((((-17 : ℚ) / 64) : ℚ) : ℝ) ((((-1 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0164Lo = ((-17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0164Hi = ((-1 : ℚ) / 4) := by decide +kernel
  have hcap : FrCWT2P0164Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0164Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0165 : ∀ x ∈ Icc ((((-1 : ℚ) / 4) : ℚ) : ℝ) ((((-15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0165Lo = ((-1 : ℚ) / 4) := by decide +kernel
  have hhi : ceFrCWT2P0165Hi = ((-15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0165Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0165Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0166 : ∀ x ∈ Icc ((((-15 : ℚ) / 64) : ℚ) : ℝ) ((((-59 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0166Lo = ((-15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0166Hi = ((-59 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0166Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0166Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0167 : ∀ x ∈ Icc ((((-59 : ℚ) / 256) : ℚ) : ℝ) ((((-29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0167Lo = ((-59 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0167Hi = ((-29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0167Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0167Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock020 : ∀ x ∈ Icc ((((-39 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0160 liftFrCWT2P0161) (cover_union liftFrCWT2P0162 liftFrCWT2P0163)) (cover_union (cover_union liftFrCWT2P0164 liftFrCWT2P0165) (cover_union liftFrCWT2P0166 liftFrCWT2P0167)))
#print axioms FrCWT2CoverBlock020

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

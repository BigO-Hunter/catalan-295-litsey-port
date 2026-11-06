module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0200
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0201
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0207

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0200 : ∀ x ∈ Icc ((((3 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0200Lo = ((3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0200Hi = ((9 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0200Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0200Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0201 : ∀ x ∈ Icc ((((9 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0201Lo = ((9 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0201Hi = ((5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0201Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0201Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0202 : ∀ x ∈ Icc ((((5 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0202Lo = ((5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0202Hi = ((13 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0202Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0202Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0203 : ∀ x ∈ Icc ((((13 : ℚ) / 256) : ℚ) : ℝ) ((((7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0203Lo = ((13 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0203Hi = ((7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0203Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0203Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0204 : ∀ x ∈ Icc ((((7 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0204Lo = ((7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0204Hi = ((17 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0204Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0204Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0205 : ∀ x ∈ Icc ((((17 : ℚ) / 256) : ℚ) : ℝ) ((((9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0205Lo = ((17 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0205Hi = ((9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0205Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0205Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0206 : ∀ x ∈ Icc ((((9 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0206Lo = ((9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0206Hi = ((21 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0206Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0206Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0207 : ∀ x ∈ Icc ((((21 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0207Lo = ((21 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0207Hi = ((11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0207Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0207Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock025 : ∀ x ∈ Icc ((((3 : ℚ) / 128) : ℚ) : ℝ) ((((11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0200 liftFrCWT2P0201) (cover_union liftFrCWT2P0202 liftFrCWT2P0203)) (cover_union (cover_union liftFrCWT2P0204 liftFrCWT2P0205) (cover_union liftFrCWT2P0206 liftFrCWT2P0207)))
#print axioms FrCWT2CoverBlock025

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

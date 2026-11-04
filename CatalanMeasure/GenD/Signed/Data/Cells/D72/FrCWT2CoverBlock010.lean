module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0087

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0080 : ∀ x ∈ Icc ((((-235 : ℚ) / 256) : ℚ) : ℝ) ((((-469 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0080Lo = ((-235 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0080Hi = ((-469 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0080Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0080Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0081 : ∀ x ∈ Icc ((((-469 : ℚ) / 512) : ℚ) : ℝ) ((((-117 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0081Lo = ((-469 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0081Hi = ((-117 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0081Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0081Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0082 : ∀ x ∈ Icc ((((-117 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0082Lo = ((-117 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0082Hi = ((-29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0082Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0082Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0083 : ∀ x ∈ Icc ((((-29 : ℚ) / 32) : ℚ) : ℝ) ((((-115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0083Lo = ((-29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0083Hi = ((-115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0083Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0083Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0084 : ∀ x ∈ Icc ((((-115 : ℚ) / 128) : ℚ) : ℝ) ((((-459 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0084Lo = ((-115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0084Hi = ((-459 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0084Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0084Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0085 : ∀ x ∈ Icc ((((-459 : ℚ) / 512) : ℚ) : ℝ) ((((-57 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0085Lo = ((-459 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0085Hi = ((-57 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0085Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0085Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0086 : ∀ x ∈ Icc ((((-57 : ℚ) / 64) : ℚ) : ℝ) ((((-113 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0086Lo = ((-57 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0086Hi = ((-113 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0086Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0086Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0087 : ∀ x ∈ Icc ((((-113 : ℚ) / 128) : ℚ) : ℝ) ((((-7 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0087Lo = ((-113 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0087Hi = ((-7 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT2P0087Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0087Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock010 : ∀ x ∈ Icc ((((-235 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0080 liftFrCWT2P0081) (cover_union liftFrCWT2P0082 liftFrCWT2P0083)) (cover_union (cover_union liftFrCWT2P0084 liftFrCWT2P0085) (cover_union liftFrCWT2P0086 liftFrCWT2P0087)))
#print axioms FrCWT2CoverBlock010

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

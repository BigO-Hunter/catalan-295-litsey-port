module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0071

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0064 : ∀ x ∈ Icc ((((-497 : ℚ) / 512) : ℚ) : ℝ) ((((-991 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0064Lo = ((-497 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0064Hi = ((-991 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0064Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0064Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0065 : ∀ x ∈ Icc ((((-991 : ℚ) / 1024) : ℚ) : ℝ) ((((-495 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0065Lo = ((-991 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0065Hi = ((-495 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0065Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0065Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0066 : ∀ x ∈ Icc ((((-495 : ℚ) / 512) : ℚ) : ℝ) ((((-247 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0066Lo = ((-495 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0066Hi = ((-247 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0066Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0066Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0067 : ∀ x ∈ Icc ((((-247 : ℚ) / 256) : ℚ) : ℝ) ((((-123 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0067Lo = ((-247 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0067Hi = ((-123 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0067Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0067Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0068 : ∀ x ∈ Icc ((((-123 : ℚ) / 128) : ℚ) : ℝ) ((((-491 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0068Lo = ((-123 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0068Hi = ((-491 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0068Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0068Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0069 : ∀ x ∈ Icc ((((-491 : ℚ) / 512) : ℚ) : ℝ) ((((-981 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0069Lo = ((-491 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0069Hi = ((-981 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0069Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0069Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0070 : ∀ x ∈ Icc ((((-981 : ℚ) / 1024) : ℚ) : ℝ) ((((-489 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0070Lo = ((-981 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0070Hi = ((-489 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0070Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0070Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0071 : ∀ x ∈ Icc ((((-489 : ℚ) / 512) : ℚ) : ℝ) ((((-61 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0071Lo = ((-489 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0071Hi = ((-61 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0071Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0071Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock008 : ∀ x ∈ Icc ((((-497 : ℚ) / 512) : ℚ) : ℝ) ((((-61 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0064 liftFrCWT2P0065) (cover_union liftFrCWT2P0066 liftFrCWT2P0067)) (cover_union (cover_union liftFrCWT2P0068 liftFrCWT2P0069) (cover_union liftFrCWT2P0070 liftFrCWT2P0071)))
#print axioms FrCWT2CoverBlock008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

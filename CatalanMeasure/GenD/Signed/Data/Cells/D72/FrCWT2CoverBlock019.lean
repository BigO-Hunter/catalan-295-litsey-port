module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0152
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0153
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0154
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0155
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0156
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0157
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0158
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0159

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0152 : ∀ x ∈ Icc ((((-97 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0152Lo = ((-97 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0152Hi = ((-3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT2P0152Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0152Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0153 : ∀ x ∈ Icc ((((-3 : ℚ) / 8) : ℚ) : ℝ) ((((-47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0153Lo = ((-3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT2P0153Hi = ((-47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0153Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0153Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0154 : ∀ x ∈ Icc ((((-47 : ℚ) / 128) : ℚ) : ℝ) ((((-23 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0154Lo = ((-47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0154Hi = ((-23 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0154Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0154Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0155 : ∀ x ∈ Icc ((((-23 : ℚ) / 64) : ℚ) : ℝ) ((((-43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0155Lo = ((-23 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0155Hi = ((-43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0155Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0155Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0156 : ∀ x ∈ Icc ((((-43 : ℚ) / 128) : ℚ) : ℝ) ((((-85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0156Lo = ((-43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0156Hi = ((-85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0156Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0156Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0157 : ∀ x ∈ Icc ((((-85 : ℚ) / 256) : ℚ) : ℝ) ((((-41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0157Lo = ((-85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0157Hi = ((-41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0157Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0157Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0158 : ∀ x ∈ Icc ((((-41 : ℚ) / 128) : ℚ) : ℝ) ((((-81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0158Lo = ((-41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0158Hi = ((-81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0158Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0158Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0159 : ∀ x ∈ Icc ((((-81 : ℚ) / 256) : ℚ) : ℝ) ((((-39 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0159Lo = ((-81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0159Hi = ((-39 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0159Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0159Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock019 : ∀ x ∈ Icc ((((-97 : ℚ) / 256) : ℚ) : ℝ) ((((-39 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0152 liftFrCWT2P0153) (cover_union liftFrCWT2P0154 liftFrCWT2P0155)) (cover_union (cover_union liftFrCWT2P0156 liftFrCWT2P0157) (cover_union liftFrCWT2P0158 liftFrCWT2P0159)))
#print axioms FrCWT2CoverBlock019

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0127

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0120 : ∀ x ∈ Icc ((((-43 : ℚ) / 64) : ℚ) : ℝ) ((((-85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0120Lo = ((-43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0120Hi = ((-85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0120Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0120Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0121 : ∀ x ∈ Icc ((((-85 : ℚ) / 128) : ℚ) : ℝ) ((((-169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0121Lo = ((-85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0121Hi = ((-169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0121Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0121Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0122 : ∀ x ∈ Icc ((((-169 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0122Lo = ((-169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0122Hi = ((-21 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0122Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0122Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0123 : ∀ x ∈ Icc ((((-21 : ℚ) / 32) : ℚ) : ℝ) ((((-83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0123Lo = ((-21 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0123Hi = ((-83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0123Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0123Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0124 : ∀ x ∈ Icc ((((-83 : ℚ) / 128) : ℚ) : ℝ) ((((-41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0124Lo = ((-83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0124Hi = ((-41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0124Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0124Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0125 : ∀ x ∈ Icc ((((-41 : ℚ) / 64) : ℚ) : ℝ) ((((-5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0125Lo = ((-41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0125Hi = ((-5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT2P0125Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0125Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0126 : ∀ x ∈ Icc ((((-5 : ℚ) / 8) : ℚ) : ℝ) ((((-39 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0126Lo = ((-5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT2P0126Hi = ((-39 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0126Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0126Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0127 : ∀ x ∈ Icc ((((-39 : ℚ) / 64) : ℚ) : ℝ) ((((-155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0127Lo = ((-39 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0127Hi = ((-155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0127Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0127Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock015 : ∀ x ∈ Icc ((((-43 : ℚ) / 64) : ℚ) : ℝ) ((((-155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0120 liftFrCWT2P0121) (cover_union liftFrCWT2P0122 liftFrCWT2P0123)) (cover_union (cover_union liftFrCWT2P0124 liftFrCWT2P0125) (cover_union liftFrCWT2P0126 liftFrCWT2P0127)))
#print axioms FrCWT2CoverBlock015

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

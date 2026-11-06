module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0185
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0186
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0187
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0188
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0189
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0190
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0191

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0184 : ∀ x ∈ Icc ((((-13 : ℚ) / 128) : ℚ) : ℝ) ((((-23 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0184Lo = ((-13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0184Hi = ((-23 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0184Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0184Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0185 : ∀ x ∈ Icc ((((-23 : ℚ) / 256) : ℚ) : ℝ) ((((-11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0185Lo = ((-23 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0185Hi = ((-11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0185Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0185Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0186 : ∀ x ∈ Icc ((((-11 : ℚ) / 128) : ℚ) : ℝ) ((((-19 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0186Lo = ((-11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0186Hi = ((-19 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0186Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0186Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0187 : ∀ x ∈ Icc ((((-19 : ℚ) / 256) : ℚ) : ℝ) ((((-9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0187Lo = ((-19 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0187Hi = ((-9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0187Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0187Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0188 : ∀ x ∈ Icc ((((-9 : ℚ) / 128) : ℚ) : ℝ) ((((-15 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0188Lo = ((-9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0188Hi = ((-15 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0188Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0188Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0189 : ∀ x ∈ Icc ((((-15 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0189Lo = ((-15 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0189Hi = ((-7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0189Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0189Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0190 : ∀ x ∈ Icc ((((-7 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0190Lo = ((-7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0190Hi = ((-11 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0190Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0190Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0191 : ∀ x ∈ Icc ((((-11 : ℚ) / 256) : ℚ) : ℝ) ((((-5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0191Lo = ((-11 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0191Hi = ((-5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0191Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0191Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock023 : ∀ x ∈ Icc ((((-13 : ℚ) / 128) : ℚ) : ℝ) ((((-5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0184 liftFrCWT2P0185) (cover_union liftFrCWT2P0186 liftFrCWT2P0187)) (cover_union (cover_union liftFrCWT2P0188 liftFrCWT2P0189) (cover_union liftFrCWT2P0190 liftFrCWT2P0191)))
#print axioms FrCWT2CoverBlock023

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

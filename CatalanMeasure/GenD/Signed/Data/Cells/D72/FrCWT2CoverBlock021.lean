module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0169
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0175

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0168 : ∀ x ∈ Icc ((((-29 : ℚ) / 128) : ℚ) : ℝ) ((((-55 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0168Lo = ((-29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0168Hi = ((-55 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0168Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0168Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0169 : ∀ x ∈ Icc ((((-55 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0169Lo = ((-55 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0169Hi = ((-27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0169Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0169Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0170 : ∀ x ∈ Icc ((((-27 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0170Lo = ((-27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0170Hi = ((-51 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0170Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0170Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0171 : ∀ x ∈ Icc ((((-51 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0171Lo = ((-51 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0171Hi = ((-25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0171Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0171Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0172 : ∀ x ∈ Icc ((((-25 : ℚ) / 128) : ℚ) : ℝ) ((((-47 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0172Lo = ((-25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0172Hi = ((-47 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0172Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0172Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0173 : ∀ x ∈ Icc ((((-47 : ℚ) / 256) : ℚ) : ℝ) ((((-23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0173Lo = ((-47 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0173Hi = ((-23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0173Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0173Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0174 : ∀ x ∈ Icc ((((-23 : ℚ) / 128) : ℚ) : ℝ) ((((-43 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0174Lo = ((-23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0174Hi = ((-43 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0174Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0174Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0175 : ∀ x ∈ Icc ((((-43 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0175Lo = ((-43 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0175Hi = ((-21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0175Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0175Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock021 : ∀ x ∈ Icc ((((-29 : ℚ) / 128) : ℚ) : ℝ) ((((-21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0168 liftFrCWT2P0169) (cover_union liftFrCWT2P0170 liftFrCWT2P0171)) (cover_union (cover_union liftFrCWT2P0172 liftFrCWT2P0173) (cover_union liftFrCWT2P0174 liftFrCWT2P0175)))
#print axioms FrCWT2CoverBlock021

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

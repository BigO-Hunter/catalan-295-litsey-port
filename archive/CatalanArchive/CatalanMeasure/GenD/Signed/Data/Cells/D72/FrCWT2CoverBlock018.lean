module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0144
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0151

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0144 : ∀ x ∈ Icc ((((-59 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0144Lo = ((-59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0144Hi = ((-29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0144Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0144Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0145 : ∀ x ∈ Icc ((((-29 : ℚ) / 64) : ℚ) : ℝ) ((((-55 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0145Lo = ((-29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0145Hi = ((-55 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0145Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0145Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0146 : ∀ x ∈ Icc ((((-55 : ℚ) / 128) : ℚ) : ℝ) ((((-107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0146Lo = ((-55 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0146Hi = ((-107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0146Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0146Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0147 : ∀ x ∈ Icc ((((-107 : ℚ) / 256) : ℚ) : ℝ) ((((-53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0147Lo = ((-107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0147Hi = ((-53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0147Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0147Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0148 : ∀ x ∈ Icc ((((-53 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0148Lo = ((-53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0148Hi = ((-51 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0148Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0148Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0149 : ∀ x ∈ Icc ((((-51 : ℚ) / 128) : ℚ) : ℝ) ((((-101 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0149Lo = ((-51 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0149Hi = ((-101 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0149Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0149Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0150 : ∀ x ∈ Icc ((((-101 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0150Lo = ((-101 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0150Hi = ((-25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0150Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0150Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0151 : ∀ x ∈ Icc ((((-25 : ℚ) / 64) : ℚ) : ℝ) ((((-97 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0151Lo = ((-25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0151Hi = ((-97 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0151Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0151Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock018 : ∀ x ∈ Icc ((((-59 : ℚ) / 128) : ℚ) : ℝ) ((((-97 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0144 liftFrCWT2P0145) (cover_union liftFrCWT2P0146 liftFrCWT2P0147)) (cover_union (cover_union liftFrCWT2P0148 liftFrCWT2P0149) (cover_union liftFrCWT2P0150 liftFrCWT2P0151)))
#print axioms FrCWT2CoverBlock018

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

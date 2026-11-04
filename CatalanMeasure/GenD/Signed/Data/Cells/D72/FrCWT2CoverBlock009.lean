module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0079

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0072 : ∀ x ∈ Icc ((((-61 : ℚ) / 64) : ℚ) : ℝ) ((((-121 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0072Lo = ((-61 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0072Hi = ((-121 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0072Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0072Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0073 : ∀ x ∈ Icc ((((-121 : ℚ) / 128) : ℚ) : ℝ) ((((-483 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0073Lo = ((-121 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0073Hi = ((-483 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0073Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0073Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0074 : ∀ x ∈ Icc ((((-483 : ℚ) / 512) : ℚ) : ℝ) ((((-481 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0074Lo = ((-483 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0074Hi = ((-481 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0074Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0074Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0075 : ∀ x ∈ Icc ((((-481 : ℚ) / 512) : ℚ) : ℝ) ((((-15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0075Lo = ((-481 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0075Hi = ((-15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0075Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0075Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0076 : ∀ x ∈ Icc ((((-15 : ℚ) / 16) : ℚ) : ℝ) ((((-477 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0076Lo = ((-15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0076Hi = ((-477 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0076Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0076Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0077 : ∀ x ∈ Icc ((((-477 : ℚ) / 512) : ℚ) : ℝ) ((((-119 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0077Lo = ((-477 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0077Hi = ((-119 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0077Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0077Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0078 : ∀ x ∈ Icc ((((-119 : ℚ) / 128) : ℚ) : ℝ) ((((-237 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0078Lo = ((-119 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0078Hi = ((-237 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0078Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0078Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0079 : ∀ x ∈ Icc ((((-237 : ℚ) / 256) : ℚ) : ℝ) ((((-235 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0079Lo = ((-237 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0079Hi = ((-235 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0079Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0079Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock009 : ∀ x ∈ Icc ((((-61 : ℚ) / 64) : ℚ) : ℝ) ((((-235 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0072 liftFrCWT2P0073) (cover_union liftFrCWT2P0074 liftFrCWT2P0075)) (cover_union (cover_union liftFrCWT2P0076 liftFrCWT2P0077) (cover_union liftFrCWT2P0078 liftFrCWT2P0079)))
#print axioms FrCWT2CoverBlock009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

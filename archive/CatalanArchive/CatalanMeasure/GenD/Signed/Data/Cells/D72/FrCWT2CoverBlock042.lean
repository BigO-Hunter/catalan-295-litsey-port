module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0336
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0337
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0338
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0339
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0340
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0341
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0342
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0343

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0336 : ∀ x ∈ Icc ((((213 : ℚ) / 256) : ℚ) : ℝ) ((((107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0336Lo = ((213 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0336Hi = ((107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0336Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0336Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0337 : ∀ x ∈ Icc ((((107 : ℚ) / 128) : ℚ) : ℝ) ((((429 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0337Lo = ((107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0337Hi = ((429 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0337Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0337Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0338 : ∀ x ∈ Icc ((((429 : ℚ) / 512) : ℚ) : ℝ) ((((859 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0338Lo = ((429 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0338Hi = ((859 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0338Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0338Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0339 : ∀ x ∈ Icc ((((859 : ℚ) / 1024) : ℚ) : ℝ) ((((215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0339Lo = ((859 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0339Hi = ((215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0339Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0339Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0340 : ∀ x ∈ Icc ((((215 : ℚ) / 256) : ℚ) : ℝ) ((((433 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0340Lo = ((215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0340Hi = ((433 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0340Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0340Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0341 : ∀ x ∈ Icc ((((433 : ℚ) / 512) : ℚ) : ℝ) ((((217 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0341Lo = ((433 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0341Hi = ((217 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0341Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0341Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0342 : ∀ x ∈ Icc ((((217 : ℚ) / 256) : ℚ) : ℝ) ((((437 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0342Lo = ((217 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0342Hi = ((437 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0342Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0342Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0343 : ∀ x ∈ Icc ((((437 : ℚ) / 512) : ℚ) : ℝ) ((((875 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0343Lo = ((437 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0343Hi = ((875 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0343Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0343Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock042 : ∀ x ∈ Icc ((((213 : ℚ) / 256) : ℚ) : ℝ) ((((875 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0336 liftFrCWT2P0337) (cover_union liftFrCWT2P0338 liftFrCWT2P0339)) (cover_union (cover_union liftFrCWT2P0340 liftFrCWT2P0341) (cover_union liftFrCWT2P0342 liftFrCWT2P0343)))
#print axioms FrCWT2CoverBlock042

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

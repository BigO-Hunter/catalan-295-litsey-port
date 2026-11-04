module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0320
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0321
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0322
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0323
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0324
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0325
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0326
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0327

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0320 : ∀ x ∈ Icc ((((195 : ℚ) / 256) : ℚ) : ℝ) ((((49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0320Lo = ((195 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0320Hi = ((49 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0320Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0320Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0321 : ∀ x ∈ Icc ((((49 : ℚ) / 64) : ℚ) : ℝ) ((((25 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0321Lo = ((49 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0321Hi = ((25 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0321Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0321Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0322 : ∀ x ∈ Icc ((((25 : ℚ) / 32) : ℚ) : ℝ) ((((201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0322Lo = ((25 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0322Hi = ((201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0322Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0322Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0323 : ∀ x ∈ Icc ((((201 : ℚ) / 256) : ℚ) : ℝ) ((((101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0323Lo = ((201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0323Hi = ((101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0323Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0323Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0324 : ∀ x ∈ Icc ((((101 : ℚ) / 128) : ℚ) : ℝ) ((((51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0324Lo = ((101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0324Hi = ((51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0324Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0324Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0325 : ∀ x ∈ Icc ((((51 : ℚ) / 64) : ℚ) : ℝ) ((((205 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0325Lo = ((51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0325Hi = ((205 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0325Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0325Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0326 : ∀ x ∈ Icc ((((205 : ℚ) / 256) : ℚ) : ℝ) ((((103 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0326Lo = ((205 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0326Hi = ((103 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0326Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0326Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0327 : ∀ x ∈ Icc ((((103 : ℚ) / 128) : ℚ) : ℝ) ((((415 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0327Lo = ((103 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0327Hi = ((415 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0327Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0327Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock040 : ∀ x ∈ Icc ((((195 : ℚ) / 256) : ℚ) : ℝ) ((((415 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0320 liftFrCWT2P0321) (cover_union liftFrCWT2P0322 liftFrCWT2P0323)) (cover_union (cover_union liftFrCWT2P0324 liftFrCWT2P0325) (cover_union liftFrCWT2P0326 liftFrCWT2P0327)))
#print axioms FrCWT2CoverBlock040

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0320
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0321
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0322
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0323
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0324
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0325
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0326
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0327

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0320 : ∀ x ∈ Icc ((((183 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0320Lo = ((183 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0320Hi = ((23 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0320Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0320Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0321 : ∀ x ∈ Icc ((((23 : ℚ) / 32) : ℚ) : ℝ) ((((369 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0321Lo = ((23 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0321Hi = ((369 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0321Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0321Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0322 : ∀ x ∈ Icc ((((369 : ℚ) / 512) : ℚ) : ℝ) ((((185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0322Lo = ((369 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0322Hi = ((185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0322Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0322Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0323 : ∀ x ∈ Icc ((((185 : ℚ) / 256) : ℚ) : ℝ) ((((187 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0323Lo = ((185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0323Hi = ((187 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0323Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0323Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0324 : ∀ x ∈ Icc ((((187 : ℚ) / 256) : ℚ) : ℝ) ((((47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0324Lo = ((187 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0324Hi = ((47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0324Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0324Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0325 : ∀ x ∈ Icc ((((47 : ℚ) / 64) : ℚ) : ℝ) ((((189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0325Lo = ((47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0325Hi = ((189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0325Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0325Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0326 : ∀ x ∈ Icc ((((189 : ℚ) / 256) : ℚ) : ℝ) ((((95 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0326Lo = ((189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0326Hi = ((95 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0326Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0326Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0327 : ∀ x ∈ Icc ((((95 : ℚ) / 128) : ℚ) : ℝ) ((((381 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0327Lo = ((95 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0327Hi = ((381 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0327Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0327Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock040 : ∀ x ∈ Icc ((((183 : ℚ) / 256) : ℚ) : ℝ) ((((381 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0320 liftFrCWT1P0321) (cover_union liftFrCWT1P0322 liftFrCWT1P0323)) (cover_union (cover_union liftFrCWT1P0324 liftFrCWT1P0325) (cover_union liftFrCWT1P0326 liftFrCWT1P0327)))
#print axioms FrCWT1CoverBlock040

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

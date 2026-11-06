module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0376
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0377
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0378
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0379
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0380
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0381
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0382

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0376 : ∀ x ∈ Icc ((((229 : ℚ) / 256) : ℚ) : ℝ) ((((115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0376Lo = ((229 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0376Hi = ((115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0376Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0376Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0377 : ∀ x ∈ Icc ((((115 : ℚ) / 128) : ℚ) : ℝ) ((((231 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0377Lo = ((115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0377Hi = ((231 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0377Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0377Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0378 : ∀ x ∈ Icc ((((231 : ℚ) / 256) : ℚ) : ℝ) ((((29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0378Lo = ((231 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0378Hi = ((29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0378Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0378Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0379 : ∀ x ∈ Icc ((((29 : ℚ) / 32) : ℚ) : ℝ) ((((59 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0379Lo = ((29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0379Hi = ((59 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0379Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0379Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0380 : ∀ x ∈ Icc ((((59 : ℚ) / 64) : ℚ) : ℝ) ((((15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0380Lo = ((59 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0380Hi = ((15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0380Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0380Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0381 : ∀ x ∈ Icc ((((15 : ℚ) / 16) : ℚ) : ℝ) ((((31 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0381Lo = ((15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0381Hi = ((31 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0381Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0381Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0382 : ∀ x ∈ Icc ((((31 : ℚ) / 32) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0382Lo = ((31 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0382Hi = ((1 : ℚ) / 1) := by decide +kernel
  have hcap : FrCWT1P0382Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0382Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock047 : ∀ x ∈ Icc ((((229 : ℚ) / 256) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union liftFrCWT1P0376 (cover_union liftFrCWT1P0377 liftFrCWT1P0378)) (cover_union (cover_union liftFrCWT1P0379 liftFrCWT1P0380) (cover_union liftFrCWT1P0381 liftFrCWT1P0382)))
#print axioms FrCWT1CoverBlock047

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

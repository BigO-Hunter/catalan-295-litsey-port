module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0368
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0369
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0370
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0371
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0372
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0373
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0374
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0375

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0368 : ∀ x ∈ Icc ((((225 : ℚ) / 256) : ℚ) : ℝ) ((((113 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0368Lo = ((225 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0368Hi = ((113 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0368Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0368Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0369 : ∀ x ∈ Icc ((((113 : ℚ) / 128) : ℚ) : ℝ) ((((453 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0369Lo = ((113 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0369Hi = ((453 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0369Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0369Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0370 : ∀ x ∈ Icc ((((453 : ℚ) / 512) : ℚ) : ℝ) ((((907 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0370Lo = ((453 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0370Hi = ((907 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0370Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0370Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0371 : ∀ x ∈ Icc ((((907 : ℚ) / 1024) : ℚ) : ℝ) ((((227 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0371Lo = ((907 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0371Hi = ((227 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0371Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0371Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0372 : ∀ x ∈ Icc ((((227 : ℚ) / 256) : ℚ) : ℝ) ((((913 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0372Lo = ((227 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0372Hi = ((913 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0372Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0372Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0373 : ∀ x ∈ Icc ((((913 : ℚ) / 1024) : ℚ) : ℝ) ((((457 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0373Lo = ((913 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0373Hi = ((457 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0373Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0373Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0374 : ∀ x ∈ Icc ((((457 : ℚ) / 512) : ℚ) : ℝ) ((((915 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0374Lo = ((457 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0374Hi = ((915 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0374Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0374Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0375 : ∀ x ∈ Icc ((((915 : ℚ) / 1024) : ℚ) : ℝ) ((((229 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0375Lo = ((915 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0375Hi = ((229 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0375Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0375Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock046 : ∀ x ∈ Icc ((((225 : ℚ) / 256) : ℚ) : ℝ) ((((229 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0368 liftFrCWT1P0369) (cover_union liftFrCWT1P0370 liftFrCWT1P0371)) (cover_union (cover_union liftFrCWT1P0372 liftFrCWT1P0373) (cover_union liftFrCWT1P0374 liftFrCWT1P0375)))
#print axioms FrCWT1CoverBlock046

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

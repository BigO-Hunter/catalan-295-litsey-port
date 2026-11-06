module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0368
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0369
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0370
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0371
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0372
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0373
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0374
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0375

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0368 : ∀ x ∈ Icc ((((899 : ℚ) / 1024) : ℚ) : ℝ) ((((225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0368Lo = ((899 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0368Hi = ((225 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0368Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0368Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0369 : ∀ x ∈ Icc ((((225 : ℚ) / 256) : ℚ) : ℝ) ((((451 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0369Lo = ((225 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0369Hi = ((451 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0369Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0369Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0370 : ∀ x ∈ Icc ((((451 : ℚ) / 512) : ℚ) : ℝ) ((((453 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0370Lo = ((451 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0370Hi = ((453 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0370Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0370Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0371 : ∀ x ∈ Icc ((((453 : ℚ) / 512) : ℚ) : ℝ) ((((227 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0371Lo = ((453 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0371Hi = ((227 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0371Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0371Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0372 : ∀ x ∈ Icc ((((227 : ℚ) / 256) : ℚ) : ℝ) ((((913 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0372Lo = ((227 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0372Hi = ((913 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0372Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0372Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0373 : ∀ x ∈ Icc ((((913 : ℚ) / 1024) : ℚ) : ℝ) ((((915 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0373Lo = ((913 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0373Hi = ((915 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0373Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0373Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0374 : ∀ x ∈ Icc ((((915 : ℚ) / 1024) : ℚ) : ℝ) ((((229 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0374Lo = ((915 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0374Hi = ((229 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0374Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0374Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0375 : ∀ x ∈ Icc ((((229 : ℚ) / 256) : ℚ) : ℝ) ((((115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0375Lo = ((229 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0375Hi = ((115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0375Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0375Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock046 : ∀ x ∈ Icc ((((899 : ℚ) / 1024) : ℚ) : ℝ) ((((115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0368 liftFrCWT0P0369) (cover_union liftFrCWT0P0370 liftFrCWT0P0371)) (cover_union (cover_union liftFrCWT0P0372 liftFrCWT0P0373) (cover_union liftFrCWT0P0374 liftFrCWT0P0375)))
#print axioms FrCWT0CoverBlock046

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

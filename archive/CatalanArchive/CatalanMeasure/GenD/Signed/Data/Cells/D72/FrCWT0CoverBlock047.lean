module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0376
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0377
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0378
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0379
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0380
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0381

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0376 : ∀ x ∈ Icc ((((115 : ℚ) / 128) : ℚ) : ℝ) ((((231 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0376Lo = ((115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0376Hi = ((231 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0376Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0376Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0377 : ∀ x ∈ Icc ((((231 : ℚ) / 256) : ℚ) : ℝ) ((((29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0377Lo = ((231 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0377Hi = ((29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0377Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0377Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0378 : ∀ x ∈ Icc ((((29 : ℚ) / 32) : ℚ) : ℝ) ((((117 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0378Lo = ((29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0378Hi = ((117 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0378Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0378Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0379 : ∀ x ∈ Icc ((((117 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0379Lo = ((117 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0379Hi = ((15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0379Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0379Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0380 : ∀ x ∈ Icc ((((15 : ℚ) / 16) : ℚ) : ℝ) ((((31 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0380Lo = ((15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0380Hi = ((31 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0380Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0380Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0381 : ∀ x ∈ Icc ((((31 : ℚ) / 32) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0381Lo = ((31 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0381Hi = ((1 : ℚ) / 1) := by decide +kernel
  have hcap : FrCWT0P0381Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0381Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock047 : ∀ x ∈ Icc ((((115 : ℚ) / 128) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union liftFrCWT0P0376 (cover_union liftFrCWT0P0377 liftFrCWT0P0378)) (cover_union liftFrCWT0P0379 (cover_union liftFrCWT0P0380 liftFrCWT0P0381)))
#print axioms FrCWT0CoverBlock047

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

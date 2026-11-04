module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0328
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0329
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0330
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0331
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0332
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0333
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0334
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0335

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0328 : ∀ x ∈ Icc ((((47 : ℚ) / 64) : ℚ) : ℝ) ((((189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0328Lo = ((47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0328Hi = ((189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0328Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0328Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0329 : ∀ x ∈ Icc ((((189 : ℚ) / 256) : ℚ) : ℝ) ((((95 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0329Lo = ((189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0329Hi = ((95 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0329Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0329Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0330 : ∀ x ∈ Icc ((((95 : ℚ) / 128) : ℚ) : ℝ) ((((381 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0330Lo = ((95 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0330Hi = ((381 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0330Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0330Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0331 : ∀ x ∈ Icc ((((381 : ℚ) / 512) : ℚ) : ℝ) ((((385 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0331Lo = ((381 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0331Hi = ((385 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0331Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0331Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0332 : ∀ x ∈ Icc ((((385 : ℚ) / 512) : ℚ) : ℝ) ((((193 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0332Lo = ((385 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0332Hi = ((193 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0332Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0332Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0333 : ∀ x ∈ Icc ((((193 : ℚ) / 256) : ℚ) : ℝ) ((((97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0333Lo = ((193 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0333Hi = ((97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0333Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0333Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0334 : ∀ x ∈ Icc ((((97 : ℚ) / 128) : ℚ) : ℝ) ((((195 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0334Lo = ((97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0334Hi = ((195 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0334Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0334Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0335 : ∀ x ∈ Icc ((((195 : ℚ) / 256) : ℚ) : ℝ) ((((49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0335Lo = ((195 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0335Hi = ((49 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0335Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0335Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock041 : ∀ x ∈ Icc ((((47 : ℚ) / 64) : ℚ) : ℝ) ((((49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0328 liftFrCWT0P0329) (cover_union liftFrCWT0P0330 liftFrCWT0P0331)) (cover_union (cover_union liftFrCWT0P0332 liftFrCWT0P0333) (cover_union liftFrCWT0P0334 liftFrCWT0P0335)))
#print axioms FrCWT0CoverBlock041

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

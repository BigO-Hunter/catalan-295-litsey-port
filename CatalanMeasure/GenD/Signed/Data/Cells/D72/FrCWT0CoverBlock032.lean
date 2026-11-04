module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0256
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0257
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0258
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0259
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0260
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0261
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0262
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0263

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0256 : ∀ x ∈ Icc ((((47 : ℚ) / 128) : ℚ) : ℝ) ((((95 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0256Lo = ((47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0256Hi = ((95 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0256Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0256Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0257 : ∀ x ∈ Icc ((((95 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0257Lo = ((95 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0257Hi = ((3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT0P0257Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0257Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0258 : ∀ x ∈ Icc ((((3 : ℚ) / 8) : ℚ) : ℝ) ((((49 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0258Lo = ((3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT0P0258Hi = ((49 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0258Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0258Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0259 : ∀ x ∈ Icc ((((49 : ℚ) / 128) : ℚ) : ℝ) ((((99 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0259Lo = ((49 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0259Hi = ((99 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0259Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0259Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0260 : ∀ x ∈ Icc ((((99 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0260Lo = ((99 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0260Hi = ((25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0260Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0260Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0261 : ∀ x ∈ Icc ((((25 : ℚ) / 64) : ℚ) : ℝ) ((((51 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0261Lo = ((25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0261Hi = ((51 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0261Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0261Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0262 : ∀ x ∈ Icc ((((51 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0262Lo = ((51 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0262Hi = ((13 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0262Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0262Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0263 : ∀ x ∈ Icc ((((13 : ℚ) / 32) : ℚ) : ℝ) ((((53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0263Lo = ((13 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0263Hi = ((53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0263Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0263Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock032 : ∀ x ∈ Icc ((((47 : ℚ) / 128) : ℚ) : ℝ) ((((53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0256 liftFrCWT0P0257) (cover_union liftFrCWT0P0258 liftFrCWT0P0259)) (cover_union (cover_union liftFrCWT0P0260 liftFrCWT0P0261) (cover_union liftFrCWT0P0262 liftFrCWT0P0263)))
#print axioms FrCWT0CoverBlock032

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

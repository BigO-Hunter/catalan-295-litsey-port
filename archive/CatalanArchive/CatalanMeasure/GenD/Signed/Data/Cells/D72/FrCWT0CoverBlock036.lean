module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0288
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0289
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0290
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0291
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0292
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0293
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0294
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0295

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0288 : ∀ x ∈ Icc ((((71 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0288Lo = ((71 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0288Hi = ((9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0288Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0288Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0289 : ∀ x ∈ Icc ((((9 : ℚ) / 16) : ℚ) : ℝ) ((((73 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0289Lo = ((9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0289Hi = ((73 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0289Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0289Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0290 : ∀ x ∈ Icc ((((73 : ℚ) / 128) : ℚ) : ℝ) ((((147 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0290Lo = ((73 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0290Hi = ((147 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0290Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0290Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0291 : ∀ x ∈ Icc ((((147 : ℚ) / 256) : ℚ) : ℝ) ((((37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0291Lo = ((147 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0291Hi = ((37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0291Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0291Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0292 : ∀ x ∈ Icc ((((37 : ℚ) / 64) : ℚ) : ℝ) ((((297 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0292Lo = ((37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0292Hi = ((297 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0292Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0292Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0293 : ∀ x ∈ Icc ((((297 : ℚ) / 512) : ℚ) : ℝ) ((((75 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0293Lo = ((297 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0293Hi = ((75 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0293Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0293Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0294 : ∀ x ∈ Icc ((((75 : ℚ) / 128) : ℚ) : ℝ) ((((151 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0294Lo = ((75 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0294Hi = ((151 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0294Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0294Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0295 : ∀ x ∈ Icc ((((151 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0295Lo = ((151 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0295Hi = ((19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0295Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0295Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock036 : ∀ x ∈ Icc ((((71 : ℚ) / 128) : ℚ) : ℝ) ((((19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0288 liftFrCWT0P0289) (cover_union liftFrCWT0P0290 liftFrCWT0P0291)) (cover_union (cover_union liftFrCWT0P0292 liftFrCWT0P0293) (cover_union liftFrCWT0P0294 liftFrCWT0P0295)))
#print axioms FrCWT0CoverBlock036

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

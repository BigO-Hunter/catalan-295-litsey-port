module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0360
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0361
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0362
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0363
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0364
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0365
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0366
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0367

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0360 : ∀ x ∈ Icc ((((219 : ℚ) / 256) : ℚ) : ℝ) ((((439 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0360Lo = ((219 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0360Hi = ((439 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0360Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0360Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0361 : ∀ x ∈ Icc ((((439 : ℚ) / 512) : ℚ) : ℝ) ((((441 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0361Lo = ((439 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0361Hi = ((441 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0361Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0361Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0362 : ∀ x ∈ Icc ((((441 : ℚ) / 512) : ℚ) : ℝ) ((((221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0362Lo = ((441 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0362Hi = ((221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0362Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0362Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0363 : ∀ x ∈ Icc ((((221 : ℚ) / 256) : ℚ) : ℝ) ((((111 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0363Lo = ((221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0363Hi = ((111 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0363Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0363Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0364 : ∀ x ∈ Icc ((((111 : ℚ) / 128) : ℚ) : ℝ) ((((891 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0364Lo = ((111 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0364Hi = ((891 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0364Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0364Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0365 : ∀ x ∈ Icc ((((891 : ℚ) / 1024) : ℚ) : ℝ) ((((893 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0365Lo = ((891 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0365Hi = ((893 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0365Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0365Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0366 : ∀ x ∈ Icc ((((893 : ℚ) / 1024) : ℚ) : ℝ) ((((449 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0366Lo = ((893 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0366Hi = ((449 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0366Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0366Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0367 : ∀ x ∈ Icc ((((449 : ℚ) / 512) : ℚ) : ℝ) ((((899 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0367Lo = ((449 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0367Hi = ((899 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0367Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0367Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock045 : ∀ x ∈ Icc ((((219 : ℚ) / 256) : ℚ) : ℝ) ((((899 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0360 liftFrCWT0P0361) (cover_union liftFrCWT0P0362 liftFrCWT0P0363)) (cover_union (cover_union liftFrCWT0P0364 liftFrCWT0P0365) (cover_union liftFrCWT0P0366 liftFrCWT0P0367)))
#print axioms FrCWT0CoverBlock045

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

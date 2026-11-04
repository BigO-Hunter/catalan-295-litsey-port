module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0312
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0313
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0314
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0315
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0316
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0317
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0318
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0319

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0312 : ∀ x ∈ Icc ((((341 : ℚ) / 512) : ℚ) : ℝ) ((((43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0312Lo = ((341 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0312Hi = ((43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0312Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0312Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0313 : ∀ x ∈ Icc ((((43 : ℚ) / 64) : ℚ) : ℝ) ((((173 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0313Lo = ((43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0313Hi = ((173 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0313Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0313Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0314 : ∀ x ∈ Icc ((((173 : ℚ) / 256) : ℚ) : ℝ) ((((347 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0314Lo = ((173 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0314Hi = ((347 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0314Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0314Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0315 : ∀ x ∈ Icc ((((347 : ℚ) / 512) : ℚ) : ℝ) ((((175 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0315Lo = ((347 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0315Hi = ((175 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0315Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0315Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0316 : ∀ x ∈ Icc ((((175 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0316Lo = ((175 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0316Hi = ((11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0316Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0316Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0317 : ∀ x ∈ Icc ((((11 : ℚ) / 16) : ℚ) : ℝ) ((((353 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0317Lo = ((11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0317Hi = ((353 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0317Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0317Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0318 : ∀ x ∈ Icc ((((353 : ℚ) / 512) : ℚ) : ℝ) ((((89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0318Lo = ((353 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0318Hi = ((89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0318Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0318Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0319 : ∀ x ∈ Icc ((((89 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0319Lo = ((89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0319Hi = ((45 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0319Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0319Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock039 : ∀ x ∈ Icc ((((341 : ℚ) / 512) : ℚ) : ℝ) ((((45 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0312 liftFrCWT0P0313) (cover_union liftFrCWT0P0314 liftFrCWT0P0315)) (cover_union (cover_union liftFrCWT0P0316 liftFrCWT0P0317) (cover_union liftFrCWT0P0318 liftFrCWT0P0319)))
#print axioms FrCWT0CoverBlock039

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

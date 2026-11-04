module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0248
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0249
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0250
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0251
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0252
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0253
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0254
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0255

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0248 : ∀ x ∈ Icc ((((41 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0248Lo = ((41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0248Hi = ((21 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0248Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0248Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0249 : ∀ x ∈ Icc ((((21 : ℚ) / 64) : ℚ) : ℝ) ((((85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0249Lo = ((21 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0249Hi = ((85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0249Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0249Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0250 : ∀ x ∈ Icc ((((85 : ℚ) / 256) : ℚ) : ℝ) ((((43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0250Lo = ((85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0250Hi = ((43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0250Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0250Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0251 : ∀ x ∈ Icc ((((43 : ℚ) / 128) : ℚ) : ℝ) ((((11 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0251Lo = ((43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0251Hi = ((11 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0251Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0251Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0252 : ∀ x ∈ Icc ((((11 : ℚ) / 32) : ℚ) : ℝ) ((((89 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0252Lo = ((11 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0252Hi = ((89 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0252Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0252Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0253 : ∀ x ∈ Icc ((((89 : ℚ) / 256) : ℚ) : ℝ) ((((91 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0253Lo = ((89 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0253Hi = ((91 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0253Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0253Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0254 : ∀ x ∈ Icc ((((91 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0254Lo = ((91 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0254Hi = ((23 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0254Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0254Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0255 : ∀ x ∈ Icc ((((23 : ℚ) / 64) : ℚ) : ℝ) ((((47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0255Lo = ((23 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0255Hi = ((47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0255Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0255Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock031 : ∀ x ∈ Icc ((((41 : ℚ) / 128) : ℚ) : ℝ) ((((47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0248 liftFrCWT0P0249) (cover_union liftFrCWT0P0250 liftFrCWT0P0251)) (cover_union (cover_union liftFrCWT0P0252 liftFrCWT0P0253) (cover_union liftFrCWT0P0254 liftFrCWT0P0255)))
#print axioms FrCWT0CoverBlock031

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

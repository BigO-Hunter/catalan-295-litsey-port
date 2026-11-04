module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0272
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0273
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0274
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0275
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0276
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0277
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0278
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0279

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0272 : ∀ x ∈ Icc ((((59 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0272Lo = ((59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0272Hi = ((15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0272Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0272Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0273 : ∀ x ∈ Icc ((((15 : ℚ) / 32) : ℚ) : ℝ) ((((61 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0273Lo = ((15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0273Hi = ((61 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0273Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0273Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0274 : ∀ x ∈ Icc ((((61 : ℚ) / 128) : ℚ) : ℝ) ((((31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0274Lo = ((61 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0274Hi = ((31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0274Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0274Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0275 : ∀ x ∈ Icc ((((31 : ℚ) / 64) : ℚ) : ℝ) ((((125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0275Lo = ((31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0275Hi = ((125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0275Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0275Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0276 : ∀ x ∈ Icc ((((125 : ℚ) / 256) : ℚ) : ℝ) ((((255 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0276Lo = ((125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0276Hi = ((255 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0276Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0276Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0277 : ∀ x ∈ Icc ((((255 : ℚ) / 512) : ℚ) : ℝ) ((((1 : ℚ) / 2) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0277Lo = ((255 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0277Hi = ((1 : ℚ) / 2) := by decide +kernel
  have hcap : FrCWT0P0277Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0277Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0278 : ∀ x ∈ Icc ((((1 : ℚ) / 2) : ℚ) : ℝ) ((((129 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0278Lo = ((1 : ℚ) / 2) := by decide +kernel
  have hhi : ceFrCWT0P0278Hi = ((129 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0278Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0278Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0279 : ∀ x ∈ Icc ((((129 : ℚ) / 256) : ℚ) : ℝ) ((((131 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0279Lo = ((129 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0279Hi = ((131 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0279Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0279Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock034 : ∀ x ∈ Icc ((((59 : ℚ) / 128) : ℚ) : ℝ) ((((131 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0272 liftFrCWT0P0273) (cover_union liftFrCWT0P0274 liftFrCWT0P0275)) (cover_union (cover_union liftFrCWT0P0276 liftFrCWT0P0277) (cover_union liftFrCWT0P0278 liftFrCWT0P0279)))
#print axioms FrCWT0CoverBlock034

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

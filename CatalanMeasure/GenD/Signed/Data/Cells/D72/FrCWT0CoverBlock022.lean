module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0176
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0177
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0178
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0179
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0180
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0181
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0182
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0183

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0176 : ∀ x ∈ Icc ((((-15 : ℚ) / 64) : ℚ) : ℝ) ((((-59 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0176Lo = ((-15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0176Hi = ((-59 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0176Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0176Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0177 : ∀ x ∈ Icc ((((-59 : ℚ) / 256) : ℚ) : ℝ) ((((-29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0177Lo = ((-59 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0177Hi = ((-29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0177Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0177Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0178 : ∀ x ∈ Icc ((((-29 : ℚ) / 128) : ℚ) : ℝ) ((((-55 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0178Lo = ((-29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0178Hi = ((-55 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0178Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0178Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0179 : ∀ x ∈ Icc ((((-55 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0179Lo = ((-55 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0179Hi = ((-27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0179Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0179Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0180 : ∀ x ∈ Icc ((((-27 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0180Lo = ((-27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0180Hi = ((-51 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0180Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0180Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0181 : ∀ x ∈ Icc ((((-51 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0181Lo = ((-51 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0181Hi = ((-25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0181Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0181Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0182 : ∀ x ∈ Icc ((((-25 : ℚ) / 128) : ℚ) : ℝ) ((((-47 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0182Lo = ((-25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0182Hi = ((-47 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0182Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0182Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0183 : ∀ x ∈ Icc ((((-47 : ℚ) / 256) : ℚ) : ℝ) ((((-23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0183Lo = ((-47 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0183Hi = ((-23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0183Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0183Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock022 : ∀ x ∈ Icc ((((-15 : ℚ) / 64) : ℚ) : ℝ) ((((-23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0176 liftFrCWT0P0177) (cover_union liftFrCWT0P0178 liftFrCWT0P0179)) (cover_union (cover_union liftFrCWT0P0180 liftFrCWT0P0181) (cover_union liftFrCWT0P0182 liftFrCWT0P0183)))
#print axioms FrCWT0CoverBlock022

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

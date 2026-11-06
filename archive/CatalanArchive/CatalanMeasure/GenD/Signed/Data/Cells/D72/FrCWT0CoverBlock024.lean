module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0192
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0193
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0194
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0195
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0196
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0197
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0198
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0199

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0192 : ∀ x ∈ Icc ((((-15 : ℚ) / 128) : ℚ) : ℝ) ((((-27 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0192Lo = ((-15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0192Hi = ((-27 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0192Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0192Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0193 : ∀ x ∈ Icc ((((-27 : ℚ) / 256) : ℚ) : ℝ) ((((-13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0193Lo = ((-27 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0193Hi = ((-13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0193Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0193Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0194 : ∀ x ∈ Icc ((((-13 : ℚ) / 128) : ℚ) : ℝ) ((((-23 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0194Lo = ((-13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0194Hi = ((-23 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0194Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0194Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0195 : ∀ x ∈ Icc ((((-23 : ℚ) / 256) : ℚ) : ℝ) ((((-11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0195Lo = ((-23 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0195Hi = ((-11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0195Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0195Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0196 : ∀ x ∈ Icc ((((-11 : ℚ) / 128) : ℚ) : ℝ) ((((-19 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0196Lo = ((-11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0196Hi = ((-19 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0196Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0196Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0197 : ∀ x ∈ Icc ((((-19 : ℚ) / 256) : ℚ) : ℝ) ((((-9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0197Lo = ((-19 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0197Hi = ((-9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0197Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0197Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0198 : ∀ x ∈ Icc ((((-9 : ℚ) / 128) : ℚ) : ℝ) ((((-15 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0198Lo = ((-9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0198Hi = ((-15 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0198Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0198Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0199 : ∀ x ∈ Icc ((((-15 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0199Lo = ((-15 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0199Hi = ((-7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0199Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0199Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock024 : ∀ x ∈ Icc ((((-15 : ℚ) / 128) : ℚ) : ℝ) ((((-7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0192 liftFrCWT0P0193) (cover_union liftFrCWT0P0194 liftFrCWT0P0195)) (cover_union (cover_union liftFrCWT0P0196 liftFrCWT0P0197) (cover_union liftFrCWT0P0198 liftFrCWT0P0199)))
#print axioms FrCWT0CoverBlock024

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0232
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0233
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0234
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0235
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0236
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0237
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0238
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0239

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0232 : ∀ x ∈ Icc ((((25 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0232Lo = ((25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0232Hi = ((13 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0232Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0232Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0233 : ∀ x ∈ Icc ((((13 : ℚ) / 64) : ℚ) : ℝ) ((((53 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0233Lo = ((13 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0233Hi = ((53 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0233Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0233Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0234 : ∀ x ∈ Icc ((((53 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0234Lo = ((53 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0234Hi = ((27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0234Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0234Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0235 : ∀ x ∈ Icc ((((27 : ℚ) / 128) : ℚ) : ℝ) ((((7 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0235Lo = ((27 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0235Hi = ((7 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0235Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0235Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0236 : ∀ x ∈ Icc ((((7 : ℚ) / 32) : ℚ) : ℝ) ((((29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0236Lo = ((7 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0236Hi = ((29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0236Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0236Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0237 : ∀ x ∈ Icc ((((29 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0237Lo = ((29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0237Hi = ((15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0237Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0237Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0238 : ∀ x ∈ Icc ((((15 : ℚ) / 64) : ℚ) : ℝ) ((((31 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0238Lo = ((15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0238Hi = ((31 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0238Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0238Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0239 : ∀ x ∈ Icc ((((31 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0239Lo = ((31 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0239Hi = ((17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0239Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0239Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock029 : ∀ x ∈ Icc ((((25 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0232 liftFrCWT0P0233) (cover_union liftFrCWT0P0234 liftFrCWT0P0235)) (cover_union (cover_union liftFrCWT0P0236 liftFrCWT0P0237) (cover_union liftFrCWT0P0238 liftFrCWT0P0239)))
#print axioms FrCWT0CoverBlock029

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

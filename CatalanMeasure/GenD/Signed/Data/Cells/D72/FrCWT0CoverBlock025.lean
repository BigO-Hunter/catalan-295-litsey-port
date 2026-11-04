module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0200
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0201
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0207

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0200 : ∀ x ∈ Icc ((((-7 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0200Lo = ((-7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0200Hi = ((-11 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0200Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0200Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0201 : ∀ x ∈ Icc ((((-11 : ℚ) / 256) : ℚ) : ℝ) ((((-5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0201Lo = ((-11 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0201Hi = ((-5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0201Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0201Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0202 : ∀ x ∈ Icc ((((-5 : ℚ) / 128) : ℚ) : ℝ) ((((-7 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0202Lo = ((-5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0202Hi = ((-7 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0202Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0202Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0203 : ∀ x ∈ Icc ((((-7 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0203Lo = ((-7 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0203Hi = ((-3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0203Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0203Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0204 : ∀ x ∈ Icc ((((-3 : ℚ) / 128) : ℚ) : ℝ) ((((-3 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0204Lo = ((-3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0204Hi = ((-3 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0204Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0204Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0205 : ∀ x ∈ Icc ((((-3 : ℚ) / 256) : ℚ) : ℝ) ((((-1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0205Lo = ((-3 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0205Hi = ((-1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0205Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0205Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0206 : ∀ x ∈ Icc ((((-1 : ℚ) / 128) : ℚ) : ℝ) ((((1 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0206Lo = ((-1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0206Hi = ((1 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0206Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0206Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0207 : ∀ x ∈ Icc ((((1 : ℚ) / 256) : ℚ) : ℝ) ((((1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0207Lo = ((1 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0207Hi = ((1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0207Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0207Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock025 : ∀ x ∈ Icc ((((-7 : ℚ) / 128) : ℚ) : ℝ) ((((1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0200 liftFrCWT0P0201) (cover_union liftFrCWT0P0202 liftFrCWT0P0203)) (cover_union (cover_union liftFrCWT0P0204 liftFrCWT0P0205) (cover_union liftFrCWT0P0206 liftFrCWT0P0207)))
#print axioms FrCWT0CoverBlock025

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

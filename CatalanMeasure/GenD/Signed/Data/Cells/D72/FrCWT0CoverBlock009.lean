module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0079

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0072 : ∀ x ∈ Icc ((((-247 : ℚ) / 256) : ℚ) : ℝ) ((((-123 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0072Lo = ((-247 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0072Hi = ((-123 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0072Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0072Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0073 : ∀ x ∈ Icc ((((-123 : ℚ) / 128) : ℚ) : ℝ) ((((-491 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0073Lo = ((-123 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0073Hi = ((-491 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0073Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0073Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0074 : ∀ x ∈ Icc ((((-491 : ℚ) / 512) : ℚ) : ℝ) ((((-981 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0074Lo = ((-491 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0074Hi = ((-981 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0074Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0074Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0075 : ∀ x ∈ Icc ((((-981 : ℚ) / 1024) : ℚ) : ℝ) ((((-489 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0075Lo = ((-981 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0075Hi = ((-489 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0075Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0075Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0076 : ∀ x ∈ Icc ((((-489 : ℚ) / 512) : ℚ) : ℝ) ((((-61 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0076Lo = ((-489 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0076Hi = ((-61 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0076Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0076Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0077 : ∀ x ∈ Icc ((((-61 : ℚ) / 64) : ℚ) : ℝ) ((((-121 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0077Lo = ((-61 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0077Hi = ((-121 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0077Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0077Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0078 : ∀ x ∈ Icc ((((-121 : ℚ) / 128) : ℚ) : ℝ) ((((-483 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0078Lo = ((-121 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0078Hi = ((-483 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0078Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0078Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0079 : ∀ x ∈ Icc ((((-483 : ℚ) / 512) : ℚ) : ℝ) ((((-15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0079Lo = ((-483 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0079Hi = ((-15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0079Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0079Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock009 : ∀ x ∈ Icc ((((-247 : ℚ) / 256) : ℚ) : ℝ) ((((-15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0072 liftFrCWT0P0073) (cover_union liftFrCWT0P0074 liftFrCWT0P0075)) (cover_union (cover_union liftFrCWT0P0076 liftFrCWT0P0077) (cover_union liftFrCWT0P0078 liftFrCWT0P0079)))
#print axioms FrCWT0CoverBlock009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0169
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0175

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0168 : ∀ x ∈ Icc ((((-41 : ℚ) / 128) : ℚ) : ℝ) ((((-81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0168Lo = ((-41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0168Hi = ((-81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0168Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0168Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0169 : ∀ x ∈ Icc ((((-81 : ℚ) / 256) : ℚ) : ℝ) ((((-39 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0169Lo = ((-81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0169Hi = ((-39 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0169Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0169Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0170 : ∀ x ∈ Icc ((((-39 : ℚ) / 128) : ℚ) : ℝ) ((((-77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0170Lo = ((-39 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0170Hi = ((-77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0170Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0170Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0171 : ∀ x ∈ Icc ((((-77 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0171Lo = ((-77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0171Hi = ((-19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0171Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0171Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0172 : ∀ x ∈ Icc ((((-19 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0172Lo = ((-19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0172Hi = ((-9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0172Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0172Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0173 : ∀ x ∈ Icc ((((-9 : ℚ) / 32) : ℚ) : ℝ) ((((-17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0173Lo = ((-9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0173Hi = ((-17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0173Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0173Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0174 : ∀ x ∈ Icc ((((-17 : ℚ) / 64) : ℚ) : ℝ) ((((-1 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0174Lo = ((-17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0174Hi = ((-1 : ℚ) / 4) := by decide +kernel
  have hcap : FrCWT0P0174Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0174Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0175 : ∀ x ∈ Icc ((((-1 : ℚ) / 4) : ℚ) : ℝ) ((((-15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0175Lo = ((-1 : ℚ) / 4) := by decide +kernel
  have hhi : ceFrCWT0P0175Hi = ((-15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0175Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0175Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock021 : ∀ x ∈ Icc ((((-41 : ℚ) / 128) : ℚ) : ℝ) ((((-15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0168 liftFrCWT0P0169) (cover_union liftFrCWT0P0170 liftFrCWT0P0171)) (cover_union (cover_union liftFrCWT0P0172 liftFrCWT0P0173) (cover_union liftFrCWT0P0174 liftFrCWT0P0175)))
#print axioms FrCWT0CoverBlock021

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0119

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0112 : ∀ x ∈ Icc ((((-99 : ℚ) / 128) : ℚ) : ℝ) ((((-197 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0112Lo = ((-99 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0112Hi = ((-197 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0112Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0112Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0113 : ∀ x ∈ Icc ((((-197 : ℚ) / 256) : ℚ) : ℝ) ((((-49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0113Lo = ((-197 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0113Hi = ((-49 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0113Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0113Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0114 : ∀ x ∈ Icc ((((-49 : ℚ) / 64) : ℚ) : ℝ) ((((-97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0114Lo = ((-49 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0114Hi = ((-97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0114Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0114Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0115 : ∀ x ∈ Icc ((((-97 : ℚ) / 128) : ℚ) : ℝ) ((((-3 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0115Lo = ((-97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0115Hi = ((-3 : ℚ) / 4) := by decide +kernel
  have hcap : FrCWT0P0115Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0115Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0116 : ∀ x ∈ Icc ((((-3 : ℚ) / 4) : ℚ) : ℝ) ((((-189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0116Lo = ((-3 : ℚ) / 4) := by decide +kernel
  have hhi : ceFrCWT0P0116Hi = ((-189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0116Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0116Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0117 : ∀ x ∈ Icc ((((-189 : ℚ) / 256) : ℚ) : ℝ) ((((-47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0117Lo = ((-189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0117Hi = ((-47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0117Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0117Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0118 : ∀ x ∈ Icc ((((-47 : ℚ) / 64) : ℚ) : ℝ) ((((-93 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0118Lo = ((-47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0118Hi = ((-93 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0118Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0118Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0119 : ∀ x ∈ Icc ((((-93 : ℚ) / 128) : ℚ) : ℝ) ((((-185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0119Lo = ((-93 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0119Hi = ((-185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0119Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0119Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock014 : ∀ x ∈ Icc ((((-99 : ℚ) / 128) : ℚ) : ℝ) ((((-185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0112 liftFrCWT0P0113) (cover_union liftFrCWT0P0114 liftFrCWT0P0115)) (cover_union (cover_union liftFrCWT0P0116 liftFrCWT0P0117) (cover_union liftFrCWT0P0118 liftFrCWT0P0119)))
#print axioms FrCWT0CoverBlock014

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

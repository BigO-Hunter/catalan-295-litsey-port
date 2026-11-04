module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0296
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0297
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0298
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0299
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0300
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0301
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0302
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0303

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0296 : ∀ x ∈ Icc ((((19 : ℚ) / 32) : ℚ) : ℝ) ((((77 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0296Lo = ((19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0296Hi = ((77 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0296Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0296Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0297 : ∀ x ∈ Icc ((((77 : ℚ) / 128) : ℚ) : ℝ) ((((155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0297Lo = ((77 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0297Hi = ((155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0297Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0297Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0298 : ∀ x ∈ Icc ((((155 : ℚ) / 256) : ℚ) : ℝ) ((((315 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0298Lo = ((155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0298Hi = ((315 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0298Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0298Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0299 : ∀ x ∈ Icc ((((315 : ℚ) / 512) : ℚ) : ℝ) ((((79 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0299Lo = ((315 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0299Hi = ((79 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0299Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0299Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0300 : ∀ x ∈ Icc ((((79 : ℚ) / 128) : ℚ) : ℝ) ((((159 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0300Lo = ((79 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0300Hi = ((159 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0300Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0300Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0301 : ∀ x ∈ Icc ((((159 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0301Lo = ((159 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0301Hi = ((5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT0P0301Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0301Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0302 : ∀ x ∈ Icc ((((5 : ℚ) / 8) : ℚ) : ℝ) ((((81 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0302Lo = ((5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT0P0302Hi = ((81 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0302Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0302Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0303 : ∀ x ∈ Icc ((((81 : ℚ) / 128) : ℚ) : ℝ) ((((163 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0303Lo = ((81 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0303Hi = ((163 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0303Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0303Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock037 : ∀ x ∈ Icc ((((19 : ℚ) / 32) : ℚ) : ℝ) ((((163 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0296 liftFrCWT0P0297) (cover_union liftFrCWT0P0298 liftFrCWT0P0299)) (cover_union (cover_union liftFrCWT0P0300 liftFrCWT0P0301) (cover_union liftFrCWT0P0302 liftFrCWT0P0303)))
#print axioms FrCWT0CoverBlock037

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0264
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0265
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0266
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0267
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0268
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0269
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0270
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0271

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0264 : ∀ x ∈ Icc ((((53 : ℚ) / 128) : ℚ) : ℝ) ((((107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0264Lo = ((53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0264Hi = ((107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0264Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0264Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0265 : ∀ x ∈ Icc ((((107 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0265Lo = ((107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0265Hi = ((27 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0265Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0265Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0266 : ∀ x ∈ Icc ((((27 : ℚ) / 64) : ℚ) : ℝ) ((((7 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0266Lo = ((27 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0266Hi = ((7 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0266Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0266Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0267 : ∀ x ∈ Icc ((((7 : ℚ) / 16) : ℚ) : ℝ) ((((113 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0267Lo = ((7 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0267Hi = ((113 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0267Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0267Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0268 : ∀ x ∈ Icc ((((113 : ℚ) / 256) : ℚ) : ℝ) ((((57 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0268Lo = ((113 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0268Hi = ((57 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0268Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0268Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0269 : ∀ x ∈ Icc ((((57 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0269Lo = ((57 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0269Hi = ((29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0269Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0269Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0270 : ∀ x ∈ Icc ((((29 : ℚ) / 64) : ℚ) : ℝ) ((((117 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0270Lo = ((29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0270Hi = ((117 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0270Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0270Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0271 : ∀ x ∈ Icc ((((117 : ℚ) / 256) : ℚ) : ℝ) ((((59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0271Lo = ((117 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0271Hi = ((59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0271Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0271Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock033 : ∀ x ∈ Icc ((((53 : ℚ) / 128) : ℚ) : ℝ) ((((59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0264 liftFrCWT0P0265) (cover_union liftFrCWT0P0266 liftFrCWT0P0267)) (cover_union (cover_union liftFrCWT0P0268 liftFrCWT0P0269) (cover_union liftFrCWT0P0270 liftFrCWT0P0271)))
#print axioms FrCWT0CoverBlock033

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

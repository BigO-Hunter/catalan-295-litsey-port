module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0071

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0064 : ∀ x ∈ Icc ((((-501 : ℚ) / 512) : ℚ) : ℝ) ((((-1001 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0064Lo = ((-501 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0064Hi = ((-1001 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0064Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0064Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0065 : ∀ x ∈ Icc ((((-1001 : ℚ) / 1024) : ℚ) : ℝ) ((((-125 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0065Lo = ((-1001 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0065Hi = ((-125 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0065Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0065Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0066 : ∀ x ∈ Icc ((((-125 : ℚ) / 128) : ℚ) : ℝ) ((((-249 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0066Lo = ((-125 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0066Hi = ((-249 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0066Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0066Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0067 : ∀ x ∈ Icc ((((-249 : ℚ) / 256) : ℚ) : ℝ) ((((-995 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0067Lo = ((-249 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0067Hi = ((-995 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0067Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0067Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0068 : ∀ x ∈ Icc ((((-995 : ℚ) / 1024) : ℚ) : ℝ) ((((-497 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0068Lo = ((-995 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0068Hi = ((-497 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0068Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0068Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0069 : ∀ x ∈ Icc ((((-497 : ℚ) / 512) : ℚ) : ℝ) ((((-991 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0069Lo = ((-497 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0069Hi = ((-991 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0069Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0069Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0070 : ∀ x ∈ Icc ((((-991 : ℚ) / 1024) : ℚ) : ℝ) ((((-495 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0070Lo = ((-991 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0070Hi = ((-495 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0070Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0070Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0071 : ∀ x ∈ Icc ((((-495 : ℚ) / 512) : ℚ) : ℝ) ((((-247 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0071Lo = ((-495 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0071Hi = ((-247 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0071Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0071Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock008 : ∀ x ∈ Icc ((((-501 : ℚ) / 512) : ℚ) : ℝ) ((((-247 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0064 liftFrCWT0P0065) (cover_union liftFrCWT0P0066 liftFrCWT0P0067)) (cover_union (cover_union liftFrCWT0P0068 liftFrCWT0P0069) (cover_union liftFrCWT0P0070 liftFrCWT0P0071)))
#print axioms FrCWT0CoverBlock008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

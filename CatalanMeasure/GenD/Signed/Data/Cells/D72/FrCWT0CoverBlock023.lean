module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0185
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0186
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0187
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0188
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0189
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0190
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0191

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0184 : ∀ x ∈ Icc ((((-23 : ℚ) / 128) : ℚ) : ℝ) ((((-43 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0184Lo = ((-23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0184Hi = ((-43 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0184Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0184Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0185 : ∀ x ∈ Icc ((((-43 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0185Lo = ((-43 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0185Hi = ((-21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0185Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0185Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0186 : ∀ x ∈ Icc ((((-21 : ℚ) / 128) : ℚ) : ℝ) ((((-39 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0186Lo = ((-21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0186Hi = ((-39 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0186Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0186Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0187 : ∀ x ∈ Icc ((((-39 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0187Lo = ((-39 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0187Hi = ((-19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0187Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0187Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0188 : ∀ x ∈ Icc ((((-19 : ℚ) / 128) : ℚ) : ℝ) ((((-35 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0188Lo = ((-19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0188Hi = ((-35 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0188Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0188Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0189 : ∀ x ∈ Icc ((((-35 : ℚ) / 256) : ℚ) : ℝ) ((((-17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0189Lo = ((-35 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0189Hi = ((-17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0189Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0189Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0190 : ∀ x ∈ Icc ((((-17 : ℚ) / 128) : ℚ) : ℝ) ((((-31 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0190Lo = ((-17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0190Hi = ((-31 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0190Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0190Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0191 : ∀ x ∈ Icc ((((-31 : ℚ) / 256) : ℚ) : ℝ) ((((-15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0191Lo = ((-31 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0191Hi = ((-15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0191Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0191Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock023 : ∀ x ∈ Icc ((((-23 : ℚ) / 128) : ℚ) : ℝ) ((((-15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0184 liftFrCWT0P0185) (cover_union liftFrCWT0P0186 liftFrCWT0P0187)) (cover_union (cover_union liftFrCWT0P0188 liftFrCWT0P0189) (cover_union liftFrCWT0P0190 liftFrCWT0P0191)))
#print axioms FrCWT0CoverBlock023

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

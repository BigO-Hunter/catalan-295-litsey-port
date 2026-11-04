module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0344
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0345
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0346
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0347
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0348
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0349
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0350
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0351

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0344 : ∀ x ∈ Icc ((((415 : ℚ) / 512) : ℚ) : ℝ) ((((13 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0344Lo = ((415 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0344Hi = ((13 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0344Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0344Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0345 : ∀ x ∈ Icc ((((13 : ℚ) / 16) : ℚ) : ℝ) ((((209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0345Lo = ((13 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0345Hi = ((209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0345Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0345Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0346 : ∀ x ∈ Icc ((((209 : ℚ) / 256) : ℚ) : ℝ) ((((105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0346Lo = ((209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0346Hi = ((105 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0346Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0346Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0347 : ∀ x ∈ Icc ((((105 : ℚ) / 128) : ℚ) : ℝ) ((((421 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0347Lo = ((105 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0347Hi = ((421 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0347Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0347Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0348 : ∀ x ∈ Icc ((((421 : ℚ) / 512) : ℚ) : ℝ) ((((53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0348Lo = ((421 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0348Hi = ((53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0348Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0348Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0349 : ∀ x ∈ Icc ((((53 : ℚ) / 64) : ℚ) : ℝ) ((((849 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0349Lo = ((53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0349Hi = ((849 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0349Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0349Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0350 : ∀ x ∈ Icc ((((849 : ℚ) / 1024) : ℚ) : ℝ) ((((425 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0350Lo = ((849 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0350Hi = ((425 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0350Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0350Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0351 : ∀ x ∈ Icc ((((425 : ℚ) / 512) : ℚ) : ℝ) ((((213 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0351Lo = ((425 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0351Hi = ((213 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0351Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0351Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock043 : ∀ x ∈ Icc ((((415 : ℚ) / 512) : ℚ) : ℝ) ((((213 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0344 liftFrCWT0P0345) (cover_union liftFrCWT0P0346 liftFrCWT0P0347)) (cover_union (cover_union liftFrCWT0P0348 liftFrCWT0P0349) (cover_union liftFrCWT0P0350 liftFrCWT0P0351)))
#print axioms FrCWT0CoverBlock043

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

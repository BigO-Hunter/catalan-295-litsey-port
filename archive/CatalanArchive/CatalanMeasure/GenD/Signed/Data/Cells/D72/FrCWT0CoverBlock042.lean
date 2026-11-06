module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0336
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0337
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0338
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0339
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0340
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0341
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0342
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0343

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0336 : ∀ x ∈ Icc ((((49 : ℚ) / 64) : ℚ) : ℝ) ((((25 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0336Lo = ((49 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0336Hi = ((25 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0336Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0336Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0337 : ∀ x ∈ Icc ((((25 : ℚ) / 32) : ℚ) : ℝ) ((((201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0337Lo = ((25 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0337Hi = ((201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0337Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0337Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0338 : ∀ x ∈ Icc ((((201 : ℚ) / 256) : ℚ) : ℝ) ((((101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0338Lo = ((201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0338Hi = ((101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0338Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0338Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0339 : ∀ x ∈ Icc ((((101 : ℚ) / 128) : ℚ) : ℝ) ((((51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0339Lo = ((101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0339Hi = ((51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0339Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0339Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0340 : ∀ x ∈ Icc ((((51 : ℚ) / 64) : ℚ) : ℝ) ((((205 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0340Lo = ((51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0340Hi = ((205 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0340Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0340Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0341 : ∀ x ∈ Icc ((((205 : ℚ) / 256) : ℚ) : ℝ) ((((411 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0341Lo = ((205 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0341Hi = ((411 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0341Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0341Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0342 : ∀ x ∈ Icc ((((411 : ℚ) / 512) : ℚ) : ℝ) ((((103 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0342Lo = ((411 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0342Hi = ((103 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0342Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0342Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0343 : ∀ x ∈ Icc ((((103 : ℚ) / 128) : ℚ) : ℝ) ((((415 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0343Lo = ((103 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0343Hi = ((415 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0343Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0343Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock042 : ∀ x ∈ Icc ((((49 : ℚ) / 64) : ℚ) : ℝ) ((((415 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0336 liftFrCWT0P0337) (cover_union liftFrCWT0P0338 liftFrCWT0P0339)) (cover_union (cover_union liftFrCWT0P0340 liftFrCWT0P0341) (cover_union liftFrCWT0P0342 liftFrCWT0P0343)))
#print axioms FrCWT0CoverBlock042

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

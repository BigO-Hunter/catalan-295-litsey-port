module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0103

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0096 : ∀ x ∈ Icc ((((-221 : ℚ) / 256) : ℚ) : ℝ) ((((-55 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0096Lo = ((-221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0096Hi = ((-55 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0096Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0096Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0097 : ∀ x ∈ Icc ((((-55 : ℚ) / 64) : ℚ) : ℝ) ((((-219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0097Lo = ((-55 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0097Hi = ((-219 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0097Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0097Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0098 : ∀ x ∈ Icc ((((-219 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0098Lo = ((-219 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0098Hi = ((-27 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0098Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0098Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0099 : ∀ x ∈ Icc ((((-27 : ℚ) / 32) : ℚ) : ℝ) ((((-215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0099Lo = ((-27 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0099Hi = ((-215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0099Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0099Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0100 : ∀ x ∈ Icc ((((-215 : ℚ) / 256) : ℚ) : ℝ) ((((-107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0100Lo = ((-215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0100Hi = ((-107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0100Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0100Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0101 : ∀ x ∈ Icc ((((-107 : ℚ) / 128) : ℚ) : ℝ) ((((-53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0101Lo = ((-107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0101Hi = ((-53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0101Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0101Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0102 : ∀ x ∈ Icc ((((-53 : ℚ) / 64) : ℚ) : ℝ) ((((-105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0102Lo = ((-53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0102Hi = ((-105 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0102Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0102Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0103 : ∀ x ∈ Icc ((((-105 : ℚ) / 128) : ℚ) : ℝ) ((((-209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0103Lo = ((-105 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0103Hi = ((-209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0103Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0103Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock012 : ∀ x ∈ Icc ((((-221 : ℚ) / 256) : ℚ) : ℝ) ((((-209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0096 liftFrCWT0P0097) (cover_union liftFrCWT0P0098 liftFrCWT0P0099)) (cover_union (cover_union liftFrCWT0P0100 liftFrCWT0P0101) (cover_union liftFrCWT0P0102 liftFrCWT0P0103)))
#print axioms FrCWT0CoverBlock012

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

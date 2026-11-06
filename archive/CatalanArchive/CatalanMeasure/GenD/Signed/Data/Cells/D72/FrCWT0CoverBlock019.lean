module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0152
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0153
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0154
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0155
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0156
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0157
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0158
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0159

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0152 : ∀ x ∈ Icc ((((-59 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0152Lo = ((-59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0152Hi = ((-29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0152Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0152Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0153 : ∀ x ∈ Icc ((((-29 : ℚ) / 64) : ℚ) : ℝ) ((((-7 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0153Lo = ((-29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0153Hi = ((-7 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0153Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0153Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0154 : ∀ x ∈ Icc ((((-7 : ℚ) / 16) : ℚ) : ℝ) ((((-111 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0154Lo = ((-7 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0154Hi = ((-111 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0154Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0154Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0155 : ∀ x ∈ Icc ((((-111 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0155Lo = ((-111 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0155Hi = ((-27 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0155Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0155Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0156 : ∀ x ∈ Icc ((((-27 : ℚ) / 64) : ℚ) : ℝ) ((((-107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0156Lo = ((-27 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0156Hi = ((-107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0156Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0156Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0157 : ∀ x ∈ Icc ((((-107 : ℚ) / 256) : ℚ) : ℝ) ((((-53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0157Lo = ((-107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0157Hi = ((-53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0157Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0157Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0158 : ∀ x ∈ Icc ((((-53 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0158Lo = ((-53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0158Hi = ((-51 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0158Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0158Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0159 : ∀ x ∈ Icc ((((-51 : ℚ) / 128) : ℚ) : ℝ) ((((-101 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0159Lo = ((-51 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0159Hi = ((-101 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0159Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0159Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock019 : ∀ x ∈ Icc ((((-59 : ℚ) / 128) : ℚ) : ℝ) ((((-101 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0152 liftFrCWT0P0153) (cover_union liftFrCWT0P0154 liftFrCWT0P0155)) (cover_union (cover_union liftFrCWT0P0156 liftFrCWT0P0157) (cover_union liftFrCWT0P0158 liftFrCWT0P0159)))
#print axioms FrCWT0CoverBlock019

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

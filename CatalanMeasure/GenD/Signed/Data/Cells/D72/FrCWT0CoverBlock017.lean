module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0143

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0136 : ∀ x ∈ Icc ((((-19 : ℚ) / 32) : ℚ) : ℝ) ((((-37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0136Lo = ((-19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0136Hi = ((-37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0136Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0136Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0137 : ∀ x ∈ Icc ((((-37 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0137Lo = ((-37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0137Hi = ((-9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0137Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0137Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0138 : ∀ x ∈ Icc ((((-9 : ℚ) / 16) : ℚ) : ℝ) ((((-35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0138Lo = ((-9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0138Hi = ((-35 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0138Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0138Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0139 : ∀ x ∈ Icc ((((-35 : ℚ) / 64) : ℚ) : ℝ) ((((-139 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0139Lo = ((-35 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0139Hi = ((-139 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0139Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0139Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0140 : ∀ x ∈ Icc ((((-139 : ℚ) / 256) : ℚ) : ℝ) ((((-69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0140Lo = ((-139 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0140Hi = ((-69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0140Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0140Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0141 : ∀ x ∈ Icc ((((-69 : ℚ) / 128) : ℚ) : ℝ) ((((-67 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0141Lo = ((-69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0141Hi = ((-67 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0141Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0141Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0142 : ∀ x ∈ Icc ((((-67 : ℚ) / 128) : ℚ) : ℝ) ((((-133 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0142Lo = ((-67 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0142Hi = ((-133 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0142Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0142Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0143 : ∀ x ∈ Icc ((((-133 : ℚ) / 256) : ℚ) : ℝ) ((((-33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0143Lo = ((-133 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0143Hi = ((-33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0143Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0143Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock017 : ∀ x ∈ Icc ((((-19 : ℚ) / 32) : ℚ) : ℝ) ((((-33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0136 liftFrCWT0P0137) (cover_union liftFrCWT0P0138 liftFrCWT0P0139)) (cover_union (cover_union liftFrCWT0P0140 liftFrCWT0P0141) (cover_union liftFrCWT0P0142 liftFrCWT0P0143)))
#print axioms FrCWT0CoverBlock017

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

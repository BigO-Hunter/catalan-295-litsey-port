module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0160
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0161
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0162
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0163
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0164
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0165
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0166
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0167

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0160 : ∀ x ∈ Icc ((((-101 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0160Lo = ((-101 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0160Hi = ((-25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0160Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0160Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0161 : ∀ x ∈ Icc ((((-25 : ℚ) / 64) : ℚ) : ℝ) ((((-97 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0161Lo = ((-25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0161Hi = ((-97 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0161Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0161Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0162 : ∀ x ∈ Icc ((((-97 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0162Lo = ((-97 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0162Hi = ((-3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT0P0162Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0162Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0163 : ∀ x ∈ Icc ((((-3 : ℚ) / 8) : ℚ) : ℝ) ((((-47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0163Lo = ((-3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT0P0163Hi = ((-47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0163Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0163Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0164 : ∀ x ∈ Icc ((((-47 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0164Lo = ((-47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0164Hi = ((-11 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0164Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0164Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0165 : ∀ x ∈ Icc ((((-11 : ℚ) / 32) : ℚ) : ℝ) ((((-43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0165Lo = ((-11 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0165Hi = ((-43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0165Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0165Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0166 : ∀ x ∈ Icc ((((-43 : ℚ) / 128) : ℚ) : ℝ) ((((-85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0166Lo = ((-43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0166Hi = ((-85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0166Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0166Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0167 : ∀ x ∈ Icc ((((-85 : ℚ) / 256) : ℚ) : ℝ) ((((-41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0167Lo = ((-85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0167Hi = ((-41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0167Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0167Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock020 : ∀ x ∈ Icc ((((-101 : ℚ) / 256) : ℚ) : ℝ) ((((-41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0160 liftFrCWT0P0161) (cover_union liftFrCWT0P0162 liftFrCWT0P0163)) (cover_union (cover_union liftFrCWT0P0164 liftFrCWT0P0165) (cover_union liftFrCWT0P0166 liftFrCWT0P0167)))
#print axioms FrCWT0CoverBlock020

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

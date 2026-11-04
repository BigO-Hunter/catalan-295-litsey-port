module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0217
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0223

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0216 : ∀ x ∈ Icc ((((9 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0216Lo = ((9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0216Hi = ((21 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0216Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0216Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0217 : ∀ x ∈ Icc ((((21 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0217Lo = ((21 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0217Hi = ((11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0217Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0217Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0218 : ∀ x ∈ Icc ((((11 : ℚ) / 128) : ℚ) : ℝ) ((((25 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0218Lo = ((11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0218Hi = ((25 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0218Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0218Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0219 : ∀ x ∈ Icc ((((25 : ℚ) / 256) : ℚ) : ℝ) ((((13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0219Lo = ((25 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0219Hi = ((13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0219Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0219Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0220 : ∀ x ∈ Icc ((((13 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0220Lo = ((13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0220Hi = ((29 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0220Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0220Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0221 : ∀ x ∈ Icc ((((29 : ℚ) / 256) : ℚ) : ℝ) ((((15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0221Lo = ((29 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0221Hi = ((15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0221Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0221Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0222 : ∀ x ∈ Icc ((((15 : ℚ) / 128) : ℚ) : ℝ) ((((33 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0222Lo = ((15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0222Hi = ((33 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0222Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0222Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0223 : ∀ x ∈ Icc ((((33 : ℚ) / 256) : ℚ) : ℝ) ((((17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0223Lo = ((33 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0223Hi = ((17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0223Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0223Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock027 : ∀ x ∈ Icc ((((9 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0216 liftFrCWT0P0217) (cover_union liftFrCWT0P0218 liftFrCWT0P0219)) (cover_union (cover_union liftFrCWT0P0220 liftFrCWT0P0221) (cover_union liftFrCWT0P0222 liftFrCWT0P0223)))
#print axioms FrCWT0CoverBlock027

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

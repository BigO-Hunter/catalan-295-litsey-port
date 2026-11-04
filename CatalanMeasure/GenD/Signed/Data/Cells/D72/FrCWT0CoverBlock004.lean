module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0039

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0032 : ∀ x ∈ Icc ((((-131069 : ℚ) / 131072) : ℚ) : ℝ) ((((-131067 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0032Lo = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT0P0032Hi = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT0P0032Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0032Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0033 : ∀ x ∈ Icc ((((-131067 : ℚ) / 131072) : ℚ) : ℝ) ((((-16383 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0033Lo = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT0P0033Hi = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT0P0033Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0033Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0034 : ∀ x ∈ Icc ((((-16383 : ℚ) / 16384) : ℚ) : ℝ) ((((-8191 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0034Lo = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT0P0034Hi = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT0P0034Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0034Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0035 : ∀ x ∈ Icc ((((-8191 : ℚ) / 8192) : ℚ) : ℝ) ((((-16381 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0035Lo = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT0P0035Hi = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT0P0035Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0035Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0036 : ∀ x ∈ Icc ((((-16381 : ℚ) / 16384) : ℚ) : ℝ) ((((-32761 : ℚ) / 32768) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0036Lo = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT0P0036Hi = ((-32761 : ℚ) / 32768) := by decide +kernel
  have hcap : FrCWT0P0036Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0036Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0037 : ∀ x ∈ Icc ((((-32761 : ℚ) / 32768) : ℚ) : ℝ) ((((-4095 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0037Lo = ((-32761 : ℚ) / 32768) := by decide +kernel
  have hhi : ceFrCWT0P0037Hi = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0037Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0037Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0038 : ∀ x ∈ Icc ((((-4095 : ℚ) / 4096) : ℚ) : ℝ) ((((-2047 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0038Lo = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0038Hi = ((-2047 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0038Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0038Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0039 : ∀ x ∈ Icc ((((-2047 : ℚ) / 2048) : ℚ) : ℝ) ((((-8187 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0039Lo = ((-2047 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0039Hi = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT0P0039Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0039Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock004 : ∀ x ∈ Icc ((((-131069 : ℚ) / 131072) : ℚ) : ℝ) ((((-8187 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0032 liftFrCWT0P0033) (cover_union liftFrCWT0P0034 liftFrCWT0P0035)) (cover_union (cover_union liftFrCWT0P0036 liftFrCWT0P0037) (cover_union liftFrCWT0P0038 liftFrCWT0P0039)))
#print axioms FrCWT0CoverBlock004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

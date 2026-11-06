module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0031

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0024 : ∀ x ∈ Icc ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ) ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0024Lo = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hhi : ceFrCWT0P0024Hi = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hcap : FrCWT0P0024Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0024Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0025 : ∀ x ∈ Icc ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ) ((((-8388607 : ℚ) / 8388608) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0025Lo = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hhi : ceFrCWT0P0025Hi = ((-8388607 : ℚ) / 8388608) := by decide +kernel
  have hcap : FrCWT0P0025Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0025Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0026 : ∀ x ∈ Icc ((((-8388607 : ℚ) / 8388608) : ℚ) : ℝ) ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0026Lo = ((-8388607 : ℚ) / 8388608) := by decide +kernel
  have hhi : ceFrCWT0P0026Hi = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hcap : FrCWT0P0026Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0026Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0027 : ∀ x ∈ Icc ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ) ((((-2097151 : ℚ) / 2097152) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0027Lo = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hhi : ceFrCWT0P0027Hi = ((-2097151 : ℚ) / 2097152) := by decide +kernel
  have hcap : FrCWT0P0027Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0027Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0028 : ∀ x ∈ Icc ((((-2097151 : ℚ) / 2097152) : ℚ) : ℝ) ((((-2097149 : ℚ) / 2097152) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0028Lo = ((-2097151 : ℚ) / 2097152) := by decide +kernel
  have hhi : ceFrCWT0P0028Hi = ((-2097149 : ℚ) / 2097152) := by decide +kernel
  have hcap : FrCWT0P0028Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0028Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0029 : ∀ x ∈ Icc ((((-2097149 : ℚ) / 2097152) : ℚ) : ℝ) ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0029Lo = ((-2097149 : ℚ) / 2097152) := by decide +kernel
  have hhi : ceFrCWT0P0029Hi = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hcap : FrCWT0P0029Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0029Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0030 : ∀ x ∈ Icc ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ) ((((-131071 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0030Lo = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hhi : ceFrCWT0P0030Hi = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT0P0030Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0030Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0031 : ∀ x ∈ Icc ((((-131071 : ℚ) / 131072) : ℚ) : ℝ) ((((-131069 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0031Lo = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT0P0031Hi = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT0P0031Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0031Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock003 : ∀ x ∈ Icc ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ) ((((-131069 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0024 liftFrCWT0P0025) (cover_union liftFrCWT0P0026 liftFrCWT0P0027)) (cover_union (cover_union liftFrCWT0P0028 liftFrCWT0P0029) (cover_union liftFrCWT0P0030 liftFrCWT0P0031)))
#print axioms FrCWT0CoverBlock003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0055

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0048 : ∀ x ∈ Icc ((((-4077 : ℚ) / 4096) : ℚ) : ℝ) ((((-4075 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0048Lo = ((-4077 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0048Hi = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0048Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0048Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0049 : ∀ x ∈ Icc ((((-4075 : ℚ) / 4096) : ℚ) : ℝ) ((((-2035 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0049Lo = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0049Hi = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0049Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0049Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0050 : ∀ x ∈ Icc ((((-2035 : ℚ) / 2048) : ℚ) : ℝ) ((((-1017 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0050Lo = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0050Hi = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0050Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0050Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0051 : ∀ x ∈ Icc ((((-1017 : ℚ) / 1024) : ℚ) : ℝ) ((((-2031 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0051Lo = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0051Hi = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0051Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0051Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0052 : ∀ x ∈ Icc ((((-2031 : ℚ) / 2048) : ℚ) : ℝ) ((((-1015 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0052Lo = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0052Hi = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0052Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0052Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0053 : ∀ x ∈ Icc ((((-1015 : ℚ) / 1024) : ℚ) : ℝ) ((((-507 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0053Lo = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT0P0053Hi = ((-507 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0053Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0053Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0054 : ∀ x ∈ Icc ((((-507 : ℚ) / 512) : ℚ) : ℝ) ((((-253 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0054Lo = ((-507 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0054Hi = ((-253 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0054Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0054Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0055 : ∀ x ∈ Icc ((((-253 : ℚ) / 256) : ℚ) : ℝ) ((((-1011 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0055Lo = ((-253 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0055Hi = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT0P0055Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0055Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock006 : ∀ x ∈ Icc ((((-4077 : ℚ) / 4096) : ℚ) : ℝ) ((((-1011 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0048 liftFrCWT0P0049) (cover_union liftFrCWT0P0050 liftFrCWT0P0051)) (cover_union (cover_union liftFrCWT0P0052 liftFrCWT0P0053) (cover_union liftFrCWT0P0054 liftFrCWT0P0055)))
#print axioms FrCWT0CoverBlock006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

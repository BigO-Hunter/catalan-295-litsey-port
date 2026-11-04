module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0055

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0048 : ∀ x ∈ Icc ((((-1015 : ℚ) / 1024) : ℚ) : ℝ) ((((-507 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0048Lo = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0048Hi = ((-507 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0048Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0048Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0049 : ∀ x ∈ Icc ((((-507 : ℚ) / 512) : ℚ) : ℝ) ((((-253 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0049Lo = ((-507 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0049Hi = ((-253 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0049Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0049Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0050 : ∀ x ∈ Icc ((((-253 : ℚ) / 256) : ℚ) : ℝ) ((((-1011 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0050Lo = ((-253 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0050Hi = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0050Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0050Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0051 : ∀ x ∈ Icc ((((-1011 : ℚ) / 1024) : ℚ) : ℝ) ((((-505 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0051Lo = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0051Hi = ((-505 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0051Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0051Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0052 : ∀ x ∈ Icc ((((-505 : ℚ) / 512) : ℚ) : ℝ) ((((-1009 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0052Lo = ((-505 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0052Hi = ((-1009 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0052Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0052Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0053 : ∀ x ∈ Icc ((((-1009 : ℚ) / 1024) : ℚ) : ℝ) ((((-63 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0053Lo = ((-1009 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0053Hi = ((-63 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0053Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0053Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0054 : ∀ x ∈ Icc ((((-63 : ℚ) / 64) : ℚ) : ℝ) ((((-2015 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0054Lo = ((-63 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0054Hi = ((-2015 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0054Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0054Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0055 : ∀ x ∈ Icc ((((-2015 : ℚ) / 2048) : ℚ) : ℝ) ((((-503 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0055Lo = ((-2015 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0055Hi = ((-503 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0055Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0055Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock006 : ∀ x ∈ Icc ((((-1015 : ℚ) / 1024) : ℚ) : ℝ) ((((-503 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0048 liftFrCWT1P0049) (cover_union liftFrCWT1P0050 liftFrCWT1P0051)) (cover_union (cover_union liftFrCWT1P0052 liftFrCWT1P0053) (cover_union liftFrCWT1P0054 liftFrCWT1P0055)))
#print axioms FrCWT1CoverBlock006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

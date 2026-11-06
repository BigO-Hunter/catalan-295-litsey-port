module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0050
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0051
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0052
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0053
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0054
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0055

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0048 : ∀ x ∈ Icc ((((-1017 : ℚ) / 1024) : ℚ) : ℝ) ((((-2031 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0048Lo = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0048Hi = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0048Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0048Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0049 : ∀ x ∈ Icc ((((-2031 : ℚ) / 2048) : ℚ) : ℝ) ((((-1015 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0049Lo = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0049Hi = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0049Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0049Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0050 : ∀ x ∈ Icc ((((-1015 : ℚ) / 1024) : ℚ) : ℝ) ((((-507 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0050Lo = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0050Hi = ((-507 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0050Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0050Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0051 : ∀ x ∈ Icc ((((-507 : ℚ) / 512) : ℚ) : ℝ) ((((-253 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0051Lo = ((-507 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0051Hi = ((-253 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0051Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0051Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0052 : ∀ x ∈ Icc ((((-253 : ℚ) / 256) : ℚ) : ℝ) ((((-1011 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0052Lo = ((-253 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0052Hi = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0052Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0052Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0053 : ∀ x ∈ Icc ((((-1011 : ℚ) / 1024) : ℚ) : ℝ) ((((-505 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0053Lo = ((-1011 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0053Hi = ((-505 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0053Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0053Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0054 : ∀ x ∈ Icc ((((-505 : ℚ) / 512) : ℚ) : ℝ) ((((-63 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0054Lo = ((-505 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0054Hi = ((-63 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0054Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0054Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0055 : ∀ x ∈ Icc ((((-63 : ℚ) / 64) : ℚ) : ℝ) ((((-1007 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0055Lo = ((-63 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0055Hi = ((-1007 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0055Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0055Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock006 : ∀ x ∈ Icc ((((-1017 : ℚ) / 1024) : ℚ) : ℝ) ((((-1007 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0048 liftFrCWT2P0049) (cover_union liftFrCWT2P0050 liftFrCWT2P0051)) (cover_union (cover_union liftFrCWT2P0052 liftFrCWT2P0053) (cover_union liftFrCWT2P0054 liftFrCWT2P0055)))
#print axioms FrCWT2CoverBlock006

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

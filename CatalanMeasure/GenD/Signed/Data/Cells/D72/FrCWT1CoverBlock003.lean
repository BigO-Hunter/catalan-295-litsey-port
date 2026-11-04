module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0031

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0024 : ∀ x ∈ Icc ((((-131071 : ℚ) / 131072) : ℚ) : ℝ) ((((-131069 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0024Lo = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT1P0024Hi = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT1P0024Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0024Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0025 : ∀ x ∈ Icc ((((-131069 : ℚ) / 131072) : ℚ) : ℝ) ((((-32767 : ℚ) / 32768) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0025Lo = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT1P0025Hi = ((-32767 : ℚ) / 32768) := by decide +kernel
  have hcap : FrCWT1P0025Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0025Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0026 : ∀ x ∈ Icc ((((-32767 : ℚ) / 32768) : ℚ) : ℝ) ((((-131067 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0026Lo = ((-32767 : ℚ) / 32768) := by decide +kernel
  have hhi : ceFrCWT1P0026Hi = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT1P0026Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0026Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0027 : ∀ x ∈ Icc ((((-131067 : ℚ) / 131072) : ℚ) : ℝ) ((((-16383 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0027Lo = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT1P0027Hi = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT1P0027Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0027Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0028 : ∀ x ∈ Icc ((((-16383 : ℚ) / 16384) : ℚ) : ℝ) ((((-8191 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0028Lo = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT1P0028Hi = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT1P0028Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0028Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0029 : ∀ x ∈ Icc ((((-8191 : ℚ) / 8192) : ℚ) : ℝ) ((((-16381 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0029Lo = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT1P0029Hi = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT1P0029Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0029Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0030 : ∀ x ∈ Icc ((((-16381 : ℚ) / 16384) : ℚ) : ℝ) ((((-4095 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0030Lo = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT1P0030Hi = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0030Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0030Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0031 : ∀ x ∈ Icc ((((-4095 : ℚ) / 4096) : ℚ) : ℝ) ((((-2047 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0031Lo = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0031Hi = ((-2047 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0031Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0031Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock003 : ∀ x ∈ Icc ((((-131071 : ℚ) / 131072) : ℚ) : ℝ) ((((-2047 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0024 liftFrCWT1P0025) (cover_union liftFrCWT1P0026 liftFrCWT1P0027)) (cover_union (cover_union liftFrCWT1P0028 liftFrCWT1P0029) (cover_union liftFrCWT1P0030 liftFrCWT1P0031)))
#print axioms FrCWT1CoverBlock003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

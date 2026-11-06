module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0031

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0024 : ∀ x ∈ Icc ((((-262143 : ℚ) / 262144) : ℚ) : ℝ) ((((-131071 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0024Lo = ((-262143 : ℚ) / 262144) := by decide +kernel
  have hhi : ceFrCWT2P0024Hi = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT2P0024Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0024Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0025 : ∀ x ∈ Icc ((((-131071 : ℚ) / 131072) : ℚ) : ℝ) ((((-131069 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0025Lo = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT2P0025Hi = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT2P0025Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0025Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0026 : ∀ x ∈ Icc ((((-131069 : ℚ) / 131072) : ℚ) : ℝ) ((((-32767 : ℚ) / 32768) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0026Lo = ((-131069 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT2P0026Hi = ((-32767 : ℚ) / 32768) := by decide +kernel
  have hcap : FrCWT2P0026Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0026Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0027 : ∀ x ∈ Icc ((((-32767 : ℚ) / 32768) : ℚ) : ℝ) ((((-131067 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0027Lo = ((-32767 : ℚ) / 32768) := by decide +kernel
  have hhi : ceFrCWT2P0027Hi = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT2P0027Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0027Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0028 : ∀ x ∈ Icc ((((-131067 : ℚ) / 131072) : ℚ) : ℝ) ((((-16383 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0028Lo = ((-131067 : ℚ) / 131072) := by decide +kernel
  have hhi : ceFrCWT2P0028Hi = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT2P0028Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0028Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0029 : ∀ x ∈ Icc ((((-16383 : ℚ) / 16384) : ℚ) : ℝ) ((((-8191 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0029Lo = ((-16383 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT2P0029Hi = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT2P0029Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0029Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0030 : ∀ x ∈ Icc ((((-8191 : ℚ) / 8192) : ℚ) : ℝ) ((((-16381 : ℚ) / 16384) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0030Lo = ((-8191 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT2P0030Hi = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hcap : FrCWT2P0030Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0030Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0031 : ∀ x ∈ Icc ((((-16381 : ℚ) / 16384) : ℚ) : ℝ) ((((-4095 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0031Lo = ((-16381 : ℚ) / 16384) := by decide +kernel
  have hhi : ceFrCWT2P0031Hi = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0031Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0031Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock003 : ∀ x ∈ Icc ((((-262143 : ℚ) / 262144) : ℚ) : ℝ) ((((-4095 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0024 liftFrCWT2P0025) (cover_union liftFrCWT2P0026 liftFrCWT2P0027)) (cover_union (cover_union liftFrCWT2P0028 liftFrCWT2P0029) (cover_union liftFrCWT2P0030 liftFrCWT2P0031)))
#print axioms FrCWT2CoverBlock003

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

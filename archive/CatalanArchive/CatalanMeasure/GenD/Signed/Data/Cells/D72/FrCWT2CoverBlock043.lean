module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0344
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0345
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0346
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0347
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0348
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0349
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0350
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0351

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0344 : ∀ x ∈ Icc ((((875 : ℚ) / 1024) : ℚ) : ℝ) ((((219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0344Lo = ((875 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0344Hi = ((219 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0344Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0344Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0345 : ∀ x ∈ Icc ((((219 : ℚ) / 256) : ℚ) : ℝ) ((((439 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0345Lo = ((219 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0345Hi = ((439 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0345Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0345Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0346 : ∀ x ∈ Icc ((((439 : ℚ) / 512) : ℚ) : ℝ) ((((441 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0346Lo = ((439 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0346Hi = ((441 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0346Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0346Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0347 : ∀ x ∈ Icc ((((441 : ℚ) / 512) : ℚ) : ℝ) ((((883 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0347Lo = ((441 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0347Hi = ((883 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0347Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0347Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0348 : ∀ x ∈ Icc ((((883 : ℚ) / 1024) : ℚ) : ℝ) ((((221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0348Lo = ((883 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0348Hi = ((221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0348Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0348Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0349 : ∀ x ∈ Icc ((((221 : ℚ) / 256) : ℚ) : ℝ) ((((443 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0349Lo = ((221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0349Hi = ((443 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0349Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0349Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0350 : ∀ x ∈ Icc ((((443 : ℚ) / 512) : ℚ) : ℝ) ((((449 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0350Lo = ((443 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0350Hi = ((449 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0350Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0350Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0351 : ∀ x ∈ Icc ((((449 : ℚ) / 512) : ℚ) : ℝ) ((((899 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0351Lo = ((449 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0351Hi = ((899 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0351Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0351Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock043 : ∀ x ∈ Icc ((((875 : ℚ) / 1024) : ℚ) : ℝ) ((((899 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0344 liftFrCWT2P0345) (cover_union liftFrCWT2P0346 liftFrCWT2P0347)) (cover_union (cover_union liftFrCWT2P0348 liftFrCWT2P0349) (cover_union liftFrCWT2P0350 liftFrCWT2P0351)))
#print axioms FrCWT2CoverBlock043

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

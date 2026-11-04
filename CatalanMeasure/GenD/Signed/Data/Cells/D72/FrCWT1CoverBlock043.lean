module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0344
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0345
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0346
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0347
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0348
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0349
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0350
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0351

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0344 : ∀ x ∈ Icc ((((105 : ℚ) / 128) : ℚ) : ℝ) ((((421 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0344Lo = ((105 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0344Hi = ((421 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0344Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0344Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0345 : ∀ x ∈ Icc ((((421 : ℚ) / 512) : ℚ) : ℝ) ((((53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0345Lo = ((421 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0345Hi = ((53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0345Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0345Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0346 : ∀ x ∈ Icc ((((53 : ℚ) / 64) : ℚ) : ℝ) ((((849 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0346Lo = ((53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0346Hi = ((849 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0346Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0346Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0347 : ∀ x ∈ Icc ((((849 : ℚ) / 1024) : ℚ) : ℝ) ((((425 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0347Lo = ((849 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0347Hi = ((425 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0347Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0347Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0348 : ∀ x ∈ Icc ((((425 : ℚ) / 512) : ℚ) : ℝ) ((((213 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0348Lo = ((425 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0348Hi = ((213 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0348Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0348Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0349 : ∀ x ∈ Icc ((((213 : ℚ) / 256) : ℚ) : ℝ) ((((107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0349Lo = ((213 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0349Hi = ((107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0349Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0349Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0350 : ∀ x ∈ Icc ((((107 : ℚ) / 128) : ℚ) : ℝ) ((((429 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0350Lo = ((107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0350Hi = ((429 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0350Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0350Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0351 : ∀ x ∈ Icc ((((429 : ℚ) / 512) : ℚ) : ℝ) ((((215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0351Lo = ((429 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0351Hi = ((215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0351Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0351Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock043 : ∀ x ∈ Icc ((((105 : ℚ) / 128) : ℚ) : ℝ) ((((215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0344 liftFrCWT1P0345) (cover_union liftFrCWT1P0346 liftFrCWT1P0347)) (cover_union (cover_union liftFrCWT1P0348 liftFrCWT1P0349) (cover_union liftFrCWT1P0350 liftFrCWT1P0351)))
#print axioms FrCWT1CoverBlock043

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

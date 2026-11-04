module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0280
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0281
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0282
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0283
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0284
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0285
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0286
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0287

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0280 : ∀ x ∈ Icc ((((17 : ℚ) / 32) : ℚ) : ℝ) ((((137 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0280Lo = ((17 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0280Hi = ((137 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0280Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0280Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0281 : ∀ x ∈ Icc ((((137 : ℚ) / 256) : ℚ) : ℝ) ((((69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0281Lo = ((137 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0281Hi = ((69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0281Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0281Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0282 : ∀ x ∈ Icc ((((69 : ℚ) / 128) : ℚ) : ℝ) ((((277 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0282Lo = ((69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0282Hi = ((277 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0282Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0282Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0283 : ∀ x ∈ Icc ((((277 : ℚ) / 512) : ℚ) : ℝ) ((((35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0283Lo = ((277 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0283Hi = ((35 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0283Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0283Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0284 : ∀ x ∈ Icc ((((35 : ℚ) / 64) : ℚ) : ℝ) ((((141 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0284Lo = ((35 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0284Hi = ((141 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0284Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0284Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0285 : ∀ x ∈ Icc ((((141 : ℚ) / 256) : ℚ) : ℝ) ((((71 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0285Lo = ((141 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0285Hi = ((71 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0285Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0285Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0286 : ∀ x ∈ Icc ((((71 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0286Lo = ((71 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0286Hi = ((9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0286Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0286Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0287 : ∀ x ∈ Icc ((((9 : ℚ) / 16) : ℚ) : ℝ) ((((73 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0287Lo = ((9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0287Hi = ((73 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0287Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0287Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock035 : ∀ x ∈ Icc ((((17 : ℚ) / 32) : ℚ) : ℝ) ((((73 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0280 liftFrCWT1P0281) (cover_union liftFrCWT1P0282 liftFrCWT1P0283)) (cover_union (cover_union liftFrCWT1P0284 liftFrCWT1P0285) (cover_union liftFrCWT1P0286 liftFrCWT1P0287)))
#print axioms FrCWT1CoverBlock035

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

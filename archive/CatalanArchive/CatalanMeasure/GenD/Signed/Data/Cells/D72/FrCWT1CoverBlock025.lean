module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0200
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0201
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0202
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0203
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0204
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0205
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0206
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0207

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0200 : ∀ x ∈ Icc ((((-7 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0200Lo = ((-7 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0200Hi = ((-3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0200Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0200Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0201 : ∀ x ∈ Icc ((((-3 : ℚ) / 128) : ℚ) : ℝ) ((((-3 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0201Lo = ((-3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0201Hi = ((-3 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0201Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0201Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0202 : ∀ x ∈ Icc ((((-3 : ℚ) / 256) : ℚ) : ℝ) ((((-1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0202Lo = ((-3 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0202Hi = ((-1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0202Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0202Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0203 : ∀ x ∈ Icc ((((-1 : ℚ) / 128) : ℚ) : ℝ) ((((1 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0203Lo = ((-1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0203Hi = ((1 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0203Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0203Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0204 : ∀ x ∈ Icc ((((1 : ℚ) / 256) : ℚ) : ℝ) ((((1 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0204Lo = ((1 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0204Hi = ((1 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0204Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0204Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0205 : ∀ x ∈ Icc ((((1 : ℚ) / 128) : ℚ) : ℝ) ((((5 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0205Lo = ((1 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0205Hi = ((5 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0205Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0205Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0206 : ∀ x ∈ Icc ((((5 : ℚ) / 256) : ℚ) : ℝ) ((((3 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0206Lo = ((5 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0206Hi = ((3 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0206Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0206Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0207 : ∀ x ∈ Icc ((((3 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0207Lo = ((3 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0207Hi = ((9 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0207Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0207Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock025 : ∀ x ∈ Icc ((((-7 : ℚ) / 256) : ℚ) : ℝ) ((((9 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0200 liftFrCWT1P0201) (cover_union liftFrCWT1P0202 liftFrCWT1P0203)) (cover_union (cover_union liftFrCWT1P0204 liftFrCWT1P0205) (cover_union liftFrCWT1P0206 liftFrCWT1P0207)))
#print axioms FrCWT1CoverBlock025

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

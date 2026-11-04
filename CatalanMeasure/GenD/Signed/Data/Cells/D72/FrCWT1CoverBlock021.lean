module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0168
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0169
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0170
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0171
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0172
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0173
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0174
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0175

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0168 : ∀ x ∈ Icc ((((-77 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0168Lo = ((-77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0168Hi = ((-19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0168Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0168Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0169 : ∀ x ∈ Icc ((((-19 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0169Lo = ((-19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0169Hi = ((-9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0169Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0169Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0170 : ∀ x ∈ Icc ((((-9 : ℚ) / 32) : ℚ) : ℝ) ((((-17 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0170Lo = ((-9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0170Hi = ((-17 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0170Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0170Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0171 : ∀ x ∈ Icc ((((-17 : ℚ) / 64) : ℚ) : ℝ) ((((-1 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0171Lo = ((-17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0171Hi = ((-1 : ℚ) / 4) := by decide +kernel
  have hcap : FrCWT1P0171Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0171Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0172 : ∀ x ∈ Icc ((((-1 : ℚ) / 4) : ℚ) : ℝ) ((((-15 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0172Lo = ((-1 : ℚ) / 4) := by decide +kernel
  have hhi : ceFrCWT1P0172Hi = ((-15 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0172Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0172Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0173 : ∀ x ∈ Icc ((((-15 : ℚ) / 64) : ℚ) : ℝ) ((((-59 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0173Lo = ((-15 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0173Hi = ((-59 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0173Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0173Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0174 : ∀ x ∈ Icc ((((-59 : ℚ) / 256) : ℚ) : ℝ) ((((-29 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0174Lo = ((-59 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0174Hi = ((-29 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0174Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0174Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0175 : ∀ x ∈ Icc ((((-29 : ℚ) / 128) : ℚ) : ℝ) ((((-55 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0175Lo = ((-29 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0175Hi = ((-55 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0175Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0175Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock021 : ∀ x ∈ Icc ((((-77 : ℚ) / 256) : ℚ) : ℝ) ((((-55 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0168 liftFrCWT1P0169) (cover_union liftFrCWT1P0170 liftFrCWT1P0171)) (cover_union (cover_union liftFrCWT1P0172 liftFrCWT1P0173) (cover_union liftFrCWT1P0174 liftFrCWT1P0175)))
#print axioms FrCWT1CoverBlock021

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

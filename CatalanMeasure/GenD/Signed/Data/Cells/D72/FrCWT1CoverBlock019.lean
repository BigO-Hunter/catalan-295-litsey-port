module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0152
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0153
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0154
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0155
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0156
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0157
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0158
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0159

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0152 : ∀ x ∈ Icc ((((-111 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0152Lo = ((-111 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0152Hi = ((-27 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0152Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0152Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0153 : ∀ x ∈ Icc ((((-27 : ℚ) / 64) : ℚ) : ℝ) ((((-107 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0153Lo = ((-27 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0153Hi = ((-107 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0153Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0153Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0154 : ∀ x ∈ Icc ((((-107 : ℚ) / 256) : ℚ) : ℝ) ((((-53 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0154Lo = ((-107 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0154Hi = ((-53 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0154Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0154Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0155 : ∀ x ∈ Icc ((((-53 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0155Lo = ((-53 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0155Hi = ((-51 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0155Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0155Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0156 : ∀ x ∈ Icc ((((-51 : ℚ) / 128) : ℚ) : ℝ) ((((-101 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0156Lo = ((-51 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0156Hi = ((-101 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0156Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0156Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0157 : ∀ x ∈ Icc ((((-101 : ℚ) / 256) : ℚ) : ℝ) ((((-25 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0157Lo = ((-101 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0157Hi = ((-25 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0157Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0157Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0158 : ∀ x ∈ Icc ((((-25 : ℚ) / 64) : ℚ) : ℝ) ((((-97 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0158Lo = ((-25 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0158Hi = ((-97 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0158Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0158Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0159 : ∀ x ∈ Icc ((((-97 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0159Lo = ((-97 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0159Hi = ((-3 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT1P0159Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0159Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock019 : ∀ x ∈ Icc ((((-111 : ℚ) / 256) : ℚ) : ℝ) ((((-3 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0152 liftFrCWT1P0153) (cover_union liftFrCWT1P0154 liftFrCWT1P0155)) (cover_union (cover_union liftFrCWT1P0156 liftFrCWT1P0157) (cover_union liftFrCWT1P0158 liftFrCWT1P0159)))
#print axioms FrCWT1CoverBlock019

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

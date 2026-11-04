module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0096
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0097
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0098
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0099
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0100
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0101
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0102
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0103

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0096 : ∀ x ∈ Icc ((((-215 : ℚ) / 256) : ℚ) : ℝ) ((((-107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0096Lo = ((-215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0096Hi = ((-107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0096Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0096Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0097 : ∀ x ∈ Icc ((((-107 : ℚ) / 128) : ℚ) : ℝ) ((((-53 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0097Lo = ((-107 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0097Hi = ((-53 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0097Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0097Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0098 : ∀ x ∈ Icc ((((-53 : ℚ) / 64) : ℚ) : ℝ) ((((-105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0098Lo = ((-53 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0098Hi = ((-105 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0098Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0098Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0099 : ∀ x ∈ Icc ((((-105 : ℚ) / 128) : ℚ) : ℝ) ((((-209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0099Lo = ((-105 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0099Hi = ((-209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0099Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0099Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0100 : ∀ x ∈ Icc ((((-209 : ℚ) / 256) : ℚ) : ℝ) ((((-13 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0100Lo = ((-209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0100Hi = ((-13 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0100Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0100Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0101 : ∀ x ∈ Icc ((((-13 : ℚ) / 16) : ℚ) : ℝ) ((((-413 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0101Lo = ((-13 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0101Hi = ((-413 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0101Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0101Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0102 : ∀ x ∈ Icc ((((-413 : ℚ) / 512) : ℚ) : ℝ) ((((-103 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0102Lo = ((-413 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0102Hi = ((-103 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0102Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0102Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0103 : ∀ x ∈ Icc ((((-103 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0103Lo = ((-103 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0103Hi = ((-51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0103Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0103Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock012 : ∀ x ∈ Icc ((((-215 : ℚ) / 256) : ℚ) : ℝ) ((((-51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0096 liftFrCWT1P0097) (cover_union liftFrCWT1P0098 liftFrCWT1P0099)) (cover_union (cover_union liftFrCWT1P0100 liftFrCWT1P0101) (cover_union liftFrCWT1P0102 liftFrCWT1P0103)))
#print axioms FrCWT1CoverBlock012

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

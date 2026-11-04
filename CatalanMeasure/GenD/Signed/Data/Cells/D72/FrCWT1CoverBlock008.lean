module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0067
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0068
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0069
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0070
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0071

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0064 : ∀ x ∈ Icc ((((-497 : ℚ) / 512) : ℚ) : ℝ) ((((-991 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0064Lo = ((-497 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0064Hi = ((-991 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0064Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0064Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0065 : ∀ x ∈ Icc ((((-991 : ℚ) / 1024) : ℚ) : ℝ) ((((-495 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0065Lo = ((-991 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0065Hi = ((-495 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0065Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0065Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0066 : ∀ x ∈ Icc ((((-495 : ℚ) / 512) : ℚ) : ℝ) ((((-247 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0066Lo = ((-495 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0066Hi = ((-247 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0066Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0066Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0067 : ∀ x ∈ Icc ((((-247 : ℚ) / 256) : ℚ) : ℝ) ((((-123 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0067Lo = ((-247 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0067Hi = ((-123 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0067Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0067Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0068 : ∀ x ∈ Icc ((((-123 : ℚ) / 128) : ℚ) : ℝ) ((((-491 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0068Lo = ((-123 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0068Hi = ((-491 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0068Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0068Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0069 : ∀ x ∈ Icc ((((-491 : ℚ) / 512) : ℚ) : ℝ) ((((-981 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0069Lo = ((-491 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0069Hi = ((-981 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0069Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0069Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0070 : ∀ x ∈ Icc ((((-981 : ℚ) / 1024) : ℚ) : ℝ) ((((-489 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0070Lo = ((-981 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0070Hi = ((-489 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0070Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0070Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0071 : ∀ x ∈ Icc ((((-489 : ℚ) / 512) : ℚ) : ℝ) ((((-61 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0071Lo = ((-489 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0071Hi = ((-61 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0071Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0071Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock008 : ∀ x ∈ Icc ((((-497 : ℚ) / 512) : ℚ) : ℝ) ((((-61 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0064 liftFrCWT1P0065) (cover_union liftFrCWT1P0066 liftFrCWT1P0067)) (cover_union (cover_union liftFrCWT1P0068 liftFrCWT1P0069) (cover_union liftFrCWT1P0070 liftFrCWT1P0071)))
#print axioms FrCWT1CoverBlock008

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

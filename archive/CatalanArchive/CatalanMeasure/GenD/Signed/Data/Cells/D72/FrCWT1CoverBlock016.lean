module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0135

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0128 : ∀ x ∈ Icc ((((-41 : ℚ) / 64) : ℚ) : ℝ) ((((-5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0128Lo = ((-41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0128Hi = ((-5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT1P0128Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0128Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0129 : ∀ x ∈ Icc ((((-5 : ℚ) / 8) : ℚ) : ℝ) ((((-79 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0129Lo = ((-5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT1P0129Hi = ((-79 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0129Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0129Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0130 : ∀ x ∈ Icc ((((-79 : ℚ) / 128) : ℚ) : ℝ) ((((-155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0130Lo = ((-79 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0130Hi = ((-155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0130Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0130Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0131 : ∀ x ∈ Icc ((((-155 : ℚ) / 256) : ℚ) : ℝ) ((((-153 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0131Lo = ((-155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0131Hi = ((-153 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0131Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0131Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0132 : ∀ x ∈ Icc ((((-153 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0132Lo = ((-153 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0132Hi = ((-19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0132Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0132Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0133 : ∀ x ∈ Icc ((((-19 : ℚ) / 32) : ℚ) : ℝ) ((((-37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0133Lo = ((-19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0133Hi = ((-37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0133Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0133Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0134 : ∀ x ∈ Icc ((((-37 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0134Lo = ((-37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0134Hi = ((-9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0134Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0134Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0135 : ∀ x ∈ Icc ((((-9 : ℚ) / 16) : ℚ) : ℝ) ((((-35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0135Lo = ((-9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0135Hi = ((-35 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0135Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0135Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock016 : ∀ x ∈ Icc ((((-41 : ℚ) / 64) : ℚ) : ℝ) ((((-35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0128 liftFrCWT1P0129) (cover_union liftFrCWT1P0130 liftFrCWT1P0131)) (cover_union (cover_union liftFrCWT1P0132 liftFrCWT1P0133) (cover_union liftFrCWT1P0134 liftFrCWT1P0135)))
#print axioms FrCWT1CoverBlock016

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0119

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0112 : ∀ x ∈ Icc ((((-3 : ℚ) / 4) : ℚ) : ℝ) ((((-95 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0112Lo = ((-3 : ℚ) / 4) := by decide +kernel
  have hhi : ceFrCWT1P0112Hi = ((-95 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0112Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0112Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0113 : ∀ x ∈ Icc ((((-95 : ℚ) / 128) : ℚ) : ℝ) ((((-189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0113Lo = ((-95 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0113Hi = ((-189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0113Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0113Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0114 : ∀ x ∈ Icc ((((-189 : ℚ) / 256) : ℚ) : ℝ) ((((-47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0114Lo = ((-189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0114Hi = ((-47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0114Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0114Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0115 : ∀ x ∈ Icc ((((-47 : ℚ) / 64) : ℚ) : ℝ) ((((-93 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0115Lo = ((-47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0115Hi = ((-93 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0115Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0115Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0116 : ∀ x ∈ Icc ((((-93 : ℚ) / 128) : ℚ) : ℝ) ((((-185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0116Lo = ((-93 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0116Hi = ((-185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0116Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0116Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0117 : ∀ x ∈ Icc ((((-185 : ℚ) / 256) : ℚ) : ℝ) ((((-91 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0117Lo = ((-185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0117Hi = ((-91 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0117Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0117Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0118 : ∀ x ∈ Icc ((((-91 : ℚ) / 128) : ℚ) : ℝ) ((((-181 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0118Lo = ((-91 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0118Hi = ((-181 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0118Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0118Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0119 : ∀ x ∈ Icc ((((-181 : ℚ) / 256) : ℚ) : ℝ) ((((-179 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0119Lo = ((-181 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0119Hi = ((-179 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0119Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0119Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock014 : ∀ x ∈ Icc ((((-3 : ℚ) / 4) : ℚ) : ℝ) ((((-179 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0112 liftFrCWT1P0113) (cover_union liftFrCWT1P0114 liftFrCWT1P0115)) (cover_union (cover_union liftFrCWT1P0116 liftFrCWT1P0117) (cover_union liftFrCWT1P0118 liftFrCWT1P0119)))
#print axioms FrCWT1CoverBlock014

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

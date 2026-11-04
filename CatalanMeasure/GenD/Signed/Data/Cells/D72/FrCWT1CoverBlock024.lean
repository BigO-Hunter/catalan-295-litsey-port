module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0192
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0193
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0194
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0195
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0196
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0197
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0198
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0199

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0192 : ∀ x ∈ Icc ((((-23 : ℚ) / 256) : ℚ) : ℝ) ((((-11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0192Lo = ((-23 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0192Hi = ((-11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0192Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0192Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0193 : ∀ x ∈ Icc ((((-11 : ℚ) / 128) : ℚ) : ℝ) ((((-19 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0193Lo = ((-11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0193Hi = ((-19 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0193Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0193Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0194 : ∀ x ∈ Icc ((((-19 : ℚ) / 256) : ℚ) : ℝ) ((((-9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0194Lo = ((-19 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0194Hi = ((-9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0194Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0194Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0195 : ∀ x ∈ Icc ((((-9 : ℚ) / 128) : ℚ) : ℝ) ((((-15 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0195Lo = ((-9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0195Hi = ((-15 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0195Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0195Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0196 : ∀ x ∈ Icc ((((-15 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0196Lo = ((-15 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0196Hi = ((-7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0196Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0196Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0197 : ∀ x ∈ Icc ((((-7 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0197Lo = ((-7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0197Hi = ((-11 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0197Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0197Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0198 : ∀ x ∈ Icc ((((-11 : ℚ) / 256) : ℚ) : ℝ) ((((-5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0198Lo = ((-11 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0198Hi = ((-5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0198Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0198Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0199 : ∀ x ∈ Icc ((((-5 : ℚ) / 128) : ℚ) : ℝ) ((((-7 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0199Lo = ((-5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0199Hi = ((-7 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0199Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0199Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock024 : ∀ x ∈ Icc ((((-23 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0192 liftFrCWT1P0193) (cover_union liftFrCWT1P0194 liftFrCWT1P0195)) (cover_union (cover_union liftFrCWT1P0196 liftFrCWT1P0197) (cover_union liftFrCWT1P0198 liftFrCWT1P0199)))
#print axioms FrCWT1CoverBlock024

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

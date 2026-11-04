module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0208
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0209
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0210
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0211
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0212
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0213
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0214
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0215

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0208 : ∀ x ∈ Icc ((((9 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0208Lo = ((9 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0208Hi = ((5 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0208Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0208Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0209 : ∀ x ∈ Icc ((((5 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0209Lo = ((5 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0209Hi = ((13 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0209Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0209Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0210 : ∀ x ∈ Icc ((((13 : ℚ) / 256) : ℚ) : ℝ) ((((7 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0210Lo = ((13 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0210Hi = ((7 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0210Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0210Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0211 : ∀ x ∈ Icc ((((7 : ℚ) / 128) : ℚ) : ℝ) ((((17 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0211Lo = ((7 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0211Hi = ((17 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0211Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0211Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0212 : ∀ x ∈ Icc ((((17 : ℚ) / 256) : ℚ) : ℝ) ((((9 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0212Lo = ((17 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0212Hi = ((9 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0212Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0212Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0213 : ∀ x ∈ Icc ((((9 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0213Lo = ((9 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0213Hi = ((21 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0213Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0213Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0214 : ∀ x ∈ Icc ((((21 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0214Lo = ((21 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0214Hi = ((11 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0214Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0214Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0215 : ∀ x ∈ Icc ((((11 : ℚ) / 128) : ℚ) : ℝ) ((((25 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0215Lo = ((11 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0215Hi = ((25 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0215Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0215Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock026 : ∀ x ∈ Icc ((((9 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0208 liftFrCWT1P0209) (cover_union liftFrCWT1P0210 liftFrCWT1P0211)) (cover_union (cover_union liftFrCWT1P0212 liftFrCWT1P0213) (cover_union liftFrCWT1P0214 liftFrCWT1P0215)))
#print axioms FrCWT1CoverBlock026

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

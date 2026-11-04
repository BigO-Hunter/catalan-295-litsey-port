module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0264
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0265
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0266
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0267
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0268
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0269
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0270
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0271

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0264 : ∀ x ∈ Icc ((((55 : ℚ) / 128) : ℚ) : ℝ) ((((111 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0264Lo = ((55 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0264Hi = ((111 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0264Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0264Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0265 : ∀ x ∈ Icc ((((111 : ℚ) / 256) : ℚ) : ℝ) ((((113 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0265Lo = ((111 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0265Hi = ((113 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0265Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0265Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0266 : ∀ x ∈ Icc ((((113 : ℚ) / 256) : ℚ) : ℝ) ((((57 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0266Lo = ((113 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0266Hi = ((57 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0266Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0266Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0267 : ∀ x ∈ Icc ((((57 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0267Lo = ((57 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0267Hi = ((29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0267Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0267Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0268 : ∀ x ∈ Icc ((((29 : ℚ) / 64) : ℚ) : ℝ) ((((117 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0268Lo = ((29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0268Hi = ((117 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0268Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0268Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0269 : ∀ x ∈ Icc ((((117 : ℚ) / 256) : ℚ) : ℝ) ((((59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0269Lo = ((117 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0269Hi = ((59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0269Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0269Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0270 : ∀ x ∈ Icc ((((59 : ℚ) / 128) : ℚ) : ℝ) ((((15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0270Lo = ((59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0270Hi = ((15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0270Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0270Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0271 : ∀ x ∈ Icc ((((15 : ℚ) / 32) : ℚ) : ℝ) ((((61 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0271Lo = ((15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0271Hi = ((61 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0271Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0271Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock033 : ∀ x ∈ Icc ((((55 : ℚ) / 128) : ℚ) : ℝ) ((((61 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0264 liftFrCWT1P0265) (cover_union liftFrCWT1P0266 liftFrCWT1P0267)) (cover_union (cover_union liftFrCWT1P0268 liftFrCWT1P0269) (cover_union liftFrCWT1P0270 liftFrCWT1P0271)))
#print axioms FrCWT1CoverBlock033

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

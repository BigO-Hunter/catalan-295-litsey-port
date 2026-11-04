module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0296
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0297
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0298
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0299
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0300
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0301
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0302
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0303

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0296 : ∀ x ∈ Icc ((((309 : ℚ) / 512) : ℚ) : ℝ) ((((155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0296Lo = ((309 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0296Hi = ((155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0296Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0296Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0297 : ∀ x ∈ Icc ((((155 : ℚ) / 256) : ℚ) : ℝ) ((((39 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0297Lo = ((155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0297Hi = ((39 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0297Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0297Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0298 : ∀ x ∈ Icc ((((39 : ℚ) / 64) : ℚ) : ℝ) ((((5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0298Lo = ((39 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0298Hi = ((5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT1P0298Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0298Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0299 : ∀ x ∈ Icc ((((5 : ℚ) / 8) : ℚ) : ℝ) ((((81 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0299Lo = ((5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT1P0299Hi = ((81 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0299Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0299Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0300 : ∀ x ∈ Icc ((((81 : ℚ) / 128) : ℚ) : ℝ) ((((163 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0300Lo = ((81 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0300Hi = ((163 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0300Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0300Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0301 : ∀ x ∈ Icc ((((163 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0301Lo = ((163 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0301Hi = ((41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0301Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0301Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0302 : ∀ x ∈ Icc ((((41 : ℚ) / 64) : ℚ) : ℝ) ((((329 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0302Lo = ((41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0302Hi = ((329 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0302Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0302Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0303 : ∀ x ∈ Icc ((((329 : ℚ) / 512) : ℚ) : ℝ) ((((83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0303Lo = ((329 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0303Hi = ((83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0303Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0303Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock037 : ∀ x ∈ Icc ((((309 : ℚ) / 512) : ℚ) : ℝ) ((((83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0296 liftFrCWT1P0297) (cover_union liftFrCWT1P0298 liftFrCWT1P0299)) (cover_union (cover_union liftFrCWT1P0300 liftFrCWT1P0301) (cover_union liftFrCWT1P0302 liftFrCWT1P0303)))
#print axioms FrCWT1CoverBlock037

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

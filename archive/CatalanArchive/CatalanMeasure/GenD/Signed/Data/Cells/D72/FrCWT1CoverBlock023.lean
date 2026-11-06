module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0184
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0185
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0186
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0187
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0188
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0189
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0190
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0191

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0184 : ∀ x ∈ Icc ((((-39 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0184Lo = ((-39 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0184Hi = ((-19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0184Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0184Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0185 : ∀ x ∈ Icc ((((-19 : ℚ) / 128) : ℚ) : ℝ) ((((-35 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0185Lo = ((-19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0185Hi = ((-35 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0185Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0185Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0186 : ∀ x ∈ Icc ((((-35 : ℚ) / 256) : ℚ) : ℝ) ((((-17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0186Lo = ((-35 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0186Hi = ((-17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0186Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0186Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0187 : ∀ x ∈ Icc ((((-17 : ℚ) / 128) : ℚ) : ℝ) ((((-31 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0187Lo = ((-17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0187Hi = ((-31 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0187Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0187Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0188 : ∀ x ∈ Icc ((((-31 : ℚ) / 256) : ℚ) : ℝ) ((((-15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0188Lo = ((-31 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0188Hi = ((-15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0188Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0188Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0189 : ∀ x ∈ Icc ((((-15 : ℚ) / 128) : ℚ) : ℝ) ((((-27 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0189Lo = ((-15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0189Hi = ((-27 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0189Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0189Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0190 : ∀ x ∈ Icc ((((-27 : ℚ) / 256) : ℚ) : ℝ) ((((-13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0190Lo = ((-27 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0190Hi = ((-13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0190Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0190Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0191 : ∀ x ∈ Icc ((((-13 : ℚ) / 128) : ℚ) : ℝ) ((((-23 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0191Lo = ((-13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0191Hi = ((-23 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0191Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0191Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock023 : ∀ x ∈ Icc ((((-39 : ℚ) / 256) : ℚ) : ℝ) ((((-23 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0184 liftFrCWT1P0185) (cover_union liftFrCWT1P0186 liftFrCWT1P0187)) (cover_union (cover_union liftFrCWT1P0188 liftFrCWT1P0189) (cover_union liftFrCWT1P0190 liftFrCWT1P0191)))
#print axioms FrCWT1CoverBlock023

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

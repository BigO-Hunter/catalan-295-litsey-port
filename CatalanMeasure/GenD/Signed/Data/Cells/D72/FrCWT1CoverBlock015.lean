module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0127

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0120 : ∀ x ∈ Icc ((((-179 : ℚ) / 256) : ℚ) : ℝ) ((((-89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0120Lo = ((-179 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0120Hi = ((-89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0120Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0120Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0121 : ∀ x ∈ Icc ((((-89 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0121Lo = ((-89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0121Hi = ((-11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0121Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0121Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0122 : ∀ x ∈ Icc ((((-11 : ℚ) / 16) : ℚ) : ℝ) ((((-43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0122Lo = ((-11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0122Hi = ((-43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0122Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0122Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0123 : ∀ x ∈ Icc ((((-43 : ℚ) / 64) : ℚ) : ℝ) ((((-85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0123Lo = ((-43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0123Hi = ((-85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0123Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0123Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0124 : ∀ x ∈ Icc ((((-85 : ℚ) / 128) : ℚ) : ℝ) ((((-169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0124Lo = ((-85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0124Hi = ((-169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0124Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0124Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0125 : ∀ x ∈ Icc ((((-169 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0125Lo = ((-169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0125Hi = ((-21 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0125Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0125Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0126 : ∀ x ∈ Icc ((((-21 : ℚ) / 32) : ℚ) : ℝ) ((((-83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0126Lo = ((-21 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0126Hi = ((-83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0126Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0126Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0127 : ∀ x ∈ Icc ((((-83 : ℚ) / 128) : ℚ) : ℝ) ((((-41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0127Lo = ((-83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0127Hi = ((-41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0127Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0127Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock015 : ∀ x ∈ Icc ((((-179 : ℚ) / 256) : ℚ) : ℝ) ((((-41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0120 liftFrCWT1P0121) (cover_union liftFrCWT1P0122 liftFrCWT1P0123)) (cover_union (cover_union liftFrCWT1P0124 liftFrCWT1P0125) (cover_union liftFrCWT1P0126 liftFrCWT1P0127)))
#print axioms FrCWT1CoverBlock015

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

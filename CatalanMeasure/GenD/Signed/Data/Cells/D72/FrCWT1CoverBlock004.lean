module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0039

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0032 : ∀ x ∈ Icc ((((-2047 : ℚ) / 2048) : ℚ) : ℝ) ((((-8187 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0032Lo = ((-2047 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0032Hi = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT1P0032Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0032Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0033 : ∀ x ∈ Icc ((((-8187 : ℚ) / 8192) : ℚ) : ℝ) ((((-4093 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0033Lo = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT1P0033Hi = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0033Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0033Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0034 : ∀ x ∈ Icc ((((-4093 : ℚ) / 4096) : ℚ) : ℝ) ((((-4091 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0034Lo = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0034Hi = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0034Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0034Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0035 : ∀ x ∈ Icc ((((-4091 : ℚ) / 4096) : ℚ) : ℝ) ((((-2045 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0035Lo = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0035Hi = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0035Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0035Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0036 : ∀ x ∈ Icc ((((-2045 : ℚ) / 2048) : ℚ) : ℝ) ((((-511 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0036Lo = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0036Hi = ((-511 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0036Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0036Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0037 : ∀ x ∈ Icc ((((-511 : ℚ) / 512) : ℚ) : ℝ) ((((-4087 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0037Lo = ((-511 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0037Hi = ((-4087 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0037Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0037Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0038 : ∀ x ∈ Icc ((((-4087 : ℚ) / 4096) : ℚ) : ℝ) ((((-2043 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0038Lo = ((-4087 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0038Hi = ((-2043 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0038Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0038Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0039 : ∀ x ∈ Icc ((((-2043 : ℚ) / 2048) : ℚ) : ℝ) ((((-4083 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0039Lo = ((-2043 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0039Hi = ((-4083 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0039Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0039Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock004 : ∀ x ∈ Icc ((((-2047 : ℚ) / 2048) : ℚ) : ℝ) ((((-4083 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0032 liftFrCWT1P0033) (cover_union liftFrCWT1P0034 liftFrCWT1P0035)) (cover_union (cover_union liftFrCWT1P0036 liftFrCWT1P0037) (cover_union liftFrCWT1P0038 liftFrCWT1P0039)))
#print axioms FrCWT1CoverBlock004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

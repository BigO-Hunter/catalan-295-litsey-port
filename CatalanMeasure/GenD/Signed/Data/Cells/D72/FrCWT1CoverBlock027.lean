module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0217
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0223

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0216 : ∀ x ∈ Icc ((((25 : ℚ) / 256) : ℚ) : ℝ) ((((13 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0216Lo = ((25 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0216Hi = ((13 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0216Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0216Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0217 : ∀ x ∈ Icc ((((13 : ℚ) / 128) : ℚ) : ℝ) ((((29 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0217Lo = ((13 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0217Hi = ((29 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0217Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0217Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0218 : ∀ x ∈ Icc ((((29 : ℚ) / 256) : ℚ) : ℝ) ((((15 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0218Lo = ((29 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0218Hi = ((15 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0218Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0218Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0219 : ∀ x ∈ Icc ((((15 : ℚ) / 128) : ℚ) : ℝ) ((((33 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0219Lo = ((15 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0219Hi = ((33 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0219Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0219Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0220 : ∀ x ∈ Icc ((((33 : ℚ) / 256) : ℚ) : ℝ) ((((17 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0220Lo = ((33 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0220Hi = ((17 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0220Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0220Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0221 : ∀ x ∈ Icc ((((17 : ℚ) / 128) : ℚ) : ℝ) ((((37 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0221Lo = ((17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0221Hi = ((37 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0221Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0221Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0222 : ∀ x ∈ Icc ((((37 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0222Lo = ((37 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0222Hi = ((19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0222Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0222Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0223 : ∀ x ∈ Icc ((((19 : ℚ) / 128) : ℚ) : ℝ) ((((41 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0223Lo = ((19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0223Hi = ((41 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0223Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0223Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock027 : ∀ x ∈ Icc ((((25 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0216 liftFrCWT1P0217) (cover_union liftFrCWT1P0218 liftFrCWT1P0219)) (cover_union (cover_union liftFrCWT1P0220 liftFrCWT1P0221) (cover_union liftFrCWT1P0222 liftFrCWT1P0223)))
#print axioms FrCWT1CoverBlock027

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

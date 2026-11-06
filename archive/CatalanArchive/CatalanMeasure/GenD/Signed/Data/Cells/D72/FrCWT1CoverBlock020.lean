module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0160
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0161
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0162
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0163
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0164
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0165
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0166
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0167

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0160 : ∀ x ∈ Icc ((((-3 : ℚ) / 8) : ℚ) : ℝ) ((((-47 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0160Lo = ((-3 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT1P0160Hi = ((-47 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0160Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0160Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0161 : ∀ x ∈ Icc ((((-47 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0161Lo = ((-47 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0161Hi = ((-11 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0161Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0161Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0162 : ∀ x ∈ Icc ((((-11 : ℚ) / 32) : ℚ) : ℝ) ((((-43 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0162Lo = ((-11 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0162Hi = ((-43 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0162Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0162Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0163 : ∀ x ∈ Icc ((((-43 : ℚ) / 128) : ℚ) : ℝ) ((((-85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0163Lo = ((-43 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0163Hi = ((-85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0163Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0163Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0164 : ∀ x ∈ Icc ((((-85 : ℚ) / 256) : ℚ) : ℝ) ((((-41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0164Lo = ((-85 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0164Hi = ((-41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0164Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0164Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0165 : ∀ x ∈ Icc ((((-41 : ℚ) / 128) : ℚ) : ℝ) ((((-81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0165Lo = ((-41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0165Hi = ((-81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0165Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0165Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0166 : ∀ x ∈ Icc ((((-81 : ℚ) / 256) : ℚ) : ℝ) ((((-39 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0166Lo = ((-81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0166Hi = ((-39 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0166Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0166Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0167 : ∀ x ∈ Icc ((((-39 : ℚ) / 128) : ℚ) : ℝ) ((((-77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0167Lo = ((-39 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0167Hi = ((-77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0167Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0167Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock020 : ∀ x ∈ Icc ((((-3 : ℚ) / 8) : ℚ) : ℝ) ((((-77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0160 liftFrCWT1P0161) (cover_union liftFrCWT1P0162 liftFrCWT1P0163)) (cover_union (cover_union liftFrCWT1P0164 liftFrCWT1P0165) (cover_union liftFrCWT1P0166 liftFrCWT1P0167)))
#print axioms FrCWT1CoverBlock020

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

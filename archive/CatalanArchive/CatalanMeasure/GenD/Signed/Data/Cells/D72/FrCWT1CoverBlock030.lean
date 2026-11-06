module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0240
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0241
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0242
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0243
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0244
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0245
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0246
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0247

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0240 : ∀ x ∈ Icc ((((73 : ℚ) / 256) : ℚ) : ℝ) ((((37 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0240Lo = ((73 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0240Hi = ((37 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0240Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0240Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0241 : ∀ x ∈ Icc ((((37 : ℚ) / 128) : ℚ) : ℝ) ((((19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0241Lo = ((37 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0241Hi = ((19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0241Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0241Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0242 : ∀ x ∈ Icc ((((19 : ℚ) / 64) : ℚ) : ℝ) ((((77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0242Lo = ((19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0242Hi = ((77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0242Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0242Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0243 : ∀ x ∈ Icc ((((77 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0243Lo = ((77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0243Hi = ((5 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0243Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0243Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0244 : ∀ x ∈ Icc ((((5 : ℚ) / 16) : ℚ) : ℝ) ((((81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0244Lo = ((5 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0244Hi = ((81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0244Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0244Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0245 : ∀ x ∈ Icc ((((81 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0245Lo = ((81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0245Hi = ((41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0245Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0245Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0246 : ∀ x ∈ Icc ((((41 : ℚ) / 128) : ℚ) : ℝ) ((((21 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0246Lo = ((41 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0246Hi = ((21 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0246Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0246Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0247 : ∀ x ∈ Icc ((((21 : ℚ) / 64) : ℚ) : ℝ) ((((85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0247Lo = ((21 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0247Hi = ((85 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0247Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0247Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock030 : ∀ x ∈ Icc ((((73 : ℚ) / 256) : ℚ) : ℝ) ((((85 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0240 liftFrCWT1P0241) (cover_union liftFrCWT1P0242 liftFrCWT1P0243)) (cover_union (cover_union liftFrCWT1P0244 liftFrCWT1P0245) (cover_union liftFrCWT1P0246 liftFrCWT1P0247)))
#print axioms FrCWT1CoverBlock030

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

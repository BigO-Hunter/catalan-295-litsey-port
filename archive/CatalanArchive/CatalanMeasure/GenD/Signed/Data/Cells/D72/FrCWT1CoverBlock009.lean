module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0072
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0073
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0074
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0075
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0076
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0077
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0078
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0079

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0072 : ∀ x ∈ Icc ((((-61 : ℚ) / 64) : ℚ) : ℝ) ((((-121 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0072Lo = ((-61 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0072Hi = ((-121 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0072Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0072Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0073 : ∀ x ∈ Icc ((((-121 : ℚ) / 128) : ℚ) : ℝ) ((((-483 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0073Lo = ((-121 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0073Hi = ((-483 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0073Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0073Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0074 : ∀ x ∈ Icc ((((-483 : ℚ) / 512) : ℚ) : ℝ) ((((-481 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0074Lo = ((-483 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0074Hi = ((-481 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0074Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0074Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0075 : ∀ x ∈ Icc ((((-481 : ℚ) / 512) : ℚ) : ℝ) ((((-15 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0075Lo = ((-481 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0075Hi = ((-15 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0075Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0075Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0076 : ∀ x ∈ Icc ((((-15 : ℚ) / 16) : ℚ) : ℝ) ((((-119 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0076Lo = ((-15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0076Hi = ((-119 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0076Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0076Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0077 : ∀ x ∈ Icc ((((-119 : ℚ) / 128) : ℚ) : ℝ) ((((-237 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0077Lo = ((-119 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0077Hi = ((-237 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0077Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0077Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0078 : ∀ x ∈ Icc ((((-237 : ℚ) / 256) : ℚ) : ℝ) ((((-473 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0078Lo = ((-237 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0078Hi = ((-473 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0078Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0078Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0079 : ∀ x ∈ Icc ((((-473 : ℚ) / 512) : ℚ) : ℝ) ((((-471 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0079Lo = ((-473 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0079Hi = ((-471 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0079Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0079Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock009 : ∀ x ∈ Icc ((((-61 : ℚ) / 64) : ℚ) : ℝ) ((((-471 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0072 liftFrCWT1P0073) (cover_union liftFrCWT1P0074 liftFrCWT1P0075)) (cover_union (cover_union liftFrCWT1P0076 liftFrCWT1P0077) (cover_union liftFrCWT1P0078 liftFrCWT1P0079)))
#print axioms FrCWT1CoverBlock009

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

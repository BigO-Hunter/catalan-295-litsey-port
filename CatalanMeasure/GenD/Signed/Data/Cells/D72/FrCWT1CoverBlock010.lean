module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0087

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0080 : ∀ x ∈ Icc ((((-471 : ℚ) / 512) : ℚ) : ℝ) ((((-117 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0080Lo = ((-471 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0080Hi = ((-117 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0080Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0080Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0081 : ∀ x ∈ Icc ((((-117 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0081Lo = ((-117 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0081Hi = ((-29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0081Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0081Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0082 : ∀ x ∈ Icc ((((-29 : ℚ) / 32) : ℚ) : ℝ) ((((-115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0082Lo = ((-29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0082Hi = ((-115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0082Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0082Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0083 : ∀ x ∈ Icc ((((-115 : ℚ) / 128) : ℚ) : ℝ) ((((-459 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0083Lo = ((-115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0083Hi = ((-459 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0083Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0083Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0084 : ∀ x ∈ Icc ((((-459 : ℚ) / 512) : ℚ) : ℝ) ((((-229 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0084Lo = ((-459 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0084Hi = ((-229 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0084Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0084Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0085 : ∀ x ∈ Icc ((((-229 : ℚ) / 256) : ℚ) : ℝ) ((((-57 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0085Lo = ((-229 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0085Hi = ((-57 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0085Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0085Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0086 : ∀ x ∈ Icc ((((-57 : ℚ) / 64) : ℚ) : ℝ) ((((-113 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0086Lo = ((-57 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0086Hi = ((-113 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0086Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0086Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0087 : ∀ x ∈ Icc ((((-113 : ℚ) / 128) : ℚ) : ℝ) ((((-225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0087Lo = ((-113 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0087Hi = ((-225 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0087Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0087Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock010 : ∀ x ∈ Icc ((((-471 : ℚ) / 512) : ℚ) : ℝ) ((((-225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0080 liftFrCWT1P0081) (cover_union liftFrCWT1P0082 liftFrCWT1P0083)) (cover_union (cover_union liftFrCWT1P0084 liftFrCWT1P0085) (cover_union liftFrCWT1P0086 liftFrCWT1P0087)))
#print axioms FrCWT1CoverBlock010

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

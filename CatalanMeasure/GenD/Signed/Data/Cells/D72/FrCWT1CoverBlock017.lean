module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0143

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0136 : ∀ x ∈ Icc ((((-35 : ℚ) / 64) : ℚ) : ℝ) ((((-139 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0136Lo = ((-35 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0136Hi = ((-139 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0136Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0136Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0137 : ∀ x ∈ Icc ((((-139 : ℚ) / 256) : ℚ) : ℝ) ((((-69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0137Lo = ((-139 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0137Hi = ((-69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0137Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0137Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0138 : ∀ x ∈ Icc ((((-69 : ℚ) / 128) : ℚ) : ℝ) ((((-67 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0138Lo = ((-69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0138Hi = ((-67 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0138Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0138Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0139 : ∀ x ∈ Icc ((((-67 : ℚ) / 128) : ℚ) : ℝ) ((((-133 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0139Lo = ((-67 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0139Hi = ((-133 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0139Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0139Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0140 : ∀ x ∈ Icc ((((-133 : ℚ) / 256) : ℚ) : ℝ) ((((-33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0140Lo = ((-133 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0140Hi = ((-33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0140Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0140Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0141 : ∀ x ∈ Icc ((((-33 : ℚ) / 64) : ℚ) : ℝ) ((((-65 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0141Lo = ((-33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0141Hi = ((-65 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0141Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0141Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0142 : ∀ x ∈ Icc ((((-65 : ℚ) / 128) : ℚ) : ℝ) ((((-1 : ℚ) / 2) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0142Lo = ((-65 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0142Hi = ((-1 : ℚ) / 2) := by decide +kernel
  have hcap : FrCWT1P0142Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0142Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0143 : ∀ x ∈ Icc ((((-1 : ℚ) / 2) : ℚ) : ℝ) ((((-63 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0143Lo = ((-1 : ℚ) / 2) := by decide +kernel
  have hhi : ceFrCWT1P0143Hi = ((-63 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0143Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0143Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock017 : ∀ x ∈ Icc ((((-35 : ℚ) / 64) : ℚ) : ℝ) ((((-63 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0136 liftFrCWT1P0137) (cover_union liftFrCWT1P0138 liftFrCWT1P0139)) (cover_union (cover_union liftFrCWT1P0140 liftFrCWT1P0141) (cover_union liftFrCWT1P0142 liftFrCWT1P0143)))
#print axioms FrCWT1CoverBlock017

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

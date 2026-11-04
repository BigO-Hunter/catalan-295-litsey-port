module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0144
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0151

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0144 : ∀ x ∈ Icc ((((-63 : ℚ) / 128) : ℚ) : ℝ) ((((-125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0144Lo = ((-63 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0144Hi = ((-125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0144Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0144Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0145 : ∀ x ∈ Icc ((((-125 : ℚ) / 256) : ℚ) : ℝ) ((((-31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0145Lo = ((-125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0145Hi = ((-31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0145Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0145Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0146 : ∀ x ∈ Icc ((((-31 : ℚ) / 64) : ℚ) : ℝ) ((((-15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0146Lo = ((-31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0146Hi = ((-15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0146Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0146Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0147 : ∀ x ∈ Icc ((((-15 : ℚ) / 32) : ℚ) : ℝ) ((((-119 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0147Lo = ((-15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0147Hi = ((-119 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0147Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0147Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0148 : ∀ x ∈ Icc ((((-119 : ℚ) / 256) : ℚ) : ℝ) ((((-59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0148Lo = ((-119 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0148Hi = ((-59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0148Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0148Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0149 : ∀ x ∈ Icc ((((-59 : ℚ) / 128) : ℚ) : ℝ) ((((-29 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0149Lo = ((-59 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0149Hi = ((-29 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0149Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0149Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0150 : ∀ x ∈ Icc ((((-29 : ℚ) / 64) : ℚ) : ℝ) ((((-7 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0150Lo = ((-29 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0150Hi = ((-7 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0150Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0150Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0151 : ∀ x ∈ Icc ((((-7 : ℚ) / 16) : ℚ) : ℝ) ((((-111 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0151Lo = ((-7 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0151Hi = ((-111 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0151Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0151Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock018 : ∀ x ∈ Icc ((((-63 : ℚ) / 128) : ℚ) : ℝ) ((((-111 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0144 liftFrCWT1P0145) (cover_union liftFrCWT1P0146 liftFrCWT1P0147)) (cover_union (cover_union liftFrCWT1P0148 liftFrCWT1P0149) (cover_union liftFrCWT1P0150 liftFrCWT1P0151)))
#print axioms FrCWT1CoverBlock018

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

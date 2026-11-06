module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0336
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0337
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0338
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0339
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0340
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0341
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0342
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0343

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0336 : ∀ x ∈ Icc ((((101 : ℚ) / 128) : ℚ) : ℝ) ((((51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0336Lo = ((101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0336Hi = ((51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0336Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0336Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0337 : ∀ x ∈ Icc ((((51 : ℚ) / 64) : ℚ) : ℝ) ((((205 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0337Lo = ((51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0337Hi = ((205 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0337Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0337Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0338 : ∀ x ∈ Icc ((((205 : ℚ) / 256) : ℚ) : ℝ) ((((411 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0338Lo = ((205 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0338Hi = ((411 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0338Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0338Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0339 : ∀ x ∈ Icc ((((411 : ℚ) / 512) : ℚ) : ℝ) ((((103 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0339Lo = ((411 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0339Hi = ((103 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0339Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0339Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0340 : ∀ x ∈ Icc ((((103 : ℚ) / 128) : ℚ) : ℝ) ((((415 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0340Lo = ((103 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0340Hi = ((415 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0340Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0340Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0341 : ∀ x ∈ Icc ((((415 : ℚ) / 512) : ℚ) : ℝ) ((((13 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0341Lo = ((415 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0341Hi = ((13 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT1P0341Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0341Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0342 : ∀ x ∈ Icc ((((13 : ℚ) / 16) : ℚ) : ℝ) ((((209 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0342Lo = ((13 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT1P0342Hi = ((209 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0342Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0342Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0343 : ∀ x ∈ Icc ((((209 : ℚ) / 256) : ℚ) : ℝ) ((((105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0343Lo = ((209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0343Hi = ((105 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0343Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0343Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock042 : ∀ x ∈ Icc ((((101 : ℚ) / 128) : ℚ) : ℝ) ((((105 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0336 liftFrCWT1P0337) (cover_union liftFrCWT1P0338 liftFrCWT1P0339)) (cover_union (cover_union liftFrCWT1P0340 liftFrCWT1P0341) (cover_union liftFrCWT1P0342 liftFrCWT1P0343)))
#print axioms FrCWT1CoverBlock042

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

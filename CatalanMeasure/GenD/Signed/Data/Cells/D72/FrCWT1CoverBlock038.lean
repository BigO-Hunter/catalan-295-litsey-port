module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0304
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0305
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0306
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0307
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0308
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0309
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0310
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0311

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0304 : ∀ x ∈ Icc ((((83 : ℚ) / 128) : ℚ) : ℝ) ((((167 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0304Lo = ((83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0304Hi = ((167 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0304Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0304Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0305 : ∀ x ∈ Icc ((((167 : ℚ) / 256) : ℚ) : ℝ) ((((335 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0305Lo = ((167 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0305Hi = ((335 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0305Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0305Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0306 : ∀ x ∈ Icc ((((335 : ℚ) / 512) : ℚ) : ℝ) ((((169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0306Lo = ((335 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0306Hi = ((169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0306Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0306Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0307 : ∀ x ∈ Icc ((((169 : ℚ) / 256) : ℚ) : ℝ) ((((85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0307Lo = ((169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0307Hi = ((85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0307Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0307Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0308 : ∀ x ∈ Icc ((((85 : ℚ) / 128) : ℚ) : ℝ) ((((341 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0308Lo = ((85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0308Hi = ((341 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0308Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0308Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0309 : ∀ x ∈ Icc ((((341 : ℚ) / 512) : ℚ) : ℝ) ((((43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0309Lo = ((341 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0309Hi = ((43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0309Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0309Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0310 : ∀ x ∈ Icc ((((43 : ℚ) / 64) : ℚ) : ℝ) ((((173 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0310Lo = ((43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0310Hi = ((173 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0310Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0310Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0311 : ∀ x ∈ Icc ((((173 : ℚ) / 256) : ℚ) : ℝ) ((((347 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0311Lo = ((173 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0311Hi = ((347 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0311Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0311Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock038 : ∀ x ∈ Icc ((((83 : ℚ) / 128) : ℚ) : ℝ) ((((347 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0304 liftFrCWT1P0305) (cover_union liftFrCWT1P0306 liftFrCWT1P0307)) (cover_union (cover_union liftFrCWT1P0308 liftFrCWT1P0309) (cover_union liftFrCWT1P0310 liftFrCWT1P0311)))
#print axioms FrCWT1CoverBlock038

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

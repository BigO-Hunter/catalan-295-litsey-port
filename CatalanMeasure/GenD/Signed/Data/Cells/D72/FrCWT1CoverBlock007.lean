module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0056
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0057
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0058
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0059
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0060
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0061
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0062
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0063

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0056 : ∀ x ∈ Icc ((((-503 : ℚ) / 512) : ℚ) : ℝ) ((((-1005 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0056Lo = ((-503 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0056Hi = ((-1005 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0056Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0056Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0057 : ∀ x ∈ Icc ((((-1005 : ℚ) / 1024) : ℚ) : ℝ) ((((-2009 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0057Lo = ((-1005 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0057Hi = ((-2009 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0057Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0057Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0058 : ∀ x ∈ Icc ((((-2009 : ℚ) / 2048) : ℚ) : ℝ) ((((-501 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0058Lo = ((-2009 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0058Hi = ((-501 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0058Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0058Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0059 : ∀ x ∈ Icc ((((-501 : ℚ) / 512) : ℚ) : ℝ) ((((-1001 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0059Lo = ((-501 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT1P0059Hi = ((-1001 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0059Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0059Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0060 : ∀ x ∈ Icc ((((-1001 : ℚ) / 1024) : ℚ) : ℝ) ((((-125 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0060Lo = ((-1001 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0060Hi = ((-125 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0060Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0060Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0061 : ∀ x ∈ Icc ((((-125 : ℚ) / 128) : ℚ) : ℝ) ((((-249 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0061Lo = ((-125 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0061Hi = ((-249 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0061Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0061Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0062 : ∀ x ∈ Icc ((((-249 : ℚ) / 256) : ℚ) : ℝ) ((((-995 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0062Lo = ((-249 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0062Hi = ((-995 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0062Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0062Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0063 : ∀ x ∈ Icc ((((-995 : ℚ) / 1024) : ℚ) : ℝ) ((((-497 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0063Lo = ((-995 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0063Hi = ((-497 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT1P0063Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0063Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock007 : ∀ x ∈ Icc ((((-503 : ℚ) / 512) : ℚ) : ℝ) ((((-497 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0056 liftFrCWT1P0057) (cover_union liftFrCWT1P0058 liftFrCWT1P0059)) (cover_union (cover_union liftFrCWT1P0060 liftFrCWT1P0061) (cover_union liftFrCWT1P0062 liftFrCWT1P0063)))
#print axioms FrCWT1CoverBlock007

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

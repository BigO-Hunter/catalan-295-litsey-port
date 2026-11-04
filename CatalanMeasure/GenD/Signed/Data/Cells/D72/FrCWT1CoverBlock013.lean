module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0111

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0104 : ∀ x ∈ Icc ((((-51 : ℚ) / 64) : ℚ) : ℝ) ((((-203 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0104Lo = ((-51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0104Hi = ((-203 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0104Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0104Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0105 : ∀ x ∈ Icc ((((-203 : ℚ) / 256) : ℚ) : ℝ) ((((-101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0105Lo = ((-203 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0105Hi = ((-101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0105Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0105Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0106 : ∀ x ∈ Icc ((((-101 : ℚ) / 128) : ℚ) : ℝ) ((((-201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0106Lo = ((-101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0106Hi = ((-201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0106Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0106Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0107 : ∀ x ∈ Icc ((((-201 : ℚ) / 256) : ℚ) : ℝ) ((((-99 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0107Lo = ((-201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0107Hi = ((-99 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0107Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0107Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0108 : ∀ x ∈ Icc ((((-99 : ℚ) / 128) : ℚ) : ℝ) ((((-197 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0108Lo = ((-99 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0108Hi = ((-197 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0108Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0108Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0109 : ∀ x ∈ Icc ((((-197 : ℚ) / 256) : ℚ) : ℝ) ((((-49 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0109Lo = ((-197 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0109Hi = ((-49 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0109Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0109Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0110 : ∀ x ∈ Icc ((((-49 : ℚ) / 64) : ℚ) : ℝ) ((((-97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0110Lo = ((-49 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0110Hi = ((-97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0110Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0110Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0111 : ∀ x ∈ Icc ((((-97 : ℚ) / 128) : ℚ) : ℝ) ((((-3 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0111Lo = ((-97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0111Hi = ((-3 : ℚ) / 4) := by decide +kernel
  have hcap : FrCWT1P0111Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0111Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock013 : ∀ x ∈ Icc ((((-51 : ℚ) / 64) : ℚ) : ℝ) ((((-3 : ℚ) / 4) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0104 liftFrCWT1P0105) (cover_union liftFrCWT1P0106 liftFrCWT1P0107)) (cover_union (cover_union liftFrCWT1P0108 liftFrCWT1P0109) (cover_union liftFrCWT1P0110 liftFrCWT1P0111)))
#print axioms FrCWT1CoverBlock013

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

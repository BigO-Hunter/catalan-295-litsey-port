module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0023

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0016 : ∀ x ∈ Icc ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ) ((((-16777213 : ℚ) / 16777216) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0016Lo = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hhi : ceFrCWT1P0016Hi = ((-16777213 : ℚ) / 16777216) := by decide +kernel
  have hcap : FrCWT1P0016Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0016Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0017 : ∀ x ∈ Icc ((((-16777213 : ℚ) / 16777216) : ℚ) : ℝ) ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0017Lo = ((-16777213 : ℚ) / 16777216) := by decide +kernel
  have hhi : ceFrCWT1P0017Hi = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hcap : FrCWT1P0017Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0017Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0018 : ∀ x ∈ Icc ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ) ((((-8388605 : ℚ) / 8388608) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0018Lo = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hhi : ceFrCWT1P0018Hi = ((-8388605 : ℚ) / 8388608) := by decide +kernel
  have hcap : FrCWT1P0018Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0018Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0019 : ∀ x ∈ Icc ((((-8388605 : ℚ) / 8388608) : ℚ) : ℝ) ((((-1048575 : ℚ) / 1048576) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0019Lo = ((-8388605 : ℚ) / 8388608) := by decide +kernel
  have hhi : ceFrCWT1P0019Hi = ((-1048575 : ℚ) / 1048576) := by decide +kernel
  have hcap : FrCWT1P0019Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0019Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0020 : ∀ x ∈ Icc ((((-1048575 : ℚ) / 1048576) : ℚ) : ℝ) ((((-524287 : ℚ) / 524288) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0020Lo = ((-1048575 : ℚ) / 1048576) := by decide +kernel
  have hhi : ceFrCWT1P0020Hi = ((-524287 : ℚ) / 524288) := by decide +kernel
  have hcap : FrCWT1P0020Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0020Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0021 : ∀ x ∈ Icc ((((-524287 : ℚ) / 524288) : ℚ) : ℝ) ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0021Lo = ((-524287 : ℚ) / 524288) := by decide +kernel
  have hhi : ceFrCWT1P0021Hi = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hcap : FrCWT1P0021Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0021Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0022 : ∀ x ∈ Icc ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ) ((((-262143 : ℚ) / 262144) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0022Lo = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hhi : ceFrCWT1P0022Hi = ((-262143 : ℚ) / 262144) := by decide +kernel
  have hcap : FrCWT1P0022Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0022Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0023 : ∀ x ∈ Icc ((((-262143 : ℚ) / 262144) : ℚ) : ℝ) ((((-131071 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0023Lo = ((-262143 : ℚ) / 262144) := by decide +kernel
  have hhi : ceFrCWT1P0023Hi = ((-131071 : ℚ) / 131072) := by decide +kernel
  have hcap : FrCWT1P0023Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0023Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock002 : ∀ x ∈ Icc ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ) ((((-131071 : ℚ) / 131072) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0016 liftFrCWT1P0017) (cover_union liftFrCWT1P0018 liftFrCWT1P0019)) (cover_union (cover_union liftFrCWT1P0020 liftFrCWT1P0021) (cover_union liftFrCWT1P0022 liftFrCWT1P0023)))
#print axioms FrCWT1CoverBlock002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

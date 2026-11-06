module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0231

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0224 : ∀ x ∈ Icc ((((41 : ℚ) / 256) : ℚ) : ℝ) ((((21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0224Lo = ((41 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0224Hi = ((21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0224Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0224Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0225 : ∀ x ∈ Icc ((((21 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0225Lo = ((21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0225Hi = ((45 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0225Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0225Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0226 : ∀ x ∈ Icc ((((45 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0226Lo = ((45 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0226Hi = ((23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0226Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0226Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0227 : ∀ x ∈ Icc ((((23 : ℚ) / 128) : ℚ) : ℝ) ((((49 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0227Lo = ((23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0227Hi = ((49 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0227Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0227Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0228 : ∀ x ∈ Icc ((((49 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0228Lo = ((49 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0228Hi = ((25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0228Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0228Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0229 : ∀ x ∈ Icc ((((25 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0229Lo = ((25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0229Hi = ((13 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0229Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0229Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0230 : ∀ x ∈ Icc ((((13 : ℚ) / 64) : ℚ) : ℝ) ((((53 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0230Lo = ((13 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0230Hi = ((53 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0230Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0230Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0231 : ∀ x ∈ Icc ((((53 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0231Lo = ((53 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0231Hi = ((27 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0231Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0231Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock028 : ∀ x ∈ Icc ((((41 : ℚ) / 256) : ℚ) : ℝ) ((((27 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0224 liftFrCWT1P0225) (cover_union liftFrCWT1P0226 liftFrCWT1P0227)) (cover_union (cover_union liftFrCWT1P0228 liftFrCWT1P0229) (cover_union liftFrCWT1P0230 liftFrCWT1P0231)))
#print axioms FrCWT1CoverBlock028

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0224
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0225
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0226
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0227
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0228
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0229
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0230
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0231

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0224 : ∀ x ∈ Icc ((((17 : ℚ) / 128) : ℚ) : ℝ) ((((37 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0224Lo = ((17 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0224Hi = ((37 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0224Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0224Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0225 : ∀ x ∈ Icc ((((37 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0225Lo = ((37 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0225Hi = ((19 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0225Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0225Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0226 : ∀ x ∈ Icc ((((19 : ℚ) / 128) : ℚ) : ℝ) ((((41 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0226Lo = ((19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0226Hi = ((41 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0226Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0226Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0227 : ∀ x ∈ Icc ((((41 : ℚ) / 256) : ℚ) : ℝ) ((((21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0227Lo = ((41 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0227Hi = ((21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0227Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0227Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0228 : ∀ x ∈ Icc ((((21 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0228Lo = ((21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0228Hi = ((45 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0228Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0228Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0229 : ∀ x ∈ Icc ((((45 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0229Lo = ((45 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0229Hi = ((23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0229Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0229Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0230 : ∀ x ∈ Icc ((((23 : ℚ) / 128) : ℚ) : ℝ) ((((49 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0230Lo = ((23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0230Hi = ((49 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0230Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0230Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0231 : ∀ x ∈ Icc ((((49 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0231Lo = ((49 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0231Hi = ((25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0231Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0231Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock028 : ∀ x ∈ Icc ((((17 : ℚ) / 128) : ℚ) : ℝ) ((((25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0224 liftFrCWT0P0225) (cover_union liftFrCWT0P0226 liftFrCWT0P0227)) (cover_union (cover_union liftFrCWT0P0228 liftFrCWT0P0229) (cover_union liftFrCWT0P0230 liftFrCWT0P0231)))
#print axioms FrCWT0CoverBlock028

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

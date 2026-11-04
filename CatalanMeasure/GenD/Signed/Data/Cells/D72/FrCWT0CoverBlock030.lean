module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0240
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0241
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0242
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0243
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0244
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0245
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0246
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0247

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0240 : ∀ x ∈ Icc ((((17 : ℚ) / 64) : ℚ) : ℝ) ((((35 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0240Lo = ((17 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0240Hi = ((35 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0240Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0240Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0241 : ∀ x ∈ Icc ((((35 : ℚ) / 128) : ℚ) : ℝ) ((((9 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0241Lo = ((35 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0241Hi = ((9 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0241Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0241Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0242 : ∀ x ∈ Icc ((((9 : ℚ) / 32) : ℚ) : ℝ) ((((73 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0242Lo = ((9 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0242Hi = ((73 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0242Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0242Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0243 : ∀ x ∈ Icc ((((73 : ℚ) / 256) : ℚ) : ℝ) ((((19 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0243Lo = ((73 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0243Hi = ((19 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0243Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0243Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0244 : ∀ x ∈ Icc ((((19 : ℚ) / 64) : ℚ) : ℝ) ((((77 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0244Lo = ((19 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0244Hi = ((77 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0244Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0244Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0245 : ∀ x ∈ Icc ((((77 : ℚ) / 256) : ℚ) : ℝ) ((((5 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0245Lo = ((77 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0245Hi = ((5 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0245Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0245Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0246 : ∀ x ∈ Icc ((((5 : ℚ) / 16) : ℚ) : ℝ) ((((81 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0246Lo = ((5 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0246Hi = ((81 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0246Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0246Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0247 : ∀ x ∈ Icc ((((81 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0247Lo = ((81 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0247Hi = ((41 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0247Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0247Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock030 : ∀ x ∈ Icc ((((17 : ℚ) / 64) : ℚ) : ℝ) ((((41 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0240 liftFrCWT0P0241) (cover_union liftFrCWT0P0242 liftFrCWT0P0243)) (cover_union (cover_union liftFrCWT0P0244 liftFrCWT0P0245) (cover_union liftFrCWT0P0246 liftFrCWT0P0247)))
#print axioms FrCWT0CoverBlock030

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

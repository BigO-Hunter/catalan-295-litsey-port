module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0304
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0305
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0306
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0307
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0308
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0309
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0310
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0311

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0304 : ∀ x ∈ Icc ((((163 : ℚ) / 256) : ℚ) : ℝ) ((((41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0304Lo = ((163 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0304Hi = ((41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0304Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0304Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0305 : ∀ x ∈ Icc ((((41 : ℚ) / 64) : ℚ) : ℝ) ((((329 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0305Lo = ((41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0305Hi = ((329 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0305Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0305Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0306 : ∀ x ∈ Icc ((((329 : ℚ) / 512) : ℚ) : ℝ) ((((83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0306Lo = ((329 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0306Hi = ((83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0306Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0306Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0307 : ∀ x ∈ Icc ((((83 : ℚ) / 128) : ℚ) : ℝ) ((((167 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0307Lo = ((83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0307Hi = ((167 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0307Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0307Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0308 : ∀ x ∈ Icc ((((167 : ℚ) / 256) : ℚ) : ℝ) ((((335 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0308Lo = ((167 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0308Hi = ((335 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0308Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0308Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0309 : ∀ x ∈ Icc ((((335 : ℚ) / 512) : ℚ) : ℝ) ((((169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0309Lo = ((335 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0309Hi = ((169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0309Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0309Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0310 : ∀ x ∈ Icc ((((169 : ℚ) / 256) : ℚ) : ℝ) ((((85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0310Lo = ((169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0310Hi = ((85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0310Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0310Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0311 : ∀ x ∈ Icc ((((85 : ℚ) / 128) : ℚ) : ℝ) ((((341 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0311Lo = ((85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0311Hi = ((341 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0311Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0311Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock038 : ∀ x ∈ Icc ((((163 : ℚ) / 256) : ℚ) : ℝ) ((((341 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0304 liftFrCWT0P0305) (cover_union liftFrCWT0P0306 liftFrCWT0P0307)) (cover_union (cover_union liftFrCWT0P0308 liftFrCWT0P0309) (cover_union liftFrCWT0P0310 liftFrCWT0P0311)))
#print axioms FrCWT0CoverBlock038

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0280
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0281
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0282
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0283
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0284
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0285
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0286
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0287

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0280 : ∀ x ∈ Icc ((((131 : ℚ) / 256) : ℚ) : ℝ) ((((33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0280Lo = ((131 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0280Hi = ((33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0280Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0280Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0281 : ∀ x ∈ Icc ((((33 : ℚ) / 64) : ℚ) : ℝ) ((((17 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0281Lo = ((33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0281Hi = ((17 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0281Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0281Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0282 : ∀ x ∈ Icc ((((17 : ℚ) / 32) : ℚ) : ℝ) ((((137 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0282Lo = ((17 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0282Hi = ((137 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0282Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0282Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0283 : ∀ x ∈ Icc ((((137 : ℚ) / 256) : ℚ) : ℝ) ((((69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0283Lo = ((137 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0283Hi = ((69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0283Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0283Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0284 : ∀ x ∈ Icc ((((69 : ℚ) / 128) : ℚ) : ℝ) ((((277 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0284Lo = ((69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0284Hi = ((277 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0284Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0284Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0285 : ∀ x ∈ Icc ((((277 : ℚ) / 512) : ℚ) : ℝ) ((((35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0285Lo = ((277 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0285Hi = ((35 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0285Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0285Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0286 : ∀ x ∈ Icc ((((35 : ℚ) / 64) : ℚ) : ℝ) ((((141 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0286Lo = ((35 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0286Hi = ((141 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0286Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0286Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0287 : ∀ x ∈ Icc ((((141 : ℚ) / 256) : ℚ) : ℝ) ((((71 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0287Lo = ((141 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0287Hi = ((71 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0287Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0287Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock035 : ∀ x ∈ Icc ((((131 : ℚ) / 256) : ℚ) : ℝ) ((((71 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0280 liftFrCWT0P0281) (cover_union liftFrCWT0P0282 liftFrCWT0P0283)) (cover_union (cover_union liftFrCWT0P0284 liftFrCWT0P0285) (cover_union liftFrCWT0P0286 liftFrCWT0P0287)))
#print axioms FrCWT0CoverBlock035

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

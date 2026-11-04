module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0080
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0081
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0082
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0083
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0084
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0085
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0086
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0087

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0080 : ∀ x ∈ Icc ((((-15 : ℚ) / 16) : ℚ) : ℝ) ((((-119 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0080Lo = ((-15 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0080Hi = ((-119 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0080Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0080Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0081 : ∀ x ∈ Icc ((((-119 : ℚ) / 128) : ℚ) : ℝ) ((((-237 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0081Lo = ((-119 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0081Hi = ((-237 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0081Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0081Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0082 : ∀ x ∈ Icc ((((-237 : ℚ) / 256) : ℚ) : ℝ) ((((-473 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0082Lo = ((-237 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0082Hi = ((-473 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0082Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0082Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0083 : ∀ x ∈ Icc ((((-473 : ℚ) / 512) : ℚ) : ℝ) ((((-471 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0083Lo = ((-473 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0083Hi = ((-471 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0083Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0083Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0084 : ∀ x ∈ Icc ((((-471 : ℚ) / 512) : ℚ) : ℝ) ((((-117 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0084Lo = ((-471 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0084Hi = ((-117 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0084Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0084Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0085 : ∀ x ∈ Icc ((((-117 : ℚ) / 128) : ℚ) : ℝ) ((((-233 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0085Lo = ((-117 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0085Hi = ((-233 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0085Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0085Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0086 : ∀ x ∈ Icc ((((-233 : ℚ) / 256) : ℚ) : ℝ) ((((-465 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0086Lo = ((-233 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0086Hi = ((-465 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0086Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0086Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0087 : ∀ x ∈ Icc ((((-465 : ℚ) / 512) : ℚ) : ℝ) ((((-29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0087Lo = ((-465 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0087Hi = ((-29 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0087Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0087Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock010 : ∀ x ∈ Icc ((((-15 : ℚ) / 16) : ℚ) : ℝ) ((((-29 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0080 liftFrCWT0P0081) (cover_union liftFrCWT0P0082 liftFrCWT0P0083)) (cover_union (cover_union liftFrCWT0P0084 liftFrCWT0P0085) (cover_union liftFrCWT0P0086 liftFrCWT0P0087)))
#print axioms FrCWT0CoverBlock010

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0320
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0321
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0322
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0323
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0324
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0325
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0326
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0327

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0320 : ∀ x ∈ Icc ((((45 : ℚ) / 64) : ℚ) : ℝ) ((((363 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0320Lo = ((45 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0320Hi = ((363 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0320Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0320Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0321 : ∀ x ∈ Icc ((((363 : ℚ) / 512) : ℚ) : ℝ) ((((91 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0321Lo = ((363 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0321Hi = ((91 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0321Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0321Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0322 : ∀ x ∈ Icc ((((91 : ℚ) / 128) : ℚ) : ℝ) ((((183 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0322Lo = ((91 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0322Hi = ((183 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0322Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0322Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0323 : ∀ x ∈ Icc ((((183 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0323Lo = ((183 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0323Hi = ((23 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0323Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0323Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0324 : ∀ x ∈ Icc ((((23 : ℚ) / 32) : ℚ) : ℝ) ((((369 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0324Lo = ((23 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0324Hi = ((369 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0324Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0324Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0325 : ∀ x ∈ Icc ((((369 : ℚ) / 512) : ℚ) : ℝ) ((((185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0325Lo = ((369 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0325Hi = ((185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0325Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0325Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0326 : ∀ x ∈ Icc ((((185 : ℚ) / 256) : ℚ) : ℝ) ((((187 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0326Lo = ((185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0326Hi = ((187 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0326Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0326Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0327 : ∀ x ∈ Icc ((((187 : ℚ) / 256) : ℚ) : ℝ) ((((47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0327Lo = ((187 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0327Hi = ((47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0327Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0327Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock040 : ∀ x ∈ Icc ((((45 : ℚ) / 64) : ℚ) : ℝ) ((((47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0320 liftFrCWT0P0321) (cover_union liftFrCWT0P0322 liftFrCWT0P0323)) (cover_union (cover_union liftFrCWT0P0324 liftFrCWT0P0325) (cover_union liftFrCWT0P0326 liftFrCWT0P0327)))
#print axioms FrCWT0CoverBlock040

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

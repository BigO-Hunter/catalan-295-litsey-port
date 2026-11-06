module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0015

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0008 : ∀ x ∈ Icc ((((-2199023255549 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((-274877906943 : ℚ) / 274877906944) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0008Lo = ((-2199023255549 : ℚ) / 2199023255552) := by decide +kernel
  have hhi : ceFrCWT0P0008Hi = ((-274877906943 : ℚ) / 274877906944) := by decide +kernel
  have hcap : FrCWT0P0008Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0008Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0009 : ∀ x ∈ Icc ((((-274877906943 : ℚ) / 274877906944) : ℚ) : ℝ) ((((-137438953471 : ℚ) / 137438953472) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0009Lo = ((-274877906943 : ℚ) / 274877906944) := by decide +kernel
  have hhi : ceFrCWT0P0009Hi = ((-137438953471 : ℚ) / 137438953472) := by decide +kernel
  have hcap : FrCWT0P0009Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0009Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0010 : ∀ x ∈ Icc ((((-137438953471 : ℚ) / 137438953472) : ℚ) : ℝ) ((((-68719476735 : ℚ) / 68719476736) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0010Lo = ((-137438953471 : ℚ) / 137438953472) := by decide +kernel
  have hhi : ceFrCWT0P0010Hi = ((-68719476735 : ℚ) / 68719476736) := by decide +kernel
  have hcap : FrCWT0P0010Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0010Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0011 : ∀ x ∈ Icc ((((-68719476735 : ℚ) / 68719476736) : ℚ) : ℝ) ((((-34359738367 : ℚ) / 34359738368) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0011Lo = ((-68719476735 : ℚ) / 68719476736) := by decide +kernel
  have hhi : ceFrCWT0P0011Hi = ((-34359738367 : ℚ) / 34359738368) := by decide +kernel
  have hcap : FrCWT0P0011Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0011Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0012 : ∀ x ∈ Icc ((((-34359738367 : ℚ) / 34359738368) : ℚ) : ℝ) ((((-17179869183 : ℚ) / 17179869184) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0012Lo = ((-34359738367 : ℚ) / 34359738368) := by decide +kernel
  have hhi : ceFrCWT0P0012Hi = ((-17179869183 : ℚ) / 17179869184) := by decide +kernel
  have hcap : FrCWT0P0012Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0012Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0013 : ∀ x ∈ Icc ((((-17179869183 : ℚ) / 17179869184) : ℚ) : ℝ) ((((-8589934591 : ℚ) / 8589934592) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0013Lo = ((-17179869183 : ℚ) / 17179869184) := by decide +kernel
  have hhi : ceFrCWT0P0013Hi = ((-8589934591 : ℚ) / 8589934592) := by decide +kernel
  have hcap : FrCWT0P0013Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0013Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0014 : ∀ x ∈ Icc ((((-8589934591 : ℚ) / 8589934592) : ℚ) : ℝ) ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0014Lo = ((-8589934591 : ℚ) / 8589934592) := by decide +kernel
  have hhi : ceFrCWT0P0014Hi = ((-4294967295 : ℚ) / 4294967296) := by decide +kernel
  have hcap : FrCWT0P0014Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0014Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0015 : ∀ x ∈ Icc ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-17179869179 : ℚ) / 17179869184) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0015Lo = ((-4294967295 : ℚ) / 4294967296) := by decide +kernel
  have hhi : ceFrCWT0P0015Hi = ((-17179869179 : ℚ) / 17179869184) := by decide +kernel
  have hcap : FrCWT0P0015Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0015Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock001 : ∀ x ∈ Icc ((((-2199023255549 : ℚ) / 2199023255552) : ℚ) : ℝ) ((((-17179869179 : ℚ) / 17179869184) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0008 liftFrCWT0P0009) (cover_union liftFrCWT0P0010 liftFrCWT0P0011)) (cover_union (cover_union liftFrCWT0P0012 liftFrCWT0P0013) (cover_union liftFrCWT0P0014 liftFrCWT0P0015)))
#print axioms FrCWT0CoverBlock001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

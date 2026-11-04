module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0144
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0145
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0146
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0147
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0148
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0149
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0150
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0151

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0144 : ∀ x ∈ Icc ((((-33 : ℚ) / 64) : ℚ) : ℝ) ((((-65 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0144Lo = ((-33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0144Hi = ((-65 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0144Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0144Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0145 : ∀ x ∈ Icc ((((-65 : ℚ) / 128) : ℚ) : ℝ) ((((-1 : ℚ) / 2) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0145Lo = ((-65 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0145Hi = ((-1 : ℚ) / 2) := by decide +kernel
  have hcap : FrCWT0P0145Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0145Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0146 : ∀ x ∈ Icc ((((-1 : ℚ) / 2) : ℚ) : ℝ) ((((-63 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0146Lo = ((-1 : ℚ) / 2) := by decide +kernel
  have hhi : ceFrCWT0P0146Hi = ((-63 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0146Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0146Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0147 : ∀ x ∈ Icc ((((-63 : ℚ) / 128) : ℚ) : ℝ) ((((-125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0147Lo = ((-63 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0147Hi = ((-125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0147Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0147Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0148 : ∀ x ∈ Icc ((((-125 : ℚ) / 256) : ℚ) : ℝ) ((((-31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0148Lo = ((-125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0148Hi = ((-31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0148Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0148Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0149 : ∀ x ∈ Icc ((((-31 : ℚ) / 64) : ℚ) : ℝ) ((((-15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0149Lo = ((-31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0149Hi = ((-15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0149Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0149Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0150 : ∀ x ∈ Icc ((((-15 : ℚ) / 32) : ℚ) : ℝ) ((((-119 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0150Lo = ((-15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0150Hi = ((-119 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0150Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0150Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0151 : ∀ x ∈ Icc ((((-119 : ℚ) / 256) : ℚ) : ℝ) ((((-59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0151Lo = ((-119 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0151Hi = ((-59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0151Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0151Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock018 : ∀ x ∈ Icc ((((-33 : ℚ) / 64) : ℚ) : ℝ) ((((-59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0144 liftFrCWT0P0145) (cover_union liftFrCWT0P0146 liftFrCWT0P0147)) (cover_union (cover_union liftFrCWT0P0148 liftFrCWT0P0149) (cover_union liftFrCWT0P0150 liftFrCWT0P0151)))
#print axioms FrCWT0CoverBlock018

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

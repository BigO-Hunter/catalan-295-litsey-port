module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0135

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0128 : ∀ x ∈ Icc ((((-169 : ℚ) / 256) : ℚ) : ℝ) ((((-21 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0128Lo = ((-169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0128Hi = ((-21 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0128Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0128Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0129 : ∀ x ∈ Icc ((((-21 : ℚ) / 32) : ℚ) : ℝ) ((((-83 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0129Lo = ((-21 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0129Hi = ((-83 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0129Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0129Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0130 : ∀ x ∈ Icc ((((-83 : ℚ) / 128) : ℚ) : ℝ) ((((-41 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0130Lo = ((-83 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0130Hi = ((-41 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0130Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0130Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0131 : ∀ x ∈ Icc ((((-41 : ℚ) / 64) : ℚ) : ℝ) ((((-5 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0131Lo = ((-41 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0131Hi = ((-5 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT0P0131Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0131Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0132 : ∀ x ∈ Icc ((((-5 : ℚ) / 8) : ℚ) : ℝ) ((((-39 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0132Lo = ((-5 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT0P0132Hi = ((-39 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0132Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0132Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0133 : ∀ x ∈ Icc ((((-39 : ℚ) / 64) : ℚ) : ℝ) ((((-155 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0133Lo = ((-39 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0133Hi = ((-155 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0133Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0133Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0134 : ∀ x ∈ Icc ((((-155 : ℚ) / 256) : ℚ) : ℝ) ((((-153 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0134Lo = ((-155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0134Hi = ((-153 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0134Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0134Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0135 : ∀ x ∈ Icc ((((-153 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0135Lo = ((-153 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0135Hi = ((-19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT0P0135Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0135Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock016 : ∀ x ∈ Icc ((((-169 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0128 liftFrCWT0P0129) (cover_union liftFrCWT0P0130 liftFrCWT0P0131)) (cover_union (cover_union liftFrCWT0P0132 liftFrCWT0P0133) (cover_union liftFrCWT0P0134 liftFrCWT0P0135)))
#print axioms FrCWT0CoverBlock016

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

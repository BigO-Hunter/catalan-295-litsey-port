module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0047

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0040 : ∀ x ∈ Icc ((((-8187 : ℚ) / 8192) : ℚ) : ℝ) ((((-4093 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0040Lo = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT0P0040Hi = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0040Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0040Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0041 : ∀ x ∈ Icc ((((-4093 : ℚ) / 4096) : ℚ) : ℝ) ((((-4091 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0041Lo = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0041Hi = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0041Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0041Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0042 : ∀ x ∈ Icc ((((-4091 : ℚ) / 4096) : ℚ) : ℝ) ((((-2045 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0042Lo = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0042Hi = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0042Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0042Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0043 : ∀ x ∈ Icc ((((-2045 : ℚ) / 2048) : ℚ) : ℝ) ((((-511 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0043Lo = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0043Hi = ((-511 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0043Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0043Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0044 : ∀ x ∈ Icc ((((-511 : ℚ) / 512) : ℚ) : ℝ) ((((-4083 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0044Lo = ((-511 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0044Hi = ((-4083 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0044Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0044Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0045 : ∀ x ∈ Icc ((((-4083 : ℚ) / 4096) : ℚ) : ℝ) ((((-2041 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0045Lo = ((-4083 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0045Hi = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT0P0045Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0045Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0046 : ∀ x ∈ Icc ((((-2041 : ℚ) / 2048) : ℚ) : ℝ) ((((-4081 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0046Lo = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT0P0046Hi = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0046Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0046Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0047 : ∀ x ∈ Icc ((((-4081 : ℚ) / 4096) : ℚ) : ℝ) ((((-4077 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0047Lo = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT0P0047Hi = ((-4077 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT0P0047Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0047Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock005 : ∀ x ∈ Icc ((((-8187 : ℚ) / 8192) : ℚ) : ℝ) ((((-4077 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0040 liftFrCWT0P0041) (cover_union liftFrCWT0P0042 liftFrCWT0P0043)) (cover_union (cover_union liftFrCWT0P0044 liftFrCWT0P0045) (cover_union liftFrCWT0P0046 liftFrCWT0P0047)))
#print axioms FrCWT0CoverBlock005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

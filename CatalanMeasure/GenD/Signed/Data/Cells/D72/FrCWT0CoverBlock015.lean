module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0120
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0121
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0122
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0123
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0124
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0125
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0126
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0127

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0120 : ∀ x ∈ Icc ((((-185 : ℚ) / 256) : ℚ) : ℝ) ((((-91 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0120Lo = ((-185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0120Hi = ((-91 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0120Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0120Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0121 : ∀ x ∈ Icc ((((-91 : ℚ) / 128) : ℚ) : ℝ) ((((-181 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0121Lo = ((-91 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0121Hi = ((-181 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0121Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0121Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0122 : ∀ x ∈ Icc ((((-181 : ℚ) / 256) : ℚ) : ℝ) ((((-179 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0122Lo = ((-181 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0122Hi = ((-179 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0122Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0122Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0123 : ∀ x ∈ Icc ((((-179 : ℚ) / 256) : ℚ) : ℝ) ((((-89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0123Lo = ((-179 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0123Hi = ((-89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0123Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0123Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0124 : ∀ x ∈ Icc ((((-89 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0124Lo = ((-89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0124Hi = ((-11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT0P0124Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0124Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0125 : ∀ x ∈ Icc ((((-11 : ℚ) / 16) : ℚ) : ℝ) ((((-43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0125Lo = ((-11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT0P0125Hi = ((-43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0125Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0125Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0126 : ∀ x ∈ Icc ((((-43 : ℚ) / 64) : ℚ) : ℝ) ((((-85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0126Lo = ((-43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0126Hi = ((-85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0126Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0126Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0127 : ∀ x ∈ Icc ((((-85 : ℚ) / 128) : ℚ) : ℝ) ((((-169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0127Lo = ((-85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0127Hi = ((-169 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0127Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0127Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock015 : ∀ x ∈ Icc ((((-185 : ℚ) / 256) : ℚ) : ℝ) ((((-169 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0120 liftFrCWT0P0121) (cover_union liftFrCWT0P0122 liftFrCWT0P0123)) (cover_union (cover_union liftFrCWT0P0124 liftFrCWT0P0125) (cover_union liftFrCWT0P0126 liftFrCWT0P0127)))
#print axioms FrCWT0CoverBlock015

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

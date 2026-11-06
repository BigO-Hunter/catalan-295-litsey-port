module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0111

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0104 : ∀ x ∈ Icc ((((-209 : ℚ) / 256) : ℚ) : ℝ) ((((-207 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0104Lo = ((-209 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0104Hi = ((-207 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0104Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0104Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0105 : ∀ x ∈ Icc ((((-207 : ℚ) / 256) : ℚ) : ℝ) ((((-413 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0105Lo = ((-207 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0105Hi = ((-413 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0105Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0105Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0106 : ∀ x ∈ Icc ((((-413 : ℚ) / 512) : ℚ) : ℝ) ((((-103 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0106Lo = ((-413 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0106Hi = ((-103 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0106Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0106Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0107 : ∀ x ∈ Icc ((((-103 : ℚ) / 128) : ℚ) : ℝ) ((((-51 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0107Lo = ((-103 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0107Hi = ((-51 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0107Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0107Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0108 : ∀ x ∈ Icc ((((-51 : ℚ) / 64) : ℚ) : ℝ) ((((-407 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0108Lo = ((-51 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0108Hi = ((-407 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0108Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0108Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0109 : ∀ x ∈ Icc ((((-407 : ℚ) / 512) : ℚ) : ℝ) ((((-101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0109Lo = ((-407 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0109Hi = ((-101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0109Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0109Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0110 : ∀ x ∈ Icc ((((-101 : ℚ) / 128) : ℚ) : ℝ) ((((-201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0110Lo = ((-101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0110Hi = ((-201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0110Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0110Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0111 : ∀ x ∈ Icc ((((-201 : ℚ) / 256) : ℚ) : ℝ) ((((-99 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0111Lo = ((-201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0111Hi = ((-99 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0111Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0111Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock013 : ∀ x ∈ Icc ((((-209 : ℚ) / 256) : ℚ) : ℝ) ((((-99 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0104 liftFrCWT0P0105) (cover_union liftFrCWT0P0106 liftFrCWT0P0107)) (cover_union (cover_union liftFrCWT0P0108 liftFrCWT0P0109) (cover_union liftFrCWT0P0110 liftFrCWT0P0111)))
#print axioms FrCWT0CoverBlock013

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

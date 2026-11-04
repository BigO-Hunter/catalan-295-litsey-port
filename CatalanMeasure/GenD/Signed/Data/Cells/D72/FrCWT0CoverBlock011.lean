module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0095

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0088 : ∀ x ∈ Icc ((((-29 : ℚ) / 32) : ℚ) : ℝ) ((((-115 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0088Lo = ((-29 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT0P0088Hi = ((-115 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0088Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0088Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0089 : ∀ x ∈ Icc ((((-115 : ℚ) / 128) : ℚ) : ℝ) ((((-459 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0089Lo = ((-115 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0089Hi = ((-459 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT0P0089Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0089Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0090 : ∀ x ∈ Icc ((((-459 : ℚ) / 512) : ℚ) : ℝ) ((((-229 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0090Lo = ((-459 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT0P0090Hi = ((-229 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0090Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0090Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0091 : ∀ x ∈ Icc ((((-229 : ℚ) / 256) : ℚ) : ℝ) ((((-57 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0091Lo = ((-229 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0091Hi = ((-57 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT0P0091Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0091Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0092 : ∀ x ∈ Icc ((((-57 : ℚ) / 64) : ℚ) : ℝ) ((((-113 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0092Lo = ((-57 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT0P0092Hi = ((-113 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0092Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0092Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0093 : ∀ x ∈ Icc ((((-113 : ℚ) / 128) : ℚ) : ℝ) ((((-225 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0093Lo = ((-113 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0093Hi = ((-225 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0093Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0093Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0094 : ∀ x ∈ Icc ((((-225 : ℚ) / 256) : ℚ) : ℝ) ((((-111 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0094Lo = ((-225 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT0P0094Hi = ((-111 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT0P0094Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0094Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0095 : ∀ x ∈ Icc ((((-111 : ℚ) / 128) : ℚ) : ℝ) ((((-221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0095Lo = ((-111 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT0P0095Hi = ((-221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT0P0095Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0095Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock011 : ∀ x ∈ Icc ((((-29 : ℚ) / 32) : ℚ) : ℝ) ((((-221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0088 liftFrCWT0P0089) (cover_union liftFrCWT0P0090 liftFrCWT0P0091)) (cover_union (cover_union liftFrCWT0P0092 liftFrCWT0P0093) (cover_union liftFrCWT0P0094 liftFrCWT0P0095)))
#print axioms FrCWT0CoverBlock011

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

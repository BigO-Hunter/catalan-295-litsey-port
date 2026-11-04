module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0095

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0088 : ∀ x ∈ Icc ((((-225 : ℚ) / 256) : ℚ) : ℝ) ((((-7 : ℚ) / 8) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0088Lo = ((-225 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0088Hi = ((-7 : ℚ) / 8) := by decide +kernel
  have hcap : FrCWT1P0088Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0088Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0089 : ∀ x ∈ Icc ((((-7 : ℚ) / 8) : ℚ) : ℝ) ((((-223 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0089Lo = ((-7 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT1P0089Hi = ((-223 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0089Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0089Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0090 : ∀ x ∈ Icc ((((-223 : ℚ) / 256) : ℚ) : ℝ) ((((-111 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0090Lo = ((-223 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0090Hi = ((-111 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT1P0090Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0090Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0091 : ∀ x ∈ Icc ((((-111 : ℚ) / 128) : ℚ) : ℝ) ((((-221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0091Lo = ((-111 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT1P0091Hi = ((-221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0091Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0091Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0092 : ∀ x ∈ Icc ((((-221 : ℚ) / 256) : ℚ) : ℝ) ((((-55 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0092Lo = ((-221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0092Hi = ((-55 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT1P0092Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0092Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0093 : ∀ x ∈ Icc ((((-55 : ℚ) / 64) : ℚ) : ℝ) ((((-219 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0093Lo = ((-55 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT1P0093Hi = ((-219 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0093Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0093Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0094 : ∀ x ∈ Icc ((((-219 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0094Lo = ((-219 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT1P0094Hi = ((-27 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT1P0094Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0094Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0095 : ∀ x ∈ Icc ((((-27 : ℚ) / 32) : ℚ) : ℝ) ((((-215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0095Lo = ((-27 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT1P0095Hi = ((-215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT1P0095Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0095Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock011 : ∀ x ∈ Icc ((((-225 : ℚ) / 256) : ℚ) : ℝ) ((((-215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0088 liftFrCWT1P0089) (cover_union liftFrCWT1P0090 liftFrCWT1P0091)) (cover_union (cover_union liftFrCWT1P0092 liftFrCWT1P0093) (cover_union liftFrCWT1P0094 liftFrCWT1P0095)))
#print axioms FrCWT1CoverBlock011

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

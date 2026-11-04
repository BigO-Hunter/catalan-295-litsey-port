module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0088
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0089
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0090
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0091
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0092
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0093
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0094
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0095

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0088 : ∀ x ∈ Icc ((((-7 : ℚ) / 8) : ℚ) : ℝ) ((((-223 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0088Lo = ((-7 : ℚ) / 8) := by decide +kernel
  have hhi : ceFrCWT2P0088Hi = ((-223 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0088Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0088Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0089 : ∀ x ∈ Icc ((((-223 : ℚ) / 256) : ℚ) : ℝ) ((((-111 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0089Lo = ((-223 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0089Hi = ((-111 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0089Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0089Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0090 : ∀ x ∈ Icc ((((-111 : ℚ) / 128) : ℚ) : ℝ) ((((-221 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0090Lo = ((-111 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0090Hi = ((-221 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0090Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0090Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0091 : ∀ x ∈ Icc ((((-221 : ℚ) / 256) : ℚ) : ℝ) ((((-109 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0091Lo = ((-221 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0091Hi = ((-109 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0091Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0091Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0092 : ∀ x ∈ Icc ((((-109 : ℚ) / 128) : ℚ) : ℝ) ((((-217 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0092Lo = ((-109 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0092Hi = ((-217 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0092Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0092Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0093 : ∀ x ∈ Icc ((((-217 : ℚ) / 256) : ℚ) : ℝ) ((((-27 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0093Lo = ((-217 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0093Hi = ((-27 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0093Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0093Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0094 : ∀ x ∈ Icc ((((-27 : ℚ) / 32) : ℚ) : ℝ) ((((-215 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0094Lo = ((-27 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0094Hi = ((-215 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0094Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0094Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0095 : ∀ x ∈ Icc ((((-215 : ℚ) / 256) : ℚ) : ℝ) ((((-107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0095Lo = ((-215 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0095Hi = ((-107 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0095Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0095Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock011 : ∀ x ∈ Icc ((((-7 : ℚ) / 8) : ℚ) : ℝ) ((((-107 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0088 liftFrCWT2P0089) (cover_union liftFrCWT2P0090 liftFrCWT2P0091)) (cover_union (cover_union liftFrCWT2P0092 liftFrCWT2P0093) (cover_union liftFrCWT2P0094 liftFrCWT2P0095)))
#print axioms FrCWT2CoverBlock011

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

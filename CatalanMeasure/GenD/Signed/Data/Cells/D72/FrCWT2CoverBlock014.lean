module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0112
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0113
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0114
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0115
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0116
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0117
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0118
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0119

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0112 : ∀ x ∈ Icc ((((-47 : ℚ) / 64) : ℚ) : ℝ) ((((-93 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0112Lo = ((-47 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0112Hi = ((-93 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0112Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0112Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0113 : ∀ x ∈ Icc ((((-93 : ℚ) / 128) : ℚ) : ℝ) ((((-185 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0113Lo = ((-93 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0113Hi = ((-185 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0113Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0113Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0114 : ∀ x ∈ Icc ((((-185 : ℚ) / 256) : ℚ) : ℝ) ((((-183 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0114Lo = ((-185 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0114Hi = ((-183 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0114Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0114Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0115 : ∀ x ∈ Icc ((((-183 : ℚ) / 256) : ℚ) : ℝ) ((((-181 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0115Lo = ((-183 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0115Hi = ((-181 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0115Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0115Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0116 : ∀ x ∈ Icc ((((-181 : ℚ) / 256) : ℚ) : ℝ) ((((-179 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0116Lo = ((-181 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0116Hi = ((-179 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0116Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0116Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0117 : ∀ x ∈ Icc ((((-179 : ℚ) / 256) : ℚ) : ℝ) ((((-89 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0117Lo = ((-179 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0117Hi = ((-89 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0117Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0117Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0118 : ∀ x ∈ Icc ((((-89 : ℚ) / 128) : ℚ) : ℝ) ((((-11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0118Lo = ((-89 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0118Hi = ((-11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0118Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0118Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0119 : ∀ x ∈ Icc ((((-11 : ℚ) / 16) : ℚ) : ℝ) ((((-43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0119Lo = ((-11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0119Hi = ((-43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0119Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0119Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock014 : ∀ x ∈ Icc ((((-47 : ℚ) / 64) : ℚ) : ℝ) ((((-43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0112 liftFrCWT2P0113) (cover_union liftFrCWT2P0114 liftFrCWT2P0115)) (cover_union (cover_union liftFrCWT2P0116 liftFrCWT2P0117) (cover_union liftFrCWT2P0118 liftFrCWT2P0119)))
#print axioms FrCWT2CoverBlock014

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

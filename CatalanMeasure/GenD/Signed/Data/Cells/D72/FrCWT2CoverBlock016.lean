module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0128
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0129
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0130
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0131
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0132
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0133
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0134
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0135

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0128 : ∀ x ∈ Icc ((((-155 : ℚ) / 256) : ℚ) : ℝ) ((((-153 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0128Lo = ((-155 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0128Hi = ((-153 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0128Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0128Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0129 : ∀ x ∈ Icc ((((-153 : ℚ) / 256) : ℚ) : ℝ) ((((-19 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0129Lo = ((-153 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0129Hi = ((-19 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0129Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0129Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0130 : ∀ x ∈ Icc ((((-19 : ℚ) / 32) : ℚ) : ℝ) ((((-37 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0130Lo = ((-19 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0130Hi = ((-37 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0130Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0130Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0131 : ∀ x ∈ Icc ((((-37 : ℚ) / 64) : ℚ) : ℝ) ((((-9 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0131Lo = ((-37 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0131Hi = ((-9 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0131Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0131Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0132 : ∀ x ∈ Icc ((((-9 : ℚ) / 16) : ℚ) : ℝ) ((((-35 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0132Lo = ((-9 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0132Hi = ((-35 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0132Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0132Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0133 : ∀ x ∈ Icc ((((-35 : ℚ) / 64) : ℚ) : ℝ) ((((-69 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0133Lo = ((-35 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0133Hi = ((-69 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0133Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0133Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0134 : ∀ x ∈ Icc ((((-69 : ℚ) / 128) : ℚ) : ℝ) ((((-67 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0134Lo = ((-69 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0134Hi = ((-67 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0134Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0134Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0135 : ∀ x ∈ Icc ((((-67 : ℚ) / 128) : ℚ) : ℝ) ((((-133 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0135Lo = ((-67 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0135Hi = ((-133 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0135Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0135Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock016 : ∀ x ∈ Icc ((((-155 : ℚ) / 256) : ℚ) : ℝ) ((((-133 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0128 liftFrCWT2P0129) (cover_union liftFrCWT2P0130 liftFrCWT2P0131)) (cover_union (cover_union liftFrCWT2P0132 liftFrCWT2P0133) (cover_union liftFrCWT2P0134 liftFrCWT2P0135)))
#print axioms FrCWT2CoverBlock016

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

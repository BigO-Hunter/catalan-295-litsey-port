module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0104
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0105
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0106
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0107
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0108
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0109
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0110
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0111

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0104 : ∀ x ∈ Icc ((((-203 : ℚ) / 256) : ℚ) : ℝ) ((((-101 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0104Lo = ((-203 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0104Hi = ((-101 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0104Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0104Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0105 : ∀ x ∈ Icc ((((-101 : ℚ) / 128) : ℚ) : ℝ) ((((-201 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0105Lo = ((-101 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0105Hi = ((-201 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0105Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0105Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0106 : ∀ x ∈ Icc ((((-201 : ℚ) / 256) : ℚ) : ℝ) ((((-99 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0106Lo = ((-201 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0106Hi = ((-99 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0106Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0106Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0107 : ∀ x ∈ Icc ((((-99 : ℚ) / 128) : ℚ) : ℝ) ((((-197 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0107Lo = ((-99 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0107Hi = ((-197 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0107Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0107Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0108 : ∀ x ∈ Icc ((((-197 : ℚ) / 256) : ℚ) : ℝ) ((((-97 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0108Lo = ((-197 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0108Hi = ((-97 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0108Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0108Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0109 : ∀ x ∈ Icc ((((-97 : ℚ) / 128) : ℚ) : ℝ) ((((-193 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0109Lo = ((-97 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0109Hi = ((-193 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0109Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0109Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0110 : ∀ x ∈ Icc ((((-193 : ℚ) / 256) : ℚ) : ℝ) ((((-189 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0110Lo = ((-193 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0110Hi = ((-189 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0110Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0110Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0111 : ∀ x ∈ Icc ((((-189 : ℚ) / 256) : ℚ) : ℝ) ((((-47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0111Lo = ((-189 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0111Hi = ((-47 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0111Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0111Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock013 : ∀ x ∈ Icc ((((-203 : ℚ) / 256) : ℚ) : ℝ) ((((-47 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0104 liftFrCWT2P0105) (cover_union liftFrCWT2P0106 liftFrCWT2P0107)) (cover_union (cover_union liftFrCWT2P0108 liftFrCWT2P0109) (cover_union liftFrCWT2P0110 liftFrCWT2P0111)))
#print axioms FrCWT2CoverBlock013

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0023

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0016 : ∀ x ∈ Icc ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ) ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0016Lo = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hhi : ceFrCWT2P0016Hi = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hcap : FrCWT2P0016Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0016Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0017 : ∀ x ∈ Icc ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ) ((((-8388607 : ℚ) / 8388608) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0017Lo = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hhi : ceFrCWT2P0017Hi = ((-8388607 : ℚ) / 8388608) := by decide +kernel
  have hcap : FrCWT2P0017Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0017Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0018 : ∀ x ∈ Icc ((((-8388607 : ℚ) / 8388608) : ℚ) : ℝ) ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0018Lo = ((-8388607 : ℚ) / 8388608) := by decide +kernel
  have hhi : ceFrCWT2P0018Hi = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hcap : FrCWT2P0018Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0018Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0019 : ∀ x ∈ Icc ((((-4194303 : ℚ) / 4194304) : ℚ) : ℝ) ((((-8388605 : ℚ) / 8388608) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0019Lo = ((-4194303 : ℚ) / 4194304) := by decide +kernel
  have hhi : ceFrCWT2P0019Hi = ((-8388605 : ℚ) / 8388608) := by decide +kernel
  have hcap : FrCWT2P0019Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0019Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0020 : ∀ x ∈ Icc ((((-8388605 : ℚ) / 8388608) : ℚ) : ℝ) ((((-1048575 : ℚ) / 1048576) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0020Lo = ((-8388605 : ℚ) / 8388608) := by decide +kernel
  have hhi : ceFrCWT2P0020Hi = ((-1048575 : ℚ) / 1048576) := by decide +kernel
  have hcap : FrCWT2P0020Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0020Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0021 : ∀ x ∈ Icc ((((-1048575 : ℚ) / 1048576) : ℚ) : ℝ) ((((-524287 : ℚ) / 524288) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0021Lo = ((-1048575 : ℚ) / 1048576) := by decide +kernel
  have hhi : ceFrCWT2P0021Hi = ((-524287 : ℚ) / 524288) := by decide +kernel
  have hcap : FrCWT2P0021Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0021Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0022 : ∀ x ∈ Icc ((((-524287 : ℚ) / 524288) : ℚ) : ℝ) ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0022Lo = ((-524287 : ℚ) / 524288) := by decide +kernel
  have hhi : ceFrCWT2P0022Hi = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hcap : FrCWT2P0022Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0022Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0023 : ∀ x ∈ Icc ((((-1048573 : ℚ) / 1048576) : ℚ) : ℝ) ((((-262143 : ℚ) / 262144) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0023Lo = ((-1048573 : ℚ) / 1048576) := by decide +kernel
  have hhi : ceFrCWT2P0023Hi = ((-262143 : ℚ) / 262144) := by decide +kernel
  have hcap : FrCWT2P0023Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0023Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock002 : ∀ x ∈ Icc ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ) ((((-262143 : ℚ) / 262144) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0016 liftFrCWT2P0017) (cover_union liftFrCWT2P0018 liftFrCWT2P0019)) (cover_union (cover_union liftFrCWT2P0020 liftFrCWT2P0021) (cover_union liftFrCWT2P0022 liftFrCWT2P0023)))
#print axioms FrCWT2CoverBlock002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

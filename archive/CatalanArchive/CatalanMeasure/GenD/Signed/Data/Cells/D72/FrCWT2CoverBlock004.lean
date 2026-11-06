module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0039

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0032 : ∀ x ∈ Icc ((((-4095 : ℚ) / 4096) : ℚ) : ℝ) ((((-8189 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0032Lo = ((-4095 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0032Hi = ((-8189 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT2P0032Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0032Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0033 : ∀ x ∈ Icc ((((-8189 : ℚ) / 8192) : ℚ) : ℝ) ((((-8187 : ℚ) / 8192) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0033Lo = ((-8189 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT2P0033Hi = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hcap : FrCWT2P0033Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0033Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0034 : ∀ x ∈ Icc ((((-8187 : ℚ) / 8192) : ℚ) : ℝ) ((((-4093 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0034Lo = ((-8187 : ℚ) / 8192) := by decide +kernel
  have hhi : ceFrCWT2P0034Hi = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0034Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0034Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0035 : ∀ x ∈ Icc ((((-4093 : ℚ) / 4096) : ℚ) : ℝ) ((((-4091 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0035Lo = ((-4093 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0035Hi = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0035Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0035Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0036 : ∀ x ∈ Icc ((((-4091 : ℚ) / 4096) : ℚ) : ℝ) ((((-2045 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0036Lo = ((-4091 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0036Hi = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0036Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0036Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0037 : ∀ x ∈ Icc ((((-2045 : ℚ) / 2048) : ℚ) : ℝ) ((((-511 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0037Lo = ((-2045 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0037Hi = ((-511 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0037Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0037Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0038 : ∀ x ∈ Icc ((((-511 : ℚ) / 512) : ℚ) : ℝ) ((((-4087 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0038Lo = ((-511 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0038Hi = ((-4087 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0038Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0038Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0039 : ∀ x ∈ Icc ((((-4087 : ℚ) / 4096) : ℚ) : ℝ) ((((-2043 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0039Lo = ((-4087 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0039Hi = ((-2043 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0039Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0039Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock004 : ∀ x ∈ Icc ((((-4095 : ℚ) / 4096) : ℚ) : ℝ) ((((-2043 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0032 liftFrCWT2P0033) (cover_union liftFrCWT2P0034 liftFrCWT2P0035)) (cover_union (cover_union liftFrCWT2P0036 liftFrCWT2P0037) (cover_union liftFrCWT2P0038 liftFrCWT2P0039)))
#print axioms FrCWT2CoverBlock004

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

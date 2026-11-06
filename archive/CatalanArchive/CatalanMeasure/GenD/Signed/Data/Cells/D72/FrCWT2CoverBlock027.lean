module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0216
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0217
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0218
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0219
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0220
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0221
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0222
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0223

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0216 : ∀ x ∈ Icc ((((19 : ℚ) / 128) : ℚ) : ℝ) ((((41 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0216Lo = ((19 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0216Hi = ((41 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0216Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0216Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0217 : ∀ x ∈ Icc ((((41 : ℚ) / 256) : ℚ) : ℝ) ((((21 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0217Lo = ((41 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0217Hi = ((21 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0217Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0217Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0218 : ∀ x ∈ Icc ((((21 : ℚ) / 128) : ℚ) : ℝ) ((((45 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0218Lo = ((21 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0218Hi = ((45 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0218Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0218Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0219 : ∀ x ∈ Icc ((((45 : ℚ) / 256) : ℚ) : ℝ) ((((23 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0219Lo = ((45 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0219Hi = ((23 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0219Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0219Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0220 : ∀ x ∈ Icc ((((23 : ℚ) / 128) : ℚ) : ℝ) ((((49 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0220Lo = ((23 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0220Hi = ((49 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0220Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0220Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0221 : ∀ x ∈ Icc ((((49 : ℚ) / 256) : ℚ) : ℝ) ((((25 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0221Lo = ((49 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0221Hi = ((25 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0221Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0221Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0222 : ∀ x ∈ Icc ((((25 : ℚ) / 128) : ℚ) : ℝ) ((((13 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0222Lo = ((25 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0222Hi = ((13 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0222Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0222Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0223 : ∀ x ∈ Icc ((((13 : ℚ) / 64) : ℚ) : ℝ) ((((53 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0223Lo = ((13 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0223Hi = ((53 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0223Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0223Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock027 : ∀ x ∈ Icc ((((19 : ℚ) / 128) : ℚ) : ℝ) ((((53 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0216 liftFrCWT2P0217) (cover_union liftFrCWT2P0218 liftFrCWT2P0219)) (cover_union (cover_union liftFrCWT2P0220 liftFrCWT2P0221) (cover_union liftFrCWT2P0222 liftFrCWT2P0223)))
#print axioms FrCWT2CoverBlock027

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

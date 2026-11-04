module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0136
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0137
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0138
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0139
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0140
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0141
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0142
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0143

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0136 : ∀ x ∈ Icc ((((-133 : ℚ) / 256) : ℚ) : ℝ) ((((-33 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0136Lo = ((-133 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0136Hi = ((-33 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0136Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0136Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0137 : ∀ x ∈ Icc ((((-33 : ℚ) / 64) : ℚ) : ℝ) ((((-65 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0137Lo = ((-33 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0137Hi = ((-65 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0137Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0137Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0138 : ∀ x ∈ Icc ((((-65 : ℚ) / 128) : ℚ) : ℝ) ((((-63 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0138Lo = ((-65 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0138Hi = ((-63 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0138Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0138Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0139 : ∀ x ∈ Icc ((((-63 : ℚ) / 128) : ℚ) : ℝ) ((((-125 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0139Lo = ((-63 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0139Hi = ((-125 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0139Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0139Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0140 : ∀ x ∈ Icc ((((-125 : ℚ) / 256) : ℚ) : ℝ) ((((-31 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0140Lo = ((-125 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0140Hi = ((-31 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0140Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0140Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0141 : ∀ x ∈ Icc ((((-31 : ℚ) / 64) : ℚ) : ℝ) ((((-15 : ℚ) / 32) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0141Lo = ((-31 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0141Hi = ((-15 : ℚ) / 32) := by decide +kernel
  have hcap : FrCWT2P0141Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0141Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0142 : ∀ x ∈ Icc ((((-15 : ℚ) / 32) : ℚ) : ℝ) ((((-119 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0142Lo = ((-15 : ℚ) / 32) := by decide +kernel
  have hhi : ceFrCWT2P0142Hi = ((-119 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0142Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0142Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0143 : ∀ x ∈ Icc ((((-119 : ℚ) / 256) : ℚ) : ℝ) ((((-59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0143Lo = ((-119 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0143Hi = ((-59 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0143Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0143Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock017 : ∀ x ∈ Icc ((((-133 : ℚ) / 256) : ℚ) : ℝ) ((((-59 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0136 liftFrCWT2P0137) (cover_union liftFrCWT2P0138 liftFrCWT2P0139)) (cover_union (cover_union liftFrCWT2P0140 liftFrCWT2P0141) (cover_union liftFrCWT2P0142 liftFrCWT2P0143)))
#print axioms FrCWT2CoverBlock017

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

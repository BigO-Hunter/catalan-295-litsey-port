module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0007

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0000Lo = ((-1 : ℚ) / 1) := by decide +kernel
  have hhi : ceFrCWT2P0000Hi = ((-1099511627775 : ℚ) / 1099511627776) := by decide +kernel
  have hcap : FrCWT2P0000Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0000Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0001 : ∀ x ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-274877906943 : ℚ) / 274877906944) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0001Lo = ((-1099511627775 : ℚ) / 1099511627776) := by decide +kernel
  have hhi : ceFrCWT2P0001Hi = ((-274877906943 : ℚ) / 274877906944) := by decide +kernel
  have hcap : FrCWT2P0001Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0001Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0002 : ∀ x ∈ Icc ((((-274877906943 : ℚ) / 274877906944) : ℚ) : ℝ) ((((-137438953471 : ℚ) / 137438953472) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0002Lo = ((-274877906943 : ℚ) / 274877906944) := by decide +kernel
  have hhi : ceFrCWT2P0002Hi = ((-137438953471 : ℚ) / 137438953472) := by decide +kernel
  have hcap : FrCWT2P0002Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0002Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0003 : ∀ x ∈ Icc ((((-137438953471 : ℚ) / 137438953472) : ℚ) : ℝ) ((((-68719476735 : ℚ) / 68719476736) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0003Lo = ((-137438953471 : ℚ) / 137438953472) := by decide +kernel
  have hhi : ceFrCWT2P0003Hi = ((-68719476735 : ℚ) / 68719476736) := by decide +kernel
  have hcap : FrCWT2P0003Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0003Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0004 : ∀ x ∈ Icc ((((-68719476735 : ℚ) / 68719476736) : ℚ) : ℝ) ((((-34359738367 : ℚ) / 34359738368) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0004Lo = ((-68719476735 : ℚ) / 68719476736) := by decide +kernel
  have hhi : ceFrCWT2P0004Hi = ((-34359738367 : ℚ) / 34359738368) := by decide +kernel
  have hcap : FrCWT2P0004Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0004Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0005 : ∀ x ∈ Icc ((((-34359738367 : ℚ) / 34359738368) : ℚ) : ℝ) ((((-17179869183 : ℚ) / 17179869184) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0005Lo = ((-34359738367 : ℚ) / 34359738368) := by decide +kernel
  have hhi : ceFrCWT2P0005Hi = ((-17179869183 : ℚ) / 17179869184) := by decide +kernel
  have hcap : FrCWT2P0005Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0005Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0006 : ∀ x ∈ Icc ((((-17179869183 : ℚ) / 17179869184) : ℚ) : ℝ) ((((-8589934591 : ℚ) / 8589934592) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0006Lo = ((-17179869183 : ℚ) / 17179869184) := by decide +kernel
  have hhi : ceFrCWT2P0006Hi = ((-8589934591 : ℚ) / 8589934592) := by decide +kernel
  have hcap : FrCWT2P0006Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0006Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0007 : ∀ x ∈ Icc ((((-8589934591 : ℚ) / 8589934592) : ℚ) : ℝ) ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0007Lo = ((-8589934591 : ℚ) / 8589934592) := by decide +kernel
  have hhi : ceFrCWT2P0007Hi = ((-4294967295 : ℚ) / 4294967296) := by decide +kernel
  have hcap : FrCWT2P0007Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0007Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock000 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0000 liftFrCWT2P0001) (cover_union liftFrCWT2P0002 liftFrCWT2P0003)) (cover_union (cover_union liftFrCWT2P0004 liftFrCWT2P0005) (cover_union liftFrCWT2P0006 liftFrCWT2P0007)))
#print axioms FrCWT2CoverBlock000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

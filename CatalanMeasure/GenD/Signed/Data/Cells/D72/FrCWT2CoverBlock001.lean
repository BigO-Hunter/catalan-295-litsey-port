module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0015

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0008 : ∀ x ∈ Icc ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0008Lo = ((-4294967295 : ℚ) / 4294967296) := by decide +kernel
  have hhi : ceFrCWT2P0008Hi = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hcap : FrCWT2P0008Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0008Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0009 : ∀ x ∈ Icc ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ) ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0009Lo = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hhi : ceFrCWT2P0009Hi = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hcap : FrCWT2P0009Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0009Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0010 : ∀ x ∈ Icc ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-2147483645 : ℚ) / 2147483648) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0010Lo = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hhi : ceFrCWT2P0010Hi = ((-2147483645 : ℚ) / 2147483648) := by decide +kernel
  have hcap : FrCWT2P0010Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0010Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0011 : ∀ x ∈ Icc ((((-2147483645 : ℚ) / 2147483648) : ℚ) : ℝ) ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0011Lo = ((-2147483645 : ℚ) / 2147483648) := by decide +kernel
  have hhi : ceFrCWT2P0011Hi = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hcap : FrCWT2P0011Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0011Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0012 : ∀ x ∈ Icc ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ) ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0012Lo = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hhi : ceFrCWT2P0012Hi = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hcap : FrCWT2P0012Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0012Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0013 : ∀ x ∈ Icc ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ) ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0013Lo = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hhi : ceFrCWT2P0013Hi = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hcap : FrCWT2P0013Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0013Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0014 : ∀ x ∈ Icc ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ) ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0014Lo = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hhi : ceFrCWT2P0014Hi = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hcap : FrCWT2P0014Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0014Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0015 : ∀ x ∈ Icc ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ) ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0015Lo = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hhi : ceFrCWT2P0015Hi = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hcap : FrCWT2P0015Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0015Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock001 : ∀ x ∈ Icc ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0008 liftFrCWT2P0009) (cover_union liftFrCWT2P0010 liftFrCWT2P0011)) (cover_union (cover_union liftFrCWT2P0012 liftFrCWT2P0013) (cover_union liftFrCWT2P0014 liftFrCWT2P0015)))
#print axioms FrCWT2CoverBlock001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

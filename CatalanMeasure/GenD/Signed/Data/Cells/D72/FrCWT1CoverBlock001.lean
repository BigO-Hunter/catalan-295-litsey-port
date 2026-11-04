module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0015

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0008 : ∀ x ∈ Icc ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0008Lo = ((-4294967295 : ℚ) / 4294967296) := by decide +kernel
  have hhi : ceFrCWT1P0008Hi = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hcap : FrCWT1P0008Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0008Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0009 : ∀ x ∈ Icc ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ) ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0009Lo = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hhi : ceFrCWT1P0009Hi = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hcap : FrCWT1P0009Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0009Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0010 : ∀ x ∈ Icc ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0010Lo = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hhi : ceFrCWT1P0010Hi = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hcap : FrCWT1P0010Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0010Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0011 : ∀ x ∈ Icc ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ) ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0011Lo = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hhi : ceFrCWT1P0011Hi = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hcap : FrCWT1P0011Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0011Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0012 : ∀ x ∈ Icc ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ) ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0012Lo = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hhi : ceFrCWT1P0012Hi = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hcap : FrCWT1P0012Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0012Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0013 : ∀ x ∈ Icc ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ) ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0013Lo = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hhi : ceFrCWT1P0013Hi = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hcap : FrCWT1P0013Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0013Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0014 : ∀ x ∈ Icc ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ) ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0014Lo = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hhi : ceFrCWT1P0014Hi = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hcap : FrCWT1P0014Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0014Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0015 : ∀ x ∈ Icc ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ) ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0015Lo = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hhi : ceFrCWT1P0015Hi = ((-16777215 : ℚ) / 16777216) := by decide +kernel
  have hcap : FrCWT1P0015Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0015Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock001 : ∀ x ∈ Icc ((((-4294967295 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-16777215 : ℚ) / 16777216) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0008 liftFrCWT1P0009) (cover_union liftFrCWT1P0010 liftFrCWT1P0011)) (cover_union (cover_union liftFrCWT1P0012 liftFrCWT1P0013) (cover_union liftFrCWT1P0014 liftFrCWT1P0015)))
#print axioms FrCWT1CoverBlock001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

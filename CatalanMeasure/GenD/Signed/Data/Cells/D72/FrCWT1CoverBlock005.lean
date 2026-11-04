module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1P0047

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT1P0040 : ∀ x ∈ Icc ((((-4083 : ℚ) / 4096) : ℚ) : ℝ) ((((-2041 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0040Lo = ((-4083 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0040Hi = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0040Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0040Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0041 : ∀ x ∈ Icc ((((-2041 : ℚ) / 2048) : ℚ) : ℝ) ((((-4081 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0041Lo = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0041Hi = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0041Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0041Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0042 : ∀ x ∈ Icc ((((-4081 : ℚ) / 4096) : ℚ) : ℝ) ((((-4077 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0042Lo = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0042Hi = ((-4077 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0042Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0042Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0043 : ∀ x ∈ Icc ((((-4077 : ℚ) / 4096) : ℚ) : ℝ) ((((-4075 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0043Lo = ((-4077 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0043Hi = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT1P0043Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0043Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0044 : ∀ x ∈ Icc ((((-4075 : ℚ) / 4096) : ℚ) : ℝ) ((((-2035 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0044Lo = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT1P0044Hi = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0044Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0044Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0045 : ∀ x ∈ Icc ((((-2035 : ℚ) / 2048) : ℚ) : ℝ) ((((-1017 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0045Lo = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0045Hi = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0045Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0045Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0046 : ∀ x ∈ Icc ((((-1017 : ℚ) / 1024) : ℚ) : ℝ) ((((-2031 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0046Lo = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT1P0046Hi = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT1P0046Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0046Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT1P0047 : ∀ x ∈ Icc ((((-2031 : ℚ) / 2048) : ℚ) : ℝ) ((((-1015 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT1P0047Lo = ((-2031 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT1P0047Hi = ((-1015 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT1P0047Literal.q2 (-89059398077) 1 (-40) = ((-89059398077 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT1P0047Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT1CoverBlock005 : ∀ x ∈ Icc ((((-4083 : ℚ) / 4096) : ℚ) : ℝ) ((((-1015 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT1Raw (poleF ceFrCWT1Raw.poles) 0 x ≤ ((((-89059398077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT1P0040 liftFrCWT1P0041) (cover_union liftFrCWT1P0042 liftFrCWT1P0043)) (cover_union (cover_union liftFrCWT1P0044 liftFrCWT1P0045) (cover_union liftFrCWT1P0046 liftFrCWT1P0047)))
#print axioms FrCWT1CoverBlock005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT1Assembly

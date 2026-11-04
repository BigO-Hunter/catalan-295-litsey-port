module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0047

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0040 : ∀ x ∈ Icc ((((-2043 : ℚ) / 2048) : ℚ) : ℝ) ((((-1021 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0040Lo = ((-2043 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0040Hi = ((-1021 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0040Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0040Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0041 : ∀ x ∈ Icc ((((-1021 : ℚ) / 1024) : ℚ) : ℝ) ((((-2041 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0041Lo = ((-1021 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0041Hi = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0041Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0041Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0042 : ∀ x ∈ Icc ((((-2041 : ℚ) / 2048) : ℚ) : ℝ) ((((-4081 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0042Lo = ((-2041 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0042Hi = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0042Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0042Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0043 : ∀ x ∈ Icc ((((-4081 : ℚ) / 4096) : ℚ) : ℝ) ((((-2039 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0043Lo = ((-4081 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0043Hi = ((-2039 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0043Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0043Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0044 : ∀ x ∈ Icc ((((-2039 : ℚ) / 2048) : ℚ) : ℝ) ((((-1019 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0044Lo = ((-2039 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0044Hi = ((-1019 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0044Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0044Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0045 : ∀ x ∈ Icc ((((-1019 : ℚ) / 1024) : ℚ) : ℝ) ((((-4075 : ℚ) / 4096) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0045Lo = ((-1019 : ℚ) / 1024) := by decide +kernel
  have hhi : ceFrCWT2P0045Hi = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hcap : FrCWT2P0045Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0045Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0046 : ∀ x ∈ Icc ((((-4075 : ℚ) / 4096) : ℚ) : ℝ) ((((-2035 : ℚ) / 2048) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0046Lo = ((-4075 : ℚ) / 4096) := by decide +kernel
  have hhi : ceFrCWT2P0046Hi = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hcap : FrCWT2P0046Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0046Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0047 : ∀ x ∈ Icc ((((-2035 : ℚ) / 2048) : ℚ) : ℝ) ((((-1017 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0047Lo = ((-2035 : ℚ) / 2048) := by decide +kernel
  have hhi : ceFrCWT2P0047Hi = ((-1017 : ℚ) / 1024) := by decide +kernel
  have hcap : FrCWT2P0047Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0047Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock005 : ∀ x ∈ Icc ((((-2043 : ℚ) / 2048) : ℚ) : ℝ) ((((-1017 : ℚ) / 1024) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0040 liftFrCWT2P0041) (cover_union liftFrCWT2P0042 liftFrCWT2P0043)) (cover_union (cover_union liftFrCWT2P0044 liftFrCWT2P0045) (cover_union liftFrCWT2P0046 liftFrCWT2P0047)))
#print axioms FrCWT2CoverBlock005

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

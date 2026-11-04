module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0296
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0297
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0298
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0299
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0300
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0301
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0302
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2P0303

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT2P0296 : ∀ x ∈ Icc ((((169 : ℚ) / 256) : ℚ) : ℝ) ((((85 : ℚ) / 128) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0296Lo = ((169 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0296Hi = ((85 : ℚ) / 128) := by decide +kernel
  have hcap : FrCWT2P0296Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0296Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0297 : ∀ x ∈ Icc ((((85 : ℚ) / 128) : ℚ) : ℝ) ((((341 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0297Lo = ((85 : ℚ) / 128) := by decide +kernel
  have hhi : ceFrCWT2P0297Hi = ((341 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0297Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0297Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0298 : ∀ x ∈ Icc ((((341 : ℚ) / 512) : ℚ) : ℝ) ((((43 : ℚ) / 64) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0298Lo = ((341 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0298Hi = ((43 : ℚ) / 64) := by decide +kernel
  have hcap : FrCWT2P0298Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0298Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0299 : ∀ x ∈ Icc ((((43 : ℚ) / 64) : ℚ) : ℝ) ((((173 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0299Lo = ((43 : ℚ) / 64) := by decide +kernel
  have hhi : ceFrCWT2P0299Hi = ((173 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0299Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0299Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0300 : ∀ x ∈ Icc ((((173 : ℚ) / 256) : ℚ) : ℝ) ((((347 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0300Lo = ((173 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0300Hi = ((347 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0300Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0300Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0301 : ∀ x ∈ Icc ((((347 : ℚ) / 512) : ℚ) : ℝ) ((((175 : ℚ) / 256) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0301Lo = ((347 : ℚ) / 512) := by decide +kernel
  have hhi : ceFrCWT2P0301Hi = ((175 : ℚ) / 256) := by decide +kernel
  have hcap : FrCWT2P0301Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0301Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0302 : ∀ x ∈ Icc ((((175 : ℚ) / 256) : ℚ) : ℝ) ((((11 : ℚ) / 16) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0302Lo = ((175 : ℚ) / 256) := by decide +kernel
  have hhi : ceFrCWT2P0302Hi = ((11 : ℚ) / 16) := by decide +kernel
  have hcap : FrCWT2P0302Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0302Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT2P0303 : ∀ x ∈ Icc ((((11 : ℚ) / 16) : ℚ) : ℝ) ((((353 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  have hlo : ceFrCWT2P0303Lo = ((11 : ℚ) / 16) := by decide +kernel
  have hhi : ceFrCWT2P0303Hi = ((353 : ℚ) / 512) := by decide +kernel
  have hcap : FrCWT2P0303Literal.q2 (-74717952001) 1 (-40) = ((-74717952001 : ℚ) / 1099511627776) := by decide +kernel
  have h := ceFrCWT2P0303Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT2CoverBlock037 : ∀ x ∈ Icc ((((169 : ℚ) / 256) : ℚ) : ℝ) ((((353 : ℚ) / 512) : ℚ) : ℝ), fieldTower ceFrCWT2Raw (poleF ceFrCWT2Raw.poles) 0 x ≤ ((((-74717952001 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT2P0296 liftFrCWT2P0297) (cover_union liftFrCWT2P0298 liftFrCWT2P0299)) (cover_union (cover_union liftFrCWT2P0300 liftFrCWT2P0301) (cover_union liftFrCWT2P0302 liftFrCWT2P0303)))
#print axioms FrCWT2CoverBlock037

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT2Assembly

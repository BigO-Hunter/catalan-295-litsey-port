module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0P0023

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 10000

private theorem liftFrCWT0P0016 : ∀ x ∈ Icc ((((-17179869179 : ℚ) / 17179869184) : ℚ) : ℝ) ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0016Lo = ((-17179869179 : ℚ) / 17179869184) := by decide +kernel
  have hhi : ceFrCWT0P0016Hi = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hcap : FrCWT0P0016Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0016Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0017 : ∀ x ∈ Icc ((((-2147483647 : ℚ) / 2147483648) : ℚ) : ℝ) ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0017Lo = ((-2147483647 : ℚ) / 2147483648) := by decide +kernel
  have hhi : ceFrCWT0P0017Hi = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hcap : FrCWT0P0017Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0017Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0018 : ∀ x ∈ Icc ((((-1073741823 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0018Lo = ((-1073741823 : ℚ) / 1073741824) := by decide +kernel
  have hhi : ceFrCWT0P0018Hi = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hcap : FrCWT0P0018Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0018Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0019 : ∀ x ∈ Icc ((((-536870911 : ℚ) / 536870912) : ℚ) : ℝ) ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0019Lo = ((-536870911 : ℚ) / 536870912) := by decide +kernel
  have hhi : ceFrCWT0P0019Hi = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hcap : FrCWT0P0019Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0019Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0020 : ∀ x ∈ Icc ((((-268435455 : ℚ) / 268435456) : ℚ) : ℝ) ((((-536870909 : ℚ) / 536870912) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0020Lo = ((-268435455 : ℚ) / 268435456) := by decide +kernel
  have hhi : ceFrCWT0P0020Hi = ((-536870909 : ℚ) / 536870912) := by decide +kernel
  have hcap : FrCWT0P0020Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0020Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0021 : ∀ x ∈ Icc ((((-536870909 : ℚ) / 536870912) : ℚ) : ℝ) ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0021Lo = ((-536870909 : ℚ) / 536870912) := by decide +kernel
  have hhi : ceFrCWT0P0021Hi = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hcap : FrCWT0P0021Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0021Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0022 : ∀ x ∈ Icc ((((-134217727 : ℚ) / 134217728) : ℚ) : ℝ) ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0022Lo = ((-134217727 : ℚ) / 134217728) := by decide +kernel
  have hhi : ceFrCWT0P0022Hi = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hcap : FrCWT0P0022Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0022Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

private theorem liftFrCWT0P0023 : ∀ x ∈ Icc ((((-67108863 : ℚ) / 67108864) : ℚ) : ℝ) ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) := by
  have hlo : ceFrCWT0P0023Lo = ((-67108863 : ℚ) / 67108864) := by decide +kernel
  have hhi : ceFrCWT0P0023Hi = ((-33554431 : ℚ) / 33554432) := by decide +kernel
  have hcap : FrCWT0P0023Literal.q2 (-25478048781) 1 (-38) = ((-25478048781 : ℚ) / 274877906944) := by decide +kernel
  have h := ceFrCWT0P0023Bound
  rw [hlo, hhi, hcap] at h
  simpa only [lfieldTower_nil_zero, add_zero] using h

theorem FrCWT0CoverBlock002 : ∀ x ∈ Icc ((((-17179869179 : ℚ) / 17179869184) : ℚ) : ℝ) ((((-33554431 : ℚ) / 33554432) : ℚ) : ℝ), fieldTower ceFrCWT0Raw (poleF ceFrCWT0Raw.poles) 0 x ≤ ((((-25478048781 : ℚ) / 274877906944) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union liftFrCWT0P0016 liftFrCWT0P0017) (cover_union liftFrCWT0P0018 liftFrCWT0P0019)) (cover_union (cover_union liftFrCWT0P0020 liftFrCWT0P0021) (cover_union liftFrCWT0P0022 liftFrCWT0P0023)))
#print axioms FrCWT0CoverBlock002

end CatalanMeasure.GenD.Signed.Data.Cells.D72.FrCWT0Assembly

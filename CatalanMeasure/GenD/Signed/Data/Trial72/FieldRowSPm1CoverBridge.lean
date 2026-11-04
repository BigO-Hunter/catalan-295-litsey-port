module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm1
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm1CoverBridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open AssemblyBindings
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

open CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell

structure Covers : Prop where
  before : ∀ y ∈ Icc (((999 : ℚ) / 1000) : ℝ) (((1023 : ℚ) / 1024) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 y ≤ (((-6317608997077 : ℚ) / 1099511627776) : ℝ)
  after : ∀ y ∈ Icc (((1023 : ℚ) / 1024) : ℝ) (((1 : ℚ) / 1) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 y ≤ (((-57030279665533 : ℚ) / 9895604649984) : ℝ)
  lower : ∀ y ∈ Icc (((98749 : ℚ) / 1000000) : ℝ) (((999 : ℚ) / 1000) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 200)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 200)).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 y ≤ (((-5779228294357 : ℚ) / 1099511627776) : ℝ)
  upper : ∀ y ∈ Icc (((98749 : ℚ) / 1000000) : ℝ) (((999 : ℚ) / 1000) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T1.spmAt ((1 : ℚ) / 16)).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T1.trial.qTn) 0 y ≤ (((-5754975790293 : ℚ) / 1099511627776) : ℝ)

theorem top (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T1.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-518573281 : ℚ) / 536870912) : ℚ) : ℝ) + ε := FieldRowSPm1.topOf
    (fun y hy => by
      have h := c.before y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit1.terms] at h ⊢
      exact h)
    (fun y hy => by
      have h := c.after y (by norm_num [Set.mem_Icc]; exact ⟨hy.1,hy.2.le⟩)
        ⟨by linarith [hy.1], hy.2⟩
      norm_num [FieldPositiveLimit1.terms] at h ⊢
      exact h)
#print axioms top

theorem offSmall (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ)+ε := FieldRowSPm1.offSmallOf (fun y hy => by
      have h := c.lower y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit1.terms] at h ⊢
      exact h)
#print axioms offSmall

theorem offWide (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-487700071 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε := FieldRowSPm1.offWideOf (fun y hy => by
      have h := c.lower y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit1.terms] at h ⊢
      exact h) (fun y hy => by
      have h := c.upper y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit1.terms] at h ⊢
      exact h)
#print axioms offWide

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm1CoverBridge

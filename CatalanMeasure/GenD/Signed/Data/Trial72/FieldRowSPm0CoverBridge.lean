module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0CoverBridge
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
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 y ≤ (((-3151596717623 : ℚ) / 549755813888) : ℝ)
  after : ∀ y ∈ Icc (((1023 : ℚ) / 1024) : ℝ) (((1 : ℚ) / 1) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 y ≤ (((-28450269804527 : ℚ) / 4947802324992) : ℝ)
  lower : ∀ y ∈ Icc (((98749 : ℚ) / 1000000) : ℝ) (((999 : ℚ) / 1000) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt ((1 : ℚ) / 200)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T0.spmAt ((1 : ℚ) / 200)).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T0.trial.qTn) 0 y ≤ (((-2882111069751 : ℚ) / 549755813888) : ℝ)

theorem top (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T0.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) + ε := FieldRowSPm0.topOf
    (fun y hy => by
      have h := c.before y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit0.terms] at h ⊢
      exact h)
    (fun y hy => by
      have h := c.after y (by norm_num [Set.mem_Icc]; exact ⟨hy.1,hy.2.le⟩)
        ⟨by linarith [hy.1], hy.2⟩
      norm_num [FieldPositiveLimit0.terms] at h ⊢
      exact h)
#print axioms top

theorem offSmall (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-256471011 : ℚ) / 536870912) : ℚ) : ℝ)+ε := FieldRowSPm0.offSmallOf (fun y hy => by
      have h := c.lower y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit0.terms] at h ⊢
      exact h)
#print axioms offSmall

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm0CoverBridge

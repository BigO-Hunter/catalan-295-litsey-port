module
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm2
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm2CoverBridge
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
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 y ≤ (((-3144710066661 : ℚ) / 549755813888) : ℝ)
  after : ∀ y ∈ Icc (((1023 : ℚ) / 1024) : ℝ) (((1 : ℚ) / 1) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt 0).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 y ≤ (((-28388289945869 : ℚ) / 4947802324992) : ℝ)
  lower : ∀ y ∈ Icc (((98749 : ℚ) / 1000000) : ℝ) (((999 : ℚ) / 1000) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 200)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 200)).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 y ≤ (((-2879621665765 : ℚ) / 549755813888) : ℝ)
  upper : ∀ y ∈ Icc (((98749 : ℚ) / 1000000) : ℝ) (((999 : ℚ) / 1000) : ℝ), y ∈ Ioo (0 : ℝ) 1 →
    fieldTower (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 16)) (poleF (CatalanMeasure.GenD.Signed.Data.Trial72.T2.spmAt ((1 : ℚ) / 16)).poles) 0 y + lfieldTower (CatalanMeasure.GenD.Signed.Data.Trial.dilTermsS CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qT CatalanMeasure.GenD.Signed.Data.Trial72.T2.trial.qTn) 0 y ≤ (((-2863106845669 : ℚ) / 549755813888) : ℝ)

theorem top (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T2.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ) + ε := FieldRowSPm2.topOf
    (fun y hy => by
      have h := c.before y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit2.terms] at h ⊢
      exact h)
    (fun y hy => by
      have h := c.after y (by norm_num [Set.mem_Icc]; exact ⟨hy.1,hy.2.le⟩)
        ⟨by linarith [hy.1], hy.2⟩
      norm_num [FieldPositiveLimit2.terms] at h ⊢
      exact h)
#print axioms top

theorem offWide (c : Covers) : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T2.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-493153623 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-460898115 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε := FieldRowSPm2.offWideOf (fun y hy => by
      have h := c.lower y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit2.terms] at h ⊢
      exact h) (fun y hy => by
      have h := c.upper y (by norm_num [Set.mem_Icc]; exact hy)
        ⟨by linarith [hy.1], by linarith [hy.2]⟩
      norm_num [FieldPositiveLimit2.terms] at h ⊢
      exact h)
#print axioms offWide

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowSPm2CoverBridge

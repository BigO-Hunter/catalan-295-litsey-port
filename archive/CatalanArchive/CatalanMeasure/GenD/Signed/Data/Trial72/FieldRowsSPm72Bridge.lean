module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72Bridge
open Set Filter CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true

structure Endpoints : Prop where
  t0top : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T0.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-519640589 : ℚ) / 536870912) : ℚ) : ℝ) + ε
  t0offSmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-256471011 : ℚ) / 536870912) : ℚ) : ℝ)+ε
  t1top : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T1.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-518573281 : ℚ) / 536870912) : ℚ) : ℝ) + ε
  t1offSmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ≤ (1/200 : ℝ), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤ ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ)+ε
  t1offWide : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-511384157 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-487700071 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε
  t2top : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ y ∈ Ioo (0 : ℝ) 1, (999/1000 : ℝ) ≤ y →
      (T2.D N).fPosMS (groupedMarkedField dc72.toParameters N) y ≤ ((((-505452203 : ℚ) / 536870912) : ℚ) : ℝ) + ε
  t2offWide : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (1/200 : ℝ) (1/16), ∀ y ∈ Ioo (0 : ℝ) 1,
      (98749/1000000 : ℝ) ≤ y → y < (999/1000 : ℝ) →
      (T2.D N).fPosMR (groupedMarkedField dc72.toParameters N) (11/8) α y ≤
        chord (1/200) (1/16) ((((-493153623 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-460898115 : ℚ) / 1073741824) : ℚ) : ℝ) α + ε

theorem hposA (r : Endpoints) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPA α + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [r.t0offSmall ε hε] with N hN α hα y hy hg hxc
    have hr : remC (1/10 : ℝ) = (11/8 : ℝ) := by norm_num [remC]
    change (T0.D N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (1/10 : ℝ)) α y ≤ _
    rw [hr]
    exact hN α hα.2 y hy hg hxc
  · filter_upwards [r.t1offWide ε hε] with N hN α hα y hy hg hxc
    have hr : remC (1/10 : ℝ) = (11/8 : ℝ) := by norm_num [remC]
    change (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (1/10 : ℝ)) α y ≤ _
    rw [hr]
    exact hN α hα y hy hg hxc
#print axioms hposA

theorem hposTopA (r : Endpoints) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPA α + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [r.t0top ε hε] with N hN α hα y hy hxc
    exact hN y hy hxc
  · filter_upwards [r.t1top ε hε] with N hN α hα y hy hxc
    exact hN y hy hxc
#print axioms hposTopA

theorem hposB (r : Endpoints) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (I.epsSplit i)) α x ≤ (capE i).lamPB α + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [r.t1offSmall ε hε] with N hN α hα y hy hg hxc
    have hr : remC (1/10 : ℝ) = (11/8 : ℝ) := by norm_num [remC]
    change (T1.D N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (1/10 : ℝ)) α y ≤ _
    rw [hr]
    exact hN α hα.2 y hy hg hxc
  · filter_upwards [r.t2offWide ε hε] with N hN α hα y hy hg hxc
    have hr : remC (1/10 : ℝ) = (11/8 : ℝ) := by norm_num [remC]
    change (T2.D N).fPosMR (groupedMarkedField dc72.toParameters N) (remC (1/10 : ℝ)) α y ≤ _
    rw [hr]
    exact hN α hα y hy hg hxc
#print axioms hposB

theorem hposTopB (r : Endpoints) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fPosMS (groupedMarkedField dc72.toParameters N) x ≤ (capE i).gPB α + ε := by
  intro i ε hε
  fin_cases i
  · filter_upwards [r.t1top ε hε] with N hN α hα y hy hxc
    exact hN y hy hxc
  · filter_upwards [r.t2top ε hε] with N hN α hα y hy hxc
    exact hN y hy hxc
#print axioms hposTopB

end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsSPm72Bridge

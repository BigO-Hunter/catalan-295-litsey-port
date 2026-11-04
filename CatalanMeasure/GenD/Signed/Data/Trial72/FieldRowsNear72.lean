module
public import CatalanMeasure.GenD.Signed.Data.Trial72.RowsCaps72
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners0
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners1
public import CatalanMeasure.GenD.Signed.Data.Trial72.FieldNearCorners2

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsNear72
open Set Filter CatalanMeasure.Signed CatalanMeasure.GenD.Analytic
open CatalanMeasure.GenD.Signed.Data.Assembly
open Inputs72 AssemblyBindings RowsCaps72
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem bilin_chord {lo hi α β L H : ℝ} (hlh : lo < hi) (hα : α ∈ Icc lo hi) :
    bilin lo hi L L H H α β = chord lo hi L H α := by
  have h0 : 0 ≤ (α-lo)/(hi-lo) := div_nonneg (sub_nonneg.mpr hα.1) (sub_nonneg.mpr hlh.le)
  have h1 : (α-lo)/(hi-lo) ≤ 1 := (div_le_iff₀ (sub_pos.mpr hlh)).mpr (by linarith [hα.2])
  unfold bilin chord interpL
  rw [min_eq_right h1, max_eq_right h0]
  ring

private theorem bilin_slope {lo hi α β : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi)
    (hα : α ∈ Icc lo hi) (hβ : β ∈ Icc 0 α) :
    bilin lo hi 0 ((5/11)*lo) 0 ((5/11)*hi) α β = (5/11)*β := by
  by_cases ha : α = 0
  · have hb : β = 0 := le_antisymm (ha ▸ hβ.2) hβ.1
    simp [bilin, ha, hb]
  · exact bilin_lin hlh (lt_of_le_of_ne (hlo.trans hα.1) (Ne.symm ha))

theorem hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSA α β + ε := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (((0 / 1 : ℚ)) : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((0 / 1 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X0 hok0 hRt0
      (lo := (((0 / 1 : ℚ)) : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-158556287 / 268435456 : ℚ)) : ℝ)) (T01 := (((-158556287 / 268435456 : ℚ)) : ℝ)) (T10 := (((-154938851 / 268435456 : ℚ)) : ℝ)) (T11 := (((-154938851 / 268435456 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners0.off0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.off0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.off1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.off2 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((0 / 1 : ℚ)) : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T01 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T10 := (((-225764819 / 536870912 : ℚ)) : ℝ)) (T11 := (((-225764819 / 536870912 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners1.off1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off2 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off3 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off4 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    exact hh
#print axioms hnearA

theorem hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1-x^2)) := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (((0 / 1 : ℚ)) : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((0 / 1 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X0 hok0 hRt0
      (lo := (((0 / 1 : ℚ)) : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-1034386673 / 1073741824 : ℚ)) : ℝ)) (G01 := (((-1034386673 / 1073741824 : ℚ)) : ℝ)) (G10 := (((-31888535 / 33554432 : ℚ)) : ℝ)) (G11 := (((-31888535 / 33554432 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((0 / 1 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 200 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners0.top0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.top0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.top1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners0.top2 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((0 / 1 : ℚ)) : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G01 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G10 := (((-428316267 / 536870912 : ℚ)) : ℝ)) (G11 := (((-428316267 / 536870912 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((1 / 200 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 16 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners1.top1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top2 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top3 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top4 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    exact hh
#print axioms hnearTopA

theorem hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSB α β + ε := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (((0 / 1 : ℚ)) : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((0 / 1 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((0 / 1 : ℚ)) : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-316571149 / 536870912 : ℚ)) : ℝ)) (T01 := (((-316571149 / 536870912 : ℚ)) : ℝ)) (T10 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T11 := (((-618669125 / 1073741824 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners1.off0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.off2 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((0 / 1 : ℚ)) : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X2 hok2 hRt2
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-303045805 / 536870912 : ℚ)) : ℝ)) (T01 := (((-303045805 / 536870912 : ℚ)) : ℝ)) (T10 := (((-27401485 / 67108864 : ℚ)) : ℝ)) (T11 := (((-27401485 / 67108864 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners2.off0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.off1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.off2 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.off3 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    exact hh
#print axioms hnearB

theorem hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1-x^2)) := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (((0 / 1 : ℚ)) : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((0 / 1 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((0 / 1 : ℚ)) : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-64440747 / 67108864 : ℚ)) : ℝ)) (G01 := (((-64440747 / 67108864 : ℚ)) : ℝ)) (G10 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G11 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((0 / 1 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 200 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners1.top0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners1.top2 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((0 / 1 : ℚ)) : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X2 hok2 hRt2
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-490033759 / 536870912 : ℚ)) : ℝ)) (G01 := (((-490033759 / 536870912 : ℚ)) : ℝ)) (G10 := (((-409800827 / 536870912 : ℚ)) : ℝ)) (G11 := (((-409800827 / 536870912 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((1 / 200 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 16 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => (FieldNearCorners2.top0 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.top1 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.top2 y hy).trans (by norm_num))
      (fun y hy => (FieldNearCorners2.top3 y hy).trans (by norm_num))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    exact hh
#print axioms hnearTopB
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsNear72

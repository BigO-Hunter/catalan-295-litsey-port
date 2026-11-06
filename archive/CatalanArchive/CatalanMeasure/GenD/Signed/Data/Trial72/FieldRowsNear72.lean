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

theorem hnearA (c0 : FieldNearCorners0.Covers) (c1 : FieldNearCorners1.Covers) (c2 : FieldNearCorners2.Covers) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSA α β + ε := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (0 : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (0 : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X0 hok0 hRt0
      (lo := (0 : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-158556287 / 268435456 : ℚ)) : ℝ)) (T01 := (((-158556287 / 268435456 : ℚ)) : ℝ)) (T10 := (((-154938851 / 268435456 : ℚ)) : ℝ)) (T11 := (((-154938851 / 268435456 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hh := (FieldNearCorners0.off0 c0 y hy).trans
          (show (((-158556287 / 268435456 : ℚ)) : ℝ) ≤ (((-158556287 / 268435456 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners0.off0 c0 y hy).trans
          (show (((-158556287 / 268435456 : ℚ)) : ℝ) ≤ (((-158556287 / 268435456 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners0.off1 c0 y hy).trans
          (show (((-157774281 / 268435456 : ℚ)) : ℝ) ≤ (((-154938851 / 268435456 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners0.off2 c0 y hy).trans
          (show (((-154938851 / 268435456 : ℚ)) : ℝ) ≤ (((-154938851 / 268435456 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (0 : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    change (T0.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T0.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (0:ℝ) (1/200:ℝ) (((-158556287 / 268435456 : ℚ)) : ℝ) (((-154938851 / 268435456 : ℚ)) : ℝ) α + ε
    norm_num at hh ⊢
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T01 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T10 := (((-225764819 / 536870912 : ℚ)) : ℝ)) (T11 := (((-225764819 / 536870912 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hh := (FieldNearCorners1.off1 c1 y hy).trans
          (show (((-630013205 / 1073741824 : ℚ)) : ℝ) ≤ (((-618669125 / 1073741824 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off2 c1 y hy).trans
          (show (((-618669125 / 1073741824 : ℚ)) : ℝ) ≤ (((-618669125 / 1073741824 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off3 c1 y hy).trans
          (show (((-593984413 / 1073741824 : ℚ)) : ℝ) ≤ (((-225764819 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off4 c1 y hy).trans
          (show (((-225764819 / 536870912 : ℚ)) : ℝ) ≤ (((-225764819 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (1/200:ℝ) (1/16:ℝ) (((-618669125 / 1073741824 : ℚ)) : ℝ) (((-225764819 / 536870912 : ℚ)) : ℝ) α + ε
    norm_num at hh ⊢
    exact hh
#print axioms hnearA

theorem hnearTopA (c0 : FieldNearCorners0.Covers) (c1 : FieldNearCorners1.Covers) (c2 : FieldNearCorners2.Covers) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DA i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1-x^2)) := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (0 : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (0 : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X0 hok0 hRt0
      (lo := (0 : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-1034386673 / 1073741824 : ℚ)) : ℝ)) (G01 := (((-1034386673 / 1073741824 : ℚ)) : ℝ)) (G10 := (((-31888535 / 33554432 : ℚ)) : ℝ)) (G11 := (((-31888535 / 33554432 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(0 : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 200 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hc : (((-1034386673 / 1073741824 : ℚ)) : ℝ) ≤ (((-1034386673 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners0.top0 c0 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-1034386673 / 1073741824 : ℚ)) : ℝ) ≤ (((-1034386673 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners0.top0 c0 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-515333355 / 536870912 : ℚ)) : ℝ) ≤ (((-31888535 / 33554432 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners0.top1 c0 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-31888535 / 33554432 : ℚ)) : ℝ) ≤ (((-31888535 / 33554432 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners0.top2 c0 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 200 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (0 : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    change (T0.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T0.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (0:ℝ) (1/200:ℝ) (((-1034386673 / 1073741824 : ℚ)) : ℝ) (((-31888535 / 33554432 : ℚ)) : ℝ) α + ε + (5/11*β+1/1000000) * (-Real.log (1-y^2))
    norm_num at hh ⊢
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G01 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G10 := (((-428316267 / 536870912 : ℚ)) : ℝ)) (G11 := (((-428316267 / 536870912 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((1 / 200 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 16 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hc : (((-1027331989 / 1073741824 : ℚ)) : ℝ) ≤ (((-1017098399 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top1 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-1017098399 / 1073741824 : ℚ)) : ℝ) ≤ (((-1017098399 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top2 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 200 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-492276207 / 536870912 : ℚ)) : ℝ) ≤ (((-428316267 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top3 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-428316267 / 536870912 : ℚ)) : ℝ) ≤ (((-428316267 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top4 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 16 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (1/200:ℝ) (1/16:ℝ) (((-1017098399 / 1073741824 : ℚ)) : ℝ) (((-428316267 / 536870912 : ℚ)) : ℝ) α + ε + (5/11*β+1/1000000) * (-Real.log (1-y^2))
    norm_num at hh ⊢
    exact hh
#print axioms hnearTopA

theorem hnearB (c0 : FieldNearCorners0.Covers) (c1 : FieldNearCorners1.Covers) (c2 : FieldNearCorners2.Covers) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).gs ≤ x → x < (capE i).xc → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).lamSB α β + ε := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (0 : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (0 : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (0 : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-316571149 / 536870912 : ℚ)) : ℝ)) (T01 := (((-316571149 / 536870912 : ℚ)) : ℝ)) (T10 := (((-618669125 / 1073741824 : ℚ)) : ℝ)) (T11 := (((-618669125 / 1073741824 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hh := (FieldNearCorners1.off0 c1 y hy).trans
          (show (((-316571149 / 536870912 : ℚ)) : ℝ) ≤ (((-316571149 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off0 c1 y hy).trans
          (show (((-316571149 / 536870912 : ℚ)) : ℝ) ≤ (((-316571149 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off1 c1 y hy).trans
          (show (((-630013205 / 1073741824 : ℚ)) : ℝ) ≤ (((-618669125 / 1073741824 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners1.off2 c1 y hy).trans
          (show (((-618669125 / 1073741824 : ℚ)) : ℝ) ≤ (((-618669125 / 1073741824 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (0 : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (0:ℝ) (1/200:ℝ) (((-316571149 / 536870912 : ℚ)) : ℝ) (((-618669125 / 1073741824 : ℚ)) : ℝ) α + ε
    norm_num at hh ⊢
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNear_cell dc72 AssemblyBindings.X2 hok2 hRt2
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (g := (98749/1000000:ℝ)) (xc := (999/1000:ℝ)) (T00 := (((-303045805 / 536870912 : ℚ)) : ℝ)) (T01 := (((-303045805 / 536870912 : ℚ)) : ℝ)) (T10 := (((-27401485 / 67108864 : ℚ)) : ℝ)) (T11 := (((-27401485 / 67108864 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hh := (FieldNearCorners2.off0 c2 y hy).trans
          (show (((-154366815 / 268435456 : ℚ)) : ℝ) ≤ (((-303045805 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners2.off1 c2 y hy).trans
          (show (((-303045805 / 536870912 : ℚ)) : ℝ) ≤ (((-303045805 / 536870912 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners2.off2 c2 y hy).trans
          (show (((-581310323 / 1073741824 : ℚ)) : ℝ) ≤ (((-27401485 / 67108864 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
      (fun y hy => by
        have hh := (FieldNearCorners2.off3 c2 y hy).trans
          (show (((-27401485 / 67108864 : ℚ)) : ℝ) ≤ (((-27401485 / 67108864 : ℚ)) : ℝ) from by norm_num)
        norm_num at hh ⊢
        exact hh)
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hg hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hg hxc
    rw [bilin_chord hlh ha] at hh
    change (T2.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T2.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (1/200:ℝ) (1/16:ℝ) (((-303045805 / 536870912 : ℚ)) : ℝ) (((-27401485 / 67108864 : ℚ)) : ℝ) α + ε
    norm_num at hh ⊢
    exact hh
#print axioms hnearB

theorem hnearTopB (c0 : FieldNearCorners0.Covers) (c1 : FieldNearCorners1.Covers) (c2 : FieldNearCorners2.Covers) : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ α ∈ Icc (I.lo i) (I.hi i), ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1,
      (capE i).xc ≤ x → (I.DB i N).fNearMS (groupedNearField dc72.toParameters N) α β x ≤ (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1-x^2)) := by
  intro i
  fin_cases i
  · intro ε hε
    have hlh : (0 : ℝ) < (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (0 : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X1 hok1 hRt1
      (lo := (0 : ℝ)) (hi := (((1 / 200 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-64440747 / 67108864 : ℚ)) : ℝ)) (G01 := (((-64440747 / 67108864 : ℚ)) : ℝ)) (G10 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (G11 := (((-1017098399 / 1073741824 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(0 : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 200 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hc : (((-64440747 / 67108864 : ℚ)) : ℝ) ≤ (((-64440747 / 67108864 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top0 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-64440747 / 67108864 : ℚ)) : ℝ) ≤ (((-64440747 / 67108864 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top0 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-1027331989 / 1073741824 : ℚ)) : ℝ) ≤ (((-1017098399 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top1 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-1017098399 / 1073741824 : ℚ)) : ℝ) ≤ (((-1017098399 / 1073741824 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners1.top2 c1 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 200 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (0 : ℝ) (((1 / 200 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T1.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (0:ℝ) (1/200:ℝ) (((-64440747 / 67108864 : ℚ)) : ℝ) (((-1017098399 / 1073741824 : ℚ)) : ℝ) α + ε + (5/11*β+1/1000000) * (-Real.log (1-y^2))
    norm_num at hh ⊢
    exact hh
  · intro ε hε
    have hlh : (((1 / 200 : ℚ)) : ℝ) < (((1 / 16 : ℚ)) : ℝ) := by norm_num
    have hlo : 0 ≤ (((1 / 200 : ℚ)) : ℝ) := by norm_num
    have key := Generic.rowNearTop_cell dc72 AssemblyBindings.X2 hok2 hRt2
      (lo := (((1 / 200 : ℚ)) : ℝ)) (hi := (((1 / 16 : ℚ)) : ℝ)) hlo hlh
      (xc := (999/1000 : ℝ)) (δ := (1/1000000:ℝ)) (G00 := (((-490033759 / 536870912 : ℚ)) : ℝ)) (G01 := (((-490033759 / 536870912 : ℚ)) : ℝ)) (G10 := (((-409800827 / 536870912 : ℚ)) : ℝ)) (G11 := (((-409800827 / 536870912 : ℚ)) : ℝ)) (r00 := 0) (r01 := (5/11)*(((1 / 200 : ℚ)) : ℝ)) (r10 := 0) (r11 := (5/11)*(((1 / 16 : ℚ)) : ℝ))
      (by norm_num) (by norm_num)
      (fun y hy => by
        have hc : (((-990301109 / 1073741824 : ℚ)) : ℝ) ≤ (((-490033759 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners2.top0 c2 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-490033759 / 536870912 : ℚ)) : ℝ) ≤ (((-490033759 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners2.top1 c2 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 200 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-947521533 / 1073741824 : ℚ)) : ℝ) ≤ (((-409800827 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners2.top2 c2 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (0 : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
      (fun y hy => by
        have hc : (((-409800827 / 536870912 : ℚ)) : ℝ) ≤ (((-409800827 / 536870912 : ℚ)) : ℝ) := by norm_num
        have hcorner := FieldNearCorners2.top3 c2 y hy
        have hh := add_le_add hc (le_refl ((5/11 * (((1 / 16 : ℚ)) : ℝ)) * (-Real.log (1-y^2))))
        norm_num at hcorner ⊢
        exact hcorner.trans (by norm_num <;> push_cast at hh <;> linarith only [hh]))
    filter_upwards [key ε hε] with N hN α hα β hβ y hy hxc
    have ha : α ∈ Icc (((1 / 200 : ℚ)) : ℝ) (((1 / 16 : ℚ)) : ℝ) := by
      norm_num at hα ⊢
      exact hα
    have hh := hN α ha β hβ y hy hxc
    rw [bilin_chord hlh ha] at hh
    rw [bilin_slope hlo hlh ha hβ] at hh
    change (T2.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ _ at hh
    change (T2.D N).fNearMS (groupedNearField dc72.toParameters N) α β y ≤ chord (1/200:ℝ) (1/16:ℝ) (((-490033759 / 536870912 : ℚ)) : ℝ) (((-409800827 / 536870912 : ℚ)) : ℝ) α + ε + (5/11*β+1/1000000) * (-Real.log (1-y^2))
    norm_num at hh ⊢
    exact hh
#print axioms hnearTopB
end CatalanMeasure.GenD.Signed.Data.Trial72.FieldRowsNear72

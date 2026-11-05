module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ.ZLBcap

@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD.Uniform.W.ZoneZ

theorem foldl_lcm_ne_zero (l : List ℕ) (a : ℕ) (ha : a ≠ 0) (hl : ∀ x ∈ l, x ≠ 0) :
    l.foldl Nat.lcm a ≠ 0 := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x t ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hl x (List.mem_cons_self))) (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem Zmom_ne : Zmom ≠ 0 := by
  unfold Zmom
  refine foldl_lcm_ne_zero _ _ one_ne_zero ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, -, J, -, rfl | rfl⟩ := hx
  · exact Rat.den_nz _
  · exact Rat.den_nz _

theorem ZcH_ne : ZcH ≠ 0 := by
  unfold ZcH
  refine foldl_lcm_ne_zero _ _ Zmom_ne ?_
  intro x hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with ⟨k, -, rfl | rfl | rfl | rfl⟩ | rfl | rfl | rfl <;> exact Rat.den_nz _

theorem ZcH6_ne : ZcH6 ≠ 0 := by
  unfold ZcH6 ZcH'
  refine Nat.lcm_ne_zero (Nat.lcm_ne_zero ZcH_ne (Nat.lcm_ne_zero ?_ ?_)) (by norm_num)
  · simpa using DqU_num_ne
  · simpa using DqY_num_ne

theorem not_dvd_ZcH6 {N p : ℕ} (hN : ZcH6 ≤ N) (hp : N < p) : ¬ p ∣ ZcH6 := fun h =>
  absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero ZcH6_ne) h) (by omega)

theorem not_dvd_ZcH' {N p : ℕ} (hN : ZcH6 ≤ N) (hp : N < p) : ¬ p ∣ ZcH' := fun h =>
  not_dvd_ZcH6 hN hp (h.trans (Nat.dvd_lcm_left _ _))

theorem no_zH6_unit72 {p : ℕ} (h : ZcH6 < p) : ¬ p ∣ ZcH6 :=
  not_dvd_ZcH6 (le_refl _) h

theorem no_zH_unit72 {p : ℕ} (h : ZcH6 < p) : ¬ p ∣ ZcH' :=
  not_dvd_ZcH' (le_refl _) h

end CatalanMeasure.GenD.Uniform.ContentBank.D72

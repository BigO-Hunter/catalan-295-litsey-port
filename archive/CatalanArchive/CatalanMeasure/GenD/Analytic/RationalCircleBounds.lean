module
public import CatalanMeasure.GenD.Analytic.S1BlockBounds
@[expose] public section
namespace CatalanMeasure.GenD.Analytic
noncomputable section

theorem rationalCirclePoint_re_antitone {r u v : ℝ} (hr : 0 ≤ r)
    (hu : 0 ≤ u) (huv : u ≤ v) :
    (rationalCirclePoint r 1 v).re ≤ (rationalCirclePoint r 1 u).re := by
  have hs : u^2 ≤ v^2 := (sq_le_sq₀ hu (hu.trans huv)).mpr huv
  change r*1*(1-v^2)/(1+v^2) ≤ r*1*(1-u^2)/(1+u^2)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hs)]

theorem rationalCirclePoint_re_side_neg (r u : ℝ) :
    (rationalCirclePoint r (-1) u).re = -(rationalCirclePoint r 1 u).re := by
  unfold rationalCirclePoint
  simp only [Complex.re]
  ring

theorem rationalCirclePoint_filter_sq_le {r a b u side : ℝ} (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hu : u ∈ Set.Icc a b) (hs : side = 1 ∨ side = -1) :
    ‖(1 : ℂ)-rationalCirclePoint r side u‖^2 ≤
      1+r^2-2*(if side=1 then (rationalCirclePoint r side b).re
        else (rationalCirclePoint r side a).re) := by
  apply filter_norm_sq_le_of_real_lower (rationalCirclePoint_norm_sq r side u hs)
  rcases hs with rfl | rfl
  · simp only [ite_true]
    exact rationalCirclePoint_re_antitone hr (ha.trans hu.1) hu.2
  · simp only [show (-1 : ℝ) ≠ 1 by norm_num, ite_false, rationalCirclePoint_re_side_neg]
    exact neg_le_neg (rationalCirclePoint_re_antitone hr ha hu.1)

theorem rationalCirclePoint_filter_ne_zero {r side u : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hs : side=1 ∨ side = -1) : ‖(1 : ℂ)-rationalCirclePoint r side u‖ ≠ 0 := by
  intro h
  have hz : rationalCirclePoint r side u = 1 := by
    exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm
  have hh := rationalCirclePoint_norm_sq r side u hs
  rw [hz, norm_one] at hh
  nlinarith

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_re_antitone
#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_filter_sq_le
#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_filter_ne_zero

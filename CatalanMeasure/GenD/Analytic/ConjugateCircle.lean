module
public import CatalanMeasure.GenD.Analytic.RationalCircleCover
public import Mathlib.Analysis.RCLike.Lemmas
@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial ComplexConjugate
noncomputable section

theorem ellipseLog_conj (v : ℂ) : ellipseLog (conj v)=ellipseLog v := by
  have hm : ‖conj v-1‖=‖v-1‖ := by
    simpa only [map_sub,map_one] using Complex.norm_conj (v-1)
  have hp : ‖conj v+1‖=‖v+1‖ := by
    simpa only [map_add,map_one] using Complex.norm_conj (v+1)
  simp only [ellipseLog,ellipseH,hm,hp]

theorem realPolynomial_circle_weight_of_charts (p : ℝ[X]) {r C : ℝ}
    (hr : 0 < r)
    (hcharts : ∀ side : ℝ, (side=1 ∨ side = -1) → ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (66 : ℝ)/130*ellipseLog ((p.map (algebraMap ℝ ℂ)).eval
        (rationalCirclePoint r side u)) +
      8*Real.log ‖(1 : ℂ)-rationalCirclePoint r side u‖ ≤ C)
    (z : ℂ) (hz : ‖z‖=r) :
    (66 : ℝ)/130*ellipseLog ((p.map (algebraMap ℝ ℂ)).eval z)+
      8*Real.log ‖(1 : ℂ)-z‖ ≤ C := by
  have hupper : ∀ w : ℂ, ‖w‖=r → 0 ≤ w.im →
      (66 : ℝ)/130*ellipseLog ((p.map (algebraMap ℝ ℂ)).eval w)+
      8*Real.log ‖(1 : ℂ)-w‖ ≤ C := by
    intro w hw hi
    obtain ⟨side,hs,u,hu,he⟩ := rationalCirclePoint_covers_upper hr w hw hi
    rw [← he]
    exact hcharts side hs u hu
  by_cases hi : 0 ≤ z.im
  · exact hupper z hz hi
  · have hh := hupper (conj z) (by simpa only [Complex.norm_conj] using hz)
      (by simp only [Complex.conj_im]; linarith [not_le.mp hi])
    have he : (p.map (algebraMap ℝ ℂ)).eval (conj z) =
        conj ((p.map (algebraMap ℝ ℂ)).eval z) := by
      simpa only [aeval_def,eval₂_eq_eval_map] using (p.aeval_conj z)
    have hn : ‖(1 : ℂ)-conj z‖=‖(1 : ℂ)-z‖ := by
      simpa only [map_sub,map_one] using Complex.norm_conj (1-z)
    rwa [he,ellipseLog_conj,hn] at hh

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.ellipseLog_conj
#print axioms CatalanMeasure.GenD.Analytic.realPolynomial_circle_weight_of_charts

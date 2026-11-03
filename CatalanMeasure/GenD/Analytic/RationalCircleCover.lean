module
public import CatalanMeasure.GenD.Analytic.S1BlockBounds
@[expose] public section
namespace CatalanMeasure.GenD.Analytic
noncomputable section

theorem circle_ratio_identities {r x y : ℝ} (hr : 0 < r) (hx : 0 ≤ x)
    (hsq : x^2+y^2=r^2) :
    r*(1-(y/(r+x))^2)/(1+(y/(r+x))^2)=x ∧
    2*r*(y/(r+x))/(1+(y/(r+x))^2)=y := by
  have hd : 0 < r+x := by linarith
  have hd2 : (r+x)^2+y^2=2*r*(r+x) := by nlinarith
  have hm2 : (r+x)^2-y^2=2*x*(r+x) := by nlinarith
  have he : 1+(y/(r+x))^2 = (2*r)/(r+x) := by
    field_simp [hd.ne']
    nlinarith
  rw [he]
  constructor
  · field_simp [hd.ne', hr.ne']
    nlinarith [hm2]
  · field_simp [hd.ne', hr.ne']

/-- Two rational charts cover the closed upper semicircle, including its ends. -/
theorem rationalCirclePoint_covers_upper {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hz : ‖z‖=r) (him : 0 ≤ z.im) :
    ∃ side : ℝ, (side=1 ∨ side = -1) ∧ ∃ u ∈ Set.Icc (0 : ℝ) 1,
      rationalCirclePoint r side u=z := by
  have hsq : z.re^2+z.im^2=r^2 := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : |z.re| ≤ r := (Complex.abs_re_le_norm z).trans_eq hz
  have hry : z.im ≤ r := (le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans_eq hz)
  let u := z.im/(r+|z.re|)
  have hd : 0 < r+|z.re| := by positivity
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith [abs_nonneg z.re]
  have hratio := circle_ratio_identities hr (abs_nonneg z.re)
    (show |z.re|^2+z.im^2=r^2 by simpa only [sq_abs] using hsq)
  by_cases hre : 0 ≤ z.re
  · refine ⟨1,Or.inl rfl,u,⟨hu0,hu1⟩,?_⟩
    apply Complex.ext
    · change r*1*(1-u^2)/(1+u^2)=z.re
      simpa only [u, mul_one, abs_of_nonneg hre] using hratio.1
    · exact hratio.2
  · refine ⟨-1,Or.inr rfl,u,⟨hu0,hu1⟩,?_⟩
    apply Complex.ext
    · change r*(-1)*(1-u^2)/(1+u^2)=z.re
      have hh : r*(1-u^2)/(1+u^2) = -z.re := by
        simpa only [u, abs_of_neg (lt_of_not_ge hre)] using hratio.1
      calc
        _ = -(r*(1-u^2)/(1+u^2)) := by ring
        _ = z.re := by rw [hh]; ring
    · exact hratio.2

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.circle_ratio_identities
#print axioms CatalanMeasure.GenD.Analytic.rationalCirclePoint_covers_upper

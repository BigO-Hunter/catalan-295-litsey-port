module
public import CatalanMeasure.GenD.Signed.Davis.S1CheckedBlocks
public import CatalanMeasure.GenD.Analytic.RationalCircleBounds
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.S1CircleArc
open Set Polynomial CatalanMeasure.GenD.Analytic
open GaussianHorner S1PolynomialBounds S1CheckedBlocks
noncomputable section

def circleRe (side u : ℚ) : ℚ := (3/5)*side*(1-u^2)/(1+u^2)
def circleIm (u : ℚ) : ℚ := 2*(3/5)*u/(1+u^2)

theorem circleRe_cast (side u : ℚ) :
    (circleRe side u : ℝ) = (rationalCirclePoint (3/5) side u).re := by
  simp [circleRe, rationalCirclePoint]
  <;> norm_num
theorem circleIm_cast (side u : ℚ) :
    (circleIm u : ℝ) = (rationalCirclePoint (3/5) side u).im := by
  simp [circleIm, rationalCirclePoint]
  <;> norm_num

structure Arc where
  lo : ℚ
  hi : ℚ
  c : ℤ × ℤ
  q : ℤ
  v : ℤ × ℤ
  um : ℤ
  up : ℤ
  H : ℚ
  R : ℚ
  W : ℚ

def arcOK (side M : ℚ) (E : ℤ) (a : Arc) : Bool := decide (
  0 < a.q ∧ 0 ≤ a.um ∧ 0 ≤ a.up ∧
  (a.v.1-scaleInt a.q)^2+a.v.2^2 ≤ a.um^2 ∧
  (a.v.1+scaleInt a.q)^2+a.v.2^2 ≤ a.up^2 ∧
  0 ≤ a.lo ∧ a.lo ≤ a.hi ∧ a.hi ≤ 1 ∧
  (a.c.1 : ℚ)/(2*a.q) = circleRe side ((a.lo+a.hi)/2) ∧
  (a.c.2 : ℚ)/(2*a.q) = circleIm ((a.lo+a.hi)/2) ∧
  ((a.um : ℚ)+a.up)/(2*scaleInt a.q)+M*(3/5)*(a.hi-a.lo) ≤ a.H ∧
  a.H ≤ a.R ∧ a.H^2-1 ≤ (a.R-a.H)^2 ∧
  1+(3/5 : ℚ)^2-2*circleRe side a.lo ≤ a.W ∧
  1+(3/5 : ℚ)^2-2*circleRe side a.hi ≤ a.W ∧
  a.R^33*a.W^260 ≤ (E : ℚ))

theorem checked_arc_weight (side M blo bhi : ℚ) (E : ℤ) (a : Arc)
    (hs : side=1 ∨ side = -1) (hM0 : 0 ≤ M)
    (hok : arcOK side M E a = true)
    (hvalue : (Normalized130.normalizedCoefficients.reverse.foldl
      (valueStep a.c a.q) ((0,0),1)).1 = a.v)
    (hcover : blo ≤ a.lo ∧ a.hi ≤ bhi)
    (hder : ∀ z ∈ Metric.closedBall
        (rationalCirclePoint (3/5) side (((blo : ℝ)+bhi)/2))
        ((3/5)*((bhi : ℝ)-blo)), ‖complexP.derivative.eval z‖ ≤ (M : ℝ))
    {C : ℝ} (hE : (E : ℝ) ≤ Real.exp (65*C))
    (u : ℝ) (hu : u ∈ Icc (a.lo : ℝ) a.hi) :
    (66 : ℝ)/130 * ellipseLog (complexP.eval (rationalCirclePoint (3/5) side u)) +
      8*Real.log ‖(1 : ℂ)-rationalCirclePoint (3/5) side u‖ ≤ C := by
  simp only [arcOK, decide_eq_true_eq] at hok
  rcases hok with ⟨hq,hum,hup,hmsq,hpsq,hlo,hlohi,hhi,hcre,hcim,hH,hHR,hsq,hWlo,hWhi,hpower⟩
  have hsR : (side : ℝ)=1 ∨ (side : ℝ) = -1 := by exact_mod_cast hs
  have hM0R : (0 : ℝ) ≤ M := by exact_mod_cast hM0
  have hcoverR : (blo : ℝ) ≤ a.lo ∧ (a.hi : ℝ) ≤ bhi := by exact_mod_cast hcover
  have hinterval : (a.lo : ℝ) ≤ a.hi := by exact_mod_cast hlohi
  have hcenter : castPair a.c/(2*(a.q : ℂ)) =
      rationalCirclePoint (3/5) side (((a.lo : ℝ)+a.hi)/2) := by
    have hcreR : (a.c.1 : ℝ)/(2*(a.q : ℝ)) =
        (circleRe side ((a.lo+a.hi)/2) : ℝ) := by exact_mod_cast hcre
    have hcimR : (a.c.2 : ℝ)/(2*(a.q : ℝ)) =
        (circleIm ((a.lo+a.hi)/2) : ℝ) := by exact_mod_cast hcim
    rw [circleRe_cast] at hcreR
    rw [circleIm_cast (side := side)] at hcimR
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hcreR hcimR
    have hd : 2*(a.q : ℂ) = ((2*(a.q : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    apply Complex.ext
    · rw [hd, Complex.div_ofReal_re]
      simpa [castPair] using hcreR
    · rw [hd, Complex.div_ofReal_im]
      simpa [castPair] using hcimR
  have hpoint := point_ellipse_bound a.c a.v hq hvalue a.um a.up hum hup hmsq hpsq
  rw [hcenter] at hpoint
  have hHRR : (a.H : ℝ) ≤ a.R := by exact_mod_cast hHR
  have hsqR : (a.H : ℝ)^2-1 ≤ ((a.R : ℝ)-a.H)^2 := by exact_mod_cast hsq
  have hHRcenter : ellipseH (complexP.eval
      (rationalCirclePoint (3/5) side (((a.lo : ℝ)+a.hi)/2))) +
        (M : ℝ)*((3/5)*((a.hi : ℝ)-a.lo)) ≤ (a.H : ℝ) := by
    have hh : ((a.um : ℝ)+(a.up : ℝ))/(2*(scaleInt a.q : ℝ))+
        (M : ℝ)*(3/5)*((a.hi : ℝ)-a.lo) ≤ (a.H : ℝ)  := by
      have hh := (Rat.cast_le (K := ℝ)).mpr hH
      push_cast at hh
      simpa only [Rat.cast_divInt, Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hh
    nlinarith
  have hW : ‖(1 : ℂ)-rationalCirclePoint (3/5) side u‖^2 ≤ (a.W : ℝ) := by
    have hh := rationalCirclePoint_filter_sq_le (by norm_num : (0 : ℝ) ≤ 3/5)
      (show (0 : ℝ) ≤ a.lo by exact_mod_cast hlo) hu hsR
    rcases hs with rfl | rfl
    · simp only [Rat.cast_one, ite_true] at hh
      have hw : 1+(3/5 : ℝ)^2-2*(circleRe 1 a.hi : ℝ) ≤ (a.W : ℝ)  := by
        have hh := (Rat.cast_le (K := ℝ)).mpr hWhi
        push_cast at hh
        exact hh
      rw [circleRe_cast] at hw
      simp only [Rat.cast_one, Rat.cast_neg] at hw
      simpa only [Rat.cast_one, Rat.cast_neg] using hh.trans hw
    · simp only [Rat.cast_neg, Rat.cast_one, show (-1 : ℝ) ≠ 1 by norm_num, ite_false] at hh
      have hw : 1+(3/5 : ℝ)^2-2*(circleRe (-1) a.lo : ℝ) ≤ (a.W : ℝ)  := by
        have hh := (Rat.cast_le (K := ℝ)).mpr hWlo
        push_cast at hh
        exact hh
      rw [circleRe_cast] at hw
      simp only [Rat.cast_one, Rat.cast_neg] at hw
      simpa only [Rat.cast_one, Rat.cast_neg] using hh.trans hw
  have hpR : (a.R : ℝ)^33*(a.W : ℝ)^260 ≤ (E : ℝ) := by exact_mod_cast hpower
  apply polynomial_circle_weight_le_of_block complexP (convex_closedBall _ _) hM0R hder
    (rationalCirclePoint_mem_block (by norm_num) _ hsR
      ⟨hcoverR.1.trans hu.1,hu.2.trans hcoverR.2⟩)
    (rationalCirclePoint_mem_block (by norm_num) _ hsR
      (show (((a.lo : ℝ)+a.hi)/2) ∈ Icc (blo : ℝ) bhi by constructor <;> linarith))
    (by simpa only [Metric.mem_closedBall,dist_eq_norm] using
      rationalCirclePoint_mem_block (by norm_num : (0 : ℝ) ≤ 3/5) (side : ℝ) hsR hu)
    hHRcenter hHRR hsqR
    (rationalCirclePoint_filter_ne_zero (by norm_num) (by norm_num) hsR) hW (hpR.trans hE)

end
end CatalanMeasure.GenD.Signed.Davis.S1CircleArc
#print axioms CatalanMeasure.GenD.Signed.Davis.S1CircleArc.checked_arc_weight

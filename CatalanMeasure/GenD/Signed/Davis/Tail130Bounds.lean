module
public import CatalanMeasure.GenD.Signed.Davis.Tail130Data
public import CatalanMeasure.GenD.Signed.Davis.S1PolynomialBounds
public import CatalanMeasure.GenD.Signed.Davis.Design72NodeCap
public import CatalanMeasure.GenD.Analytic.GaussianNumericBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis.Tail130Bounds
open Set Polynomial CatalanMeasure.GenD.Analytic
open GaussianHorner GaussianCertificate GaussianNumericBounds
open S1PolynomialBounds Tail130Data CatalanMeasure.Refinement.Trimmed130
noncomputable section

theorem real_derivative_eval (t : ℝ) :
    complexP.derivative.eval (t : ℂ) = ((realP.derivative.eval t : ℝ) : ℂ) := by
  simp only [complexP, derivative_map]
  exact eval_map_apply (algebraMap ℝ ℂ) (p := realP.derivative) t

theorem tail_argument_bound {t : ℝ} (ht : t ∈ Icc tailStart72 1) :
    ‖2 * ((1 : ℤ) : ℂ) * (t : ℂ) - castPair (2,0)‖ ≤ (2 : ℝ) / 1998001 := by
  have he : 2 * ((1 : ℤ) : ℂ) * (t : ℂ) - castPair (2,0) = ((2*t-2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [castPair]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp [tailStart72] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem horner_bound :
    normHorner (weights.map (fun (a : ℤ) => (a : ℝ))) ((2 : ℝ) / 1998001) =
      (numerator : ℝ) / 1998001^129 := by
  have hh := positiveHorner_sound weights 2 1998001 (by norm_num)
  rw [sum_check, shape_check.1] at hh
  simp only [Int.cast_ofNat] at hh
  apply (eq_div_iff (by positivity : (1998001 : ℝ)^129 ≠ 0)).mpr
  have he : (1998001 : ℝ)^130 = 1998001^129 * 1998001 := by ring
  rw [he] at hh
  nlinarith

theorem derivative_upper (t : ℝ) (ht : t ∈ Icc tailStart72 1) :
    ‖realP.derivative.eval t‖ ≤ 20000 := by
  have hn : (numerator : ℝ) ≤ 20000 * (coefficientDenominator : ℝ) * 1998001^129 := by
    exact_mod_cast witness.2.1
  have hB : ‖(polynomialOfPairs cs).derivative.eval
      (2 * ((1 : ℤ) : ℂ) * (t : ℂ) - castPair (2,0))‖ ≤
      20000 * (coefficientDenominator : ℝ) := by
    apply derivative_norm_le_of_checks cs weights norm_checks.1 2 1998001 numerator
      (by norm_num) (by norm_num) sum_check _ _ (tail_argument_bound ht)
    rw [shape_check.1]
    simp only [Int.cast_ofNat]
    calc
      (numerator : ℝ) * 1998001 ≤
          (20000 * (coefficientDenominator : ℝ) * 1998001^129) * 1998001 :=
        mul_le_mul_of_nonneg_right hn (by norm_num)
      _ = 1998001^130 * (20000 * (coefficientDenominator : ℝ)) := by ring
  have hh := derivative_norm_bound cs (2,0) (q := 1) (by norm_num) translation
    (t : ℂ) (M := 20000) hB (by simp)
  rw [real_derivative_eval, Complex.norm_real, Real.norm_eq_abs] at hh
  simpa only [Real.norm_eq_abs] using hh

theorem derivative_positive (t : ℝ) (ht : t ∈ Icc tailStart72 1) :
    0 < realP.derivative.eval t := by
  let z : ℂ := 2 * ((1 : ℤ) : ℂ) * (t : ℂ) - castPair (2,0)
  have hl := evalPairs_re_lower (h1,0) (weightedPairs 1 cs.tail).tail
    (weights.tail.map (fun (a : ℤ) => (a : ℝ))) (normsOK_sound norm_checks.2)
    (by positivity : (0 : ℝ) ≤ 2 / 1998001) z (tail_argument_bound ht)
  have heval : (polynomialOfPairs cs).derivative.eval z =
      evalPairs ((h1,0) :: (weightedPairs 1 cs.tail).tail) z := by
    rw [polynomialOfPairs_derivative, polynomialOfPairs_eval]
    conv_lhs => rw [shape_check.2.1]
  rw [← heval] at hl
  have hshape : normHorner (weights.map (fun (a : ℤ) => (a : ℝ))) ((2 : ℝ)/1998001) =
      (h1 : ℝ) + (2 / 1998001) *
        normHorner (weights.tail.map (fun (a : ℤ) => (a : ℝ))) (2 / 1998001) := by
    conv_lhs => rw [shape_check.2.2.1]
    rfl
  have hpositive : (0 : ℝ) < 2*(h1 : ℝ)*1998001^129-(numerator : ℝ) := by
    exact_mod_cast witness.1
  have hlpos : 0 < ((polynomialOfPairs cs).derivative.eval z).re := by
    have hden : (0 : ℝ) < 1998001^129 := by positivity
    have hsmall : (numerator : ℝ) / 1998001^129 < 2*(h1 : ℝ) :=
      (div_lt_iff₀ hden).mpr (by linarith)
    rw [horner_bound] at hshape
    linarith
  have hd := polynomial_derivative_affine_identity complexP (polynomialOfPairs cs)
    (2 * ((1 : ℤ) : ℂ)) (-castPair (2,0)) (blockScale 1)
    (translated_eval cs (2,0) (q := 1) (by norm_num) translation) (t : ℂ)
  have hD : (coefficientDenominator : ℂ) ≠ 0 := by exact_mod_cast coefficientDenominator_pos.ne'
  have hfactor : (2 * ((1 : ℤ) : ℂ)) / blockScale 1 = 1 / (coefficientDenominator : ℂ) := by
    simp only [blockScale, Int.cast_one, one_pow, mul_one]
    field_simp
    <;> ring
  rw [hfactor, real_derivative_eval] at hd
  have hmul : (polynomialOfPairs cs).derivative.eval z =
      (coefficientDenominator : ℂ) * ((realP.derivative.eval t : ℝ) : ℂ) := by
    dsimp only [z]
    rw [sub_eq_add_neg]
    have hd' : ((realP.derivative.eval t : ℝ) : ℂ) =
        (polynomialOfPairs cs).derivative.eval (2 * ((1 : ℤ) : ℂ) * (t : ℂ) + -castPair (2,0)) /
          (coefficientDenominator : ℂ) := by
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hd
    simpa only [mul_comm] using ((eq_div_iff hD).mp hd').symm
  rw [hmul] at hlpos
  have hreal : ((coefficientDenominator : ℂ) * ((realP.derivative.eval t : ℝ) : ℂ)).re =
      (coefficientDenominator : ℝ) * realP.derivative.eval t := by simp
  rw [hreal] at hlpos
  exact (mul_pos_iff_of_pos_left (by exact_mod_cast coefficientDenominator_pos)).mp hlpos

theorem endpoint_lower : 1 ≤ realP.eval 1 := by
  have he := translated_eval_mul cs (2,0) (q := 1) (by norm_num) translation ((1 : ℤ) : ℂ)
  simp only [Int.cast_one, mul_one] at he
  have harg : (2 : ℂ) - castPair (2,0) = 0 := by
    apply Complex.ext <;> simp [castPair]
  rw [harg, polynomialOfPairs_eval, shape_check.2.2.2] at he
  simp only [evalPairs, zero_mul, add_zero, castPair_real, blockScale, Int.cast_one,
    one_pow, mul_one, complexP, eval_map_apply] at he
  have hp : (realP.map (algebraMap ℝ ℂ)).eval 1 = ((realP.eval 1 : ℝ) : ℂ) := by
    simpa using! (eval_map_apply (algebraMap ℝ ℂ) (p := realP) (1 : ℝ))
  rw [hp] at he
  have hre := congrArg Complex.re he
  have hw : 2*(coefficientDenominator : ℝ) ≤ (h0 : ℝ) := by exact_mod_cast witness.2.2
  have hD : (0 : ℝ) < coefficientDenominator := by exact_mod_cast coefficientDenominator_pos
  norm_num at hre
  nlinarith

theorem tail_strictMono : StrictMonoOn realP.eval (Icc tailStart72 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) realP.continuous.continuousOn
  intro t ht
  rw [realP.deriv]
  exact derivative_positive t (interior_subset ht)

def geometry72 : CatalanMeasure.GenD.Signed.Data.Assembly.Generic.NodeGeometryData dc72 :=
  geometry72_of_tail tail_strictMono derivative_upper endpoint_lower

end
end CatalanMeasure.GenD.Signed.Davis.Tail130Bounds
#print axioms CatalanMeasure.GenD.Signed.Davis.Tail130Bounds.derivative_upper
#print axioms CatalanMeasure.GenD.Signed.Davis.Tail130Bounds.derivative_positive
#print axioms CatalanMeasure.GenD.Signed.Davis.Tail130Bounds.endpoint_lower
#print axioms CatalanMeasure.GenD.Signed.Davis.Tail130Bounds.tail_strictMono
#print axioms CatalanMeasure.GenD.Signed.Davis.Tail130Bounds.geometry72

module

public import CatalanMeasure.GenD.Signed.Davis.Design72Nodes
public import CatalanMeasure.GenD.Signed.NodeGeometry
public import CatalanMeasure.GenD.Analytic.InverseImageLevels
public import CatalanMeasure.GenD.Analytic.NodeCapFromPolynomial
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis
open Set Filter Polynomial CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open CatalanMeasure.Refinement.Trimmed130 CatalanMeasure.Improvement.Fields
noncomputable section

def tailStart72 : ℝ := 1998000 / 1998001

theorem tailStart72_eq : realCoordinateInv (999 / 1000) = tailStart72 := by
  norm_num [realCoordinateInv, tailStart72]

theorem defect72_of_derivative_bound
    (hM : ∀ t ∈ Icc tailStart72 1, ‖realP.derivative.eval t‖ ≤ 20000)
    (hp1 : 1 ≤ realP.eval 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hxc : (999 / 1000 : ℝ) ≤ x) :
    1 - realP.eval (realCoordinateInv x) ≤ 20000 * (1 - x) ^ 2 / (1 + x ^ 2) := by
  have ht0 : tailStart72 ≤ realCoordinateInv x := by
    rw [← tailStart72_eq]
    exact realCoordinateInv_strictMonoOn.monotoneOn (by norm_num) hx hxc
  have ht1 : realCoordinateInv x ≤ 1 := by
    have hh := one_sub_realCoordinateInv x
    have hn : 0 ≤ (1 - x) ^ 2 / (1 + x ^ 2) := by positivity
    linarith
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc tailStart72 1) => (realP.hasDerivAt t).hasDerivWithinAt)
    hM (convex_Icc tailStart72 1) ⟨ht0, ht1⟩
    (show (1 : ℝ) ∈ Icc tailStart72 1 by norm_num [tailStart72])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)] at hbound
  have hle := (le_abs_self (realP.eval 1 - realP.eval (realCoordinateInv x))).trans hbound
  rw [one_sub_realCoordinateInv] at hle
  calc
    1 - realP.eval (realCoordinateInv x) ≤
        realP.eval 1 - realP.eval (realCoordinateInv x) := by linarith
    _ ≤ 20000 * ((1 - x) ^ 2 / (1 + x ^ 2)) := hle
    _ = _ := by ring

theorem nodeCap72_of_tail
    (hmono : StrictMonoOn realP.eval (Icc tailStart72 1))
    (hM : ∀ t ∈ Icc tailStart72 1, ‖realP.derivative.eval t‖ ≤ 20000)
    (hp1 : 1 ≤ realP.eval 1) {N : ℕ} (hN : 10 ≤ N) :
    CatalanMeasure.Signed.NodeCapAsym (19501 / 100000) (98749 / 1000000)
      (999 / 1000) (467829 / 1000000) (72 * (N : ℝ)) (umin72 N)
      (fun a => realCoordinate (tau72 N a)) := by
  let K := inverseImageDegree (66 * N) 130
  have hK0 : 0 < K := inverseImageDegree_pos (by omega) (by norm_num)
  have hK : 130 * K ≤ 66 * N + 130 := by
    have hb := (inverseImageDegree_bounds (66 * N) (by norm_num : 0 < 130)).2
    dsimp only [K]
    omega
  apply davis_nodeCapAsym_of_polynomial hN hK0 hK realP (tau72 N)
    (fun a => realCoordinate (tau72 N a))
    (inverseQuadratureLevel dc72.toParameters (by norm_num : 0 < 130) N) (t0 := tailStart72)
    (fun a => realCoordinate_mem (tau72_mem N a)) (tau72_support N)
    (tau72_injective N) (fun a => (tau72_mem N a).2.le)
  · intro a b
    have ha := realCoordinate_mem (tau72_mem N a)
    have hb := realCoordinate_mem (tau72_mem N b)
    have ea := realCoordinate_right_inverse (tau72_mem N a)
    have eb := realCoordinate_right_inverse (tau72_mem N b)
    constructor
    · intro h
      have hh := realCoordinateInv_strictMonoOn.monotoneOn ha hb h
      rwa [ea, eb] at hh
    · intro h
      apply le_of_realCoordinateInv_le ha hb
      rwa [ea, eb]
  · intro a hxc
    rw [← tailStart72_eq]
    have hh := realCoordinateInv_strictMonoOn.monotoneOn (by norm_num)
      (realCoordinate_mem (tau72_mem N a)) hxc
    rwa [realCoordinate_right_inverse (tau72_mem N a)] at hh
  · exact hmono
  · intro a
    exact inverseQuadratureNodes_eval_level dc72.toParameters branchCertificate (by norm_num) N a
  · intro a hxc
    have hh := defect72_of_derivative_bound hM hp1 (realCoordinate_mem (tau72_mem N a)) hxc
    rwa [realCoordinate_right_inverse (tau72_mem N a)] at hh

def geometry72_of_tail
    (hmono : StrictMonoOn realP.eval (Icc tailStart72 1))
    (hM : ∀ t ∈ Icc tailStart72 1, ‖realP.derivative.eval t‖ ≤ 20000)
    (hp1 : 1 ≤ realP.eval 1) :
    CatalanMeasure.GenD.Signed.Data.Assembly.Generic.NodeGeometryData dc72 where
  tau := tau72
  gsN := 19501 / 100000
  gsP := 98749 / 1000000
  xc := 999 / 1000
  C1 := 467829 / 1000000
  umin := umin72
  gsN_pos := by norm_num
  gsP_pos := by norm_num
  umin_pos := umin72_pos
  umin_le_one := umin72_le_one
  hlogu := umin72_log_sublinear
  cap := by
    filter_upwards [Filter.eventually_ge_atTop (10 : ℕ)] with N hN
    simpa only [DesignConst.d0, dc72, Nat.reduceSub, Nat.cast_mul, Nat.cast_ofNat] using nodeCap72_of_tail hmono hM hp1 hN

end
end CatalanMeasure.GenD.Signed.Davis
#print axioms CatalanMeasure.GenD.Signed.Davis.defect72_of_derivative_bound
#print axioms CatalanMeasure.GenD.Signed.Davis.nodeCap72_of_tail
#print axioms CatalanMeasure.GenD.Signed.Davis.geometry72_of_tail

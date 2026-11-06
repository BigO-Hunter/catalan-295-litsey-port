module

public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import CatalanMeasure.GenD.Signed.RouteI.InterceptSource
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option Elab.async false

/-!
# Route I `CorrelatedIntercept` (plan row C9): `Q0 + I0` cancellation and PSD curvature

* `I_mix`: `I ((1-t) z0 + t z1) = (1-t) I z0 + t I z1 - t(1-t) I (z0 - z1)`.
* `correlated_upper`: with the exact `Q0 = -I z0`, `Q0 + I(z_t) <= t(-a+b) - t(1-t) H`; the `t = 0`
  case cancels exactly, so no independently rounded upper cap for `I0` is used.
* `cross_le`, `curvature_lower`, `curvature_scalar`: PSD at `z0 - (51/50) z1` gives
  `H = I (z0 - z1) >= a/51 - b/50`; `curvature_numeric`: `54226975831/85e12 > .00063`.
* `InterceptSpace.gasI_le`, `InterceptSpace.anchI_le`, `gasICap`, `anchICap`: the two intercept fields
  of `CapFields.CapBundle`, bound to the source by the defining identities of `InterceptSource`.
-/


open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.InterceptSource
noncomputable section

namespace CatalanMeasure.GenD.Signed.RouteI.InterceptSource.PSDForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : PSDForm V)

/-- Mixing identity for the energy (polarization of the completed-Gram energy). -/
theorem I_mix (z0 z1 : V) (t : ℝ) :
    Q.I ((1 - t) • z0 + t • z1) = (1 - t) * Q.I z0 + t * Q.I z1 - t * (1 - t) * Q.I (z0 - z1) := by
  have h1 : Q.B ((1 - t) • z0) (t • z1) = (1 - t) * t * Q.B z0 z1 := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  rw [I_add, I_smul, I_smul, h1, I_sub]
  ring

/-- Correlated intercept: with the exact reference `Q0 = -I z0`, the upper bound for
`Q0 + I (z_t)` cancels at `t = 0` (no independently rounded upper cap for `I0`). -/
theorem correlated_upper (z0 z1 : V) {Q0 a b H t : ℝ} (hQ0 : Q0 = -Q.I z0)
    (ha : a ≤ Q.I z0) (hb : Q.I z1 ≤ b) (hH : H ≤ Q.I (z0 - z1)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Q0 + Q.I ((1 - t) • z0 + t • z1) ≤ t * (-a + b) - t * (1 - t) * H := by
  rw [I_mix, hQ0]
  have h1 : t * Q.I z1 ≤ t * b := mul_le_mul_of_nonneg_left hb ht0
  have h2 : t * (1 - t) * H ≤ t * (1 - t) * Q.I (z0 - z1) :=
    mul_le_mul_of_nonneg_left hH (mul_nonneg ht0 (by linarith))
  have h3 : t * a ≤ t * Q.I z0 := mul_le_mul_of_nonneg_left ha ht0
  nlinarith

/-- PSD at `z0 - u z1`: `2 B01 <= I0/u + u I1` (`u > 0`). -/
theorem cross_le (z0 z1 : V) {u : ℝ} (hu : 0 < u) :
    2 * Q.B z0 z1 ≤ Q.I z0 / u + u * Q.I z1 := by
  have h := Q.psd (z0 - u • z1)
  have e : Q.B (z0 - u • z1) (z0 - u • z1) = Q.I z0 - 2 * u * Q.B z0 z1 + u ^ 2 * Q.I z1 := by
    have := I_sub Q z0 (u • z1)
    have h2 : Q.B z0 (u • z1) = u * Q.B z0 z1 := by simp
    have h3 := I_smul Q u z1
    unfold I at this h3 ⊢
    rw [h2] at this
    rw [this, h3]; ring
  rw [e] at h
  rw [div_add' _ _ _ hu.ne', le_div_iff₀ hu]
  nlinarith

/-- Curvature lower bound: `I(z0 - z1) >= I0 (1 - 1/u) + I1 (1 - u)`. -/
theorem curvature_lower (z0 z1 : V) {u : ℝ} (hu : 0 < u) :
    Q.I z0 * (1 - 1 / u) + Q.I z1 * (1 - u) ≤ Q.I (z0 - z1) := by
  have h := cross_le Q z0 z1 hu
  rw [I_sub]
  have : Q.I z0 / u = Q.I z0 * (1 / u) := by ring
  nlinarith

/-- The `u = 51/50` instance: `H >= a/51 - b/50`. -/
theorem curvature_scalar (z0 z1 : V) {a b : ℝ} (ha : a ≤ Q.I z0) (hb : Q.I z1 ≤ b) :
    a / 51 - b / 50 ≤ Q.I (z0 - z1) := by
  have h := curvature_lower Q z0 z1 (u := 51 / 50) (by norm_num)
  have e1 : (1 - 1 / (51 / 50 : ℝ)) = 1 / 51 := by norm_num
  have e2 : (1 - (51 / 50 : ℝ)) = -(1 / 50) := by norm_num
  rw [e1, e2] at h
  nlinarith

end CatalanMeasure.GenD.Signed.RouteI.InterceptSource.PSDForm

namespace CatalanMeasure.GenD.Signed.RouteI.InterceptSource.InterceptSpace
variable {S : CapSource} {V : Type*} [AddCommGroup V] [Module ℝ V] (X : InterceptSpace S V)

/-- The curvature of the current anchors: `1.7416175854986/51 - 1.67557/50 = 54226975831/85e12 > .00063`. -/
theorem curvature_numeric :
    (54226975831 / 85000000000000 : ℝ) = 1.7416175854986 / 51 - 1.67557 / 50 ∧
      (0.00063 : ℝ) < 54226975831 / 85000000000000 := by
  constructor <;> norm_num

/-- Caps for the explicit `CapBundle` intercepts. `gasICap` uses the exact `-Q0` and the correlated
decrement; the anchor-0 intercept is capped by itself (`-Q0`, no separate rounded cap); the
marked anchor by `b`. Premises: `Q0 <= -a` (lower reference bound), `I1 <= b`, and the curvature
`H <= I (z0 - z1)` (e.g. `curvature_scalar`). -/
def gasICap (S : CapSource) (a b H t : ℝ) : ℝ := - refQuad S 0 + t * (b - a) - t * (1 - t) * H
def anchICap (S : CapSource) (b : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then - refQuad S 0 else b

theorem gasI_le {a b H t : ℝ} (ha : a ≤ - refQuad S 0) (hb : X.anchI 1 ≤ b)
    (hH : H ≤ X.Q.I (X.z 0 - X.z 1)) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    X.gasI t ≤ gasICap S a b H t := by
  have h := PSDForm.correlated_upper X.Q (X.z 0) (X.z 1) (Q0 := refQuad S 0) (a := a) (b := b) (H := H) (t := t)
    (by rw [X.i0_eq]; ring) (by rw [X.i0_eq]; exact ha) hb hH ht0 ht1
  unfold gasI gasICap
  linarith

theorem anchI_le {b : ℝ} (hb : X.anchI 1 ≤ b) :
    ∀ i : Fin 2, X.anchI i ≤ anchICap S b i := by
  intro i
  fin_cases i
  · simp [anchICap, X.anchI_zero]
  · simpa [anchICap] using hb

/-- With `curvature_scalar`: the caps with `H = a/51 - b/50`. -/
theorem gasI_le_scalar {a b t : ℝ} (ha : a ≤ - refQuad S 0) (hb : X.anchI 1 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    X.gasI t ≤ gasICap S a b (a / 51 - b / 50) t :=
  X.gasI_le ha hb (PSDForm.curvature_scalar X.Q (X.z 0) (X.z 1)
    (by rw [X.i0_eq]; exact ha) hb) ht0 ht1

end CatalanMeasure.GenD.Signed.RouteI.InterceptSource.InterceptSpace


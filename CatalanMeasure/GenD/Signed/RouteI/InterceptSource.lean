module

public import CatalanMeasure.GenD.Signed.RouteI.CapFields
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option Elab.async false

/-!
# Route I `InterceptSource` (plan row C9): reference quadratic and the intercept bindings

* `energy`, `dilL`, `refQuad`: the source reference quadratic
  `Q_a = E(F_a,F_a)/2 + E(C_a,C_a) - E(F_a, 2 C_a)` of `route_i_tangent_intercept.verify`, defined on
  the cell lists `refRow a`, `refCol a` of the `CapFields` source record.
* `PSDForm`: the shape of the completed-Gram energy (symmetric PSD bilinear form).
* `InterceptSpace S V`: reference vectors `z_0, z_1` in a PSD energy space with the single
  identification premise `I z_0 = - refQuad S 0` (PROOF-RI 12.26, not proved here).
* `InterceptSpace.anchI`, `InterceptSpace.gasI`: the explicit intercepts consumed by
  `CapFields.CapBundle`, defined as `anchI a = I z_a` and `gasI t = I ((1-t) z_0 + t z_1)`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.InterceptSource


open CatalanMeasure.GenD.Signed.RouteI.CapFields
noncomputable section

/-! ### Source quadratic of the reference pair (route_i_tangent_intercept.verify) -/

/-- Logarithmic energy `iint log |y - s| dF(y) dG(s)` of two cell lists (rows in the `Y`
coordinate, columns already dilated to it). -/
def energy (F G : List YCell) : ℝ := (F.map fun c => c.avg (potL G)).sum

/-- The cell list `C` of a column reference, doubled into the row coordinate. -/
def dilL (C : List YCell) : List YCell := C.map YCell.dil2

/-- Reference quadratic `Q_a = E(F,F)/2 + E(C,C) - E(F, 2C)` of the anchor-`a` reference pair
`(F_a, C_a) = (refRow a, refCol a)` of the source record. -/
def refQuad (S : CapSource) (a : Fin 2) : ℝ :=
  energy (S.refRow a) (S.refRow a) / 2 + energy (S.refCol a) (S.refCol a) -
    energy (S.refRow a) (dilL (S.refCol a))

/-- A symmetric positive semidefinite bilinear form on a real vector space: the shape of the
completed-Gram energy on the common-mass signed space (PROOF-RI 12.26). -/
structure PSDForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ x y, B x y = B y x
  psd : ∀ x, 0 ≤ B x x

namespace PSDForm
variable {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : PSDForm V)

/-- The energy `I z = B z z`. -/
def I (z : V) : ℝ := Q.B z z

lemma I_sub (x y : V) : Q.I (x - y) = Q.I x - 2 * Q.B x y + Q.I y := by
  unfold I
  simp only [map_sub, LinearMap.sub_apply]
  rw [Q.symm y x]; ring

lemma I_smul (c : ℝ) (x : V) : Q.I (c • x) = c ^ 2 * Q.I x := by
  unfold I
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring

lemma I_add (x y : V) : Q.I (x + y) = Q.I x + 2 * Q.B x y + Q.I y := by
  unfold I
  simp only [map_add, LinearMap.add_apply]
  rw [Q.symm y x]; ring

end PSDForm

/-- The reference vectors of the two anchors in a PSD energy space, bound to the source record:
`I z_0 = -Q_0` is the defining identity of the anchor-0 intercept (the reference is a
quadratic with `Q0 = -I0`), the marked anchor is `z_1`. The completed-Gram identification
`I z_0 = - refQuad S 0` is the premise `i0_eq`. -/
structure InterceptSpace (S : CapSource) (V : Type*) [AddCommGroup V] [Module ℝ V] where
  Q : PSDForm V
  z : Fin 2 → V
  i0_eq : Q.I (z 0) = - refQuad S 0

namespace InterceptSpace
variable {S : CapSource} {V : Type*} [AddCommGroup V] [Module ℝ V] (X : InterceptSpace S V)

/-- The anchor intercepts consumed by `CapFields.CapBundle`: `anchI a = I z_a`. -/
def anchI (a : Fin 2) : ℝ := X.Q.I (X.z a)

/-- The gas intercept at mixing parameter `t`: `gasI t = I ((1-t) z_0 + t z_1)`. -/
def gasI (t : ℝ) : ℝ := X.Q.I ((1 - t) • X.z 0 + t • X.z 1)

/-- The anchor-0 intercept is `-Q_0` exactly. -/
theorem anchI_zero : X.anchI 0 = - refQuad S 0 := X.i0_eq

end InterceptSpace

end
end CatalanMeasure.GenD.Signed.RouteI.InterceptSource

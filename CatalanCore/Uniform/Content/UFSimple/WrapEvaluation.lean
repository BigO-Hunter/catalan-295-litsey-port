module

public import CatalanCore.Uniform.Content.UFSimple.WrapParameter
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Safe evaluation at a generic prefix Cauchy test point -/

open Polynomial Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapEvaluation

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable (phi : R →+* K) (point : R)

/-- A deformed entry with a clearing denominator that is a unit at the
original parameter value. This relation never includes a generic pivot. -/
def Rel (x : WrapParameter.Extension phi) (x0 : R) : Prop :=
  ∃ f D : R[X], IsUnit (D.eval point) ∧
    algebraMap R[X] (WrapParameter.Extension phi) D*x=
      algebraMap R[X] (WrapParameter.Extension phi) f ∧
    f.eval point=D.eval point*x0

namespace Rel

variable {phi point} {x y : WrapParameter.Extension phi} {x0 y0 : R}

theorem constant (a : R) : Rel phi point (algebraMap R[X] _ (Polynomial.C a)) a := by
  refine ⟨Polynomial.C a,1,by simp,by simp,by simp⟩

theorem zero : Rel phi point 0 0 := by simpa using constant (phi:=phi) (0:R)
theorem one : Rel phi point 1 1 := by simpa using constant (phi:=phi) (1:R)

theorem add (hx : Rel phi point x x0) (hy : Rel phi point y y0) : Rel phi point (x+y) (x0+y0) := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  obtain ⟨g,E,hE,hy,hy0⟩ := hy
  refine ⟨f*E+g*D,D*E,by simpa only [Polynomial.eval_mul] using hD.mul hE,?_,?_⟩
  · simp only [map_mul,map_add]
    calc
      _=algebraMap R[X] _ E*(algebraMap R[X] _ D*x)+
        algebraMap R[X] _ D*(algebraMap R[X] _ E*y) := by ring
      _=_ := by rw [hx,hy]; ring
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,hx0,hy0]
    ring

theorem neg (hx : Rel phi point x x0) : Rel phi point (-x) (-x0) := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  refine ⟨-f,D,hD,?_,?_⟩
  · calc
      _=-(algebraMap R[X] _ D*x) := by ring
      _=_ := by rw [hx,map_neg]
  · rw [Polynomial.eval_neg,hx0,mul_neg]

theorem mul (hx : Rel phi point x x0) (hy : Rel phi point y y0) : Rel phi point (x*y) (x0*y0) := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  obtain ⟨g,E,hE,hy,hy0⟩ := hy
  refine ⟨f*g,D*E,by simpa only [Polynomial.eval_mul] using hD.mul hE,?_,?_⟩
  · simp only [map_mul]
    calc
      _=(algebraMap R[X] _ D*x)*(algebraMap R[X] _ E*y) := by ring
      _=_ := by rw [hx,hy]
  · simp only [Polynomial.eval_mul,hx0,hy0]
    ring


/-- Test scalar divisibility follows after descending the original
cleared numerator. Only its original elementary denominator is canceled. -/
theorem descend (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (hx : Rel phi point x x0) (k : ℕ) (y : WrapParameter.Extension phi)
    (h : x=WrapParameter.uniformizer phi pi^k*y) : pi^k∣x0 := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  have hf : Polynomial.C pi^k∣f := by
    apply WrapParameter.descend phi pi hker hpi f k
      (algebraMap R[X] (WrapParameter.Extension phi) D*y)
    rw [← hx,h]
    ring
  have he : pi^k∣f.eval point := by
    obtain ⟨g,hg⟩ := hf
    refine ⟨g.eval point,?_⟩
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C] using
      congrArg (Polynomial.eval point) hg
  rw [hx0] at he
  obtain ⟨u,hu⟩ := hD
  obtain ⟨z,hz⟩ := he
  refine ⟨↑u⁻¹*z,?_⟩
  calc
    x0=↑u⁻¹*(D.eval point*x0) := by rw [← hu]; simp
    _=pi^k*(↑u⁻¹*z) := by rw [hz]; ring


/-- A nonzero test residue proves a nonzero generic residue. Only the
original elementary clearing denominator must survive this test point;
no generic inverse pivot is evaluated. -/
theorem residue_ne (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (hx : Rel phi point x x0) (hx0 : phi x0≠0) : WrapParameter.residue phi x≠0 := by
  intro hz
  obtain ⟨y,hy⟩ := (WrapParameter.residue_zero_iff phi pi hker x).mp hz
  have hd := descend pi hker hpi hx 1 y (by simpa only [pow_one] using hy)
  apply hx0
  apply (hker x0).mpr
  simpa only [pow_one] using hd

end Rel

/-- Integral deformed values and their test values form a ring. -/
noncomputable def pairedRing : Subring (WrapParameter.Extension phi × R) where
  carrier := {z | Rel phi point z.1 z.2}
  zero_mem' := Rel.zero
  one_mem' := Rel.one
  add_mem' := fun ha hb => Rel.add ha hb
  neg_mem' := fun ha => Rel.neg ha
  mul_mem' := fun ha hb => Rel.mul ha hb

/-- The original scalar determinant inherits the elementary entry
specializations, without any assumption about elimination pivots. -/
theorem determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (WrapParameter.Extension phi)) (Q0 : Matrix ι ι R)
    (h : ∀ i j,Rel phi point (Q i j) (Q0 i j)) : Rel phi point Q.det Q0.det := by
  let M : Matrix ι ι (pairedRing phi point) := fun i j => ⟨(Q i j,Q0 i j),h i j⟩
  let fst : pairedRing phi point →+* WrapParameter.Extension phi :=
    (RingHom.fst _ _).comp (pairedRing phi point).subtype
  let snd : pairedRing phi point →+* R :=
    (RingHom.snd _ _).comp (pairedRing phi point).subtype
  have hfst : M.map fst=Q := rfl
  have hsnd : M.map snd=Q0 := rfl
  have hh : Rel phi point (fst M.det) (snd M.det) := M.det.property
  rw [RingHom.map_det,RingHom.map_det] at hh
  change Rel phi point (M.map fst).det (M.map snd).det at hh
  rwa [hfst,hsnd] at hh

end CatalanCore.Uniform.Content.UFSimple.WrapEvaluation

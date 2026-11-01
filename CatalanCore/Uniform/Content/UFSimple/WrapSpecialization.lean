module

public import CatalanCore.Uniform.Content.UFSimple.WrapParameter
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Specialization of integral deformed entries and scalar determinants -/

open Polynomial Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapSpecialization

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
variable (phi : R →+* K)

/-- A deformed entry with a clearing denominator that is a unit at the
original parameter value. This relation never includes a generic pivot. -/
def Rel (x : WrapParameter.Extension phi) (x0 : R) : Prop :=
  ∃ f D : R[X], IsUnit (D.eval 0) ∧
    algebraMap R[X] (WrapParameter.Extension phi) D*x=
      algebraMap R[X] (WrapParameter.Extension phi) f ∧
    f.eval 0=D.eval 0*x0

namespace Rel

variable {phi} {x y : WrapParameter.Extension phi} {x0 y0 : R}

theorem constant (a : R) : Rel phi (algebraMap R[X] _ (Polynomial.C a)) a := by
  refine ⟨Polynomial.C a,1,by simp,by simp,by simp⟩

theorem zero : Rel phi 0 0 := by simpa using constant (phi:=phi) (0:R)
theorem one : Rel phi 1 1 := by simpa using constant (phi:=phi) (1:R)

theorem add (hx : Rel phi x x0) (hy : Rel phi y y0) : Rel phi (x+y) (x0+y0) := by
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

theorem neg (hx : Rel phi x x0) : Rel phi (-x) (-x0) := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  refine ⟨-f,D,hD,?_,?_⟩
  · calc
      _=-(algebraMap R[X] _ D*x) := by ring
      _=_ := by rw [hx,map_neg]
  · rw [Polynomial.eval_neg,hx0,mul_neg]

theorem mul (hx : Rel phi x x0) (hy : Rel phi y y0) : Rel phi (x*y) (x0*y0) := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  obtain ⟨g,E,hE,hy,hy0⟩ := hy
  refine ⟨f*g,D*E,by simpa only [Polynomial.eval_mul] using hD.mul hE,?_,?_⟩
  · simp only [map_mul]
    calc
      _=(algebraMap R[X] _ D*x)*(algebraMap R[X] _ E*y) := by ring
      _=_ := by rw [hx,hy]
  · simp only [Polynomial.eval_mul,hx0,hy0]
    ring


/-- Original scalar divisibility follows after descending the original
cleared numerator. Only its original elementary denominator is canceled. -/
theorem descend (pi : R) (hker : ∀ a,phi a=0 ↔ pi∣a) (hpi : Prime pi)
    (hx : Rel phi x x0) (k : ℕ) (y : WrapParameter.Extension phi)
    (h : x=WrapParameter.uniformizer phi pi^k*y) : pi^k∣x0 := by
  obtain ⟨f,D,hD,hx,hx0⟩ := hx
  have hf : Polynomial.C pi^k∣f := by
    apply WrapParameter.descend phi pi hker hpi f k
      (algebraMap R[X] (WrapParameter.Extension phi) D*y)
    rw [← hx,h]
    ring
  have he : pi^k∣f.eval 0 := by
    obtain ⟨g,hg⟩ := hf
    refine ⟨g.eval 0,?_⟩
    simpa only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C] using
      congrArg (Polynomial.eval (0:R)) hg
  rw [hx0] at he
  obtain ⟨u,hu⟩ := hD
  obtain ⟨z,hz⟩ := he
  refine ⟨↑u⁻¹*z,?_⟩
  calc
    x0=↑u⁻¹*(D.eval 0*x0) := by rw [← hu]; simp
    _=pi^k*(↑u⁻¹*z) := by rw [hz]; ring

end Rel

/-- Integral deformed values and their original values form a ring. -/
noncomputable def pairedRing : Subring (WrapParameter.Extension phi × R) where
  carrier := {z | Rel phi z.1 z.2}
  zero_mem' := Rel.zero
  one_mem' := Rel.one
  add_mem' := fun ha hb => Rel.add ha hb
  neg_mem' := fun ha => Rel.neg ha
  mul_mem' := fun ha hb => Rel.mul ha hb

/-- The original scalar determinant inherits the elementary entry
specializations, without any assumption about elimination pivots. -/
theorem determinant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (WrapParameter.Extension phi)) (Q0 : Matrix ι ι R)
    (h : ∀ i j,Rel phi (Q i j) (Q0 i j)) : Rel phi Q.det Q0.det := by
  let M : Matrix ι ι (pairedRing phi) := fun i j => ⟨(Q i j,Q0 i j),h i j⟩
  let fst : pairedRing phi →+* WrapParameter.Extension phi :=
    (RingHom.fst _ _).comp (pairedRing phi).subtype
  let snd : pairedRing phi →+* R :=
    (RingHom.snd _ _).comp (pairedRing phi).subtype
  have hfst : M.map fst=Q := rfl
  have hsnd : M.map snd=Q0 := rfl
  have hh : Rel phi (fst M.det) (snd M.det) := M.det.property
  rw [RingHom.map_det,RingHom.map_det] at hh
  change Rel phi (M.map fst).det (M.map snd).det at hh
  rwa [hfst,hsnd] at hh

end CatalanCore.Uniform.Content.UFSimple.WrapSpecialization

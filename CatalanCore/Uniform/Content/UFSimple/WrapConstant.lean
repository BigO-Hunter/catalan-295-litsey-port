module

public import CatalanCore.Uniform.Content.UFSimple.WrapTestPoint

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapConstant

variable (p : ℕ) [Fact p.Prime]

/-- A residue with no dependence on the original spectral variable. -/
def Has (x : GaussLoc p) : Prop := ∃ z:ZMod p,res p x=rfH p z

namespace Has

variable {p} {x y : GaussLoc p}

theorem zero : Has p 0 := ⟨0,by simp⟩
theorem one : Has p 1 := ⟨1,by simp⟩
theorem natCast (n : ℕ) : Has p (n:GaussLoc p) := ⟨n,WrapSimplePole.res_nat p n⟩
theorem add (hx : Has p x) (hy : Has p y) : Has p (x+y) := by
  obtain ⟨a,ha⟩ := hx; obtain ⟨b,hb⟩ := hy
  exact ⟨a+b,by rw [map_add,ha,hb,map_add]⟩
theorem neg (hx : Has p x) : Has p (-x) := by
  obtain ⟨a,ha⟩ := hx
  exact ⟨-a,by rw [map_neg,ha,map_neg]⟩
theorem sub (hx : Has p x) (hy : Has p y) : Has p (x-y) := by
  simpa only [sub_eq_add_neg] using add hx (neg hy)
theorem mul (hx : Has p x) (hy : Has p y) : Has p (x*y) := by
  obtain ⟨a,ha⟩ := hx; obtain ⟨b,hb⟩ := hy
  exact ⟨a*b,by rw [map_mul,ha,hb,map_mul]⟩
theorem inverse (hx : Has p x) (hu : IsUnit x) : Has p (Ring.inverse x) := by
  obtain ⟨a,ha⟩ := hx
  refine ⟨a⁻¹,?_⟩
  rw [res_inverse _ hu,ha,map_inv₀]
theorem sq (hx : Has p x) : Has p (x^2) := by
  simpa only [pow_two] using mul hx hx

theorem sum {ι : Type*} (s : Finset ι) (f : ι → GaussLoc p)
    (h : ∀ i∈s,Has p (f i)) : Has p (∑ i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using (zero (p:=p))
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact add (h i (mem_insert_self _ _)) (ih (fun j hj => h j (mem_insert_of_mem hj)))

end Has

theorem point (q j0 b epsilon : ℕ) (hq : res p (q:GaussLoc p)≠0) :
    Has p (WrapTestPoint.point p q j0 b epsilon) := by
  unfold WrapTestPoint.point
  exact Has.sub (Has.sub (Has.add (Has.natCast b) Has.one) (Has.natCast epsilon))
    (Has.mul (Has.natCast j0) (Has.inverse (Has.natCast q) (isUnit_of_res_ne _ hq)))

theorem normalized (n : ℕ) (h2 : ¬p^2∣n) :
    Has p (WrapPole.originalNormalized p (n:GaussLoc p)) := by
  classical
  by_cases hd : p∣n
  · have hz := (WrapSimplePole.res_nat_zero p n).mpr hd
    rw [WrapPole.originalNormalized,dif_pos hz,WrapPoleResidue.quotient_nat]
    apply Has.inverse (Has.natCast (n/p))
    simpa only [WrapPoleResidue.quotient_nat] using WrapSimplePole.quotient_unit p n h2 hz
  · refine ⟨0,?_⟩
    rw [WrapPoleResidue.original_normalized p n h2,if_neg hd,map_zero]

theorem pole_value (n q : ℕ) (point : GaussLoc p) (hc : Has p point)
    (hpole : ∀ hz : res p (n:GaussLoc p)=0,
      IsUnit (WrapPole.quotient p (n:GaussLoc p) hz+(q:GaussLoc p)*point)) :
    Has p (WrapPoleTest.value p (n:GaussLoc p) (q:GaussLoc p) point) := by
  classical
  by_cases hz : res p (n:GaussLoc p)=0
  · rw [WrapPoleTest.value,dif_pos hz]
    apply Has.inverse
    · rw [WrapPoleResidue.quotient_nat]
      exact Has.add (Has.natCast (n/p)) (Has.mul (Has.natCast q) hc)
    · exact hpole hz
  · refine ⟨0,?_⟩
    rw [WrapPoleTest.value,dif_neg hz,map_mul,res_piL,zero_mul,map_zero]

end CatalanCore.Uniform.Content.UFSimple.WrapConstant

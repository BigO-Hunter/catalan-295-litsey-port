module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapSimplePole
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Exact generic residues of the original deformed pole increments -/

open Polynomial CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapPoleResidue

variable (p : ℕ) [Fact p.Prime]

abbrev Residue := RatFunc (RatFunc (ZMod p))

theorem constant (a : GaussLoc p) :
    WrapDeform.residue p (WrapDeform.embed p (Polynomial.C a))=RatFunc.C (res p a) := by
  unfold WrapDeform.residue WrapDeform.embed
  erw [WrapParameter.residue_map]
  change algebraMap (RatFunc (ZMod p))[X] (Residue p) ((Polynomial.C a).map (res p))=_
  rw [Polynomial.map_C,RatFunc.algebraMap_C]

theorem constant_nat (n : ℕ) :
    WrapDeform.residue p (WrapDeform.embed p (Polynomial.C (n:GaussLoc p)))=(n:Residue p) := by
  rw [constant,WrapSimplePole.res_nat]
  simp only [map_natCast]

theorem affine (a b : GaussLoc p) :
    WrapDeform.residue p (WrapPole.affine p a b)=
      RatFunc.C (res p a)+RatFunc.C (res p b)*(RatFunc.X:Residue p) := by
  unfold WrapPole.affine WrapDeform.residue WrapDeform.embed
  erw [WrapParameter.residue_map]
  change algebraMap (RatFunc (ZMod p))[X] (Residue p)
    ((Polynomial.C a+Polynomial.C b*Polynomial.X).map (res p))=_
  rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,Polynomial.map_X,
    map_add,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_C,RatFunc.algebraMap_X]

theorem inverse (x : WrapDeform.Extension p) (hx : IsUnit x) :
    WrapDeform.residue p (Ring.inverse x)=(WrapDeform.residue p x)⁻¹ := by
  have hh := congrArg (WrapDeform.residue p) (Ring.mul_inverse_cancel x hx)
  rw [map_mul,map_one] at hh
  exact eq_inv_of_mul_eq_one_right hh

/-- The chosen original quotient is the actual integer pole quotient. -/
theorem quotient_nat (n : ℕ) (ha : res p (n:GaussLoc p)=0) :
    WrapPole.quotient p (n:GaussLoc p) ha=((n/p:ℕ):GaussLoc p) := by
  have hd := (WrapSimplePole.res_nat_zero p n).mp ha
  have heNat : n=p*(n/p) := by simpa only [Nat.mul_comm] using (Nat.div_mul_cancel hd).symm
  have he : (n:GaussLoc p)=piL p*((n/p:ℕ):GaussLoc p) := by
    have hh := congrArg (fun z : ℕ => (z:GaussLoc p)) heNat
    simpa only [Nat.cast_mul,WrapSimplePole.pi_eq_natCast] using hh
  apply mul_left_cancel₀ (WrapDeform.pi_prime p).ne_zero
  exact (WrapPole.quotient_spec p (n:GaussLoc p) ha).symm.trans he

theorem original_normalized (n : ℕ) (h2 : ¬p^2∣n) :
    res p (WrapPole.originalNormalized p (n:GaussLoc p))=
      if p∣n then (1:RatFunc (ZMod p))/((n/p:ℕ):RatFunc (ZMod p)) else 0 := by
  classical
  by_cases hd : p∣n
  · have ha := (WrapSimplePole.res_nat_zero p n).mpr hd
    rw [if_pos hd,WrapPole.originalNormalized,dif_pos ha,
      UFMoments.res_inverse _ (WrapSimplePole.quotient_unit p n h2 ha),quotient_nat,WrapSimplePole.res_nat]
    simp only [map_natCast,one_div]
  · have ha : res p (n:GaussLoc p)≠0 := fun hz => hd ((WrapSimplePole.res_nat_zero p n).mp hz)
    rw [if_neg hd,WrapPole.originalNormalized,dif_neg ha,map_mul,res_piL,zero_mul]

theorem pure_constant (n : ℕ) (h2 : ¬p^2∣n) :
    WrapDeform.residue p (WrapDeform.embed p (Polynomial.C (WrapPole.originalNormalized p (n:GaussLoc p))))=
      if p∣n then (1:Residue p)/((n/p:ℕ):Residue p) else 0 := by
  rw [constant,original_normalized p n h2]
  by_cases hd : p∣n <;> simp only [hd,↓reduceIte,map_div₀,map_one,map_natCast,map_zero]

/-- Every deformed fractional pole has its actual quotient-plus-qY
residue. Original nonpoles vanish after normalization. -/
theorem normalized_nat (n q : ℕ) (hq : res p (q:GaussLoc p)≠0) :
    WrapDeform.residue p (WrapPole.normalizedInverse p (n:GaussLoc p) (q:GaussLoc p))=
      if p∣n then (1:Residue p)/(((n/p:ℕ):Residue p)+(q:Residue p)*RatFunc.X) else 0 := by
  classical
  by_cases hd : p∣n
  · have ha := (WrapSimplePole.res_nat_zero p n).mpr hd
    rw [if_pos hd,WrapPole.normalizedInverse,dif_pos ha,
      inverse _ _ (WrapPole.affine_unit p _ _ hq),affine,quotient_nat,WrapSimplePole.res_nat,
      WrapSimplePole.res_nat]
    simp only [map_natCast,one_div]
  · rw [if_neg hd]
    exact WrapPole.normalized_nonpole_residue p _ _
      (fun hz => hd ((WrapSimplePole.res_nat_zero p n).mp hz))

/-- Exact residue of the actual integral normalized two-term increment. -/
theorem delta (q o t : ℕ) (hq : res p (q:GaussLoc p)≠0)
    (hle : o≤q*t) (ht2 : ¬p^2∣t) :
    WrapDeform.residue p (WrapIncrement.delta p q o t)=
      (if p∣t then (1:Residue p)/((t/p:ℕ):Residue p) else 0)-
      (q:Residue p)*(if p∣q*t-o then (1:Residue p)/((((q*t-o)/p:ℕ):Residue p)+
        (q:Residue p)*RatFunc.X) else 0) := by
  rw [WrapIncrement.delta,map_sub,map_mul,pure_constant p t ht2,constant_nat,
    WrapSimplePole.argument_nat p q o t hle,normalized_nat p (q*t-o) q hq]

end CatalanCore.Uniform.Content.UFSimple.WrapPoleResidue

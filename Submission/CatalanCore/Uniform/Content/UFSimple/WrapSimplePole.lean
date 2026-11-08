module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapIncrement
public import Submission.CatalanCore.Uniform.Content.UFMoments.NodeLoc

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Original single-level arithmetic discharges all elementary units -/

open Polynomial CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapSimplePole

variable (p : ℕ) [Fact p.Prime]

theorem pi_eq_natCast : piL p=(p:GaussLoc p) := by simp only [piL,map_natCast]

theorem res_nat (n : ℕ) : res p (n:GaussLoc p)=rfH p (n:ZMod p) := by
  simp only [map_natCast]

theorem res_nat_zero (n : ℕ) : res p (n:GaussLoc p)=0 ↔ p∣n := by
  rw [res_nat]
  constructor
  · intro hz
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    apply rfH_injective
    simpa only [map_zero] using hz
  · intro hd
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd,map_zero]

theorem natural_unit (n : ℕ) (hn : ¬p∣n) : IsUnit (n:GaussLoc p) := by
  apply isUnit_of_res_ne
  exact fun hz => hn ((res_nat_zero p n).mp hz)

/-- A simple original pole has an original unit quotient after dividing
by pi. This is independent of every generic elimination pivot. -/
theorem quotient_unit (n : ℕ) (h2 : ¬p^2∣n) (ha : res p (n:GaussLoc p)=0) :
    IsUnit (WrapPole.quotient p (n:GaussLoc p) ha) := by
  obtain ⟨k,hk⟩ := (res_nat_zero p n).mp ha
  have hnk : ¬p∣k := by
    intro hd
    apply h2
    rw [hk,pow_two]
    exact Nat.mul_dvd_mul_left p hd
  have hu := natural_unit p k hnk
  have he : (n:GaussLoc p)=piL p*(k:GaussLoc p) := by
    rw [hk,Nat.cast_mul,pi_eq_natCast]
  have hquot : WrapPole.quotient p (n:GaussLoc p) ha=(k:GaussLoc p) := by
    apply mul_left_cancel₀ (WrapDeform.pi_prime p).ne_zero
    exact (WrapPole.quotient_spec p (n:GaussLoc p) ha).symm.trans he
  rwa [hquot]

theorem argument_nat (q o t : ℕ) (hle : o≤q*t) :
    WrapIncrement.argument p q o t=((q*t-o:ℕ):GaussLoc p) := by
  unfold WrapIncrement.argument
  rw [Nat.cast_sub hle,Nat.cast_mul]

theorem argument_quotient_unit (q o t : ℕ) (hle : o≤q*t) (h2 : ¬p^2∣q*t-o)
    (ha : res p (WrapIncrement.argument p q o t)=0) :
    IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) ha) := by
  have he := argument_nat p q o t hle
  have hh : res p ((q*t-o:ℕ):GaussLoc p)=0 := by rw [← he]; exact ha
  have hu := quotient_unit p (q*t-o) h2 hh
  simpa only [he] using hu

theorem q_res_ne (q : ℕ) (hq0 : 0<q) (hqp : q<p) : res p (q:GaussLoc p)≠0 := by
  intro hz
  have hd := (res_nat_zero p q).mp hz
  have hh := Nat.le_of_dvd hq0 hd
  omega

/-- Actual two-term increments specialize under the original arithmetic
hypotheses alone; all elementary unit suppliers are discharged. -/
theorem delta_specializes (q o t : ℕ) (hq0 : 0<q) (hqp : q<p)
    (hle : o≤q*t) (h2 : ¬p^2∣q*t-o) :
    WrapPole.Specializes p (WrapIncrement.delta p q o t) (WrapIncrement.originalDelta p q o t) :=
  WrapIncrement.delta_specializes p q o t (q_res_ne p q hq0 hqp)
    (fun ha => argument_quotient_unit p q o t hle h2 ha)
    (fun h => isUnit_of_res_ne _ h)

theorem dsq_specializes (q o t : ℕ) (hq0 : 0<q) (hqp : q<p)
    (hle : o≤q*t) (h2 : ¬p^2∣q*t-o) :
    WrapPole.Specializes p (WrapIncrement.dsq p q o t) (WrapIncrement.originalDsq p q o t) :=
  WrapIncrement.dsq_specializes p q o t (q_res_ne p q hq0 hqp)
    (fun ha => argument_quotient_unit p q o t hle h2 ha)
    (fun h => isUnit_of_res_ne _ h)

end CatalanCore.Uniform.Content.UFSimple.WrapSimplePole

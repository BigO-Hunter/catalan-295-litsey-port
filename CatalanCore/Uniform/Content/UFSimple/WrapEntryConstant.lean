module

public import CatalanCore.Uniform.Content.UFSimple.WrapConstant
public import CatalanCore.Uniform.Content.UFSimple.WrapEntryTest
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapEntryConstant

variable (p : ℕ) [Fact p.Prime]

open WrapConstant

theorem delta (q o t : ℕ) (point : GaussLoc p) (hc : Has p point)
    (hle : o≤q*t) (ht2 : ¬p^2∣t)
    (hpole : ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point)) :
    Has p (WrapIncrementTest.testDelta p q o t point) := by
  unfold WrapIncrementTest.testDelta
  apply Has.sub (WrapConstant.normalized p t ht2)
  apply Has.mul (Has.natCast q)
  have he := WrapSimplePole.argument_nat p q o t hle
  have hu : ∀ hz : res p ((q*t-o:ℕ):GaussLoc p)=0,
      IsUnit (WrapPole.quotient p ((q*t-o:ℕ):GaussLoc p) hz+(q:GaussLoc p)*point) := by
    simpa only [he] using hpole
  simpa only [he] using WrapConstant.pole_value p (q*t-o) q point hc hu

theorem dsq (q o t : ℕ) (point : GaussLoc p) (hc : Has p point)
    (hle : o≤q*t) (ht2 : ¬p^2∣t)
    (hpole : ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point)) :
    Has p (WrapIncrementTest.testDsq p q o t point) := by
  unfold WrapIncrementTest.testDsq
  apply Has.sub (Has.sq (WrapConstant.normalized p t ht2))
  apply Has.mul (Has.sq (Has.natCast q))
  apply Has.sq
  have he := WrapSimplePole.argument_nat p q o t hle
  have hu : ∀ hz : res p ((q*t-o:ℕ):GaussLoc p)=0,
      IsUnit (WrapPole.quotient p ((q*t-o:ℕ):GaussLoc p) hz+(q:GaussLoc p)*point) := by
    simpa only [he] using hpole
  simpa only [he] using WrapConstant.pole_value p (q*t-o) q point hc hu

/-- Test entries have constant prime-field residues; the only spectral
variable in an own core is its original common-node diagonal. -/
theorem entry (q o N : ℕ) (point u : GaussLoc p) (hc : Has p point) (hu : Has p u)
    (hoq : o<q) (hN : N<p*p)
    (hpole : ∀ t,1≤t → t<N → ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point))
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    Has p (WrapEntryTest.value p q o point u a b) := by
  classical
  by_cases hab : a=b
  · rw [WrapEntryTest.value,if_pos hab]
    apply Has.neg
    apply Has.mul hu
    apply Has.sum
    intro t ht
    have ht1 := (mem_Icc.mp ht).1
    have htN : t<N := lt_of_le_of_lt (mem_Icc.mp ht).2 ha
    have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
    exact dsq p q o t point hc hle (Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN))
      (hpole t ht1 htN)
  · rw [WrapEntryTest.value,if_neg hab]
    apply Has.mul
    · apply Has.mul hu
      apply WrapConstant.normalized
      have hwidth : 1≤max a b-min a b := by omega
      have hsmall : max a b-min a b<N := by have := max_lt ha hb; omega
      exact Smith.not_sq_dvd_of_lt hwidth (lt_trans hsmall hN)
    · apply Has.sum
      intro t ht
      have ht1 : 1≤t := by have := (mem_Ioc.mp ht).1; omega
      have htN : t<N := lt_of_le_of_lt (mem_Ioc.mp ht).2 (max_lt ha hb)
      have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
      exact delta p q o t point hc hle (Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN))
        (hpole t ht1 htN)

end CatalanCore.Uniform.Content.UFSimple.WrapEntryConstant

module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapOwnTest
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPoleResidue
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPoleLoad
public import Submission.CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapLoadTest

variable (p : ℕ) [Fact p.Prime]

theorem value_nat (n q : ℕ) (point : GaussLoc p)
    (hpole : ∀ hz : res p (n:GaussLoc p)=0,
      IsUnit (WrapPole.quotient p (n:GaussLoc p) hz+(q:GaussLoc p)*point)) :
    res p (WrapPoleTest.value p (n:GaussLoc p) (q:GaussLoc p) point)=
      if p∣n then (1:RatFunc (ZMod p))/
        (((n/p:ℕ):RatFunc (ZMod p))+(q:RatFunc (ZMod p))*res p point) else 0 := by
  classical
  by_cases hd : p∣n
  · have hz := (WrapSimplePole.res_nat_zero p n).mpr hd
    rw [if_pos hd,WrapPoleTest.value,dif_pos hz,res_inverse _ (hpole hz),
      map_add,map_mul,WrapPoleResidue.quotient_nat]
    simp only [map_natCast,one_div]
  · have hz : res p (n:GaussLoc p)≠0 := fun h => hd ((WrapSimplePole.res_nat_zero p n).mp h)
    rw [if_neg hd,WrapPoleTest.value,dif_neg hz,map_mul,res_piL,zero_mul]

theorem delta (q o t : ℕ) (point : GaussLoc p) (hle : o≤q*t) (ht2 : ¬p^2∣t)
    (hpole : ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point)) :
    res p (WrapIncrementTest.testDelta p q o t point)=
      (if p∣t then (1:RatFunc (ZMod p))/((t/p:ℕ):RatFunc (ZMod p)) else 0)-
      (q:RatFunc (ZMod p))*(if p∣q*t-o then (1:RatFunc (ZMod p))/
        ((((q*t-o)/p:ℕ):RatFunc (ZMod p))+(q:RatFunc (ZMod p))*res p point) else 0) := by
  have he := WrapSimplePole.argument_nat p q o t hle
  have hu : ∀ hz : res p ((q*t-o:ℕ):GaussLoc p)=0,
      IsUnit (WrapPole.quotient p ((q*t-o:ℕ):GaussLoc p) hz+(q:GaussLoc p)*point) := by
    simpa only [he] using hpole
  rw [WrapIncrementTest.testDelta,map_sub,map_mul,WrapPoleResidue.original_normalized p t ht2,
    he,value_nat p (q*t-o) q point hu,map_natCast]

/-- Exact residue of the actual cumulative test load. -/
theorem load_residue (q o k j0 gamma j N : ℕ) (point : GaussLoc p)
    (hq0 : 0<q) (hqp : q<p) (hoq : o<q) (hk0 : 0<k) (hk : k≤p)
    (hg : gamma<p) (hroot : q*k=j0*p+o) (hN : N<p*p) (hnode : gamma+j*p<N)
    (hpole : ∀ t,1≤t → t≤gamma+j*p → ∀ hz : res p (WrapIncrement.argument p q o t)=0,
      IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+(q:GaussLoc p)*point)) :
    res p (∑ t∈Icc 1 (gamma+j*p),WrapIncrementTest.testDelta p q o t point)=
      WrapHarmonic.load ((j0:RatFunc (ZMod p))/(q:RatFunc (ZMod p))+res p point)
        (decide (k≤gamma)) j := by
  have hp := (Fact.out : p.Prime).pos
  have hqb := WrapSimplePole.q_res_ne p q hq0 hqp
  have hqf : (q:ZMod p)≠0 := by
    intro hz
    apply hqb
    exact (WrapSimplePole.res_nat_zero p q).mpr ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hqr : (q:RatFunc (ZMod p))≠0 := by simpa only [map_natCast] using hqb
  have hh : res p (∑ t∈Icc 1 (gamma+j*p),WrapIncrementTest.testDelta p q o t point)=
      WrapPoleLoad.pure p (gamma+j*p)-WrapPoleLoad.fractional p q o k
        (res p point) (gamma+j*p) := by
    rw [map_sum]
    unfold WrapPoleLoad.pure WrapPoleLoad.fractional
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht1 := (Finset.mem_Icc.mp ht).1
    have htend := (Finset.mem_Icc.mp ht).2
    have htN : t<N := lt_of_le_of_lt htend hnode
    have ht2 : ¬p^2∣t := Smith.not_sq_dvd_of_lt ht1 (lt_trans htN hN)
    have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
    rw [delta p q o t point hle ht2 (hpole t ht1 htend)]
    have hiff := WrapPoleLoad.fractional_pole_iff p q o k j0 t hoq ht1 hroot hqf
    by_cases hd : p∣q*t-o
    · rw [if_pos hd,if_pos (hiff.mp hd)]
      simp only [one_div,div_eq_mul_inv,one_mul]
    · rw [if_neg hd,if_neg (fun h => hd (hiff.mpr h)),mul_zero]
  exact hh.trans (WrapPoleLoad.load_eq p q o k j0 gamma j (res p point) hp hk0 hk hg hroot hqr)

/-- The actual own-fibre test load is the integer Cauchy potential. -/
theorem own_load (q o k j0 gamma j m N b : ℕ)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p) (hroot : q*k=j0*p+o)
    (hsize : 2*m≤N) (hN : q*N<p*p) (hnode : gamma+j*p<N)
    (hb : b≤m/p+1) (hb0 : 1≤b) :
    res p (∑ t∈Icc 1 (gamma+j*p),WrapIncrementTest.testDelta p q o t
      (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)))=
      WrapHarmonic.potential b (0:RatFunc (ZMod p))-
        WrapHarmonic.potential b (j:RatFunc (ZMod p))-
          (if k≤gamma then 1/(b:RatFunc (ZMod p)) else 0) := by
  classical
  have hsingle : N<p*p := lt_of_le_of_lt (Nat.le_mul_of_pos_left N hq0) hN
  have hrel := load_residue p q o k j0 gamma j N
    (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0))
    hq0 hqp hoq hk0 hk hg hroot hsingle hnode
    (fun t ht1 ht hz => WrapOwnTest.pole_unit_before p q o k j0 gamma j m N b t
      hq0 hqp hq2 hoq hk0 hk hg hroot hsize hN hnode hb hb0 ht1 ht hz)
  have hpnt := WrapTestPoint.point_residue p q j0 b (if k≤gamma then 1 else 0)
    (WrapSimplePole.q_res_ne p q hq0 hqp)
  have he : (j0:RatFunc (ZMod p))/(q:RatFunc (ZMod p))+
      res p (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0))=
      WrapHarmonic.testShift b (decide (k≤gamma)) := by
    rw [hpnt]
    unfold WrapHarmonic.testShift
    by_cases hkg : k≤gamma <;> simp [hkg] <;> ring
  rw [he,WrapHarmonic.load_test] at hrel
  simpa only [Bool.decide_iff] using hrel

end CatalanCore.Uniform.Content.UFSimple.WrapLoadTest

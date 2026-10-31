module

public import CatalanCore.Uniform.Content.UFSimple.WrapTestPoint
public import CatalanCore.Uniform.Content.UFSimple.WrapEntryTest

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapOwnTest

variable (p : ℕ) [Fact p.Prime]

/-- All elementary denominators required by one own-colour core and
its virtual reference survive its actual Cauchy test. -/
theorem pole_unit_before (q o k j0 gamma j m N b t : ℕ)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p) (hroot : q*k=j0*p+o)
    (hsize : 2*m≤N) (hN : q*N<p*p) (hnode : gamma+j*p<N)
    (hb : b≤m/p+1) (hb0 : 1≤b) (ht1 : 1≤t) (ht : t≤gamma+j*p)
    (hz : res p (WrapIncrement.argument p q o t)=0) :
    IsUnit (WrapPole.quotient p (WrapIncrement.argument p q o t) hz+
      (q:GaussLoc p)*WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)) := by
  classical
  have hp := (Fact.out : p.Prime).pos
  have hle : o≤q*t := by have := Nat.le_mul_of_pos_right q ht1; omega
  have he := WrapSimplePole.argument_nat p q o t hle
  have hzn : res p ((q*t-o:ℕ):GaussLoc p)=0 := by rw [← he]; exact hz
  have hd := (WrapSimplePole.res_nat_zero p (q*t-o)).mp hzn
  have hqf : (q:ZMod p)≠0 := by
    intro hzq
    have := (ZMod.natCast_eq_zero_iff _ _).mp hzq
    have := Nat.le_of_dvd hq0 this
    omega
  have hc := (WrapPoleLoad.fractional_pole_iff p q o k j0 t hoq ht1 hroot hqf).mp hd
  have hmem : t∈(Icc 1 (gamma+j*p)).filter (fun a => a%p=k%p) := by
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ht1,ht⟩,hc⟩
  rw [WrapPoleCount.filter_eq_image p k gamma j hp hk0 hk hg] at hmem
  obtain ⟨h,hh,hth⟩ := mem_image.mp hmem
  have hcount := mem_range.mp hh
  have hj : j≤(gamma+j*p)/p := by
    rw [Nat.add_mul_div_right _ _ hp]
    exact Nat.le_add_left j (gamma/p)
  have heps : (if k≤gamma then 1 else 0 : ℕ)≤1 := by split_ifs <;> omega
  have hu := WrapTestPoint.pole_unit p q o k j0 m N (gamma+j*p) b j
    (if k≤gamma then 1 else 0) h hq0 hqp hq2 hroot hsize hN hnode hb hb0 hj heps
    (by simpa only [WrapPoleCount.count] using hcount)
    (by simpa only [hth] using hzn)
  simpa only [hth,he] using hu

/-- Actual deformed entries on this own fibre can be tested without
assuming any elementary denominator units or any generic pivot units. -/
theorem entry_at (q o k j0 gamma j m N b : ℕ)
    (hq0 : 0<q) (hqp : q<p) (hq2 : 2≤q) (hoq : o<q)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p) (hroot : q*k=j0*p+o)
    (hsize : 2*m≤N) (hN : q*N<p*p) (hnode : gamma+j*p<N)
    (hb : b≤m/p+1) (hb0 : 1≤b)
    (u : GaussLoc p) (a c : ℕ) (ha : a≤gamma+j*p) (hc : c≤gamma+j*p) :
    WrapPoleTest.At p (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0))
      (WrapDeformedEntry.entry p q o u a c)
      (WrapEntryTest.value p q o (WrapTestPoint.point p q j0 b (if k≤gamma then 1 else 0)) u a c) := by
  apply WrapEntryTest.at_point p q o (gamma+j*p+1) _
    (WrapSimplePole.q_res_ne p q hq0 hqp) _ u a c (by omega) (by omega)
  intro t ht1 ht hz
  exact pole_unit_before p q o k j0 gamma j m N b t hq0 hqp hq2 hoq
    hk0 hk hg hroot hsize hN hnode hb hb0 ht1 (by omega) hz

end CatalanCore.Uniform.Content.UFSimple.WrapOwnTest

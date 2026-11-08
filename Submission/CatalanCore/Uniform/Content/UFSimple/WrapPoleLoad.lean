module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPoleCount
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapHarmonic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Original pole sums equal the harmonic prefix load -/

open Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapPoleLoad

variable {K : Type*} [Field K]

noncomputable def pure (p t : ℕ) : K :=
  ∑ a∈Icc 1 t,if p∣a then (1:K)/((a/p:ℕ):K) else 0
noncomputable def fractional (p q o k : ℕ) (Y : K) (t : ℕ) : K :=
  ∑ a∈Icc 1 t,if a%p=k%p then (q:K)/((((q*a-o)/p:ℕ):K)+(q:K)*Y) else 0

theorem pure_eq (p gamma j : ℕ) (hp : 0<p) (hg : gamma<p) :
    pure (K:=K) p (gamma+j*p)=∑ h∈range j,(1:K)/(1+(h:K)) := by
  have hh := WrapPoleCount.sum_class (fun a => (1:K)/((a/p:ℕ):K))
    p p gamma j hp hp le_rfl hg
  simp only [WrapPoleCount.count,if_neg (not_le.mpr hg),Nat.add_zero,Nat.mod_self] at hh
  unfold pure
  simp only [Nat.dvd_iff_mod_eq_zero]
  rw [hh]
  apply Finset.sum_congr rfl; intro h _
  rw [Nat.add_mul_div_right _ _ hp,Nat.div_self hp]
  simp only [Nat.cast_add,Nat.cast_one]

theorem fractional_quotient (p q o k j0 h : ℕ) (hp : 0<p)
    (hroot : q*k=j0*p+o) : (q*(k+h*p)-o)/p=j0+q*h := by
  have he : q*(k+h*p)=(j0+q*h)*p+o := by nlinarith [hroot]
  have hge : o≤q*(k+h*p) := by omega
  have hs : q*(k+h*p)-o=(j0+q*h)*p := (Nat.sub_eq_iff_eq_add hge).mpr he
  rw [hs,Nat.mul_div_cancel _ hp]

theorem q_div (q j0 h : ℕ) (Y : K) (hq : (q:K)≠0) :
    (q:K)/(((j0+q*h:ℕ):K)+(q:K)*Y)=(1:K)/((j0:K)/(q:K)+Y+(h:K)) := by
  have hd : ((j0+q*h:ℕ):K)+(q:K)*Y=(q:K)*((j0:K)/(q:K)+Y+(h:K)) := by
    push_cast
    field_simp [hq]
    <;> ring
  rw [hd,div_eq_mul_inv,mul_inv_rev,one_div]
  calc
    _=((q:K)*(q:K)⁻¹)*((j0:K)/(q:K)+Y+(h:K))⁻¹ := by ring
    _=_ := by rw [mul_inv_cancel₀ hq,one_mul]

/-- The original fractional pole quotient retains every full period. -/
theorem fractional_eq (p q o k j0 gamma j : ℕ) (Y : K) (hp : 0<p)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p)
    (hroot : q*k=j0*p+o) (hq : (q:K)≠0) :
    fractional p q o k Y (gamma+j*p)=
      ∑ h∈range (WrapPoleCount.count k gamma j),(1:K)/((j0:K)/(q:K)+Y+(h:K)) := by
  unfold fractional
  rw [WrapPoleCount.sum_class _ p k gamma j hp hk0 hk hg]
  apply Finset.sum_congr rfl; intro h _
  rw [fractional_quotient p q o k j0 h hp hroot]
  exact q_div q j0 h Y hq

/-- Identify the raw integer-index pole sums with the actual harmonic
load at the node gamma+j*p. -/
theorem load_eq (p q o k j0 gamma j : ℕ) (Y : K) (hp : 0<p)
    (hk0 : 0<k) (hk : k≤p) (hg : gamma<p)
    (hroot : q*k=j0*p+o) (hq : (q:K)≠0) :
    pure p (gamma+j*p)-fractional p q o k Y (gamma+j*p)=
      WrapHarmonic.load ((j0:K)/(q:K)+Y) (decide (k≤gamma)) j := by
  rw [pure_eq p gamma j hp hg,fractional_eq p q o k j0 gamma j Y hp hk0 hk hg hroot hq]
  unfold WrapHarmonic.load WrapPoleCount.count
  simp

/-- The fractional class mask is exactly the original arithmetic pole
condition; no additional exceptional prime is introduced. -/
theorem fractional_pole_iff (p q o k j0 t : ℕ) [Fact p.Prime]
    (hoq : o<q) (ht : 1≤t) (hroot : q*k=j0*p+o) (hq : (q:ZMod p)≠0) :
    p∣q*t-o ↔ t%p=k%p := by
  have hge : o≤q*t := by have hh := Nat.le_mul_of_pos_right q ht; omega
  have hkt : (q:ZMod p)*(k:ZMod p)=(o:ZMod p) := by
    have hh := congrArg (fun a : ℕ => (a:ZMod p)) hroot
    simpa only [Nat.cast_mul,Nat.cast_add,ZMod.natCast_self,mul_zero,zero_add] using hh
  constructor
  · intro hd
    have hz : ((q*t-o:ℕ):ZMod p)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    rw [Nat.cast_sub hge,Nat.cast_mul,← hkt] at hz
    have he : (t:ZMod p)=(k:ZMod p) := mul_left_cancel₀ hq (sub_eq_zero.mp hz)
    exact (ZMod.natCast_eq_natCast_iff' t k p).mp he
  · intro he
    have hz : (t:ZMod p)=(k:ZMod p) := (ZMod.natCast_eq_natCast_iff' t k p).mpr he
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hge,Nat.cast_mul,hz,hkt,sub_self]

end CatalanCore.Uniform.Content.UFSimple.WrapPoleLoad

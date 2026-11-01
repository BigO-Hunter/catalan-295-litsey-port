module

public import CatalanCore.Uniform.Content.UFSimple.WrapOriginalIncrement
public import CatalanCore.Uniform.Content.UFSimple.WrapDeformedEntry
public import CatalanCore.Uniform.Content.UFSimple.WrapParameterLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Exact original-node displacement of integral deformed entries -/

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapEntryRelation

variable (p : ℕ) [Fact p.Prime]

noncomputable def constants := (WrapDeform.embed p).comp
  (Polynomial.C:GaussLoc p →+* (GaussLoc p)[X])
noncomputable def load (q o t : ℕ) : WrapDeform.Extension p :=
  ∑ k∈Icc 1 t,WrapIncrement.delta p q o k

theorem uniformizer_cast : (p:WrapDeform.Extension p)=WrapDeform.uniformizer p := by
  change (p:WrapDeform.Extension p)=constants p (piL p)
  rw [WrapSimplePole.pi_eq_natCast,map_natCast]

theorem factor (w : ℕ) (h2 : ¬p^2∣w) :
    (w:WrapDeform.Extension p)*constants p (WrapPole.originalNormalized p (w:GaussLoc p))=
      WrapDeform.uniformizer p := by
  have ho := WrapIncrement.original_mul_normalized p (w:GaussLoc p)
    (fun ha => WrapSimplePole.quotient_unit p w h2 ha) (fun h => isUnit_of_res_ne _ h)
  rw [WrapSimplePole.pi_eq_natCast] at ho
  have hh := congrArg (constants p) ho
  rw [← uniformizer_cast p]
  simpa only [map_mul,map_natCast] using hh

theorem prefix_sub (q o a b : ℕ) (hab : a≤b) :
    load p q o b-load p q o a=∑ k∈Ioc a b,WrapIncrement.delta p q o k := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold load
  rw [he,he,← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem entry_symm (q o : ℕ) (u : GaussLoc p) (a b : ℕ) :
    WrapDeformedEntry.entry p q o u a b=WrapDeformedEntry.entry p q o u b a := by
  classical
  by_cases hab : a=b
  · subst b; rfl
  · simp only [WrapDeformedEntry.entry,hab,(Ne.symm hab),↓reduceIte,min_comm a b,max_comm a b]

theorem commutator_of_lt (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (hab : a<b) (hb : b<N) :
    ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*WrapDeformedEntry.entry p q o u a b=
      WrapDeform.uniformizer p*(constants p u*(load p q o b-load p q o a)) := by
  have hw2 : ¬p^2∣b-a := Smith.not_sq_dvd_of_lt (by omega) (by omega)
  rw [WrapDeformedEntry.entry,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le,
    ← prefix_sub p q o a b hab.le]
  rw [← Nat.cast_sub hab.le]
  change ((b-a:ℕ):WrapDeform.Extension p)*
    (constants p u*constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*
      (load p q o b-load p q o a))=_
  calc
    _=(((b-a:ℕ):WrapDeform.Extension p)*
      constants p (WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p)))*
        (constants p u*(load p q o b-load p q o a)) := by ring
    _=_ := by rw [factor p (b-a) hw2]

/-- Actual two-term displacement in the generic parameter ring. -/
theorem commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    ((b:WrapDeform.Extension p)-(a:WrapDeform.Extension p))*WrapDeformedEntry.entry p q o u a b=
      WrapDeform.uniformizer p*(constants p u*(load p q o b-load p q o a)) := by
  rcases lt_trichotomy a b with hab|hab|hba
  · exact commutator_of_lt p q o N u hN a b hab hb
  · subst b; simp
  · have hh := commutator_of_lt p q o N u hN b a hba ha
    rw [entry_symm p q o u b a] at hh
    linear_combination -hh

/-- Cancel pi on an actual own-colour fibre. Its coordinates are the
original quotient nodes; independent row/column nodes are retained. -/
theorem divided_commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) (hcol : (a:ZMod p)=(b:ZMod p)) :
    (((b/p:ℕ):WrapDeform.Extension p)-((a/p:ℕ):WrapDeform.Extension p))*
      WrapDeformedEntry.entry p q o u a b=
        constants p u*(load p q o b-load p q o a) := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp hcol
  have hpa := Nat.mod_add_div a p
  have hpb := Nat.mod_add_div b p
  have hn : b+p*(a/p)=a+p*(b/p) := by omega
  have hh := congrArg (fun n : ℕ => (n:WrapDeform.Extension p)) hn
  push_cast at hh
  have hc : (b:WrapDeform.Extension p)-(a:WrapDeform.Extension p)=
      WrapDeform.uniformizer p*(((b/p:ℕ):WrapDeform.Extension p)-((a/p:ℕ):WrapDeform.Extension p)) := by
    rw [← uniformizer_cast]
    linear_combination hh
  have hpi := WrapParameterLift.uniformizer_prime (R:=GaussLoc p) (K:=RatFunc (ZMod p))
    (res p) (piL p) (res_eq_zero_iff p) (WrapDeform.pi_prime p)
  have hpne : WrapDeform.uniformizer p ≠ 0 := hpi.ne_zero
  apply mul_left_cancel₀ hpne
  have hr := commutator p q o N u hN a b ha hb
  rw [hc] at hr
  simpa only [mul_assoc] using hr

end CatalanCore.Uniform.Content.UFSimple.WrapEntryRelation

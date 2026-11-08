module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapOriginalIncrement
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapEntryTest
public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapParameterLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Exact original-node displacement of integral deformed entries -/

open Polynomial Finset CatalanCore.Uniform.Content.UFMoments

namespace CatalanCore.Uniform.Content.UFSimple.WrapTestEntryRelation

variable (p : ℕ) [Fact p.Prime]

variable (point : GaussLoc p)

noncomputable def load (q o t : ℕ) : GaussLoc p :=
  ∑ k∈Icc 1 t,WrapIncrementTest.testDelta p q o k point

theorem factor (w : ℕ) (h2 : ¬p^2∣w) :
    (w:GaussLoc p)*WrapPole.originalNormalized p (w:GaussLoc p)=piL p :=
  WrapIncrement.original_mul_normalized p (w:GaussLoc p)
    (fun ha => WrapSimplePole.quotient_unit p w h2 ha) (fun h => isUnit_of_res_ne _ h)

theorem prefix_sub (q o a b : ℕ) (hab : a≤b) :
    load p point q o b-load p point q o a=∑ k∈Ioc a b,WrapIncrementTest.testDelta p q o k point := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold load
  rw [he,he,← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem entry_symm (q o : ℕ) (u : GaussLoc p) (a b : ℕ) :
    WrapEntryTest.value p q o point u a b=WrapEntryTest.value p q o point u b a := by
  classical
  by_cases hab : a=b
  · subst b; rfl
  · simp only [WrapEntryTest.value,hab,(Ne.symm hab),↓reduceIte,min_comm a b,max_comm a b]

theorem commutator_of_lt (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (hab : a<b) (hb : b<N) :
    ((b:GaussLoc p)-(a:GaussLoc p))*WrapEntryTest.value p q o point u a b=
      piL p*(u*(load p point q o b-load p point q o a)) := by
  have hw2 : ¬p^2∣b-a := Smith.not_sq_dvd_of_lt (by omega) (by omega)
  rw [WrapEntryTest.value,if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le,
    ← prefix_sub p point q o a b hab.le]
  rw [← Nat.cast_sub hab.le]
  change ((b-a:ℕ):GaussLoc p)*
    (u*WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p)*
      (load p point q o b-load p point q o a))=_
  calc
    _=(((b-a:ℕ):GaussLoc p)*
      WrapPole.originalNormalized p ((b-a:ℕ):GaussLoc p))*
        (u*(load p point q o b-load p point q o a)) := by ring
    _=_ := by rw [factor p (b-a) hw2]

/-- Actual two-term displacement in the generic parameter ring. -/
theorem commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) :
    ((b:GaussLoc p)-(a:GaussLoc p))*WrapEntryTest.value p q o point u a b=
      piL p*(u*(load p point q o b-load p point q o a)) := by
  rcases lt_trichotomy a b with hab|hab|hba
  · exact commutator_of_lt p point q o N u hN a b hab hb
  · subst b; simp
  · have hh := commutator_of_lt p point q o N u hN b a hba ha
    rw [entry_symm p point q o u b a] at hh
    calc
      _=-(((a:GaussLoc p)-(b:GaussLoc p))*WrapEntryTest.value p q o point u a b) := by ring
      _=-(piL p*(u*(load p point q o a-load p point q o b))) := congrArg Neg.neg hh
      _=_ := by ring

/-- Cancel pi on an actual own-colour fibre. Its coordinates are the
original quotient nodes; independent row/column nodes are retained. -/
theorem divided_commutator (q o N : ℕ) (u : GaussLoc p) (hN : N<p*p)
    (a b : ℕ) (ha : a<N) (hb : b<N) (hcol : (a:ZMod p)=(b:ZMod p)) :
    (((b/p:ℕ):GaussLoc p)-((a/p:ℕ):GaussLoc p))*
      WrapEntryTest.value p q o point u a b=
        u*(load p point q o b-load p point q o a) := by
  have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp hcol
  have hpa := Nat.mod_add_div a p
  have hpb := Nat.mod_add_div b p
  have hn : b+p*(a/p)=a+p*(b/p) := by omega
  have hh := congrArg (fun n : ℕ => (n:GaussLoc p)) hn
  push_cast at hh
  have hc : (b:GaussLoc p)-(a:GaussLoc p)=
      piL p*(((b/p:ℕ):GaussLoc p)-((a/p:ℕ):GaussLoc p)) := by
    rw [WrapSimplePole.pi_eq_natCast]
    calc
      _=((b:GaussLoc p)+(p:GaussLoc p)*((a/p:ℕ):GaussLoc p))-
        ((a:GaussLoc p)+(p:GaussLoc p)*((a/p:ℕ):GaussLoc p)) := by ring
      _=((a:GaussLoc p)+(p:GaussLoc p)*((b/p:ℕ):GaussLoc p))-
        ((a:GaussLoc p)+(p:GaussLoc p)*((a/p:ℕ):GaussLoc p)) := by rw [hh]
      _=_ := by ring
  apply mul_left_cancel₀ (WrapDeform.pi_prime p).ne_zero
  have hr := commutator p point q o N u hN a b ha hb
  rw [hc] at hr
  simpa only [mul_assoc] using hr

end CatalanCore.Uniform.Content.UFSimple.WrapTestEntryRelation

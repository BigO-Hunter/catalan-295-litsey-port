module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.RuleOfSigns
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K shared R3 reserve; actual descending decode pilot unmeasured
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial

def rangeCoeffs {R : Type} [Semiring R] (p : Polynomial R) (n : Nat) : List R :=
  (List.range n).map p.coeff

theorem rangeCoeffs_succ {R : Type} [Semiring R] (p : Polynomial R) (n : Nat)
    (hn : p.natDegree<n) : rangeCoeffs p (n+1)=rangeCoeffs p n++[0] := by
  simp only [rangeCoeffs,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Reverse into Mathlib's descending convention; extra high coefficients are zeros. -/
theorem reversed_range_variations {R : Type} [Semiring R] [LinearOrder R]
    (p : Polynomial R) (n : Nat) (hn : p.natDegree<n) :
    List.signVariations (rangeCoeffs p n).reverse=p.signVariations := by
  have hbase : List.signVariations (rangeCoeffs p (p.natDegree+1)).reverse=
      p.signVariations := by
    by_cases hp : p=0
    · subst p
      simp [rangeCoeffs,Polynomial.signVariations,List.signVariations]
    · simp only [rangeCoeffs,Polynomial.signVariations,Polynomial.coeffList,
        Polynomial.withBotSucc_degree_eq_natDegree_add_one hp,List.map_reverse]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hn)
  induction k with
  | zero => simpa only [Nat.add_zero] using hbase
  | succ k ih =>
    rw [Nat.add_succ,rangeCoeffs_succ p _ (by omega),List.reverse_append]
    simpa only [List.reverse_singleton,List.singleton_append,
      List.signVariations_zero_cons] using ih (by omega)

theorem rangeCoeffs_map (p : Polynomial Int) (n : Nat) :
    rangeCoeffs (p.map (Int.castRingHom Real)) n=
      (rangeCoeffs p n).map (Int.castRingHom Real) := by
  simp only [rangeCoeffs,Polynomial.coeff_map_eq_comp,List.map_map,Function.comp_def]

/-- The canonical integer embedding preserves coefficient sign variations. -/
theorem real_map_variations (p : Polynomial Int) :
    (p.map (Int.castRingHom Real)).signVariations=p.signVariations := by
  let n := p.natDegree+1
  have hp : p.natDegree<n := by dsimp [n]; omega
  have hreal : (p.map (Int.castRingHom Real)).natDegree<n :=
    Polynomial.natDegree_map_le.trans_lt hp
  have hf : StrictMono (Int.castRingHom Real) := by
    intro a b hab
    simp only [Int.coe_castRingHom]
    exact_mod_cast hab
  rw [← reversed_range_variations _ n hreal,rangeCoeffs_map,
    ← reversed_range_variations p n hp]
  simpa only [List.map_reverse] using
    (List.signVariations_map (fun z : Int => hf.sign_comp z) (rangeCoeffs p n).reverse)

/-- A computational checker using descending decoded digits, matching Mathlib directly. -/
def decodedVariations (B : Int) (n : Nat) (v : Int) : Nat :=
  List.signVariations (decode B n v).2.reverse

theorem decoded_coeffs {k : Int} (hk : 0<k) (p : Polynomial Int) (n : Nat)
    (hn : p.natDegree<n) (hg : ∀ i,-k<p.coeff i ∧ p.coeff i≤k) :
    (decode (2*k) n (p.eval (2*k))).2=rangeCoeffs p n := by
  have hlen : (coeffRange p n).length=n := by simp [coeffRange]
  have he := decode_pack hk (coeffRange p n) (guard_coeffRange p n hg)
  rw [hlen,pack_coeffRange p hn] at he
  exact congrArg Prod.snd he

/-- This is a bound on positive REAL roots counted with multiplicity. -/
theorem real_positive_roots_le_decoded {k : Int} (hk : 0<k)
    (p : Polynomial Int) (n : Nat) (hn : p.natDegree<n)
    (hg : ∀ i,-k<p.coeff i ∧ p.coeff i≤k) (v : Nat)
    (hcheck : decodedVariations (2*k) n (p.eval (2*k))=v) :
    (p.map (Int.castRingHom Real)).roots.countP (0<·)≤v := by
  have hvar : (p.map (Int.castRingHom Real)).signVariations=v := by
    rw [real_map_variations,← reversed_range_variations p n hn]
    simpa only [decodedVariations,decoded_coeffs hk p n hn hg] using hcheck
  exact (Polynomial.roots_countP_pos_le_signVariations
    (p.map (Int.castRingHom Real))).trans_eq hvar

theorem real_positive_roots_le_expression {k : Int} (hk : 0<k)
    (e : Expr) (n : Nat) (hd : e.degree<n) (hm : (e.mass : Int)<k) (v : Nat)
    (hcheck : decodedVariations (2*k) n (e.eval (2*k))=v) :
    (e.poly.map (Int.castRingHom Real)).roots.countP (0<·)≤v := by
  apply real_positive_roots_le_decoded hk e.poly n
    ((expr_natDegree_le e).trans_lt hd) (expr_coeff_guard e hm) v
  simpa only [expr_eval] using hcheck

#print axioms reversed_range_variations
#print axioms real_map_variations
#print axioms decoded_coeffs
#print axioms real_positive_roots_le_decoded
#print axioms real_positive_roots_le_expression
end CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode

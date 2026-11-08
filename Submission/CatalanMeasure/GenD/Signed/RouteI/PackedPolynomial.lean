module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
set_option Elab.async false

/-!
# `PackedPolynomial` (row X2): packed decode, polynomial equality, and the list adapter

Data-free. Shared by C5 (`MarkedTransfer`, `MarkedSourceBound`) and C7.

* Part 1 (`PackedDecode`): centred base-`2k` digit decode of `pack (2k) cs`, `Guard k cs` meaning
  every digit lies in `(-k, k]`; `pack_injective_of_guard`, sign-change counting
  (`countDigits_sound`), the homogenised tree packing.
* Part 2 (`PolynomialMass`): the `l1` norm `norm1` of an integer polynomial is subadditive and
  submultiplicative; every coefficient is bounded by it.
* Part 3: `polynomial_eq_of_packed_eval` (equality of two integer polynomials of degree `< n`
  with centred coefficients from equality of their values at `2k`), the expression language
  `Expr` with `expression_eq_of_packed_eval`, `count_expression_sound`,
  `mobius_packed_count_sound`.
* Part 4 (list adapter): `ofList`, `l1`, and `laurent_poly_of_packed_eval`, which turns one
  integer identity of packed values at `2k` into the polynomial identity
  `H = C c * (4 A^2 - (1-X^2)^2 B^2) + R` of list polynomials, under degree bounds and the
  centred mass bound `|c| (4 l1 A^2 + 4 l1 B^2) + l1 R < k` (`k = 2^255` in the Route I
  instance, `laurent_poly_of_packed_eval_2_255`).

Parts 1-3 are the accepted standalone R2 modules `PackedDecodeConsumer`, `PolynomialMass`,
`PackedPolynomialConsumer`, proofs unchanged (namespaces merged).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial

open Polynomial
open scoped BigOperators

/-! ### Part 1: centred packed decode -/

def pack (B : Int) : List Int → Int
  | [] => 0
  | c :: cs => c+B*pack B cs

def digit (B v : Int) : Int :=
  let r := v%B
  if r ≤ B/2 then r else r-B

def quotient (B v : Int) : Int := (v-digit B v)/B

def decode (B : Int) : Nat → Int → Int × List Int
  | 0,v => (v,[])
  | n+1,v =>
    let rest := decode B n (quotient B v)
    (rest.1,digit B v::rest.2)

def Guard (k : Int) (cs : List Int) : Prop := ∀ c ∈ cs, -k < c ∧ c ≤ k

theorem digit_pack_head {k c q : Int} (hk : 0 < k) (hc : -k < c ∧ c ≤ k) :
    digit (2*k) (c+2*k*q) = c := by
  unfold digit
  rw [Int.add_mul_emod_self_left]
  have hhalf : (2*k)/2 = k := by omega
  rw [hhalf]
  by_cases hnonneg : 0 ≤ c
  · have hlt : c < 2*k := by omega
    rw [Int.emod_eq_of_lt hnonneg hlt]
    simp [hc.2]
  · have hlo : 0 ≤ c+2*k := by omega
    have hhi : c+2*k < 2*k := by omega
    have hshift : (c+2*k)%(2*k) = c%(2*k) := by
      simpa only [mul_one] using Int.add_mul_emod_self_left c (2*k) 1
    have hmod : c%(2*k) = c+2*k := by
      rw [← hshift]
      exact Int.emod_eq_of_lt hlo hhi
    rw [hmod]
    have hnot : ¬ c+2*k ≤ k := by omega
    simp only [hnot, ↓reduceIte]
    ring

theorem quotient_pack_head {k c q : Int} (hk : 0 < k) (hc : -k < c ∧ c ≤ k) :
    quotient (2*k) (c+2*k*q) = q := by
  unfold quotient
  rw [digit_pack_head hk hc]
  have he : c+2*k*q-c = (2*k)*q := by ring
  rw [he,Int.mul_ediv_cancel_left q (by omega : 2*k ≠ 0)]

theorem decode_pack {k : Int} (hk : 0 < k) (cs : List Int) (hg : Guard k cs) :
    decode (2*k) cs.length (pack (2*k) cs) = (0,cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hg c (by simp)
    have ht : Guard k cs := fun z hz => hg z (by simp [hz])
    simp only [List.length_cons,pack,decode]
    rw [digit_pack_head hk hc,quotient_pack_head hk hc,ih ht]

theorem pack_injective_of_guard {k : Int} (hk : 0 < k) {a b : List Int}
    (ha : Guard k a) (hb : Guard k b) (hlen : a.length=b.length)
    (he : pack (2*k) a = pack (2*k) b) : a=b := by
  have h := decode_pack hk a ha
  rw [he,hlen,decode_pack hk b hb] at h
  exact (Prod.mk.inj h).2.symm

def sign (z : Int) : Int := if z=0 then 0 else if z>0 then 1 else -1

def signChanges : List Int → Int → Nat → Nat
  | [],_,count => count
  | c::cs,last,count =>
    let s := sign c
    let next := if s=0 then last else s
    let count := if s≠0 ∧ last≠0 ∧ s≠last then count+1 else count
    signChanges cs next count

def countDigits (B : Int) : Nat → Int → Int → Nat → Int × Nat
  | 0,v,_,count => (v,count)
  | n+1,v,last,count =>
    let s := sign (digit B v)
    let next := if s=0 then last else s
    let count := if s≠0 ∧ last≠0 ∧ s≠last then count+1 else count
    countDigits B n (quotient B v) next count

theorem countDigits_pack {k : Int} (hk : 0 < k) (cs : List Int) (hg : Guard k cs)
    (last : Int) (count : Nat) :
    countDigits (2*k) cs.length (pack (2*k) cs) last count =
      (0,signChanges cs last count) := by
  induction cs generalizing last count with
  | nil => rfl
  | cons c cs ih =>
    have hc := hg c (by simp)
    have ht : Guard k cs := fun z hz => hg z (by simp [hz])
    simp only [List.length_cons,pack,countDigits,signChanges]
    rw [digit_pack_head hk hc,quotient_pack_head hk hc,ih ht]

theorem countDigits_sound {k n : Int} (hk : 0 < k) (cs : List Int)
    (hg : Guard k cs) (he : n=pack (2*k) cs) {v : Nat}
    (hcheck : countDigits (2*k) cs.length n 0 0 = (0,v)) :
    signChanges cs 0 0 = v := by
  rw [he,countDigits_pack hk cs hg] at hcheck
  exact (Prod.mk.inj hcheck).2

theorem pack_append (B : Int) (a b : List Int) :
    pack B (a++b) = pack B a+B^a.length*pack B b := by
  induction a with
  | nil => simp [pack]
  | cons c a ih =>
    simp only [List.cons_append,List.length_cons,pack,ih,pow_succ]
    ring

inductive Tree where
  | leaf : Int → Tree
  | node : Nat → Nat → Tree → Tree → Tree

def coeffs : Tree → List Int
  | .leaf c => [c]
  | .node _ _ l r => coeffs l++coeffs r

def WellFormed : Tree → Prop
  | .leaf _ => True
  | .node nl nr l r => nl=(coeffs l).length ∧ nr=(coeffs r).length ∧ WellFormed l ∧ WellFormed r

def hom (p q : Int) : Tree → Int
  | .leaf c => c
  | .node nl nr l r => q^nr*hom p q l+p^nl*hom p q r

theorem hom_one_eq_pack (t : Tree) (h : WellFormed t) (B : Int) :
    hom B 1 t = pack B (coeffs t) := by
  induction t with
  | leaf c => simp [hom,coeffs,pack]
  | node nl nr l r ihl ihr =>
    obtain ⟨hl,hr,hwfl,hwfr⟩ := h
    change 1^nr*hom B 1 l+B^nl*hom B 1 r = pack B (coeffs l++coeffs r)
    rw [one_pow,one_mul,ihl hwfl,ihr hwfr,pack_append,hl]

theorem guarded_tree_decode {k : Int} (hk : 0 < k) (t : Tree) (hw : WellFormed t)
    (hg : Guard k (coeffs t)) {v : Nat}
    (hcheck : countDigits (2*k) (coeffs t).length (hom (2*k) 1 t) 0 0 = (0,v)) :
    signChanges (coeffs t) 0 0 = v := by
  apply countDigits_sound hk (coeffs t) hg (hom_one_eq_pack t hw (2*k)) hcheck

theorem negative_unbounded_collision :
    pack 16 [9,0] = pack 16 [-7,1] ∧ ([9,0] : List Int) ≠ [-7,1] := by decide +kernel

/-! ### Part 2: the `l1` norm of an integer polynomial -/

noncomputable def norm1 (p : Polynomial Int) : Nat :=
  ∑ i ∈ p.support, (p.coeff i).natAbs

theorem norm1_monomial (n : Nat) (c : Int) : norm1 (monomial n c) = c.natAbs := by
  classical
  by_cases hc : c=0
  · simp [hc,norm1]
  · simp [norm1,Polynomial.support_monomial,hc]

theorem norm1_add_le (p q : Polynomial Int) : norm1 (p+q) ≤ norm1 p+norm1 q := by
  classical
  have hzero (s : Polynomial Int) (i : Nat) (hi : i ∉ s.support) : s.coeff i=0 := by
    simpa only [Polynomial.mem_support_iff,not_not] using hi
  have hp : ∑ i ∈ p.support ∪ q.support, (p.coeff i).natAbs = norm1 p := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    simp [hzero p i hi]
  have hq : ∑ i ∈ p.support ∪ q.support, (q.coeff i).natAbs = norm1 q := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro i _ hi
    simp [hzero q i hi]
  have hpq : norm1 (p+q) = ∑ i ∈ p.support ∪ q.support, ((p+q).coeff i).natAbs := by
    apply Finset.sum_subset Polynomial.support_add
    intro i _ hi
    simp [hzero (p+q) i hi]
  rw [hpq]
  calc
    (∑ i ∈ p.support ∪ q.support, ((p+q).coeff i).natAbs) ≤
        ∑ i ∈ p.support ∪ q.support, ((p.coeff i).natAbs+(q.coeff i).natAbs) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.coeff_add]
      exact Int.natAbs_add_le _ _
    _ = norm1 p+norm1 q := by rw [Finset.sum_add_distrib,hp,hq]

theorem norm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial Int) :
    norm1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, norm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm1]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (norm1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem norm1_mul_le (p q : Polynomial Int) : norm1 (p*q) ≤ norm1 p*norm1 q := by
  classical
  have hexp : p*q = ∑ i ∈ p.support, ∑ j ∈ q.support,
      monomial (i+j) (p.coeff i*q.coeff j) := by
    calc
      p*q = (p.sum fun i c => monomial i c)*(q.sum fun j c => monomial j c) :=
        congrArg₂ (fun a b : Polynomial Int => a*b)
          (Polynomial.sum_monomial_eq p).symm (Polynomial.sum_monomial_eq q).symm
      _ = ∑ i ∈ p.support, ∑ j ∈ q.support, monomial (i+j) (p.coeff i*q.coeff j) := by
        simp only [Polynomial.sum,Finset.sum_mul,Finset.mul_sum,Polynomial.monomial_mul_monomial]
        rw [Finset.sum_comm]
  rw [hexp]
  calc
    norm1 (∑ i ∈ p.support, ∑ j ∈ q.support, monomial (i+j) (p.coeff i*q.coeff j)) ≤
        ∑ i ∈ p.support, norm1 (∑ j ∈ q.support, monomial (i+j) (p.coeff i*q.coeff j)) := norm1_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, (p.coeff i).natAbs*(q.coeff j).natAbs := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm1_monomial,Int.natAbs_mul] using
        norm1_sum_le q.support (fun j => monomial (i+j) (p.coeff i*q.coeff j))
    _ = norm1 p*norm1 q := by
      unfold norm1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

theorem coeff_natAbs_le_norm1 (p : Polynomial Int) (i : Nat) :
    (p.coeff i).natAbs ≤ norm1 p := by
  classical
  by_cases h : p.coeff i=0
  · simp [h]
  · unfold norm1
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (p.coeff j).natAbs)
      (Polynomial.mem_support_iff.mpr h)

/-! ### Part 3: polynomial equality from packed evaluation -/

theorem pack_range (B : Int) (f : Nat → Int) (n : Nat) :
    pack B ((List.range n).map f) = ∑ i ∈ Finset.range n, f i*B^i := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,pack_append,
      List.length_map,List.length_range,pack,ih,Finset.sum_range_succ]
    ring

def coeffRange (P : Polynomial Int) (n : Nat) : List Int := (List.range n).map P.coeff

theorem pack_coeffRange (P : Polynomial Int) {n : Nat} (hn : P.natDegree<n) (B : Int) :
    pack B (coeffRange P n) = P.eval B := by
  rw [coeffRange,pack_range]
  exact (Polynomial.eval_eq_sum_range' hn B).symm

theorem guard_coeffRange {k : Int} (P : Polynomial Int) (n : Nat)
    (h : ∀ i,-k<P.coeff i ∧ P.coeff i≤k) : Guard k (coeffRange P n) := by
  intro c hc
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
  exact h i

theorem polynomial_eq_of_packed_eval {k : Int} (hk : 0<k) (P Q : Polynomial Int) (n : Nat)
    (hP : P.natDegree<n) (hQ : Q.natDegree<n)
    (hgP : ∀ i,-k<P.coeff i ∧ P.coeff i≤k)
    (hgQ : ∀ i,-k<Q.coeff i ∧ Q.coeff i≤k)
    (he : P.eval (2*k)=Q.eval (2*k)) : P=Q := by
  have hlist : coeffRange P n=coeffRange Q n := by
    apply pack_injective_of_guard hk (guard_coeffRange P n hgP) (guard_coeffRange Q n hgQ)
    · simp [coeffRange]
    · rw [pack_coeffRange P hP,pack_coeffRange Q hQ,he]
  apply Polynomial.ext
  intro i
  by_cases hi : i<n
  · have h := congrArg (fun l : List Int => l[i]?) hlist
    simpa [coeffRange,hi] using h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hP (Nat.le_of_not_gt hi)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hQ (Nat.le_of_not_gt hi))]

inductive Expr where
  | c : Int → Expr
  | x : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Nat → Expr

noncomputable def Expr.poly : Expr → Polynomial Int
  | .c z => C z
  | .x => X
  | .add e f => e.poly+f.poly
  | .mul e f => e.poly*f.poly
  | .pow e n => e.poly^n

def Expr.eval (B : Int) : Expr → Int
  | .c z => z
  | .x => B
  | .add e f => e.eval B+f.eval B
  | .mul e f => e.eval B*f.eval B
  | .pow e n => (e.eval B)^n

def Expr.mass : Expr → Nat
  | .c z => z.natAbs
  | .x => 1
  | .add e f => e.mass+f.mass
  | .mul e f => e.mass*f.mass
  | .pow e n => e.mass^n

def Expr.degree : Expr → Nat
  | .c _ => 0
  | .x => 1
  | .add e f => max e.degree f.degree
  | .mul e f => e.degree+f.degree
  | .pow e n => e.degree*n

theorem expr_eval (e : Expr) (B : Int) : e.poly.eval B=e.eval B := by
  induction e with
  | c z => simp [Expr.poly,Expr.eval]
  | x => simp [Expr.poly,Expr.eval]
  | add e f ihe ihf => simp [Expr.poly,Expr.eval,ihe,ihf]
  | mul e f ihe ihf => simp [Expr.poly,Expr.eval,ihe,ihf]
  | pow e n ih => simp [Expr.poly,Expr.eval,ih]

theorem norm1_pow_le (P : Polynomial Int) (n : Nat) : norm1 (P^n)≤(norm1 P)^n := by
  induction n with
  | zero =>
    simpa using (norm1_monomial 0 (1 : Int)).le
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (norm1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

theorem expr_norm1_le_mass (e : Expr) : norm1 e.poly≤e.mass := by
  induction e with
  | c z => simpa [Expr.poly,Expr.mass] using (norm1_monomial 0 z).le
  | x =>
    change norm1 (X : Polynomial Int)≤1
    rw [← Polynomial.monomial_one_one_eq_X,norm1_monomial]
    decide
  | add e f ihe ihf => exact (norm1_add_le _ _).trans (Nat.add_le_add ihe ihf)
  | mul e f ihe ihf => exact (norm1_mul_le _ _).trans (Nat.mul_le_mul ihe ihf)
  | pow e n ih => exact (norm1_pow_le _ _).trans (Nat.pow_le_pow_left ih n)

theorem expr_natDegree_le (e : Expr) : e.poly.natDegree≤e.degree := by
  induction e with
  | c z => simp [Expr.poly,Expr.degree]
  | x => simp [Expr.poly,Expr.degree]
  | add e f ihe ihf => exact (Polynomial.natDegree_add_le _ _).trans (max_le_max ihe ihf)
  | mul e f ihe ihf =>
    simpa only [Expr.poly,Expr.degree] using
      (Polynomial.natDegree_mul_le (p:=e.poly) (q:=f.poly)).trans (Nat.add_le_add ihe ihf)
  | pow e n ih =>
    have h : (e.poly^n).natDegree ≤ n*e.degree :=
      (Polynomial.natDegree_pow_le (p:=e.poly) (n:=n)).trans (Nat.mul_le_mul_left n ih)
    simpa only [Expr.poly,Expr.degree,Nat.mul_comm] using h

theorem expr_coeff_guard (e : Expr) {k : Int} (hm : (e.mass : Int)<k) (i : Nat) :
    -k<e.poly.coeff i ∧ e.poly.coeff i≤k := by
  have h := (coeff_natAbs_le_norm1 e.poly i).trans (expr_norm1_le_mass e)
  have hc : ((e.poly.coeff i).natAbs : Int)≤(e.mass : Int) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hc
  have ha := abs_lt.mp (lt_of_le_of_lt hc hm)
  exact ⟨ha.1,ha.2.le⟩

theorem expression_eq_of_packed_eval {k : Int} (hk : 0<k) (e f : Expr) (n : Nat)
    (he : e.degree<n) (hf : f.degree<n) (hme : (e.mass : Int)<k) (hmf : (f.mass : Int)<k)
    (hcheck : e.eval (2*k)=f.eval (2*k)) : e.poly=f.poly := by
  apply polynomial_eq_of_packed_eval hk _ _ n
    ((expr_natDegree_le e).trans_lt he) ((expr_natDegree_le f).trans_lt hf)
    (expr_coeff_guard e hme) (expr_coeff_guard f hmf)
  simpa only [expr_eval] using hcheck

theorem count_expression_sound {k : Int} (hk : 0<k) (e : Expr) (n : Nat)
    (hd : e.degree<n) (hm : (e.mass : Int)<k) {v : Nat}
    (hcheck : countDigits (2*k) n (e.eval (2*k)) 0 0=(0,v)) :
    signChanges (coeffRange e.poly n) 0 0=v := by
  apply countDigits_sound hk (coeffRange e.poly n) (guard_coeffRange _ _ (expr_coeff_guard e hm))
  · rw [pack_coeffRange e.poly ((expr_natDegree_le e).trans_lt hd),expr_eval]
  · simpa [coeffRange] using hcheck

def homExpr (p q : Expr) : Tree → Expr
  | .leaf c => .c c
  | .node nl nr l r => .add (.mul (.pow q nr) (homExpr p q l))
      (.mul (.pow p nl) (homExpr p q r))

theorem homExpr_eval (t : Tree) (p q : Expr) (B : Int) :
    (homExpr p q t).eval B=hom (p.eval B) (q.eval B) t := by
  induction t with
  | leaf c => rfl
  | node nl nr l r ihl ihr => simp [homExpr,Expr.eval,hom,ihl,ihr]

def mobiusExpr (a b d : Int) (t : Tree) : Expr :=
  homExpr (.add (.c a) (.mul (.c b) .x)) (.add (.c d) (.mul (.c d) .x)) t

theorem mobius_packed_count_sound {k : Int} (hk : 0<k) (a b d : Int) (t : Tree) (n : Nat)
    (hd : (mobiusExpr a b d t).degree<n) (hm : ((mobiusExpr a b d t).mass : Int)<k)
    {v : Nat} (hcheck : countDigits (2*k) n (hom (a+b*(2*k)) (d+d*(2*k)) t) 0 0=(0,v)) :
    signChanges (coeffRange (mobiusExpr a b d t).poly n) 0 0=v := by
  apply count_expression_sound hk _ n hd hm
  simpa only [mobiusExpr,homExpr_eval,Expr.eval] using hcheck

/-! ### Part 4: the list adapter -/

/-- The polynomial of a coefficient list (index = power of the variable); Horner form. -/
noncomputable def ofList : List Int → Polynomial Int
  | [] => 0
  | a :: t => C a + X * ofList t

/-- `l1` of a coefficient list. -/
def l1 : List Int → Nat
  | [] => 0
  | a :: t => a.natAbs + l1 t

theorem eval_ofList (B : Int) (l : List Int) : (ofList l).eval B = pack B l := by
  induction l with
  | nil => simp [ofList, pack]
  | cons a t ih => simp [ofList, pack, ih]

theorem coeff_ofList (l : List Int) (i : Nat) : (ofList l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [ofList]
  | cons a t ih =>
    cases i with
    | zero => simp [ofList]
    | succ i =>
      simp only [ofList, Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul,
        ih, zero_add]
      simp

theorem natDegree_ofList_le (l : List Int) : (ofList l).natDegree ≤ l.length - 1 := by
  induction l with
  | nil => simp [ofList]
  | cons a t ih =>
    cases t with
    | nil => simp [ofList]
    | cons b u =>
      have h1 : (X * ofList (b :: u)).natDegree ≤ 1 + (ofList (b :: u)).natDegree :=
        (Polynomial.natDegree_mul_le).trans (Nat.add_le_add_right Polynomial.natDegree_X_le _)
      have h2 := Polynomial.natDegree_add_le (C a) (X * ofList (b :: u))
      rw [Polynomial.natDegree_C] at h2
      show (C a + X * ofList (b :: u)).natDegree ≤ (a :: b :: u).length - 1
      simp only [List.length_cons] at ih ⊢
      exact h2.trans (max_le (Nat.zero_le _) (by omega))

theorem norm1_ofList_le (l : List Int) : norm1 (ofList l) ≤ l1 l := by
  induction l with
  | nil => simp [ofList, l1, norm1]
  | cons a t ih =>
    have hX : norm1 (X : Polynomial Int) ≤ 1 := by
      rw [← Polynomial.monomial_one_one_eq_X, norm1_monomial]; decide
    have h1 : norm1 (X * ofList t) ≤ l1 t :=
      (norm1_mul_le _ _).trans (by simpa using Nat.mul_le_mul hX ih)
    have h2 : norm1 (C a + X * ofList t) ≤ norm1 (C a) + norm1 (X * ofList t) := norm1_add_le _ _
    have h3 : norm1 (C a) = a.natAbs := by
      rw [← Polynomial.monomial_zero_left]; exact norm1_monomial 0 a
    simp only [ofList, l1]
    omega

theorem norm1_neg (p : Polynomial Int) : norm1 (-p) = norm1 p := by
  simp [norm1, Polynomial.support_neg, Polynomial.coeff_neg]

theorem norm1_sub_le (p q : Polynomial Int) : norm1 (p - q) ≤ norm1 p + norm1 q := by
  rw [sub_eq_add_neg]
  simpa [norm1_neg] using norm1_add_le p (-q)

theorem norm1_C (a : Int) : norm1 (C a) = a.natAbs := by
  rw [← Polynomial.monomial_zero_left]; exact norm1_monomial 0 a

theorem norm1_one_sub_sq_sq_le : norm1 ((1 - X ^ 2 : Polynomial Int) ^ 2) ≤ 4 := by
  have h1 : norm1 (1 : Polynomial Int) = 1 := by
    simpa using norm1_C 1
  have h2 : norm1 ((X : Polynomial Int) ^ 2) = 1 := by
    rw [← Polynomial.monomial_one_one_eq_X, Polynomial.monomial_pow]
    simpa using norm1_monomial 2 1
  have h3 : norm1 (1 - X ^ 2 : Polynomial Int) ≤ 2 := by
    have := norm1_sub_le (1 : Polynomial Int) (X ^ 2)
    omega
  have := norm1_pow_le (1 - X ^ 2 : Polynomial Int) 2
  nlinarith [Nat.pow_le_pow_left h3 2]

/-- Mass bound of the Laurent right-hand side. -/
theorem norm1_laurent_le (c : Int) (A B R : List Int) :
    norm1 (C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2) + ofList R) ≤
      c.natAbs * (4 * l1 A ^ 2 + 4 * l1 B ^ 2) + l1 R := by
  have h4 : norm1 (4 : Polynomial Int) = 4 := by
    have : (4 : Polynomial Int) = C 4 := by simp
    rw [this]; simpa using norm1_C 4
  have hA : norm1 (ofList A ^ 2) ≤ l1 A ^ 2 :=
    (norm1_pow_le _ 2).trans (Nat.pow_le_pow_left (norm1_ofList_le A) 2)
  have hB : norm1 (ofList B ^ 2) ≤ l1 B ^ 2 :=
    (norm1_pow_le _ 2).trans (Nat.pow_le_pow_left (norm1_ofList_le B) 2)
  have t1 : norm1 (4 * ofList A ^ 2) ≤ 4 * l1 A ^ 2 :=
    (norm1_mul_le _ _).trans (by rw [h4]; exact Nat.mul_le_mul_left 4 hA)
  have t2 : norm1 ((1 - X ^ 2 : Polynomial Int) ^ 2 * ofList B ^ 2) ≤ 4 * l1 B ^ 2 :=
    (norm1_mul_le _ _).trans (Nat.mul_le_mul norm1_one_sub_sq_sq_le hB)
  have t3 : norm1 (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2) ≤
      4 * l1 A ^ 2 + 4 * l1 B ^ 2 := (norm1_sub_le _ _).trans (Nat.add_le_add t1 t2)
  have t4 : norm1 (C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2)) ≤
      c.natAbs * (4 * l1 A ^ 2 + 4 * l1 B ^ 2) :=
    (norm1_mul_le _ _).trans (by rw [norm1_C]; exact Nat.mul_le_mul_left _ t3)
  exact (norm1_add_le _ _).trans (Nat.add_le_add t4 (norm1_ofList_le R))

theorem guard_ofList {K : Int} (l : List Int) (hK : 0 < K) (hg : Guard K l) (i : Nat) :
    -K < (ofList l).coeff i ∧ (ofList l).coeff i ≤ K := by
  rw [coeff_ofList]
  by_cases hi : i < l.length
  · have h : l.getD i 0 = l[i] := by simp [hi]
    rw [h]
    exact hg _ (List.getElem_mem hi)
  · have h : l.getD i 0 = 0 := by simp [Nat.le_of_not_gt hi]
    rw [h]
    exact ⟨by omega, by omega⟩

theorem guard_of_l1_lt {K : Int} (l : List Int) (h : (l1 l : Int) < K) : Guard K l := by
  have hmem : ∀ c ∈ l, c.natAbs ≤ l1 l := by
    induction l with
    | nil => simp
    | cons a t ih =>
      intro c hc
      simp only [l1]
      rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · have : (l1 t : Int) < K := by simp only [l1] at h; omega
        have := ih this c hc
        omega
  intro c hc
  have := hmem c hc
  omega

/-- The list adapter. One integer identity of packed values at `2K` gives the polynomial identity
of the list polynomials `H = C c (4 A^2 - (1-X^2)^2 B^2) + R`, provided: degrees (`H`, `R` have
at most `n` entries, `A^2` and `(1-X^2)^2 B^2` have degree `< n`), the centred digits of `H` lie in
`(-K, K]`, and the mass `|c| (4 l1 A^2 + 4 l1 B^2) + l1 R < K`. -/
theorem laurent_poly_of_packed_eval {K : Int} (hK : 0 < K) (c : Int) (H A B R : List Int) (n : Nat)
    (hH : H.length ≤ n) (hA : 2 * (A.length - 1) < n) (hB : 4 + 2 * (B.length - 1) < n)
    (hR : R.length ≤ n)
    (hgH : Guard K H)
    (hmass : ((c.natAbs * (4 * l1 A ^ 2 + 4 * l1 B ^ 2) + l1 R : Nat) : Int) < K)
    (hcheck : pack (2 * K) H =
      c * (4 * pack (2 * K) A ^ 2 - (1 - (2 * K) ^ 2) ^ 2 * pack (2 * K) B ^ 2) +
        pack (2 * K) R) :
    ofList H = C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2) + ofList R := by
  apply polynomial_eq_of_packed_eval hK _ _ n
  · exact lt_of_le_of_lt (natDegree_ofList_le H) (by omega)
  · have h1 : (C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2)).natDegree < n := by
      refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
      have hs := Polynomial.natDegree_sub_le (4 * ofList A ^ 2) ((1 - X ^ 2) ^ 2 * ofList B ^ 2 : Polynomial Int)
      have ha : (4 * ofList A ^ 2 : Polynomial Int).natDegree ≤ 2 * (A.length - 1) := by
        have h4 : (4 : Polynomial Int).natDegree = 0 := by
          have : (4 : Polynomial Int) = C 4 := by simp
          rw [this]; exact Polynomial.natDegree_C 4
        have := Polynomial.natDegree_mul_le (p := (4 : Polynomial Int)) (q := ofList A ^ 2)
        have h5 : (ofList A ^ 2).natDegree ≤ 2 * (natDegree (ofList A)) :=
          by simp
        have := natDegree_ofList_le A
        omega
      have hb : ((1 - X ^ 2) ^ 2 * ofList B ^ 2 : Polynomial Int).natDegree ≤ 4 + 2 * (B.length - 1) := by
        have hm := Polynomial.natDegree_mul_le (p := ((1 - X ^ 2) ^ 2 : Polynomial Int)) (q := ofList B ^ 2)
        have hw : ((1 - X ^ 2 : Polynomial Int) ^ 2).natDegree ≤ 4 := by
          have h1 := Polynomial.natDegree_pow_le (p := (1 - X ^ 2 : Polynomial Int)) (n := 2)
          have h2 : (1 - X ^ 2 : Polynomial Int).natDegree ≤ 2 := by
            have := Polynomial.natDegree_sub_le (1 : Polynomial Int) (X ^ 2)
            have h3 : (X ^ 2 : Polynomial Int).natDegree = 2 := by simp
            simp at this
            omega
          omega
        have h5 : (ofList B ^ 2).natDegree ≤ 2 * (natDegree (ofList B)) :=
          by simp
        have := natDegree_ofList_le B
        omega
      have : max (4 * ofList A ^ 2 : Polynomial Int).natDegree
          ((1 - X ^ 2) ^ 2 * ofList B ^ 2 : Polynomial Int).natDegree ≤ 4 + 2 * (B.length - 1) ∨
          max (4 * ofList A ^ 2 : Polynomial Int).natDegree
          ((1 - X ^ 2) ^ 2 * ofList B ^ 2 : Polynomial Int).natDegree ≤ 2 * (A.length - 1) := by
        omega
      omega
    have h2 := natDegree_ofList_le R
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    exact max_lt h1 (lt_of_le_of_lt h2 (by omega))
  · exact guard_ofList H hK hgH
  · intro i
    have h := (coeff_natAbs_le_norm1 _ i).trans (norm1_laurent_le c A B R)
    have hc : (((C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2) + ofList R).coeff i).natAbs : Int)
        ≤ ((c.natAbs * (4 * l1 A ^ 2 + 4 * l1 B ^ 2) + l1 R : Nat) : Int) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at hc
    have ha := abs_lt.mp (lt_of_le_of_lt hc hmass)
    exact ⟨ha.1, ha.2.le⟩
  · rw [eval_ofList]
    simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_ofList, eval_one, eval_X]
    simpa using hcheck

/-- The Route I instance: centred guard `|c| ≤ k`, `k = 2^255` (radix `2^256`). -/
theorem laurent_poly_of_packed_eval_2_255 (c : Int) (H A B R : List Int) (n : Nat)
    (hH : H.length ≤ n) (hA : 2 * (A.length - 1) < n) (hB : 4 + 2 * (B.length - 1) < n)
    (hR : R.length ≤ n)
    (hgH : Guard (2 ^ 255) H)
    (hmass : ((c.natAbs * (4 * l1 A ^ 2 + 4 * l1 B ^ 2) + l1 R : Nat) : Int) < 2 ^ 255)
    (hcheck : pack (2 ^ 256) H =
      c * (4 * pack (2 ^ 256) A ^ 2 - (1 - (2 ^ 256) ^ 2) ^ 2 * pack (2 ^ 256) B ^ 2) +
        pack (2 ^ 256) R) :
    ofList H = C c * (4 * ofList A ^ 2 - (1 - X ^ 2) ^ 2 * ofList B ^ 2) + ofList R := by
  have h2 : (2 : Int) ^ 256 = 2 * 2 ^ 255 := by norm_num
  rw [h2] at hcheck
  exact laurent_poly_of_packed_eval (by norm_num) c H A B R n hH hA hB hR hgH hmass hcheck

#print axioms polynomial_eq_of_packed_eval
#print axioms expression_eq_of_packed_eval
#print axioms count_expression_sound
#print axioms mobius_packed_count_sound
#print axioms countDigits_sound
#print axioms guarded_tree_decode
#print axioms laurent_poly_of_packed_eval
#print axioms laurent_poly_of_packed_eval_2_255

end CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial

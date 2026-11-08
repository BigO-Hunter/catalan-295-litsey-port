module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K R3 reserve; this homogeneous bridge is only part of R3
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal
noncomputable section
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial
open scoped BigOperators

def evalList (x : Real) : List Int → Real
  | [] => 0
  | c::cs => (c : Real)+x*evalList x cs

theorem evalList_append (x : Real) (l r : List Int) :
    evalList x (l++r)=evalList x l+x^l.length*evalList x r := by
  induction l with
  | nil => simp [evalList]
  | cons c cs ih => simp only [List.cons_append,evalList,List.length_cons,ih,pow_succ]; ring

theorem evalList_range (x : Real) (f : Nat → Int) (n : Nat) :
    evalList x ((List.range n).map f)=∑ i ∈ Finset.range n,(f i : Real)*x^i := by
  induction n with
  | zero => simp [evalList]
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,
      evalList_append,evalList,List.length_map,List.length_range,ih,
      Finset.sum_range_succ]
    ring

theorem evalList_coeffRange (p : Polynomial Int) {n : Nat}
    (hn : p.natDegree<n) (x : Real) :
    evalList x (coeffRange p n)=p.eval₂ (Int.castRingHom Real) x := by
  simpa only [coeffRange,evalList_range,Int.coe_castRingHom] using
    (Polynomial.eval₂_eq_sum_range' (Int.castRingHom Real) hn x).symm

def homReal (p q : Real) : Tree → Real
  | .leaf c => c
  | .node nl nr l r => q^nr*homReal p q l+p^nl*homReal p q r

theorem coeffs_length_pos (t : Tree) : 0<(coeffs t).length := by
  induction t with
  | leaf c => simp [coeffs]
  | node nl nr l r ihl ihr => simp only [coeffs,List.length_append]; omega

/-- The source-tree identity, including the recorded child-length guards. -/
theorem homReal_scaled (t : Tree) (hw : WellFormed t) (q z : Real) :
    homReal (q*z) q t=q^((coeffs t).length-1)*evalList z (coeffs t) := by
  induction t with
  | leaf c => simp [homReal,coeffs,evalList]
  | node nl nr l r ihl ihr =>
    obtain ⟨hl,hr,hwl,hwr⟩ := hw
    have hnl : 0<nl := by rw [hl]; exact coeffs_length_pos l
    have hnr : 0<nr := by rw [hr]; exact coeffs_length_pos r
    have hpL : q^nr*q^((coeffs l).length-1)=q^((coeffs l).length+(coeffs r).length-1) := by
      rw [← pow_add]
      congr 1
      omega
    have hpR : q^nl*q^((coeffs r).length-1)=q^((coeffs l).length+(coeffs r).length-1) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [homReal,ihl hwl,ihr hwr,mul_pow,coeffs,List.length_append,evalList_append]
    calc
      q^nr*(q^((coeffs l).length-1)*evalList z (coeffs l))+
          q^nl*z^nl*(q^((coeffs r).length-1)*evalList z (coeffs r)) =
          (q^nr*q^((coeffs l).length-1))*evalList z (coeffs l)+
          (q^nl*q^((coeffs r).length-1))*z^nl*evalList z (coeffs r) := by ring
      _ = q^((coeffs l).length+(coeffs r).length-1)*
          (evalList z (coeffs l)+z^(coeffs l).length*evalList z (coeffs r)) := by
        rw [hpL,hpR,hl]
        ring

def realExpr (x : Real) : Expr → Real
  | .c c => c
  | .x => x
  | .add e f => realExpr x e+realExpr x f
  | .mul e f => realExpr x e*realExpr x f
  | .pow e n => realExpr x e^n

theorem realExpr_poly (e : Expr) (x : Real) :
    e.poly.eval₂ (Int.castRingHom Real) x=realExpr x e := by
  induction e with
  | c c => exact Polynomial.eval₂_C _ _
  | x => exact Polynomial.eval₂_X _ _
  | add e f he hf => simpa only [Expr.poly,realExpr,Polynomial.eval₂_add,he,hf]
  | mul e f he hf => simpa only [Expr.poly,realExpr,Polynomial.eval₂_mul,he,hf]
  | pow e n he => simpa only [Expr.poly,realExpr,Polynomial.eval₂_pow,he]

theorem homExpr_real (t : Tree) (p q : Expr) (x : Real) :
    realExpr x (homExpr p q t)=homReal (realExpr x p) (realExpr x q) t := by
  induction t with
  | leaf c => rfl
  | node nl nr l r ihl ihr => simp only [homExpr,realExpr,homReal,ihl,ihr]

/-- Both polynomial and tree refer to exactly the same ascending source leaves. -/
theorem mobius_eval (a b d : Int) (t : Tree) (hw : WellFormed t)
    (p : Polynomial Int) (hdegree : p.natDegree<(coeffs t).length)
    (hleaves : coeffs t=coeffRange p (coeffs t).length) (y : Real)
    (hden : (d : Real)+(d : Real)*y≠0) :
    (mobiusExpr a b d t).poly.eval₂ (Int.castRingHom Real) y =
      ((d : Real)+(d : Real)*y)^((coeffs t).length-1)*
      p.eval₂ (Int.castRingHom Real)
        (((a : Real)+(b : Real)*y)/((d : Real)+(d : Real)*y)) := by
  rw [realExpr_poly]
  simp only [mobiusExpr,homExpr_real,realExpr]
  have hmul : ((d : Real)+(d : Real)*y)*
      (((a : Real)+(b : Real)*y)/((d : Real)+(d : Real)*y)) =
      (a : Real)+(b : Real)*y := mul_div_cancel₀ _ hden
  calc
    homReal ((a : Real)+(b : Real)*y) ((d : Real)+(d : Real)*y) t =
        homReal (((d : Real)+(d : Real)*y)*
          (((a : Real)+(b : Real)*y)/((d : Real)+(d : Real)*y)))
          ((d : Real)+(d : Real)*y) t := by rw [hmul]
    _ = ((d : Real)+(d : Real)*y)^((coeffs t).length-1)*
        evalList (((a : Real)+(b : Real)*y)/((d : Real)+(d : Real)*y)) (coeffs t) :=
      homReal_scaled t hw _ _
    _ = _ := by
      congr 1
      rw [hleaves]
      exact evalList_coeffRange p hdegree _

def T (a b d y : Real) := (a+b*y)/(d*(1+y))
def U (a b d x : Real) := (d*x-a)/(b-d*x)

theorem T_mem (a b d y : Real) (hab : a<b) (hd : 0<d) (hy : 0<y) :
    a/d<T a b d y ∧ T a b d y<b/d := by
  have h1 : 0<1+y := by linarith
  have hden : 0<d*(1+y) := mul_pos hd h1
  constructor
  · rw [T,div_lt_div_iff₀ hd hden]
    nlinarith [mul_pos (mul_pos hd hy) (sub_pos.mpr hab)]
  · rw [T,div_lt_div_iff₀ hden hd]
    nlinarith [mul_pos hd (sub_pos.mpr hab)]

theorem U_pos (a b d x : Real) (hd : 0<d) (hx : a/d<x ∧ x<b/d) :
    0<U a b d x := by
  have hleft : a<d*x := by have hh := (div_lt_iff₀ hd).mp hx.1; nlinarith
  have hright : d*x<b := by have hh := (lt_div_iff₀ hd).mp hx.2; nlinarith
  exact div_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)

theorem T_U (a b d x : Real) (hab : a<b) (hd : 0<d)
    (hx : a/d<x ∧ x<b/d) : T a b d (U a b d x)=x := by
  have hb : b-d*x≠0 := by
    have hh := (lt_div_iff₀ hd).mp hx.2
    nlinarith
  have hu : 1+U a b d x≠0 := ne_of_gt (by have hh := U_pos a b d x hd hx; linarith)
  have hba : -a+b≠0 := by linarith
  dsimp [T,U] at hu ⊢
  field_simp [ne_of_gt hd,hb,hu,hba]
  <;> ring_nf
  <;> field_simp [hba]
  <;> ring

theorem U_T (a b d y : Real) (hab : a<b) (hd : 0<d) (hy : 0<y) :
    U a b d (T a b d y)=y := by
  have h1 : 1+y≠0 := ne_of_gt (by linarith)
  have hba : -a+b≠0 := by linarith
  have hb : b-d*T a b d y≠0 := by
    have hh := (lt_div_iff₀ hd).mp (T_mem a b d y hab hd hy).2
    nlinarith
  dsimp [T] at hb
  dsimp [T,U]
  field_simp [ne_of_gt hd,h1,hb,hba]
  <;> ring_nf
  <;> field_simp [hba]
  <;> ring

theorem mobius_root_iff (a b d : Int) (t : Tree) (hw : WellFormed t)
    (p : Polynomial Int) (hdegree : p.natDegree<(coeffs t).length)
    (hleaves : coeffs t=coeffRange p (coeffs t).length) (y : Real)
    (hd : (0 : Real)<d) (hy : 0<y) :
    (mobiusExpr a b d t).poly.eval₂ (Int.castRingHom Real) y=0 ↔
      p.eval₂ (Int.castRingHom Real) (T a b d y)=0 := by
  have hden : (d : Real)+(d : Real)*y≠0 := ne_of_gt (by positivity)
  have heq : (d : Real)+(d : Real)*y=(d : Real)*(1+y) := by ring
  have hpow : ((d : Real)*(1+y))^((coeffs t).length-1)≠0 :=
    pow_ne_zero _ (mul_ne_zero (ne_of_gt hd) (ne_of_gt (by linarith)))
  rw [mobius_eval a b d t hw p hdegree hleaves y hden,heq,mul_eq_zero]
  simp only [hpow,false_or,T]

#print axioms homReal_scaled
#print axioms mobius_eval
#print axioms T_mem
#print axioms U_pos
#print axioms T_U
#print axioms U_T
#print axioms mobius_root_iff
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal

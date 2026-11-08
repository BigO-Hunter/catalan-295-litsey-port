module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Order.Interval.Set.Infinite
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated <=149 K shared R3 reserve; full count/instance consumption still open
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusMultiplicity
noncomputable section
open CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal

def forms (a b d : Real) (i : Fin 2) : Polynomial Real :=
  if i=0 then Polynomial.C a+Polynomial.C b*Polynomial.X
  else Polynomial.C d*(1+Polynomial.X)

def H (a b d : Real) (p : Polynomial Real) (n : Nat) : Polynomial Real :=
  MvPolynomial.eval₂Hom Polynomial.C (forms a b d) (p.homogenize n)

theorem H_eval (a b d : Real) (p : Polynomial Real) (n : Nat)
    (hn : p.natDegree≤n) (y : Real) (hd : d*(1+y)≠0) :
    (H a b d p n).eval y=p.eval (T a b d y)*(d*(1+y))^n := by
  have hc : (Polynomial.evalRingHom y).comp
      (Polynomial.C : Real →+* Polynomial Real)=RingHom.id Real := by
    ext c
    simp
  have hm := MvPolynomial.map_eval₂Hom
    (Polynomial.C : Real →+* Polynomial Real) (forms a b d)
    (Polynomial.evalRingHom y) (p.homogenize n)
  rw [hc] at hm
  have hforms : (fun i : Fin 2 => (Polynomial.evalRingHom y) (forms a b d i))=
      (fun i : Fin 2 => if i=0 then a+b*y else d*(1+y)) := by
    funext i
    by_cases hi : i=0 <;>
      simp only [forms,hi,↓reduceIte,Polynomial.coe_evalRingHom,Polynomial.eval_add,
        Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  rw [hforms] at hm
  calc
    (H a b d p n).eval y =
        MvPolynomial.eval (fun i : Fin 2 => if i=0 then a+b*y else d*(1+y))
          (p.homogenize n) := by
      exact hm
    _ = p.eval (T a b d y)*(d*(1+y))^n := by
      simpa [T] using
        (Polynomial.eval_homogenize hn
          (fun i : Fin 2 => if i=0 then a+b*y else d*(1+y)) hd)

theorem H_mul (a b d : Real) (p q : Polynomial Real) (m n : Nat)
    (hp : p.natDegree≤m) (hq : q.natDegree≤n) :
    H a b d (p*q) (m+n)=H a b d p m*H a b d q n := by
  simp only [H,Polynomial.homogenize_mul p q hp hq,map_mul]

theorem H_pow (a b d : Real) (p : Polynomial Real) (n : Nat)
    (hp : p.natDegree≤n) (m : Nat) :
    H a b d (p^m) (m*n)=(H a b d p n)^m := by
  induction m with
  | zero => simp [H,Polynomial.homogenize_one,forms]
  | succ m ih =>
    rw [pow_succ,Nat.succ_mul,H_mul a b d (p^m) p (m*n) n
      (Polynomial.natDegree_pow_le_of_le m hp) hp,ih,pow_succ]

theorem H_linear (a b d r : Real) :
    H a b d (Polynomial.X-Polynomial.C r) 1 =
      Polynomial.C (a-d*r)+Polynomial.C (b-d*r)*Polynomial.X := by
  unfold H
  rw [Polynomial.homogenize_sub,Polynomial.homogenize_X (by decide : 1≠0),
    Polynomial.homogenize_C]
  simp only [Nat.sub_self,pow_zero,mul_one,pow_one,map_sub,map_mul,
    MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C]
  simp [forms,Polynomial.C_sub,Polynomial.C_mul]
  <;> ring

/-- The actual integer source-tree transform is the same real homogeneous polynomial. -/
theorem tree_map_eq_H (a b d : Int) (t : CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.Tree)
    (hw : CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.WellFormed t) (p : Polynomial Int)
    (hdegree : p.natDegree<(CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t).length)
    (hleaves : CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t=
      CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffRange p (CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t).length)
    (hd : (0 : Real)<d) :
    (CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.mobiusExpr a b d t).poly.map (Int.castRingHom Real) =
      H a b d (p.map (Int.castRingHom Real)) ((CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t).length-1) := by
  have hn : (p.map (Int.castRingHom Real)).natDegree≤(CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t).length-1 :=
    Polynomial.natDegree_map_le.trans (by omega)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : Real)).mono
  intro y hy
  change 0<y at hy
  change ((CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.mobiusExpr a b d t).poly.map (Int.castRingHom Real)).eval y =
    (H a b d (p.map (Int.castRingHom Real)) ((CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial.coeffs t).length-1)).eval y
  have hden : (d : Real)*(1+y)≠0 := mul_ne_zero (ne_of_gt hd) (ne_of_gt (by linarith))
  have heq : (d : Real)+(d : Real)*y=(d : Real)*(1+y) := by ring
  rw [Polynomial.eval_map,H_eval a b d _ _ hn y hden,Polynomial.eval_map]
  have hm := mobius_eval a b d t hw p hdegree hleaves y (by rwa [heq])
  rw [heq] at hm
  simpa only [T,mul_comm] using hm

/-- A nonzero real polynomial remains nonzero under this interval transform. -/
theorem H_ne_zero (a b d : Real) (hab : a<b) (hd : 0<d)
    (p : Polynomial Real) (hp : p≠0) (n : Nat) (hn : p.natDegree≤n) :
    H a b d p n≠0 := by
  intro hz
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  have habd : a/d<b/d := (div_lt_div_iff_of_pos_right hd).mpr hab
  apply (Set.Ioo_infinite habd).mono
  intro x hx
  have hu := U_pos a b d x hd hx
  have hden : d*(1+U a b d x)≠0 :=
    mul_ne_zero (ne_of_gt hd) (ne_of_gt (by linarith))
  have he := H_eval a b d p n hn (U a b d x) hden
  rw [hz,Polynomial.eval_zero,T_U a b d x hab hd hx] at he
  exact (mul_eq_zero.mp he.symm).resolve_right (pow_ne_zero _ hden)

/-- Root multiplicities are transported over REALS, not merely over the rationals. -/
theorem rootMultiplicity_H (a b d : Real) (hab : a<b) (hd : 0<d)
    (p : Polynomial Real) (hp : p≠0) (n : Nat) (hn : p.natDegree≤n)
    (r : Real) (hr : a/d<r ∧ r<b/d) :
    (H a b d p n).rootMultiplicity (U a b d r)=p.rootMultiplicity r := by
  classical
  let m := p.rootMultiplicity r
  obtain ⟨g,hfact,hnot⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  have hg : g.eval r≠0 := by
    intro he
    exact hnot (Polynomial.dvd_iff_isRoot.mpr he)
  have hg0 : g≠0 := by intro he; apply hg; rw [he,Polynomial.eval_zero]
  have hdeg : p.natDegree=m+g.natDegree := by
    rw [hfact,Polynomial.natDegree_mul
      (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero r)) hg0,
      Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C]
    simp only [Nat.mul_one,m]
  have hmn : m≤n := by omega
  have hgn : g.natDegree≤n-m := by omega
  have hpower : ((Polynomial.X-Polynomial.C r)^m : Polynomial Real).natDegree≤m := by
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,Nat.mul_one]
    exact le_rfl
  let u := U a b d r
  let s := b-d*r
  have hs : 0<s := by
    have hh := (lt_div_iff₀ hd).mp hr.2
    dsimp [s]
    nlinarith
  have hsu : s*u=d*r-a := by
    dsimp [s,u,U]
    exact mul_div_cancel₀ _ (ne_of_gt hs)
  have hlin : H a b d (Polynomial.X-Polynomial.C r) 1 =
      Polynomial.C s*(Polynomial.X-Polynomial.C u) := by
    rw [H_linear]
    have hc : a-d*r=-(s*u) := by linarith
    rw [hc]
    dsimp [s]
    simp only [Polynomial.C_neg,Polynomial.C_mul]
    ring
  have hu : 0<u := U_pos a b d r hd hr
  have hden : d*(1+u)≠0 := mul_ne_zero (ne_of_gt hd) (ne_of_gt (by linarith))
  have hge : (H a b d g (n-m)).eval u≠0 := by
    rw [H_eval a b d g (n-m) hgn u hden]
    have he : T a b d u=r := T_U a b d r hab hd hr
    rw [he]
    exact mul_ne_zero hg (pow_ne_zero _ hden)
  have hq0 : H a b d g (n-m)≠0 := by
    intro he
    apply hge
    rw [he,Polynomial.eval_zero]
  have hbase : Polynomial.C (s^m)*H a b d g (n-m)≠0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ (ne_of_gt hs))) hq0
  have hbaseEval : (Polynomial.C (s^m)*H a b d g (n-m)).eval u≠0 := by
    rw [Polynomial.eval_mul,Polynomial.eval_C]
    exact mul_ne_zero (pow_ne_zero _ (ne_of_gt hs)) hge
  have hwhole : H a b d p n =
      (Polynomial.C (s^m)*H a b d g (n-m))*(Polynomial.X-Polynomial.C u)^m := by
    calc
      H a b d p n = H a b d ((Polynomial.X-Polynomial.C r)^m*g) (m+(n-m)) := by
        rw [Nat.add_sub_of_le hmn]
        exact congrArg (fun q => H a b d q n) hfact
      _ = H a b d ((Polynomial.X-Polynomial.C r)^m) m*H a b d g (n-m) :=
        H_mul a b d _ _ m (n-m) hpower hgn
      _ = _ := by
        have hh := H_pow a b d (Polynomial.X-Polynomial.C r) 1
          (Polynomial.natDegree_X_sub_C_le r) m
        simp only [Nat.mul_one] at hh
        rw [hh,hlin,mul_pow]
        rw [← map_pow (Polynomial.C : Real →+* Polynomial Real) s m]
        ring
  rw [hwhole,Polynomial.rootMultiplicity_mul_X_sub_C_pow hbase,
    Polynomial.rootMultiplicity_eq_zero hbaseEval,zero_add]

#print axioms H_eval
#print axioms tree_map_eq_H
#print axioms H_ne_zero
#print axioms rootMultiplicity_H
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusMultiplicity

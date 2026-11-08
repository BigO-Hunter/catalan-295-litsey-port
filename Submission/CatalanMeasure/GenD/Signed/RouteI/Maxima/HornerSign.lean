module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic soundness only (no data); sign checks themselves are instance work
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign
noncomputable section
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal

/-- Homogeneous Horner value: the integer `Σ c_j p^j q^(n-j)` with `n+1` coefficients,
ascending list. -/
def hornerQ (q p : Int) : List Int → Int
  | [] => 0
  | c::cs => hornerQ q p cs*p+c*q^cs.length

/-- The exact fold shape used by `RootSignProbe`/`XRootSignProbe` (weights `2^(80 k)`). -/
def probeEval (s : Nat) (cs : List Int) (p : Int) : Int :=
  (cs.reverse.foldl (fun (st : Int × Nat) c => (st.1*p+c*(2 : Int)^st.2,st.2+s)) (0,0)).1

theorem foldl_state_snd (s : Nat) (cs : List Int) (k : Nat) (a : Int) (p : Int) :
    (cs.foldl (fun (st : Int × Nat) c => (st.1*p+c*(2 : Int)^st.2,st.2+s)) (a,k)).2
      =k+s*cs.length := by
  induction cs generalizing a k with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons,ih,List.length_cons]
    ring

theorem probeEval_eq_hornerQ (s : Nat) (cs : List Int) (p : Int) :
    probeEval s cs p=hornerQ ((2 : Int)^s) p cs := by
  induction cs with
  | nil => simp [probeEval,hornerQ]
  | cons c cs ih =>
    have h : probeEval s (c::cs) p=probeEval s cs p*p+c*(2 : Int)^(s*cs.length) := by
      simp only [probeEval,List.reverse_cons,List.foldl_append,List.foldl_cons,
        List.foldl_nil]
      rw [foldl_state_snd s cs.reverse 0 0 p]
      simp only [List.length_reverse,Nat.zero_add]
    rw [h,ih,hornerQ,pow_mul]

/-- A homogeneous Horner value is `q^len/q` times the real evaluation at `p/q`. -/
theorem hornerQ_real (q p : Int) (hq : q≠0) (cs : List Int) :
    (hornerQ q p cs : Real)=(q : Real)^cs.length*evalList ((p : Real)/q) cs/q := by
  have hq' : (q : Real)≠0 := by exact_mod_cast hq
  induction cs with
  | nil => simp [hornerQ,evalList]
  | cons c cs ih =>
    simp only [hornerQ,evalList,List.length_cons]
    push_cast
    rw [ih]
    field_simp
    ring

theorem hornerQ_real_eval (q p : Int) (hq : q≠0) (P : Polynomial Int) (n : Nat)
    (hn : P.natDegree<n) :
    (hornerQ q p (coeffRange P n) : Real)=
      (q : Real)^n*((P.map (Int.castRingHom Real)).eval ((p : Real)/q))/q := by
  rw [hornerQ_real q p hq,evalList_coeffRange P hn,Polynomial.eval_map]
  simp [coeffRange]

theorem eval_sign_of_horner (q p : Int) (hq : 0<q) (P : Polynomial Int) (n : Nat)
    (hn : P.natDegree<n) :
    (0<hornerQ q p (coeffRange P n) ↔ 0<(P.map (Int.castRingHom Real)).eval ((p : Real)/q)) ∧
    (hornerQ q p (coeffRange P n)<0 ↔ (P.map (Int.castRingHom Real)).eval ((p : Real)/q)<0) ∧
    (hornerQ q p (coeffRange P n)=0 ↔ (P.map (Int.castRingHom Real)).eval ((p : Real)/q)=0) := by
  have hq' : (0 : Real)<q := by exact_mod_cast hq
  have hf := hornerQ_real_eval q p hq.ne' P n hn
  have hpos : (0 : Real)<(q : Real)^n/q := by positivity
  set E := (P.map (Int.castRingHom Real)).eval ((p : Real)/q)
  have hh : (hornerQ q p (coeffRange P n) : Real)=((q : Real)^n/q)*E := by
    rw [hf]; ring
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro h
      have h' : (0 : Real)<(hornerQ q p (coeffRange P n) : Real) := by exact_mod_cast h
      rw [hh] at h'
      exact pos_of_mul_pos_right h' hpos.le
    · intro h
      have : (0 : Real)<(hornerQ q p (coeffRange P n) : Real) := by rw [hh]; positivity
      exact_mod_cast this
  · constructor
    · intro h
      have h' : (hornerQ q p (coeffRange P n) : Real)<0 := by exact_mod_cast h
      rw [hh] at h'
      exact neg_of_mul_neg_right h' hpos.le
    · intro h
      have : (hornerQ q p (coeffRange P n) : Real)<0 := by
        rw [hh]; exact mul_neg_of_pos_of_neg hpos h
      exact_mod_cast this
  · constructor
    · intro h
      have h' : (hornerQ q p (coeffRange P n) : Real)=0 := by exact_mod_cast h
      rw [hh] at h'
      exact (mul_eq_zero.mp h').resolve_left hpos.ne'
    · intro h
      have : (hornerQ q p (coeffRange P n) : Real)=0 := by rw [hh,h,mul_zero]
      exact_mod_cast this

/-- Opposite signs at two integer numerators over the same positive denominator. -/
theorem bracket_sign_sound (q l r : Int) (hq : 0<q) (P : Polynomial Int) (n : Nat)
    (hn : P.natDegree<n)
    (hcheck : hornerQ q l (coeffRange P n)*hornerQ q r (coeffRange P n)<0) :
    (P.map (Int.castRingHom Real)).eval ((l : Real)/q)*
      (P.map (Int.castRingHom Real)).eval ((r : Real)/q)<0 := by
  have hq' : (0 : Real)<q := by exact_mod_cast hq
  have hl := hornerQ_real_eval q l hq.ne' P n hn
  have hr := hornerQ_real_eval q r hq.ne' P n hn
  have hc : (hornerQ q l (coeffRange P n) : Real)*hornerQ q r (coeffRange P n)<0 := by
    exact_mod_cast hcheck
  rw [hl,hr] at hc
  have hpos : (0 : Real)<((q : Real)^n/q)*((q : Real)^n/q) := by positivity
  have : ((q : Real)^n/q)*((q : Real)^n/q)*
      ((P.map (Int.castRingHom Real)).eval ((l : Real)/q)*
        (P.map (Int.castRingHom Real)).eval ((r : Real)/q))<0 := by
    have e : (q : Real)^n*(P.map (Int.castRingHom Real)).eval ((l : Real)/q)/q*
        ((q : Real)^n*(P.map (Int.castRingHom Real)).eval ((r : Real)/q)/q)=
        ((q : Real)^n/q)*((q : Real)^n/q)*
        ((P.map (Int.castRingHom Real)).eval ((l : Real)/q)*
          (P.map (Int.castRingHom Real)).eval ((r : Real)/q)) := by ring
    rw [← e]; exact hc
  exact neg_of_mul_neg_right this hpos.le

/-- Nonzero cut: a nonzero Horner value gives a nonroot at the rational cut. -/
theorem cut_nonroot_sound (q c : Int) (hq : 0<q) (P : Polynomial Int) (n : Nat)
    (hn : P.natDegree<n) (hcheck : hornerQ q c (coeffRange P n)≠0) :
    (P.map (Int.castRingHom Real)).eval ((c : Real)/q)≠0 := fun h =>
  hcheck ((eval_sign_of_horner q c hq P n hn).2.2.mpr h)

#print axioms probeEval_eq_hornerQ
#print axioms hornerQ_real_eval
#print axioms eval_sign_of_horner
#print axioms bracket_sign_sound
#print axioms cut_nonroot_sound
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign

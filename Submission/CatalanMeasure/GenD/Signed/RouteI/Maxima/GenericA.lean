module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public meta import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic structural lemmas, no data
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
  CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign CatalanMeasure.CellCert

/-! ### integer leaves of rational poles -/

def leafOfPole (q : PoleR) : Leaf :=
  ⟨q.rr.num*(q.ri.den : Int),q.ri.num*(q.rr.den : Int),q.pr.num*(q.pi.den : Int),
    q.pi.num*(q.pr.den : Int),((q.pr.den : Int)*(q.pi.den : Int)),
    ((q.rr.den : Int)*(q.ri.den : Int))⟩

theorem rat_over (a b : Rat) :
    (((a.num*(b.den : Int) : Int) : Rat))/(((a.den : Int)*(b.den : Int) : Int) : Rat)=a := by
  have ha : (a.den : Rat)≠0 := by exact_mod_cast a.den_nz
  have hb : (b.den : Rat)≠0 := by exact_mod_cast b.den_nz
  push_cast
  rw [mul_div_mul_right _ _ hb]
  exact Rat.num_div_den a

theorem leafOfPole_pole (q : PoleR) : (leafOfPole q).pole=q := by
  obtain ⟨rr,ri,pr,pi⟩ := q
  have h1 := rat_over rr ri
  have h2 := rat_over ri rr
  have h3 := rat_over pr pi
  have h4 := rat_over pi pr
  simp only [leafOfPole,Leaf.pole]
  rw [mul_comm (ri.den : Int) (rr.den : Int)] at h2
  rw [mul_comm (pi.den : Int) (pr.den : Int)] at h4
  simp only [PoleR.mk.injEq]
  exact ⟨h1,h2,h3,h4⟩

/-! ### balanced pole trees -/

def flatLeaves (l : List PoleTree) : List Leaf := l.flatMap PoleTree.leaves

theorem pairUp_flat : ∀ l : List PoleTree, flatLeaves (pairUp l)=flatLeaves l
  | [] => rfl
  | [a] => rfl
  | a::b::rest => by
    have ih := pairUp_flat rest
    simp only [pairUp,flatLeaves,List.flatMap_cons,PoleTree.leaves,List.append_assoc] at ih ⊢
    rw [ih]

theorem pairUp_length : ∀ l : List PoleTree, (pairUp l).length=(l.length+1)/2
  | [] => rfl
  | [a] => by simp [pairUp]
  | a::b::rest => by
    have ih := pairUp_length rest
    simp only [pairUp,List.length_cons] at ih ⊢
    omega

theorem buildPT_leaves : ∀ (f : Nat) (l : List PoleTree), l≠[] → l.length≤2^f →
    (buildPT f l).leaves=flatLeaves l := by
  intro f
  induction f with
  | zero =>
    intro l hne hlen
    match l, hne, hlen with
    | [a],_,_ => simp [buildPT,flatLeaves]
    | _::_::_,_,h => simp at h
  | succ f ih =>
    intro l hne hlen
    have hp : pairUp l≠[] := by
      intro h
      have := pairUp_length l
      rw [h] at this
      cases l with
      | nil => exact hne rfl
      | cons a t => simp at this; omega
    have hl : (pairUp l).length≤2^f := by
      rw [pairUp_length]
      rw [pow_succ] at hlen
      omega
    rw [buildPT,ih _ hp hl,pairUp_flat]

theorem buildPT_leaves_map (f : Nat) (ls : List Leaf) (hne : ls≠[]) (hlen : ls.length≤2^f) :
    (buildPT f (ls.map PoleTree.leaf)).leaves=ls := by
  have h := buildPT_leaves f (ls.map PoleTree.leaf) (by simpa using hne) (by simpa using hlen)
  rw [h]
  have key : ∀ l : List Leaf, flatLeaves (l.map PoleTree.leaf)=l := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp only [flatLeaves, List.map_cons, List.flatMap_cons, PoleTree.leaves, List.singleton_append] at ih ⊢; rw [ih]
  exact key ls

/-! ### coefficient lists, polynomial and Horner expression -/

noncomputable def listPoly : List Int → Polynomial Int
  | [] => 0
  | c::cs => Polynomial.C c+Polynomial.X*listPoly cs

theorem listPoly_coeff : ∀ (cs : List Int) (i : Nat), (listPoly cs).coeff i=cs.getD i 0
  | [],i => by simp [listPoly]
  | c::cs,0 => by simp [listPoly]
  | c::cs,i+1 => by
    simp only [listPoly,Polynomial.coeff_add,Polynomial.coeff_C_succ,zero_add,
      Polynomial.coeff_X_mul,List.getD_cons_succ]
    exact listPoly_coeff cs i

theorem listPoly_natDegree_lt (cs : List Int) (hne : cs≠[]) :
    (listPoly cs).natDegree<cs.length := by
  have hpos : 0<cs.length := List.length_pos_of_ne_nil hne
  have : (listPoly cs).natDegree≤cs.length-1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [listPoly_coeff]
    exact List.getD_eq_default _ _ (by omega)
  omega

theorem coeffRange_listPoly (cs : List Int) :
    coeffRange (listPoly cs) cs.length=cs := by
  apply List.ext_getElem
  · simp [coeffRange]
  · intro i h1 h2
    simp [coeffRange,listPoly_coeff,List.getD_eq_getElem?_getD,h2]

theorem hornerExpr_poly : ∀ cs : List Int, (hornerExpr cs).poly=listPoly cs
  | [] => by simp [hornerExpr,Expr.poly,listPoly]
  | c::cs => by simp [hornerExpr,Expr.poly,listPoly,hornerExpr_poly cs]

theorem hornerExpr_degree : ∀ cs : List Int, (hornerExpr cs).degree=cs.length
  | [] => rfl
  | c::cs => by
    simp only [hornerExpr,Expr.degree,hornerExpr_degree cs,List.length_cons]
    omega

/-! ### balanced coefficient trees -/

theorem buildTree_spec : ∀ (f : Nat) (cs : List Int), cs≠[] → cs.length≤2^f →
    coeffs (buildTree f cs)=cs ∧ WellFormed (buildTree f cs) := by
  intro f
  induction f with
  | zero =>
    intro cs hne hlen
    match cs, hne, hlen with
    | [a],_,_ => simp [buildTree,coeffs,WellFormed]
    | _::_::_,_,h => simp at h
  | succ f ih =>
    intro cs hne hlen
    by_cases h1 : cs.length≤1
    · match cs, hne, h1 with
      | [a],_,_ => simp [buildTree,coeffs,WellFormed]
      | _::_::_,_,h => simp at h
    · have hlt : 2≤cs.length := by omega
      have hh : cs.length/2≤2^f := by rw [pow_succ] at hlen; omega
      have hr : cs.length-cs.length/2≤2^f := by rw [pow_succ] at hlen; omega
      have hne1 : cs.take (cs.length/2)≠[] := List.ne_nil_of_length_pos (by simp; omega)
      have hne2 : cs.drop (cs.length/2)≠[] := List.ne_nil_of_length_pos (by simp; omega)
      obtain ⟨c1,w1⟩ := ih _ hne1 (by simp; omega)
      obtain ⟨c2,w2⟩ := ih _ hne2 (by simp; omega)
      simp only [buildTree,h1,ite_false]
      have l1 : (coeffs (buildTree f (cs.take (cs.length/2)))).length=cs.length/2 := by
        rw [c1]; simp; omega
      have l2 : (coeffs (buildTree f (cs.drop (cs.length/2)))).length=cs.length-cs.length/2 := by
        rw [c2]; simp
      refine ⟨?_,?_⟩
      · simp only [coeffs,c1,c2,List.take_append_drop]
      · exact ⟨l1.symm,l2.symm,w1,w2⟩

theorem listPoly_append : ∀ (a b : List Int),
    listPoly (a++b)=listPoly a+Polynomial.X^a.length*listPoly b
  | [],b => by simp [listPoly]
  | c::a,b => by
    simp only [List.cons_append,listPoly,List.length_cons,listPoly_append a b,pow_succ]
    ring

theorem homExpr_poly_X : ∀ t : Tree,WellFormed t → (homExpr .x (.c 1) t).poly=listPoly (coeffs t)
  | .leaf c,_ => by simp [homExpr,Expr.poly,coeffs,listPoly]
  | .node nl nr l r,h => by
    obtain ⟨hl,hr,wl,wr⟩ := h
    simp only [homExpr,Expr.poly,coeffs,listPoly_append,homExpr_poly_X l wl,
      homExpr_poly_X r wr,hl]
    simp

theorem treeExpr_poly (cs : List Int) (hne : cs≠[]) (hlen : cs.length≤512) :
    (treeExpr cs).poly=listPoly cs := by
  have h := buildTree_spec 9 cs hne (by simpa using hlen)
  unfold treeExpr
  rw [homExpr_poly_X _ h.2,h.1]

/-! ### homogeneous Horner by a running weight -/

theorem fold_snd (q p : Int) (L : List Int) (a w : Int) :
    (L.foldl (fun (st : Int × Int) c => (st.1*p+c*st.2,st.2*q)) (a,w)).2=w*q^L.length := by
  induction L generalizing a w with
  | nil => simp
  | cons c L ih =>
    simp only [List.foldl_cons,ih,List.length_cons]
    ring

theorem hornerF_eq (q p : Int) (cs : List Int) : hornerF q p cs=hornerQ q p cs := by
  induction cs with
  | nil => simp [hornerF,hornerQ]
  | cons c cs ih =>
    have h : hornerF q p (c::cs)=hornerF q p cs*p+c*q^cs.length := by
      simp only [hornerF,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [fold_snd q p cs.reverse 0 1]
      simp only [List.length_reverse,one_mul]
    rw [h,ih,hornerQ]

/-! ### cancelled linear factors at a rational point -/

theorem cancel_eval (q l : Int) (hq : 0<q) (fs : List (Int × Int)) :
    reval (cancelPoly fs) ((l : Real)/q)=(cancelProd q l fs : Real)/(q : Real)^fs.length := by
  have hq' : (q : Real)≠0 := by exact_mod_cast hq.ne'
  induction fs with
  | nil => simp [cancelPoly,cancelProd,reval]
  | cons f fs ih =>
    obtain ⟨a,d⟩ := f
    simp only [cancelPoly,reval_mul,reval_sub,reval_C,reval_X,ih,cancelProd,List.map_cons,
      List.prod_cons,List.length_cons,pow_succ]
    push_cast
    field_simp

theorem cancel_sign (q l : Int) (hq : 0<q) (fs : List (Int × Int)) :
    (cancelProd q l fs<0 ↔ reval (cancelPoly fs) ((l : Real)/q)<0) ∧
    (cancelProd q l fs≠0 ↔ reval (cancelPoly fs) ((l : Real)/q)≠0) := by
  have hq' : (0 : Real)<q := by exact_mod_cast hq
  have hp : (0 : Real)<(q : Real)^fs.length := by positivity
  rw [cancel_eval q l hq]
  refine ⟨?_,?_⟩
  · rw [div_neg_iff]
    constructor
    · intro h
      right
      exact ⟨by exact_mod_cast h,hp⟩
    · rintro (⟨_,h2⟩ | ⟨h1,_⟩)
      · exact absurd h2 (not_lt.mpr hp.le)
      · exact_mod_cast h1
  · constructor
    · intro h h0
      apply h
      have := (div_eq_zero_iff.mp h0).resolve_right hp.ne'
      exact_mod_cast this
    · intro h h0
      apply h
      rw [h0]; simp

#print axioms leafOfPole_pole
#print axioms buildPT_leaves_map
#print axioms coeffRange_listPoly
#print axioms hornerExpr_poly
#print axioms treeExpr_poly
#print axioms hornerExpr_degree
#print axioms buildTree_spec
#print axioms hornerF_eq
#print axioms cancel_sign
end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA

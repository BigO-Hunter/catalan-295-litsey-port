module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic composition only; per-cell decode counts and Horner sign checks are instance work
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding
noncomputable section
open Set CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusReal CatalanMeasure.GenD.Signed.RouteI.Maxima.MobiusMultiplicity
  CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover CatalanMeasure.GenD.Signed.RouteI.Maxima.HornerSign

def cellReal (c : Cell) : Real × Real := ((c.a : Real)/c.d,(c.b : Real)/c.d)

/-- All premises of one cell count: the source polynomial `P` is the leaf list of the
tree, the transformed expression fits the packing guard, and the descending decoded
sign-variation count is `v`. -/
def CellCert (k : Int) (P : Polynomial Int) (c : Cell) (t : Tree) (n v : Nat) : Prop :=
  0<c.d ∧ c.a<c.b ∧ WellFormed t ∧ P.natDegree<(coeffs t).length ∧
  coeffs t=coeffRange P (coeffs t).length ∧
  (mobiusExpr c.a c.b c.d t).degree<n ∧
  ((mobiusExpr c.a c.b c.d t).mass : Int)<k ∧
  decodedVariations (2*k) n ((mobiusExpr c.a c.b c.d t).eval (2*k))=v

theorem map_ne_zero (P : Polynomial Int) (hP : P≠0) :
    P.map (Int.castRingHom Real)≠0 := fun h =>
  hP ((Polynomial.map_eq_zero_iff (RingHom.injective_int (Int.castRingHom Real))).mp h)

/-- One cell: distinct REAL roots in the open cell are at most the decoded count. -/
theorem cell_count {k : Int} (hk : 0<k) (P : Polynomial Int) (hP : P≠0) (c : Cell)
    (t : Tree) (n v : Nat) (h : CellCert k P c t n v) :
    (rootSet (P.map (Int.castRingHom Real))
      (Ioo ((c.a : Real)/c.d) ((c.b : Real)/c.d))).card≤v := by
  obtain ⟨hd,hab,hw,hdeg,hleaves,hdegn,hmass,hcheck⟩ := h
  have hdR : (0 : Real)<c.d := by exact_mod_cast hd
  have habR : (c.a : Real)<c.b := by exact_mod_cast hab
  have hn : (P.map (Int.castRingHom Real)).natDegree≤(coeffs t).length-1 :=
    Polynomial.natDegree_map_le.trans (by omega)
  have h1 := interval_card_le_positive_roots (c.a : Real) (c.b : Real) (c.d : Real) habR hdR
    _ (map_ne_zero P hP) _ hn
  rw [← tree_map_eq_H c.a c.b c.d t hw P hdeg hleaves hdR] at h1
  exact h1.trans (real_positive_roots_le_expression hk _ n hdegn hmass v hcheck)

/-- A chain of cells with nonroot internal cuts: distinct roots in `(A,B)` are bounded by the
sum of the decoded counts. Cut nonroots are required only for cuts other than `B`. -/
theorem cover_count (k : Nat → Int) (hk : ∀ i,0<k i) (P : Polynomial Int) (hP : P≠0) (A B : Real)
    (cs : List Cell) (tr : Fin cs.length → Tree) (n v : Fin cs.length → Nat)
    (hchain : Chain A B (cs.map cellReal))
    (hcuts : ∀ c∈cs,(c.b : Real)/c.d≠B →
      (P.map (Int.castRingHom Real)).eval ((c.b : Real)/c.d)≠0)
    (hcert : ∀ i : Fin cs.length,CellCert (k i) P (cs.get i) (tr i) (n i) (v i)) :
    (rootSet (P.map (Int.castRingHom Real)) (Ioo A B)).card≤∑ i,v i := by
  classical
  apply cover_card_le_sum (P.map (Int.castRingHom Real)) (map_ne_zero P hP) (Ioo A B)
    Finset.univ
    (fun i => Ioo (((cs.get i).a : Real)/(cs.get i).d) (((cs.get i).b : Real)/(cs.get i).d)) v
  · intro x hx hroot
    have hcuts' : ∀ c∈cs.map cellReal,c.2≠B →
        (P.map (Int.castRingHom Real)).eval c.2≠0 := by
      intro c hc hne
      obtain ⟨c0,hc0,rfl⟩ := List.mem_map.mp hc
      exact hcuts c0 hc0 hne
    obtain ⟨c,hc,hxc⟩ := chain_covers_roots (P.map (Int.castRingHom Real)) A B
      (cs.map cellReal) hchain hcuts' x hx hroot
    obtain ⟨c0,hc0,rfl⟩ := List.mem_map.mp hc
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hc0
    subst hi
    exact ⟨i,Finset.mem_univ _,hxc⟩
  · intro i _
    exact cell_count (hk i) P hP _ _ _ _ (hcert i)

theorem brackets_disjoint (q : Int) (hq : 0<q) (N : Nat) (l r : Fin N → Int)
    (hord : ∀ i j,i<j → r i<l j) :
    ∀ i j,i≠j → Disjoint (Icc ((l i : Real)/q) ((r i : Real)/q))
      (Icc ((l j : Real)/q) ((r j : Real)/q)) := by
  have hq' : (0 : Real)<q := by exact_mod_cast hq
  have key : ∀ i j : Fin N,i<j → Disjoint (Icc ((l i : Real)/q) ((r i : Real)/q))
      (Icc ((l j : Real)/q) ((r j : Real)/q)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have h1 : (r i : Real)<l j := by exact_mod_cast hord i j hij
    have h2 : (r i : Real)/q<(l j : Real)/q := (div_lt_div_iff_of_pos_right hq').mpr h1
    linarith [hxi.2,hxj.1]
  intro i j hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- Terminal cover theorem: decoded counts summing to `N`, plus `N` ordered integer brackets
over denominator `q` with Horner sign changes, saturate: every distinct root in `(A,B)`
is the unique root of exactly one bracket, and no bracket has an extra root.
No simplicity of roots is claimed. -/
theorem root_cover_saturation (k : Nat → Int) (hk : ∀ i,0<k i) (P : Polynomial Int) (hP : P≠0)
    (A B : Real) (cs : List Cell) (tr : Fin cs.length → Tree) (n v : Fin cs.length → Nat)
    (hchain : Chain A B (cs.map cellReal))
    (hcuts : ∀ c∈cs,(c.b : Real)/c.d≠B →
      (P.map (Int.castRingHom Real)).eval ((c.b : Real)/c.d)≠0)
    (hcert : ∀ i : Fin cs.length,CellCert (k i) P (cs.get i) (tr i) (n i) (v i))
    (q : Int) (hq : 0<q) (N : Nat) (hN : ∑ i,v i=N) (l r : Fin N → Int)
    (m : Nat) (hm : P.natDegree<m)
    (hlr : ∀ i,l i<r i) (hord : ∀ i j,i<j → r i<l j)
    (hA : ∀ i,A<(l i : Real)/q) (hB : ∀ i,(r i : Real)/q<B)
    (hsign : ∀ i,hornerQ q (l i) (coeffRange P m)*hornerQ q (r i) (coeffRange P m)<0) :
    ∃ rho : Fin N → Real,
      (∀ i,rho i∈Ioo ((l i : Real)/q) ((r i : Real)/q) ∧
        (P.map (Int.castRingHom Real)).IsRoot (rho i)) ∧
      Function.Injective rho ∧
      (∀ x∈Ioo A B,(P.map (Int.castRingHom Real)).IsRoot x → ∃ i,x=rho i) ∧
      (∀ i x,x∈Icc ((l i : Real)/q) ((r i : Real)/q) →
        (P.map (Int.castRingHom Real)).IsRoot x → x=rho i) := by
  have hq' : (0 : Real)<q := by exact_mod_cast hq
  have hupper : (rootSet (P.map (Int.castRingHom Real)) (Ioo A B)).card≤N :=
    hN ▸ cover_count k hk P hP A B cs tr n v hchain hcuts hcert
  apply bracket_saturation (P.map (Int.castRingHom Real)) (map_ne_zero P hP) (Ioo A B) N
    (fun i => (l i : Real)/q) (fun i => (r i : Real)/q)
  · intro i
    have : (l i : Real)<r i := by exact_mod_cast hlr i
    exact (div_lt_div_iff_of_pos_right hq').mpr this
  · intro i
    exact bracket_sign_sound q (l i) (r i) hq P m hm (hsign i)
  · intro i x hx
    exact ⟨(hA i).trans_le hx.1,hx.2.trans_lt (hB i)⟩
  · exact brackets_disjoint q hq N l r hord
  · exact hupper

#print axioms cell_count
#print axioms cover_count
#print axioms brackets_disjoint
#print axioms root_cover_saturation
end
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding

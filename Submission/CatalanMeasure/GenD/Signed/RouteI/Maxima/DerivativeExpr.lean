module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: generic Expr representations + packed polynomial identity; instance data not included
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.CellCert CatalanMeasure.Cert

theorem leafNumExpr_poly (r : Leaf) : (leafNumExpr r).poly=r.num := by
  simp [leafNumExpr,Expr.poly,Leaf.num]

theorem leafDenExpr_poly (r : Leaf) : (leafDenExpr r).poly=r.den := by
  simp [leafDenExpr,Expr.poly,Leaf.den]

theorem pairExpr_poly (t : PoleTree) :
    (pairExpr t).1.poly=t.pair.1 ∧ (pairExpr t).2.poly=t.pair.2 := by
  induction t with
  | leaf r => exact ⟨leafNumExpr_poly r,leafDenExpr_poly r⟩
  | node l r ihl ihr =>
    simp only [pairExpr,PoleTree.pair,Expr.poly,ihl.1,ihl.2,ihr.1,ihr.2,and_self]

theorem zExpr_poly (Z : List Int) : (zExpr Z).poly=zPoly Z := by
  induction Z with
  | nil => simp [zExpr,zPoly,Expr.poly]
  | cons c cs ih => simp [zExpr,zPoly,Expr.poly,ih]

theorem fullNumExpr_poly (Z : List Int) (t : PoleTree) :
    (fullNumExpr Z t).poly=fullNum Z t := by
  simp only [fullNumExpr,fullNum,Expr.poly,zExpr_poly,(pairExpr_poly t).1,
    (pairExpr_poly t).2]

theorem cancelExpr_poly (fs : List (Int × Int)) : (cancelExpr fs).poly=cancelPoly fs := by
  induction fs with
  | nil => simp [cancelExpr,cancelPoly,Expr.poly]
  | cons f fs ih =>
    obtain ⟨a,d⟩ := f
    simp [cancelExpr,cancelPoly,Expr.poly,ih,sub_eq_add_neg]

theorem rhsExpr_poly (scale : Int) (eN : Expr) (fs : List (Int × Int)) :
    (rhsExpr scale eN fs).poly=Polynomial.C scale*(eN.poly*cancelPoly fs) := by
  simp only [rhsExpr,Expr.poly,cancelExpr_poly]

/-- Packed evaluation at `2k` of the full numerator and of scale*reduced*cancelled
factors proves the exact polynomial identity (guards by mass, degrees by `n`). -/
theorem full_identity_of_packed {k : Int} (hk : 0<k) (Z : List Int) (t : PoleTree)
    (eN : Expr) (fs : List (Int × Int)) (scale : Int) (n : Nat)
    (hdl : (fullNumExpr Z t).degree<n) (hdr : (rhsExpr scale eN fs).degree<n)
    (hml : ((fullNumExpr Z t).mass : Int)<k) (hmr : ((rhsExpr scale eN fs).mass : Int)<k)
    (hcheck : (fullNumExpr Z t).eval (2*k)=(rhsExpr scale eN fs).eval (2*k)) :
    fullNum Z t=Polynomial.C scale*(eN.poly*cancelPoly fs) := by
  have h := expression_eq_of_packed_eval hk _ _ n hdl hdr hml hmr hcheck
  rwa [fullNumExpr_poly,rhsExpr_poly] at h

theorem reval_eq_map_eval (P : Polynomial Int) (x : Real) :
    reval P x=(P.map (Int.castRingHom Real)).eval x := by
  rw [Polynomial.eval_map]; rfl

/-- Actual-binding derivative theorem: the packed identity transports derivative zeros of the
original (peel-free) field to REAL roots of the reduced Expr polynomial, on safe poles/factors. -/
theorem derivative_root_iff_packed {S : Spec} {D : PolyData} {F : Real → Real}
    (hS : S.Sound D F) (hpeel : S.peel=none) (t : PoleTree)
    (hpoles : S.poles=t.leaves.map Leaf.pole) (Z : List Int) (hZ : D.Z=Z)
    (eN : Expr) (fs : List (Int × Int)) (scale : Int)
    {k : Int} (hk : 0<k) (n : Nat)
    (hdl : (fullNumExpr Z t).degree<n) (hdr : (rhsExpr scale eN fs).degree<n)
    (hml : ((fullNumExpr Z t).mass : Int)<k) (hmr : ((rhsExpr scale eN fs).mass : Int)<k)
    (hcheck : (fullNumExpr Z t).eval (2*k)=(rhsExpr scale eN fs).eval (2*k))
    (hflags : ∀ r ∈ t.leaves,0<r.D ∧ 0<r.E ∧ SafePole r)
    (hfs : ∀ f ∈ fs,SafeFactor f) (hscale : scale≠0)
    {x : Real} (hx : x ∈ Set.Ioo (-1 : Real) 1) (h0 : x≠0) :
    deriv F x=0 ↔ (eN.poly.map (Int.castRingHom Real)).eval x=0 := by
  rw [← reval_eq_map_eval]
  exact source_root_binding_safe hS hpeel t hpoles Z hZ eN.poly fs scale
    (full_identity_of_packed hk Z t eN fs scale n hdl hdr hml hmr hcheck)
    hflags hfs hscale hx h0

#print axioms pairExpr_poly
#print axioms fullNumExpr_poly
#print axioms cancelExpr_poly
#print axioms full_identity_of_packed
#print axioms derivative_root_iff_packed
end CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr

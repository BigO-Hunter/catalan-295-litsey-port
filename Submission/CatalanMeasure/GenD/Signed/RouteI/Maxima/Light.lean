module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 0
-- Light definitions shared by the heavy-kernel instance checks (import closure ~ DescartesDecodeEM, no CatalanMeasure)
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative

structure Leaf where
  rr : Int
  ri : Int
  pr : Int
  pi : Int
  D : Int
  E : Int
  deriving DecidableEq

def SafePole (r : Leaf) : Prop := r.pi≠0 ∨ r.pr=0 ∨ r.D≤r.pr ∨ r.pr≤-r.D

inductive PoleTree where
  | leaf : Leaf → PoleTree
  | node : PoleTree → PoleTree → PoleTree

def PoleTree.leaves : PoleTree → List Leaf
  | .leaf r => [r]
  | .node l r => l.leaves++r.leaves

def SafeFactor (f : Int × Int) : Prop := 0<f.2 ∧ (f.1=0 ∨ f.2≤f.1 ∨ f.1≤-f.2)

instance : DecidablePred SafePole := fun r => by unfold SafePole; infer_instance
instance : DecidablePred SafeFactor := fun f => by unfold SafeFactor; infer_instance

end CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding
/-- A Mobius cell `(a/d, b/d)`, `x=(a+b y)/(d(1+y))`. -/
structure Cell where
  a : Int
  b : Int
  d : Int
end CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative

def leafNumExpr (r : Leaf) : Expr :=
  .add (.mul (.c (r.D*r.D*r.rr)) .x) (.c (-r.D*(r.rr*r.pr+r.ri*r.pi)))

def leafDenExpr (r : Leaf) : Expr :=
  .add (.add (.mul (.c (r.E*r.D*r.D)) (.pow .x 2)) (.mul (.c (-2*r.E*r.D*r.pr)) .x))
    (.c (r.E*(r.pr^2+r.pi^2)))

def pairExpr : PoleTree → Expr × Expr
  | .leaf r => (leafNumExpr r,leafDenExpr r)
  | .node l r =>
    (.add (.mul (pairExpr l).1 (pairExpr r).2) (.mul (pairExpr r).1 (pairExpr l).2),
      .mul (pairExpr l).2 (pairExpr r).2)

def zExpr : List Int → Expr
  | [] => .c 0
  | c::cs => .add (.c c) (.mul .x (zExpr cs))

def fullNumExpr (Z : List Int) (t : PoleTree) : Expr :=
  .add (.mul (.c 1099511627776) (pairExpr t).1) (.mul (zExpr Z) (pairExpr t).2)

def cancelExpr : List (Int × Int) → Expr
  | [] => .c 1
  | (a,d)::fs => .mul (.add (.mul (.c d) .x) (.c (-a))) (cancelExpr fs)

def rhsExpr (scale : Int) (eN : Expr) (fs : List (Int × Int)) : Expr :=
  .mul (.c scale) (.mul eN (cancelExpr fs))

end CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative

def pairUp : List PoleTree → List PoleTree
  | a::b::rest => PoleTree.node a b :: pairUp rest
  | l => l

def dflt : PoleTree := PoleTree.leaf ⟨0,0,0,0,1,1⟩

def buildPT : Nat → List PoleTree → PoleTree
  | 0,l => l.headD dflt
  | f+1,l => buildPT f (pairUp l)

def buildTree : Nat → List Int → Tree
  | 0,cs => .leaf (cs.headD 0)
  | f+1,cs => if cs.length≤1 then .leaf (cs.headD 0)
      else .node (cs.length/2) (cs.length-cs.length/2)
        (buildTree f (cs.take (cs.length/2))) (buildTree f (cs.drop (cs.length/2)))

def hornerF (q p : Int) (cs : List Int) : Int :=
  (cs.reverse.foldl (fun (st : Int × Int) c => (st.1*p+c*st.2,st.2*q)) (0,1)).1

def cancelProd (q l : Int) (fs : List (Int × Int)) : Int :=
  (fs.map (fun f => f.2*l-f.1*q)).prod

def hornerExpr : List Int → Expr
  | [] => .c 0
  | c::cs => .add (.c c) (.mul .x (hornerExpr cs))

/-- Balanced evaluation tree for a coefficient list: same polynomial as the Horner form but
the packed evaluation keeps only O(log n) levels of intermediate values. -/
def treeExpr (cs : List Int) : Expr := homExpr .x (.c 1) (buildTree 9 cs)

end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCoverBinding CatalanMeasure.GenD.Signed.RouteI.Maxima.DescartesDecode

def ratCell (c : Cell) : Rat × Rat := ((c.a : Rat)/c.d,(c.b : Rat)/c.d)

def cellExpr (cs : List Int) (c : Cell) : Expr := mobiusExpr c.a c.b c.d (buildTree 9 cs)

def cellK (cs : List Int) (c : Cell) : Int := ((cellExpr cs c).mass : Int)+1

def cellCheck (cs : List Int) (c : Cell) (v : Nat) : Bool :=
  decide (0<c.d) && decide (c.a<c.b) && decide ((cellExpr cs c).degree<cs.length) &&
  (decodedVariations (2*cellK cs c) cs.length ((cellExpr cs c).eval (2*cellK cs c)) == v) &&
  (decide (c.b=c.d) || decide (hornerF c.d c.b cs≠0))

def qB : Int := 2^80

def dI : Int := 2^30

def boxOK (l : Int) : Bool :=
  (decide (dI≤l) || decide (l+1≤-dI)) && decide (l+1≤qB-dI) && decide (-qB<l)

def bracketOK (cs : List Int) (l : Int) : Bool :=
  decide (hornerF qB l cs*hornerF qB (l+1) cs<0) && boxOK l

def keepB (cs : List Int) (fs : List (Int × Int)) (l : Int) : Bool :=
  decide (¬ (hornerF qB l cs*cancelProd qB l fs<0))

def midQ (l : Int) : Rat := ((2*l+1 : Int) : Rat)/2^81

def adj : List Int → Bool
  | a::b::rest => decide (a+1<b) && adj (b::rest)
  | _ => true

end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericC

namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD
open CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.PackedPolynomial CatalanMeasure.GenD.Signed.RouteI.Maxima.Derivative CatalanMeasure.GenD.Signed.RouteI.Maxima.DerivativeExpr CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericA

def packK (e1 e2 : Expr) : Int := ((max e1.mass e2.mass : Nat) : Int)+1

def PackOK (Z : List Int) (t : PoleTree) (cs : List Int) (scale : Int)
    (fs : List (Int × Int)) : Prop :=
  (fullNumExpr Z t).degree<467 ∧ (rhsExpr scale (treeExpr cs) fs).degree<467 ∧
  (fullNumExpr Z t).eval (2*packK (fullNumExpr Z t) (rhsExpr scale (treeExpr cs) fs))=
    (rhsExpr scale (treeExpr cs) fs).eval
      (2*packK (fullNumExpr Z t) (rhsExpr scale (treeExpr cs) fs))

instance (Z : List Int) (t : PoleTree) (cs : List Int) (scale : Int)
    (fs : List (Int × Int)) : Decidable (PackOK Z t cs scale fs) := by
  unfold PackOK; infer_instance

end CatalanMeasure.GenD.Signed.RouteI.Maxima.GenericD

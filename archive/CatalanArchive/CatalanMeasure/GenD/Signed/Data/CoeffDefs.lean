module

public import CatalanMeasure.GenD.Signed.TaylorCell

@[expose] public section

/-!
# Stage A cost (cost measurement only): total Taylor coefficients of an SN-type field cell

COST PILOT, no soundness theorem: the coefficient computations (exact Taylor shift of the polynomial
part, polynomial-times-log pieces `P(x) log|x-e|` with the log value supplied, and the pole sum by
`poleCoeff`) and the Boolean cell check are exactly the arithmetic the Phase 2 field checker performs.
Removed (or turned into the sound generic checker) at Stage C.
-/

namespace CatalanMeasure.GenD.Signed.Data
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

def toQ (n d : ℤ) : ℚ := (n : ℚ) / (d : ℚ)
def qlist (ns ds : List ℤ) : List ℚ := List.zipWith toQ ns ds

/-- running Horner values (high to low) -/
def runs (c : ℚ) : List ℚ → ℚ → List ℚ
  | [], _ => []
  | a :: as, prev => let b := a + c * prev; b :: runs c as b

/-- `M+1` Taylor coefficients at `c` of the polynomial with coefficients `a` listed high to low. -/
def taylorHL (c : ℚ) : ℕ → List ℚ → List ℚ
  | 0, a => [(runs c a 0).getLast?.getD 0]
  | M + 1, a =>
    let b := runs c a 0
    (b.getLast?.getD 0) :: taylorHL c M b.dropLast

def taylorQ (c : ℚ) (M : ℕ) (p : List ℚ) : List ℚ := taylorHL c M p.reverse

/-- Taylor coefficients (k = 0..M) of `P(x) log|x-e|` at `c`, `L = log|c-e|`. -/
def plogCoeffs (P : List ℚ) (e c L : ℚ) (M : ℕ) : List ℚ :=
  let Pk := taylorQ c M P
  let d := c - e
  (List.range (M + 1)).map fun k =>
    L * Pk.getD k 0 + ((List.range k).map fun j =>
      Pk.getD j 0 * ((-1 : ℚ) ^ (k - j - 1) / (((k - j : ℕ) : ℚ) * d ^ (k - j)))).sum

def addL : List ℚ → List ℚ → List ℚ
  | a :: as, b :: bs => (a + b) :: addL as bs
  | [], bs => bs
  | as, [] => as

/-- total Taylor coefficients `k = 0..M` of the field at `c` (each part computed once). -/
def ctot (poly : List ℚ) (es Ls : List ℚ) (Ps : List (List ℚ)) (poles : List PoleR) (c : ℚ)
    (M : ℕ) : List ℚ :=
  let pl := (List.zip es (List.zip Ls Ps)).foldl (fun acc t => addL acc (plogCoeffs t.2.2 t.1 c t.2.1 M)) []
  addL (taylorQ c M poly) (addL pl ((List.range (M + 1)).map fun k => poleCoeff poles c k))

def bndOK (cs : List ℚ) : ℕ → List ℚ → Bool
  | _, [] => true
  | k, b :: bs => decide (qabs' (cs.getD k 0) ≤ b) && bndOK cs (k + 1) bs

def cellOK (poly es Ls : List ℚ) (Ps : List (List ℚ)) (poles : List PoleR) (lo hi A0 l1 u1 A2 : ℚ)
    (Bl : List ℚ) (BM T : ℚ) : Bool :=
  let c := (lo + hi) / 2
  let M := Bl.length + 3
  let cs := ctot poly es Ls Ps poles c M
  decide (l1 ≤ cs.getD 1 0) && decide (cs.getD 1 0 ≤ u1) && decide (cs.getD 2 0 ≤ A2) &&
  bndOK cs 3 Bl && decide (tmUBQ A0 l1 u1 A2 ((hi - lo) / 2) Bl BM ≤ T)

def mkPoles : List ℤ → List PoleR
  | a :: b :: c :: d :: e :: f :: g :: h :: rest =>
    ⟨toQ a b, toQ c d, toQ e f, toQ g h⟩ :: mkPoles rest
  | _ => []

end CatalanMeasure.GenD.Signed.Data

module

public import CatalanCore.Uniform.Content.UFSimple.Cell
public import CatalanCore.Uniform.Content.BankShared.Check.Expr

@[expose] public section

/-! # Existing-checker expressions for the complementary family price

Six unconditional candidates at each prefix depth avoid introducing a floor
of a virtual node. These are expression identities; validity of the content
layer is supplied separately by the mixed-source theorem.
-/

open CatalanCore.Uniform.Content.BankShared.Check

namespace CatalanCore.Uniform.Content.UFSimple.WrapExpr

open Expr

def dim (m p : ℕ) : ℕ := min (m%p) (p-m%p)
def virtual (r m p : ℕ) : ℕ := r+m-dim m p

def eD : Expr := dist vm
def eA : Expr := tsub (add vr vm) eD
def eN : Expr := add eA (smul 2 eD)
def eOvl (lo hi : Expr) : Expr := tsub (mn eN (add hi (cst 1))) (mx eA lo)
def eBeta (lo hi : Expr) : Expr :=
  add (add (eOvl lo hi) (eOvl (add lo vp) (add hi vp)))
    (eOvl (tsub lo vp) (tsub hi vp))
def eBound (t0 tv w0 : Expr) : Expr :=
  tsub (smul 2 (add eA eD))
    (add (add eD (tsub (tsub (mn (add tv (cst 1)) eN) t0) eD))
      (tsub (tsub (tsub (mn (add tv (cst 1)) eN) t0) eD)
        (tsub vp (add (tsub (add tv (cst 1)) w0)
          (tsub (smul 2 eD) (eBeta w0 tv))))))
def eCandidate (n j : ℕ) (z : Bool) : Expr :=
  let B := add ap (smul (n+j) vp)
  let lo := if z then vk else cst 0
  let hi := if z then tsub vp (cst 1) else tsub vk (cst 1)
  let tv := mn (add B hi) (tsub (add eA vp) (cst 1))
  eBound (mx eA (add B lo)) tv (add B lo)

def candidate (r p m k n j : ℕ) (z : Bool) : ℕ :=
  let d := dim m p
  let a := virtual r m p
  let B := p*(r/p)+(n+j)*p
  let lo := if z then k else 0
  let hi := if z then p-1 else k-1
  let tv := min (B+hi) (a+p-1)
  closedBound d a p (max a (B+lo)) tv (B+lo)

def tWrap (n : ℕ) : Expr :=
  mn (mn (mn (eCandidate n 0 false) (eCandidate n 0 true))
    (mn (eCandidate n 1 false) (eCandidate n 1 true)))
    (mn (eCandidate n 2 false) (eCandidate n 2 true))

def price (r p m k n : ℕ) : ℕ :=
  min (min (min (candidate r p m k n 0 false) (candidate r p m k n 0 true))
    (min (candidate r p m k n 1 false) (candidate r p m k n 1 true)))
    (min (candidate r p m k n 2 false) (candidate r p m k n 2 true))

/-- Exact integer transcription into the existing bank expression language. -/
theorem evalN_candidate (r p m k n j : ℕ) (z : Bool) :
    (eCandidate n j z).evalN r p m k = candidate r p m k n j z := by
  cases z <;> rfl

theorem evalN_tWrap (r p m k n : ℕ) :
    (tWrap n).evalN r p m k = price r p m k n := by
  simp only [tWrap, Expr.evalN, evalN_candidate, price]

/-- Complementary dimension never exceeds the original border dimension. -/
theorem dim_le (m p : ℕ) : dim m p ≤ m :=
  (min_le_left _ _).trans (Nat.mod_le _ _)

theorem virtual_add_dim (r m p : ℕ) : virtual r m p + dim m p = r+m := by
  have := dim_le m p
  unfold virtual
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapExpr

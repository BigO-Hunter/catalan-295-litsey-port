module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixLayer
public import CatalanCore.Uniform.Content.BankShared.Check.UF

@[expose] public section

open CatalanCore.Uniform.Content.BankShared.Check

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

/-- The lower endpoint of original prefix strip n. -/
def prefixLo (n : ℕ) : Cond := ⟨0,-(n:ℤ),1,0,0,false⟩

/-- The strict upper endpoint keeps the next whole period out. -/
def prefixHi (n : ℕ) : Cond := ⟨0,(n+1:ℕ),-1,0,0,true⟩

/-- The intended zero-debit six-candidate prefix expression. Its
arithmetic conditions identify exactly one original prefix strip. -/
def brPrefix (n : ℕ) : Branch := ⟨WrapExpr.tWrap n,[prefixLo n,prefixHi n],0⟩

theorem prefixLo_iff (r p m k n : ℕ) : (prefixLo n).Holds r p m k ↔ n*p≤m := by
  simp only [prefixLo,Cond.Holds,Cond.L,Bool.false_eq_true,ite_false,zero_mul,zero_add,
    one_mul,mul_zero,add_zero]
  constructor
  · intro h
    exact_mod_cast (show (n:ℤ)*p≤m by linarith)
  · intro h
    have hh : (n:ℤ)*p≤m := by exact_mod_cast h
    linarith

theorem prefixHi_iff (r p m k n : ℕ) : (prefixHi n).Holds r p m k ↔ m<(n+1)*p := by
  simp only [prefixHi,Cond.Holds,Cond.L,ite_true,zero_mul,zero_add,neg_one_mul,mul_zero,add_zero]
  constructor
  · intro h
    exact_mod_cast (show (m:ℤ)<(n+1:ℕ)*p by linarith)
  · intro h
    have hh : (m:ℤ)<(n+1:ℕ)*p := by exact_mod_cast h
    linarith

/-- Checker strip conditions recover the exact original full-period
count and residual border; they never replace the original common size. -/
theorem strip_decomposition (r p m k n : ℕ) (hp : 0<p)
    (hlo : (prefixLo n).Holds r p m k) (hhi : (prefixHi n).Holds r p m k) :
    m/p=n ∧ m=n*p+m%p ∧ m%p<p := by
  have hl := (prefixLo_iff r p m k n).mp hlo
  have hu := (prefixHi_iff r p m k n).mp hhi
  have hdl := (Nat.le_div_iff_mul_le hp).mpr hl
  have hdu := (Nat.div_lt_iff_lt_mul hp).mpr hu
  have hd : m/p=n := by omega
  refine ⟨hd,?_,Nat.mod_lt m hp⟩
  have he := Nat.mod_add_div m p
  rw [hd,Nat.mul_comm p n] at he
  omega

/-- Existing two-term bank arithmetic supplies the original prefix
region, with the full common size and all n original periods restored. -/
noncomputable def arithmeticRegion {Fr : CatalanCore.Frame} {q o p : ℕ} [Fact p.Prime]
    (T : CatalanCore.Uniform.Content.Smith.TwoTermData Fr q o)
    {nm : ℕ} (hnorm : Fr.norm=(nm:ℚ))
    (r m n k j : ℕ) (hn : 1≤n) (hqp : q<p)
    (hqN : q*(r+2*m)<p*p) (hm : m=n*p+m%p)
    (hk0 : 1≤k) (hkp : k<p) (hk : q*k=j*p+o) (hpn : ¬p∣nm) :
    WrapPrefixClosed.Region (p:=p) Fr q o r n (m%p) (p/2) (r+2*m) T := by
  have hp0 := (Fact.out:p.Prime).pos
  have hp2 : p≠2 := by have := T.o_pos; have := T.o_lt; omega
  have hodd : p%2=1 := (Fact.out:p.Prime).eq_two_or_odd.resolve_left hp2
  have hp : p=2*(p/2)+1 := by have := Nat.mod_add_div p 2; omega
  have hgood := CatalanCore.Uniform.Content.BankShared.TwoTerm.norm_good hnorm hpn
  exact
    { hn := hn
      hp := hp
      he := Nat.mod_lt m hp0
      hqp := hqp
      hN := hqN
      hsize := by omega
      hsq := CatalanCore.Uniform.Content.BankShared.TwoTerm.not_sq_dvd_of_qN T hqN.le
      hnorm := hgood.1
      hnorm0 := hgood.2
      root := k
      j0 := j
      hroot0 := hk0
      hrootp := hkp.le
      hroot := hk }

/-! ## The checker supplier, parametrised by the retained-set input

`catValid_prefix_of` turns the stronger layer theorem into the validity of
any prefix branch whose expression evaluates to `priceG cr`.  The retained
bound enters only through `WrapPrefixLayer.Supply`: route R1 (the credited
interval alone) is instantiated below, the routes with outside kills reuse
the same supplier with larger credits. -/

section Supplier

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.TwoTerm

/-- The core of the supplier, with the border size abstract. -/
theorem prefix_core {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm=(nm:ℚ)) {p : ℕ} [Fact p.Prime] (hpn : ¬p∣nm) (hqp : q<p)
    (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hsup : WrapPrefixLayer.Supply Fr q o cr)
    (r m n k j : ℕ) (hn : 1≤n) (hqN : q*(r+2*m)<p*p) (hm : m=n*p+m%p)
    (hk0 : 1≤k) (hkp : k<p) (hk : q*k=j*p+o) (S : Finset (Fin r)) :
    GLE p (WrapPrefixLayer.priceG cr r p m k n) (commonMinorPoly Fr r m S) := by
  have A := arithmeticRegion T hnorm r m n k j hn hqp hqN hm hk0 hkp hk hpn
  have hrho : p∣q*k-o := ⟨j,by rw [hk,Nat.add_sub_cancel,Nat.mul_comm]⟩
  have hg := WrapPrefixLayer.commonMinor_gle_G cr hsup A k hk0 hkp hrho S
  rw [← hm] at hg
  exact hg

/-- Validity of a prefix branch with expression `E = priceG cr` for every
strip `n ≥ 1`, from the retained-set input `Supply Fr q o cr`. -/
theorem catValid_prefix_of (c : ℚ) (hc : 0<c) {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm=(nm:ℚ))
    (depth Pbad N0 n : ℕ) (hn : 1≤n)
    (hP : ∀ p : ℕ,p.Prime → Pbad<p → ¬p∣nm ∧ q<p)
    (cr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (hsup : WrapPrefixLayer.Supply Fr q o cr) (E : Expr)
    (hE : ∀ r p m k,E.evalN r p m k=WrapPrefixLayer.priceG cr r p m k n) :
    CatValid c hc Fr depth q o Pbad N0 [(⟨E,[prefixLo n,prefixHi n],0⟩ : Branch)] := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  subst hb
  obtain ⟨hpn,hqp⟩ := hP p Fact.out hPb
  have hp0 := (Fact.out:p.Prime).pos
  have hlo := hcond (prefixLo n) (by simp)
  have hhi := hcond (prefixHi n) (by simp)
  obtain ⟨-,hm,-⟩ := strip_decomposition i.1 p _ k n hp0 hlo hhi
  have hg := prefix_core T hnorm hpn hqp cr hsup i.1 ((altGeom c hc).borderSize i.1) n k j hn hqN hm hk0 hkp hk
    (retainedFin (altGeom_hybShape c hc hi.2) i.2)
  have he := altGeom_member_commonMinor c hc Fr depth hi.2 i.2
  refine ⟨WrapPrefixLayer.priceG cr i.1 p ((altGeom c hc).borderSize i.1) k n,?_,?_⟩
  · exact he.symm ▸ hg
  · simp [hE]

/-- **Route R1**: the branch with the credited-interval price, the outside
kill term `2d - β` dropped. -/
def eBound1 (t0 tv w0 : Expr) : Expr :=
  Expr.tsub (Expr.smul 2 (Expr.add WrapExpr.eA WrapExpr.eD))
    (Expr.add (Expr.add WrapExpr.eD
        (Expr.tsub (Expr.tsub (Expr.mn (Expr.add tv (Expr.cst 1)) WrapExpr.eN) t0) WrapExpr.eD))
      (Expr.tsub (Expr.tsub (Expr.tsub (Expr.mn (Expr.add tv (Expr.cst 1)) WrapExpr.eN) t0) WrapExpr.eD)
        (Expr.tsub Expr.vp (Expr.tsub (Expr.add tv (Expr.cst 1)) w0))))

def eCandidate1 (n j : ℕ) (z : Bool) : Expr :=
  let B := Expr.add Expr.ap (Expr.smul (n+j) Expr.vp)
  let lo := if z then Expr.vk else Expr.cst 0
  let hi := if z then Expr.tsub Expr.vp (Expr.cst 1) else Expr.tsub Expr.vk (Expr.cst 1)
  let tv := Expr.mn (Expr.add B hi) (Expr.tsub (Expr.add WrapExpr.eA Expr.vp) (Expr.cst 1))
  eBound1 (Expr.mx WrapExpr.eA (Expr.add B lo)) tv (Expr.add B lo)

def tWrap1 (n : ℕ) : Expr :=
  Expr.mn (Expr.mn (Expr.mn (eCandidate1 n 0 false) (eCandidate1 n 0 true))
    (Expr.mn (eCandidate1 n 1 false) (eCandidate1 n 1 true)))
    (Expr.mn (eCandidate1 n 2 false) (eCandidate1 n 2 true))

theorem evalN_eCandidate1 (r p m k n j : ℕ) (z : Bool) :
    (eCandidate1 n j z).evalN r p m k=WrapPrefixLayer.candG WrapPrefixLayer.cr1 r p m k n j z := by
  cases z <;> rfl

theorem evalN_tWrap1 (r p m k n : ℕ) :
    (tWrap1 n).evalN r p m k=WrapPrefixLayer.priceG WrapPrefixLayer.cr1 r p m k n := by
  simp only [tWrap1,Expr.evalN,evalN_eCandidate1,WrapPrefixLayer.priceG]

/-- The R1 prefix branch (debit zero). -/
def brPrefix1 (n : ℕ) : Branch := ⟨tWrap1 n,[prefixLo n,prefixHi n],0⟩

/-- **R1 instance**: every original prefix strip `n ≥ 1` with the closed
credited-interval price, from built theorems only. -/
theorem catValid_prefix_R1 (c : ℚ) (hc : 0<c) {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm=(nm:ℚ))
    (depth Pbad N0 n : ℕ) (hn : 1≤n)
    (hP : ∀ p : ℕ,p.Prime → Pbad<p → ¬p∣nm ∧ q<p) :
    CatValid c hc Fr depth q o Pbad N0 [brPrefix1 n] :=
  catValid_prefix_of c hc T hnorm depth Pbad N0 n hn hP WrapPrefixLayer.cr1
    (WrapPrefixLayer.supply_R1 Fr q o) (tWrap1 n) (fun r p m k => evalN_tWrap1 r p m k n)

/-- The full checker branch `brPrefix n` (expression `tWrap n`, the
`(2d - β)` credit) is valid as soon as the retained-set input is supplied
for the credit `cr3`: this is the target of routes R2 and R3. -/
theorem catValid_prefix (c : ℚ) (hc : 0<c) {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm=(nm:ℚ))
    (depth Pbad N0 n : ℕ) (hn : 1≤n)
    (hP : ∀ p : ℕ,p.Prime → Pbad<p → ¬p∣nm ∧ q<p)
    (hsup : WrapPrefixLayer.Supply Fr q o WrapPrefixLayer.cr3) :
    CatValid c hc Fr depth q o Pbad N0 [brPrefix n] :=
  catValid_prefix_of c hc T hnorm depth Pbad N0 n hn hP WrapPrefixLayer.cr3 hsup
    (WrapExpr.tWrap n) (fun r p m k => by
      rw [WrapExpr.evalN_tWrap,WrapPrefixLayer.price_eq_priceG])

end Supplier

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

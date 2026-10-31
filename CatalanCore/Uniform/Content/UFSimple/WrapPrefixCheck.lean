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

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

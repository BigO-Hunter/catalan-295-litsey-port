module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapLayer
public import Submission.CatalanCore.Uniform.Content.BankShared.Check.UF

@[expose] public section

/-! # The proved wrapped zero-debit checker branch -/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.BankShared.Check

namespace CatalanCore.Uniform.Content.UFSimple.WrapCheck

def cmLtP : Cond := ⟨0,1,-1,0,0,true⟩
def cpLe2m : Cond := ⟨0,-1,2,0,0,false⟩

/-- The first wrapped strip, priced for the entire deletion family. -/
def brWrap : Branch := ⟨WrapExpr.tWrap 0,[cmLtP,cpLe2m],0⟩

/-- Existing two-term bank arithmetic discharges every matrix hypothesis. -/
theorem catValid_wrap (c : ℚ) (hc : 0<c) {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm=(nm:ℚ))
    (depth Pbad N0 : ℕ)
    (hP : ∀ p : ℕ,p.Prime → Pbad<p → ¬p∣nm ∧ q<p) :
    CatValid c hc Fr depth q o Pbad N0 [brWrap] := by
  intro b hb i hi hr0 p _ hPb _ hqN j k hk hj0 hjq hk0 hkp hcond
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  subst hb
  obtain ⟨hpn,hqp⟩ := hP p Fact.out hPb
  have hm : (altGeom c hc).borderSize i.1<p := by
    have h := hcond cmLtP (by simp [brWrap])
    simp only [cmLtP,Cond.Holds,Cond.L,ite_true] at h
    push_cast at h
    omega
  have hmp : p≤2*(altGeom c hc).borderSize i.1 := by
    have h := hcond cpLe2m (by simp [brWrap])
    simp only [cpLe2m,Cond.Holds,Cond.L,Bool.false_eq_true,ite_false] at h
    push_cast at h
    omega
  have hqpos : 1≤q := by have := T.o_pos; have := T.o_lt; omega
  have hN : i.1+2*(altGeom c hc).borderSize i.1<p*p :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hqpos) hqN
  have hn := norm_good hnorm hpn
  have hrho : p∣q*k-o := ⟨j,by rw [hk,Nat.add_sub_cancel,Nat.mul_comm]⟩
  have hg := WrapLayer.commonMinor_gle T i.1 _ k hqp hN
    (not_sq_dvd_of_qN T hqN.le) hn.1 hn.2 hm hmp hk0 hkp hrho
    (retainedFin (altGeom_hybShape c hc hi.2) i.2)
  have he := altGeom_member_commonMinor c hc Fr depth hi.2 i.2
  refine ⟨(WrapExpr.tWrap 0).evalN i.1 p ((altGeom c hc).borderSize i.1) k,?_,?_⟩
  · exact he.symm ▸ hg
  · simp only [brWrap,zero_mul,add_zero]
    exact le_rfl

end CatalanCore.Uniform.Content.UFSimple.WrapCheck

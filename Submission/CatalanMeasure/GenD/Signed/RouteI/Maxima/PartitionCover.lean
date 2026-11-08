module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.RootCover
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
-- kcost: estimated within149KsharedR3reserve; actual cut signs remain instance checks
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover
open Set

def Chain (a b : Real) : List (Real × Real) → Prop
  | [] => a=b
  | (l,r)::cs => l=a ∧ l<r ∧ Chain r b cs

def chainOK (a b : Rat) : List (Rat × Rat) → Bool
  | [] => decide (a=b)
  | (l,r)::cs => decide (l=a) && decide (l<r) && chainOK r b cs

noncomputable def castCell (c : Rat × Rat) : Real × Real := (c.1,c.2)

theorem chainOK_sound (a b : Rat) (cs : List (Rat × Rat)) (h : chainOK a b cs=true) :
    Chain a b (cs.map castCell) := by
  induction cs generalizing a with
  | nil =>
    have he : a=b := by simpa only [chainOK,decide_eq_true_eq] using h
    simpa only [List.map_nil,Chain] using congrArg (fun q : Rat => (q : Real)) he
  | cons c cs ih =>
    obtain ⟨l,r⟩ := c
    have hh : (l=a ∧ l<r) ∧ chainOK r b cs=true := by
      simpa only [chainOK,Bool.and_eq_true,decide_eq_true_eq] using h
    simp only [List.map_cons,castCell,Chain]
    refine ⟨?_,?_,ih r hh.2⟩
    · exact_mod_cast hh.1.1
    · exact_mod_cast hh.1.2

/-- The nonroot-cut premise is required only for internal cuts; physical endpoints are
excluded by the open interval and are not silently included in the count. -/
theorem chain_covers_roots (p : Polynomial Real) (a b : Real) (cs : List (Real × Real))
    (hc : Chain a b cs)
    (hcuts : ∀ c∈cs,c.2≠b → p.eval c.2≠0) :
    ∀ x∈Ioo a b,p.IsRoot x → ∃ c∈cs,x∈Ioo c.1 c.2 := by
  induction cs generalizing a with
  | nil =>
    intro x hx hp
    change a=b at hc
    exact False.elim (by linarith [hx.1,hx.2])
  | cons c cs ih =>
    obtain ⟨l,r⟩ := c
    obtain ⟨hla,hlr,hrest⟩ := hc
    intro x hx hp
    by_cases hxr : x<r
    · exact ⟨(l,r),by simp,⟨by simpa only [hla] using hx.1,hxr⟩⟩
    · have hrx : r≤x := le_of_not_gt hxr
      have hne : x≠r := by
        intro he
        have hrb : r≠b := by intro heb; rw [he,heb] at hx; exact (lt_irrefl b hx.2)
        apply hcuts (l,r) (by simp) hrb
        have h2 : p.IsRoot r := he ▸ hp
        exact h2
      have hlt : r<x := lt_of_le_of_ne hrx (Ne.symm hne)
      obtain ⟨c,hc,hxc⟩ := ih r hrest
        (fun c hc hcb => hcuts c (by simp [hc]) hcb) x ⟨hlt,hx.2⟩ hp
      exact ⟨c,by simp [hc],hxc⟩

#print axioms chainOK_sound
#print axioms chain_covers_roots
end CatalanMeasure.GenD.Signed.RouteI.Maxima.PartitionCover

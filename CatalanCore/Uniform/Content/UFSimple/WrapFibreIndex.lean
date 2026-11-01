module

public import CatalanCore.Uniform.Content.UFSimple.WrapFibreCount
public import CatalanCore.Uniform.Content.UFSimple.WrapOwnCore

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CatalanCore.Uniform.Content.UFSimple.WrapFibreIndex

variable (p : ℕ) [Fact p.Prime]
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

def colour (c : ι → ℕ) (xs : β → ℕ) : ι ⊕ β → ZMod p :=
  Sum.elim (fun i => (c i:ZMod p)) (fun j => (xs j:ZMod p))

abbrev Common (c : ι → ℕ) (gamma : ZMod p) := {i // (c i:ZMod p)=gamma}
abbrev Balanced (xs : β → ℕ) (gamma : ZMod p) := {j // (xs j:ZMod p)=gamma}
abbrev Whole (c : ι → ℕ) (xs : β → ℕ) (gamma : ZMod p) :=
  {a // colour p c xs a=gamma}

noncomputable def balancedEquiv (xs : β → ℕ) (gamma : ZMod p) :
    Fin (Fintype.card (Balanced p xs gamma)) ≃ Balanced p xs gamma :=
  (Fintype.equivFin _).symm

/-- Actual own-colour indices separate the retained common nodes and
balanced nodes; only the latter are enumerated by their actual cardinality. -/
noncomputable def equiv (c : ι → ℕ) (xs : β → ℕ) (gamma : ZMod p) :
    (Common p c gamma ⊕ Fin (Fintype.card (Balanced p xs gamma))) ≃ Whole p c xs gamma :=
  (Equiv.sumCongr (Equiv.refl _) (balancedEquiv p xs gamma)).trans
    (Equiv.subtypeSum (p:=fun a => colour p c xs a=gamma)).symm


/-- Recover each original node, including its actual quotient index. -/
theorem node_eq (a : ℕ) (gamma : ZMod p) (ha : (a:ZMod p)=gamma) :
    a=gamma.val+(a/p)*p := by
  have hv := congrArg ZMod.val ha
  rw [ZMod.val_natCast] at hv
  have hh := Nat.mod_add_div a p
  rw [hv] at hh
  simpa only [Nat.mul_comm] using hh.symm

def commonQuotient (c : ι → ℕ) (gamma : ZMod p) : Common p c gamma → ℕ :=
  fun i => c i.1/p
noncomputable def rowQuotient (xs : β → ℕ) (gamma : ZMod p) :
    Fin (Fintype.card (Balanced p xs gamma)) → ℕ :=
  fun i => xs (balancedEquiv p xs gamma i).1/p
noncomputable def colQuotient (xs ys : β → ℕ) (gamma : ZMod p) :
    Fin (Fintype.card (Balanced p xs gamma)) → ℕ :=
  fun i => ys (balancedEquiv p xs gamma i).1/p

theorem common_node (c : ι → ℕ) (gamma : ZMod p) (i : Common p c gamma) :
    c i.1=gamma.val+commonQuotient p c gamma i*p := node_eq p _ _ i.2

theorem row_node (xs : β → ℕ) (gamma : ZMod p)
    (i : Fin (Fintype.card (Balanced p xs gamma))) :
    xs (balancedEquiv p xs gamma i).1=gamma.val+rowQuotient p xs gamma i*p :=
  node_eq p _ _ (balancedEquiv p xs gamma i).2

theorem col_node (xs ys : β → ℕ) (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (gamma : ZMod p) (i : Fin (Fintype.card (Balanced p xs gamma))) :
    ys (balancedEquiv p xs gamma i).1=gamma.val+colQuotient p xs ys gamma i*p :=
  node_eq p _ _ ((hcol _).symm.trans (balancedEquiv p xs gamma i).2)

theorem row_injective (xs : β → ℕ) (hx : Function.Injective xs) (gamma : ZMod p) :
    Function.Injective (rowQuotient p xs gamma) := by
  apply WrapFibreCount.quotient_injective p _
    (hx.comp (Subtype.val_injective.comp (balancedEquiv p xs gamma).injective)) gamma.val
  intro i
  have hh := congrArg ZMod.val (balancedEquiv p xs gamma i).2
  simpa only [ZMod.val_natCast,Function.comp_apply] using hh

theorem col_injective (xs ys : β → ℕ) (hy : Function.Injective ys)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p)) (gamma : ZMod p) :
    Function.Injective (colQuotient p xs ys gamma) := by
  apply WrapFibreCount.quotient_injective p _
    (hy.comp (Subtype.val_injective.comp (balancedEquiv p xs gamma).injective)) gamma.val
  intro i
  have hh := congrArg ZMod.val ((hcol _).symm.trans (balancedEquiv p xs gamma i).2)
  simpa only [ZMod.val_natCast,Function.comp_apply] using hh

theorem quotient_disjoint (xs ys : β → ℕ)
    (hcol : ∀ i,(xs i:ZMod p)=(ys i:ZMod p))
    (hdis : ∀ i j,xs i≠ys j) (gamma : ZMod p)
    (i j : Fin (Fintype.card (Balanced p xs gamma))) :
    colQuotient p xs ys gamma j≠rowQuotient p xs gamma i := by
  intro he
  apply hdis (balancedEquiv p xs gamma i).1 (balancedEquiv p xs gamma j).1
  rw [row_node p xs gamma i,col_node p xs ys hcol gamma j,he]

end CatalanCore.Uniform.Content.UFSimple.WrapFibreIndex

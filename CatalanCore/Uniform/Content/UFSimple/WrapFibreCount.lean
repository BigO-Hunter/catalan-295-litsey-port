module

public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixGeometry
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

open Finset

namespace CatalanCore.Uniform.Content.UFSimple.WrapFibreCount

variable (p : ℕ) [Fact p.Prime]

def colour (r : ℕ) (i : Fin p) : ZMod p := ((r+2*(i:ℕ):ℕ):ZMod p)

theorem colour_injective (r : ℕ) (hp2 : 2<p) : Function.Injective (colour p r) := by
  have h2 : (2:ZMod p)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by omega : 0<2) hd
    omega
  intro i j he
  apply Fin.ext
  simp only [colour,Nat.cast_add,Nat.cast_mul] at he
  have hh : ((i:ℕ):ZMod p)=((j:ℕ):ZMod p) := mul_left_cancel₀ h2 (add_left_cancel he)
  have hm := (ZMod.natCast_eq_natCast_iff' (i:ℕ) (j:ℕ) p).mp hh
  simpa only [Nat.mod_eq_of_lt i.2,Nat.mod_eq_of_lt j.2] using hm

theorem colour_bijective (r : ℕ) (hp2 : 2<p) : Function.Bijective (colour p r) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨colour_injective p r hp2,by simp⟩

theorem fibre_card {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Bijective f) (b : β) : Fintype.card {a // f a=b}=1 := by
  classical
  obtain ⟨a,ha⟩ := hf.2 b
  letI : Unique {a // f a=b} :=
    { default := ⟨a,ha⟩
      uniq := fun x => Subtype.ext (hf.1 (x.2.trans ha.symm)) }
  exact Fintype.card_unique

/-- Each original full period contains exactly one row of every colour. -/
theorem full_colour (r : ℕ) {n : ℕ} (c : Fin n) (i : Fin p) :
    (WrapCycles.row r p c i:ZMod p)=colour p r i := by
  simp [WrapCycles.row,colour]

noncomputable def fullEquiv (r n : ℕ) (gamma : ZMod p) :
    {a : Fin n × Fin p // (WrapCycles.row r p a.1 a.2:ZMod p)=gamma} ≃
      Fin n × {i : Fin p // colour p r i=gamma} where
  toFun a := (a.1.1,⟨a.1.2,by simpa only [full_colour] using a.2⟩)
  invFun a := ⟨(a.1,a.2.1),by simpa only [full_colour] using a.2.2⟩
  left_inv := by rintro ⟨⟨a,b⟩,h⟩; rfl
  right_inv := by rintro ⟨a,⟨b,h⟩⟩; rfl

theorem full_card (r n : ℕ) (hp2 : 2<p) (gamma : ZMod p) :
    Fintype.card {a : Fin n × Fin p // (WrapCycles.row r p a.1 a.2:ZMod p)=gamma}=n := by
  rw [Fintype.card_congr (fullEquiv p r n gamma),Fintype.card_prod,Fintype.card_fin,
    fibre_card (colour p r) (colour_bijective p r hp2) gamma,mul_one]

/-- An injective residual row-slot family of length below p contributes
at most one node of any fixed colour. -/
theorem residual_injective {α : Type*} (r : ℕ) (hp2 : 2<p) (slot : α → ℕ)
    (hinj : Function.Injective slot) (hsmall : ∀ i,slot i<p) :
    Function.Injective (fun i => ((r+2*slot i:ℕ):ZMod p)) := by
  intro i j he
  apply hinj
  have hh := colour_injective p r hp2
    (show colour p r ⟨slot i,hsmall i⟩=colour p r ⟨slot j,hsmall j⟩ from he)
  exact congrArg Fin.val hh

def balancedRow (r n : ℕ) {b : ℕ} (slot : Fin b → ℕ) : (Fin n × Fin p) ⊕ Fin b → ℕ
  | Sum.inl a => WrapCycles.row r p a.1 a.2
  | Sum.inr j => r+2*n*p+2*slot j

/-- Exact original prefix own-fibre dimensions: n full periods plus
zero or one residual balanced node. -/
theorem balanced_card_bounds (r n b : ℕ) (hp2 : 2<p) (slot : Fin b → ℕ)
    (hinj : Function.Injective slot) (hsmall : ∀ i,slot i<p) (gamma : ZMod p) :
    n≤Fintype.card {a // (balancedRow p r n slot a:ZMod p)=gamma} ∧
      Fintype.card {a // (balancedRow p r n slot a:ZMod p)=gamma}≤n+1 := by
  classical
  have hf : Fintype.card {a : Fin n × Fin p //
      (balancedRow p r n slot (Sum.inl a):ZMod p)=gamma}=n := full_card p r n hp2 gamma
  have hs : Subsingleton {a : Fin b //
      (balancedRow p r n slot (Sum.inr a):ZMod p)=gamma} := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    exact residual_injective p (r+2*n*p) hp2 slot hinj hsmall (a.2.trans b.2.symm)
  have hp : Fintype.card {a : Fin b //
      (balancedRow p r n slot (Sum.inr a):ZMod p)=gamma}≤1 :=
    Fintype.card_le_one_iff_subsingleton.mpr hs
  have he := Fintype.card_congr (Equiv.subtypeSum
    (p:=fun a => (balancedRow p r n slot a:ZMod p)=gamma))
  rw [Fintype.card_sum,hf] at he
  omega

/-- Original quotient coordinates distinguish same-colour nodes. -/
theorem quotient_injective {α : Type*} (node : α → ℕ) (hinj : Function.Injective node)
    (gamma : ℕ) (hcol : ∀ i,node i%p=gamma) : Function.Injective (fun i => node i/p) := by
  intro i j he
  apply hinj
  have hi := Nat.mod_add_div (node i) p
  have hj := Nat.mod_add_div (node j) p
  rw [hcol i] at hi
  rw [hcol j] at hj
  change node i/p=node j/p at he
  rw [he] at hi
  omega

end CatalanCore.Uniform.Content.UFSimple.WrapFibreCount

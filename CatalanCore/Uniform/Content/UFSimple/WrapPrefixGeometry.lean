module

public import CatalanCore.Uniform.Content.UFSimple.WrapCycles
public import CatalanCore.Uniform.Content.UFSimple.WrapExpr
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Original-coordinate prefix chains and compressed surplus coordinates -/

namespace CatalanCore.Uniform.Content.UFSimple.WrapPrefixGeometry

variable {n p e b d : ℕ}

noncomputable def rowBorderEquiv (er : (Fin b ⊕ Fin d) ≃ Fin e) :
    (((Fin n × Fin p) ⊕ Fin b) ⊕ Fin d) ≃ Fin (n*p+e) :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr finProdFinEquiv er).trans finSumFinEquiv)

noncomputable def colBorderEquiv (hp : 0<p) (s : ℕ)
    (ec : (Fin b ⊕ Fin d) ≃ Fin e) :
    (((Fin n × Fin p) ⊕ Fin b) ⊕ Fin d) ≃ Fin (n*p+e) :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr
      ((Equiv.prodCongr (Equiv.refl (Fin n)) (WrapCycles.permutation p hp s)).trans finProdFinEquiv)
      ec).trans finSumFinEquiv)

noncomputable def rowFullEquiv (ι : Type*) (er : (Fin b ⊕ Fin d) ≃ Fin e) :
    ((ι ⊕ ((Fin n × Fin p) ⊕ Fin b)) ⊕ Fin d) ≃ (ι ⊕ Fin (n*p+e)) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl ι) (rowBorderEquiv er))

noncomputable def colFullEquiv (ι : Type*) (hp : 0<p) (s : ℕ)
    (ec : (Fin b ⊕ Fin d) ≃ Fin e) :
    ((ι ⊕ ((Fin n × Fin p) ⊕ Fin b)) ⊕ Fin d) ≃ (ι ⊕ Fin (n*p+e)) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl ι) (colBorderEquiv hp s ec))

/-- The cycle rows in the combined equivalence are the actual original rows. -/
theorem row_cycle (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e) (c : Fin n) (i : Fin p) :
    r+2*(rowBorderEquiv er (Sum.inl (Sum.inl (c,i))):ℕ)=WrapCycles.row r p c i := by
  change r+2*((i:ℕ)+p*(c:ℕ))=r+2*((c:ℕ)*p+(i:ℕ))
  ring

theorem col_cycle (r : ℕ) (hp : 0<p) (s : ℕ)
    (ec : (Fin b ⊕ Fin d) ≃ Fin e) (c : Fin n) (i : Fin p) :
    r+2*(colBorderEquiv hp s ec (Sum.inl (Sum.inl (c,i))):ℕ)+1=
      WrapCycles.col r p hp s c i := by
  change r+2*((WrapCycles.shift p hp s i:ℕ)+p*(c:ℕ))+1=
    r+2*((c:ℕ)*p+(WrapCycles.shift p hp s i:ℕ))+1
  ring

/-- Residual slots are placed after all actual full cycles. -/
theorem row_surplus (r : ℕ) (er : (Fin b ⊕ Fin d) ≃ Fin e) (i : Fin d) :
    r+2*(rowBorderEquiv (n:=n) (p:=p) er (Sum.inr i):ℕ)=
      r+2*n*p+2*(er (Sum.inr i):ℕ) := by
  change r+2*(n*p+(er (Sum.inr i):ℕ))=r+2*n*p+2*(er (Sum.inr i):ℕ)
  ring

theorem col_surplus (r : ℕ) (hp : 0<p) (s : ℕ)
    (ec : (Fin b ⊕ Fin d) ≃ Fin e) (i : Fin d) :
    r+2*(colBorderEquiv (n:=n) hp s ec (Sum.inr i):ℕ)+1=
      r+2*n*p+2*(ec (Sum.inr i):ℕ)+1 := by
  change r+2*(n*p+(ec (Sum.inr i):ℕ))+1=r+2*n*p+2*(ec (Sum.inr i):ℕ)+1
  ring

/-- The checker's compressed coordinate differs from the original node
by n full periods, for both axes and either residual orientation. -/
theorem surplus_translation (r n p slot bit : ℕ) :
    r+2*n*p+2*slot+bit=(r+n*p+2*slot+bit)+n*p := by ring

theorem translation_colour (p x n : ℕ) :
    ((x+n*p:ℕ):ZMod p)=(x:ZMod p) := by simp

/-- Source windows lift back to actual nodes by the same translation;
the quotient index changes by n, never by a guessed prefix index. -/
theorem translation_quotient (p x n : ℕ) (hp : 0<p) :
    (x+n*p)/p=x/p+n := by
  rw [Nat.add_mul_div_right _ _ hp]

end CatalanCore.Uniform.Content.UFSimple.WrapPrefixGeometry

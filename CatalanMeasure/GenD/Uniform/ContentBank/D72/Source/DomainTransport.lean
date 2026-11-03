module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.Source.DomainRows
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.Source
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.W.Charts6 CatalanMeasure.GenD.Uniform.W.Prof
noncomputable section
variable {p : Nat} [Fact p.Prime]

def slotPolynomial {K : Nat} (x : Fin p → Fin K → ZMod p) :
    List (Fin K × Int) → (ZMod p)[X]
  | [] => 0
  | (k,z)::ts => C (z : ZMod p) * polx x k + slotPolynomial x ts

theorem scalarPol_slotLinear {n K : Nat}
    (I : (Fin n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → Fin n → ZMod p) (terms : List (Fin K × Int)) :
    scalarPol ((slotLinear terms).comp I) x = slotPolynomial (fun e => I (x e)) terms := by
  induction terms with
  | nil => simp [slotLinear, slotPolynomial, scalarPol, polx]
  | cons t terms ih =>
    obtain ⟨k,z⟩ := t
    unfold scalarPol at ih ⊢
    simp only [polx, slotLinear, slotPolynomial, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, map_add, map_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum] at ih ⊢
    rw [← ih]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring

theorem slotPolynomial_taylor_zero {n K : Nat}
    (I : (Fin n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → Fin n → ZMod p) (terms : List (Fin K × Int))
    (a : ZMod p) (k : Nat)
    (h : slotLinear terms (I (CatalanMeasure.GenD.Uniform.W.Charts3.taylorJet a k x)) = 0) :
    (taylor a (slotPolynomial (fun e => I (x e)) terms)).coeff k = 0 := by
  rw [← scalarPol_slotLinear I x terms, scalarPol_taylor]
  exact h

theorem slotPolynomial_tail_zero {n K : Nat}
    (I : (Fin n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → Fin n → ZMod p) (terms : List (Fin K × Int)) (r : Nat)
    (h : ∀ j < p - r, slotLinear terms (I (physicalJet .infinity j x)) = 0) :
    ∀ i, r ≤ i → (slotPolynomial (fun e => I (x e)) terms).coeff i = 0 := by
  rw [← scalarPol_slotLinear I x terms]
  exact scalarPol_tail _ x r h

theorem slotPolynomial_zero {n K : Nat}
    (I : (Fin n → ZMod p) →ₗ[ZMod p] (Fin K → ZMod p))
    (x : Fin p → Fin n → ZMod p) (terms : List (Fin K × Int))
    (h : ∀ j < p, slotLinear terms (I (physicalJet .zero j x)) = 0) :
    slotPolynomial (fun e => I (x e)) terms = 0 := by
  rw [← scalarPol_slotLinear I x terms]
  ext i
  simp only [Polynomial.coeff_zero]
  by_cases hi : i < p
  · have h0 := h i hi
    unfold scalarPol
    rw [← jet0_coord]
    simpa [physicalJet, jet0, hi] using h0
  · have hd : (p : WithBot Nat) ≤ i := by exact_mod_cast Nat.le_of_not_gt hi
    exact coeff_eq_zero_of_degree_lt ((scalarPol_degree _ x).trans_le hd)

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.Source

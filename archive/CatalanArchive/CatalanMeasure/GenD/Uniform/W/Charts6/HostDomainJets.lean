module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostJetPrefix
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts6
open Polynomial Finset CatalanMeasure.GenD.Uniform.W.Charts4
noncomputable section
variable {p : Nat} [Fact p.Prime]

def scalarPol {d : Nat} (F : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin p → Fin d → ZMod p) : (ZMod p)[X] :=
  polx (fun e (_ : Fin 1) => F (x e)) 0

theorem scalarPol_degree {d : Nat} (F : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin p → Fin d → ZMod p) : (scalarPol F x).degree < p :=
  polx_degree _ _

theorem scalarPol_taylor {d : Nat} (F : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin p → Fin d → ZMod p) (a : ZMod p) (k : Nat) :
    (taylor a (scalarPol F x)).coeff k = F (Charts3.taylorJet a k x) := by
  unfold scalarPol
  rw [← taylorJet_coord]
  simp [Charts3.taylorJet, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]

theorem scalarPol_inf {d : Nat} (F : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin p → Fin d → ZMod p) (k : Nat) (hk : k < p) :
    (scalarPol F x).coeff (p - 1 - k) = F (jetInf k x) := by
  unfold scalarPol
  have h := jetInf_coord k (fun e (_ : Fin 1) => F (x e)) 0
  rw [if_pos hk] at h
  rw [← h]
  simp [jetInf, hk]

theorem scalarPol_tail {d : Nat} (F : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (x : Fin p → Fin d → ZMod p) (r : Nat)
    (hinf : ∀ k < p - r, F (physicalJet .infinity k x) = 0) :
    ∀ i, r ≤ i → (scalarPol F x).coeff i = 0 := by
  intro i hi
  by_cases hp : i < p
  · let k := p - 1 - i
    have hk : k < p := by dsimp [k]; omega
    have hr : k < p - r := by dsimp [k]; omega
    have he : p - 1 - k = i := by dsimp [k]; omega
    rw [← he, scalarPol_inf F x k hk]
    exact hinf k hr
  · have hd : (p : WithBot Nat) ≤ i := by exact_mod_cast Nat.le_of_not_gt hp
    exact coeff_eq_zero_of_degree_lt ((scalarPol_degree F x).trans_le hd)

end
end CatalanMeasure.GenD.Uniform.W.Charts6

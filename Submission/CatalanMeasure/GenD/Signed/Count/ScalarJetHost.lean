module

public import Submission.CatalanMeasure.GenD.Uniform.W.Profile
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts3.PStepPoly

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxHeartbeats 1000000

/-!
One complete ScalarJetHost layer, standalone G2b. A full-profile physical
host is an explicit input. Scalar jets commute with EVERY profile inclusion;
the restricted joint kernel embeds into the same actual slot system.
This file does not construct the physical-prefix host or certify any source.
-/

namespace Decay2ScalarJetHost
open Finset Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3
  CatalanCore.Uniform.Content

noncomputable section

section Naturality
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] {m : ℕ}

def coeffMap (f : V →ₗ[K] W) : (Fin m → V) →ₗ[K] (Fin m → W) :=
  LinearMap.pi fun i => f.comp (LinearMap.proj i)

@[simp] theorem coeffMap_apply (f : V →ₗ[K] W) (x : Fin m → V) (i : Fin m) :
    coeffMap f x i = f (x i) := rfl

theorem coeffMap_injective (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Injective (coeffMap (m := m) f) := by
  intro x y h
  funext i
  exact hf (congrFun h i)

theorem scalarJet_natural (f : V →ₗ[K] W) (lam : Fin m → K) (x : Fin m → V) :
    scalarJet lam (coeffMap f x) = f (scalarJet lam x) := by
  simp [scalarJet, map_sum, map_smul]

end Naturality

section Host
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
variable {C : Type*} [Fintype C]

/-- Semantic full-profile input. Scalar coefficients, rather than arbitrary
V-valued jets, make restriction to every constant subspace possible. -/
structure CountHost (S : SlotSystem P N p) (m : ℕ) (e width : C → ℕ)
    (B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p))
    (lam : ∀ c, Fin (width c) → Fin m → ZMod p) (a r : ℕ) where
  xi : (Fin m → V) →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p)
  dom : ∀ x, (∀ c k, B c (scalarJet (lam c k) x) = 0) → xi x ∈ S.dom
  inj : ∀ x, (∀ c k, B c (scalarJet (lam c k) x) = 0) → xi x = 0 → x = 0
  kill : ∀ x, (∀ c k, B c (scalarJet (lam c k) x) = 0) →
    ∃ G : (ZMod p)[X], G.degree < (r : WithBot ℕ) ∧
    ∀ j, P.b N ≤ j → j + a * p < P.L N → ∑ v ∈ range (a + 1),
      ((-1 : ZMod p) ^ (a - v) * (a.choose v : ZMod p)) *
        S.resp (j / p + v) (j % p) (xi x) = G.eval (j : ZMod p)

variable {S : SlotSystem P N p} {m : ℕ} {e width : C → ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin m → ZMod p} {a r : ℕ}

theorem restricted_constraint (U : Submodule (ZMod p) V) (x : Fin m → U) :
    (∀ c k, (B c).comp U.subtype (scalarJet (lam c k) x) = 0) ↔
      ∀ c k, B c (scalarJet (lam c k) (coeffMap U.subtype x)) = 0 := by
  simp only [scalarJet_natural, LinearMap.comp_apply]

/-- Restricts the entire physical host, retaining exactly the same slot system,
scalar jets and p-step response. No choice of a basis or packet is involved. -/
def CountHost.restrict (I : CountHost S m e width B lam a r)
    (U : Submodule (ZMod p) V) :
    CountHost S m e width (fun c => (B c).comp U.subtype) lam a r where
  xi := I.xi.comp (coeffMap U.subtype)
  dom x hx := I.dom _ ((restricted_constraint U x).mp hx)
  inj x hx hz := by
    have hfull : coeffMap U.subtype x = 0 :=
      I.inj _ ((restricted_constraint U x).mp hx) hz
    exact (coeffMap_injective U.subtype Subtype.val_injective)
      (by simpa using hfull)
  kill x hx := I.kill _ ((restricted_constraint U x).mp hx)

/-- Complete packet-free host count, with the actual p-step slot theorem. -/
theorem CountHost.count [FiniteDimensional (ZMod p) V]
    (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (hq : P.q N = a * p + r) :
    m * finrank (ZMod p) V -
      ∑ c, width c * finrank (ZMod p) (LinearMap.range (B c)) ≤ nullity P N p := by
  let jet := fun c k => scalarJet (V := V) (lam c k)
  let Φ := constraintMap width B jet
  have hker : ∀ x : Fin m → V, Φ x = 0 ↔
      ∀ c k, B c (scalarJet (lam c k) x) = 0 :=
    fun x => constraintMap_eq_zero_iff width B jet x
  let ξ' : LinearMap.ker Φ →ₗ[ZMod p] (Fin S.D → Fin S.K → ZMod p) :=
    I.xi.comp (LinearMap.ker Φ).subtype
  have h := slot_nullity_pstep_poly S hP hN hp2 hH hq ξ'
    (fun u => I.dom u.1 ((hker u.1).mp u.2))
    (by
      intro u v huv
      refine Subtype.ext (sub_eq_zero.mp ?_)
      refine I.inj (u.1 - v.1) ?_ ?_
      · exact (hker _).mp (Submodule.sub_mem _ u.2 v.2)
      · simpa [ξ', map_sub, sub_eq_zero] using huv)
    (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)
    (fun u _ => I.kill u.1 ((hker u.1).mp u.2))
  have hr0 : finrank (ZMod p)
      (LinearMap.range (0 : LinearMap.ker Φ →ₗ[ZMod p] LinearMap.ker Φ)) = 0 := by simp
  rw [hr0, Nat.sub_zero] at h
  have hdim : m * finrank (ZMod p) V -
      ∑ c, width c * finrank (ZMod p) (LinearMap.range (B c)) ≤
        finrank (ZMod p) (LinearMap.ker Φ) :=
    rank_layer_lower_nat width B jet
  exact hdim.trans h

/-- EVERY profile subspace; the source producer supplies only the full host. -/
theorem CountHost.count_every_subspace [FiniteDimensional (ZMod p) V]
    (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (hq : P.q N = a * p + r)
    (U : Submodule (ZMod p) V) :
    m * finrank (ZMod p) U -
      ∑ c, width c * finrank (ZMod p) (LinearMap.range ((B c).comp U.subtype)) ≤
        nullity P N p :=
  (I.restrict U).count hP hN hp2 hH hq

/-- Finite matrix/rank producers may supply upper bounds only. -/
theorem CountHost.count_of_rank_bounds [FiniteDimensional (ZMod p) V]
    (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (hq : P.q N = a * p + r)
    (U : Submodule (ZMod p) V) (ranks : C → ℕ)
    (hr : ∀ c, finrank (ZMod p) (LinearMap.range ((B c).comp U.subtype)) ≤ ranks c) :
    m * finrank (ZMod p) U - ∑ c, width c * ranks c ≤ nullity P N p := by
  have h := I.count_every_subspace hP hN hp2 hH hq U
  have hb : (∑ c, width c *
      finrank (ZMod p) (LinearMap.range ((B c).comp U.subtype))) ≤
        ∑ c, width c * ranks c :=
    Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hr c)
  omega

/-- Signed Euler form, so floor-error estimates need no natural subtraction. -/
theorem CountHost.count_int [FiniteDimensional (ZMod p) V]
    (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) (hq : P.q N = a * p + r)
    (U : Submodule (ZMod p) V) :
    (m : ℤ) * (finrank (ZMod p) U : ℤ) -
      ∑ c, (width c : ℤ) *
        (finrank (ZMod p) (LinearMap.range ((B c).comp U.subtype)) : ℤ) ≤
          (nullity P N p : ℤ) := by
  have h := I.count_every_subspace hP hN hp2 hH hq U
  have hi : ((m * finrank (ZMod p) U : ℕ) : ℤ) -
      ((∑ c, width c *
        finrank (ZMod p) (LinearMap.range ((B c).comp U.subtype)) : ℕ) : ℤ) ≤
          (nullity P N p : ℤ) := by omega
  simpa only [Nat.cast_mul, Nat.cast_sum] using hi

end Host

#print axioms coeffMap_injective
#print axioms scalarJet_natural
#print axioms restricted_constraint
#print axioms CountHost.restrict
#print axioms CountHost.count
#print axioms CountHost.count_every_subspace
#print axioms CountHost.count_of_rank_bounds
#print axioms CountHost.count_int

end
end Decay2ScalarJetHost


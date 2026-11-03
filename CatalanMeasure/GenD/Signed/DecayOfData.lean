module

public import CatalanMeasure.GenD.Signed.NodeGeometry
public import CatalanMeasure.GenD.Signed.MarkedCap
public import CatalanMeasure.GenD.Analytic.DeltaSmall

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Polynomial
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Signed
noncomputable section

namespace Generic

open CatalanMeasure.GenD.Signed

def gapPredicate (dc : DesignConst) : ℝ → Prop := fun u => (dc.gstar : ℝ) ≤ |u|

/-- The three actual sheet bounds and the matched S1 weight certificate imply
delta-small at the same determinant design and n0² normalization. -/
theorem delta_small (dc : DesignConst) (target cost Psi0 α1 : ℝ)
    (hfirst : FreeFirstBound dc.toParameters target ((dc.n0 : ℝ) * cost))
    (hnear : FreeNearBound dc.toParameters (gapPredicate dc) (NodeSub (nodesτ dc))
      target ((dc.n0 : ℝ) * cost) α1)
    (hlarge : FreeLargeBound dc.toParameters (gapPredicate dc) target ((dc.n0 : ℝ) * cost) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc.toParameters.n N →
      ∀ k : ℕ, k < dc.toParameters.n N → ∀ a : Fin (dc.d0 * N),
      |(rowCommonFactor dc.toParameters N).eval (nodesτ dc N a)| *
        |restrictedWeight dc.toParameters N k (nodesτ dc N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (Psi0 * N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(((dc.n0 : ℝ) * cost + Psi0) * N)) →
      |aeval x (deltaPoly dc.toParameters N)| ≤
        Real.exp (-(((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2) - ε) * (N : ℝ)^2)) := by
  have hpoint : WeightedAtomPointBinom dc.toParameters (nodesτ dc) (gapPredicate dc)
      target ((dc.n0 : ℝ) * cost + Psi0) :=
    weighted_atom_point_binom_of_signed dc.toParameters dc.admissible (nodesτ dc)
      (gapPredicate dc) (NodeSub (nodesτ dc))
      (fun N m y a ha h => ⟨a, ha, h⟩) hfirst hnear hlarge le_rfl le_rfl le_rfl hweights
  exact delta_small_binom dc.toParameters dc.admissible (nodesτ dc) (gapPredicate dc)
    (fun N => gap_nodes_injective (astar_pos dc) (astar_lt_one dc) _)
    (fun N i => (gap_nodes_bounds (astar_pos dc) (astar_lt_one dc) _ i).1)
    (fun N i => gap_nodes_ne_zero (astar_pos dc) (astar_lt_one dc) _ i)
    (fun N i => by
      have h := (gap_nodes_coordinate (g := (dc.gstar : ℝ))
        (by exact_mod_cast dc.gstar_mem.1) (by exact_mod_cast dc.gstar_mem.2)
        (dc.d0 * N) i).2
      rw [← astar_eq dc] at h
      exact h)
    target ((dc.n0 : ℝ) * cost + Psi0)
    ((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2)) rfl hpoint

theorem delta_small_nodes (dc : DesignConst)
    (tau : (N : ℕ) → Fin (dc.d0 * N) → ℝ) (G : ℝ → Prop)
    (hinj : ∀ N, Function.Injective (tau N))
    (hmem : ∀ N a, tau N a ∈ Ioo (-1 : ℝ) 1)
    (hzero : ∀ N a, tau N a ≠ 0)
    (hsupport : ∀ N a, G (realCoordinate (tau N a)))
    (target cost Psi0 α1 : ℝ)
    (hfirst : FreeFirstBound dc.toParameters target ((dc.n0 : ℝ) * cost))
    (hnear : FreeNearBound dc.toParameters G (NodeSub tau)
      target ((dc.n0 : ℝ) * cost) α1)
    (hlarge : FreeLargeBound dc.toParameters G target ((dc.n0 : ℝ) * cost) α1)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc.toParameters.n N →
      ∀ k : ℕ, k < dc.toParameters.n N → ∀ a : Fin (dc.d0 * N),
      |(rowCommonFactor dc.toParameters N).eval (tau N a)| *
        |restrictedWeight dc.toParameters N k (tau N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤ 108000 * (N : ℝ) * Real.exp (Psi0 * N)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(((dc.n0 : ℝ) * cost + Psi0) * N)) →
      |aeval x (deltaPoly dc.toParameters N)| ≤
        Real.exp (-(((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2) - ε) * (N : ℝ)^2)) := by
  have hpoint : WeightedAtomPointBinom dc.toParameters tau G
      target ((dc.n0 : ℝ) * cost + Psi0) :=
    weighted_atom_point_binom_of_signed dc.toParameters dc.admissible tau
      G (NodeSub tau)
      (fun N m y a ha h => ⟨a, ha, h⟩) hfirst hnear hlarge le_rfl le_rfl le_rfl hweights
  exact delta_small_binom dc.toParameters dc.admissible tau G hinj hmem hzero hsupport
    target ((dc.n0 : ℝ) * cost + Psi0)
    ((dc.n0 : ℝ)^2 * (target - Real.log 2 / 2)) rfl hpoint

end Generic

end
end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.delta_small

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.delta_small_nodes

module

public import CatalanMeasure.GenD.Signed.Data.Assembly.Nodes
public import CatalanMeasure.GenD.Signed.Data.S1.Psi
public import CatalanMeasure.GenD.Signed.Data.S1.TrialEnd
public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.Analytic.WeightedAtom
public import CatalanMeasure.GenD.D58.Budget590

@[expose] public section

/-!
# 410 assembly, G6: `delta_small` from the three cases and the weight side

`delta_small_410`: given the first-case bound (`FreeFirstBound`), the second case with `m ≥ α₁ n`
(`FreeLargeBound`, `α₁ = 1/16`) and the signed near bound `FreeNearBound` with the node-set predicate
`NodeSub τ` of the real gap nodes, the weight side `Psi.s1_hweights_Psi0` (`w = 87.9663`) gives
`delta_small` with `ρ = K590.rhoEnd 87.9663 = 58 · secondCost' + 87.9663` and
`tΔ = 58² (target0 - log 2 / 2)`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly

open Set Filter Polynomial
open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Signed CatalanMeasure.GenD.Signed.Data.S1

open CatalanMeasure.GenD.D58

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

end Generic


/-- The second-population gap predicate: `g ≤ |u|` with `g = 401/2500`. -/
def G410 : ℝ → Prop := fun u => (401 / 2500 : ℝ) ≤ |u|

/-- The cost of the near case: `c2 = 58 · secondCost'`. -/
def c2_410 : ℝ := 58 * K590.secondCost'

/-- **`delta_small` of the 410 design**, from the three cases. -/
theorem delta_small_410
    (hfirst : FreeFirstBound D58.Odd.design K590.target0 ((D58.Odd.design.n0 : ℝ) * K590.secondCost'))
    (hnear : FreeNearBound D58.Odd.design G410 (NodeSub nodesτ) K590.target0 c2_410 (1 / 16))
    (hlarge : FreeLargeBound D58.Odd.design G410 K590.target0
      ((D58.Odd.design.n0 : ℝ) * K590.secondCost') (1 / 16)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(K590.rhoEnd (879663 / 10000) * (N : ℝ))) →
        |aeval x (deltaPoly D58.Odd.design N)| ≤
          Real.exp (-((58 ^ 2 * (K590.target0 - Real.log 2 / 2) - ε) * (N : ℝ) ^ 2))  := by
  have ha : (dc58.astar : ℝ) = S1.aGap := by norm_num [S1.aGap, S1.aQ]
  have hg : (dc58.gstar : ℝ) = (401 / 2500 : ℝ) := by norm_num
  have hnodes : Generic.nodesτ dc58 = nodesτ := by
    simp only [Generic.nodesτ, nodesτ, dc58_toParameters, D58.Odd.design, ha] <;> rfl
  have hgap : Generic.gapPredicate dc58 = G410 := by
    funext u
    simp only [Generic.gapPredicate, G410, hg]
  have hf : FreeFirstBound dc58.toParameters K590.target0 ((dc58.n0 : ℝ) * K590.secondCost') :=
    hfirst
  have hNd : NodeSub (Generic.nodesτ dc58) = NodeSub nodesτ := by
    funext N m y
    simp only [NodeSub, Generic.nodesτ, nodesτ, dc58_d0, dc58_toParameters,
      D58.Odd.design, ha] <;> rfl
  have hn : FreeNearBound dc58.toParameters (Generic.gapPredicate dc58)
      (NodeSub (Generic.nodesτ dc58)) K590.target0 ((dc58.n0 : ℝ) * K590.secondCost') (1 / 16) := by
    simpa only [hgap, hNd, dc58_n0, Nat.cast_ofNat, c2_410,
      dc58_toParameters, D58.Odd.design] using hnear
  have hl : FreeLargeBound dc58.toParameters (Generic.gapPredicate dc58) K590.target0
      ((dc58.n0 : ℝ) * K590.secondCost') (1 / 16) := by
    simpa only [hgap, dc58_n0, Nat.cast_ofNat, dc58_toParameters, D58.Odd.design] using hlarge
  have hw : ∀ᶠ N : ℕ in atTop, ∀ p m : ℕ, p + m = dc58.toParameters.n N →
      ∀ k : ℕ, k < dc58.toParameters.n N → ∀ a : Fin (dc58.d0 * N),
      |(rowCommonFactor dc58.toParameters N).eval (Generic.nodesτ dc58 N a)| *
        |restrictedWeight dc58.toParameters N k (Generic.nodesτ dc58 N) a| *
        (CatalanMeasure.binomBeta p m k : ℝ) ≤
          108000 * (N : ℝ) * Real.exp ((879663 / 10000) * N) := by
    have h53 : (58 - 5 : ℕ) = 53 := by decide
    simpa only [hnodes, nodesτ, dc58_toParameters, D58.Odd.design, dc58_d0, h53]
      using S1.Psi.s1_hweights_Psi0
  have h := Generic.delta_small dc58 K590.target0 K590.secondCost' (879663 / 10000) (1 / 16)
    hf hn hl hw
  simpa only [K590.rhoEnd_eq, dc58_n0, Nat.cast_ofNat, dc58_toParameters, D58.Odd.design] using h

end

end CatalanMeasure.GenD.Signed.Data.Assembly
#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.delta_small_410

#print axioms CatalanMeasure.GenD.Signed.Data.Assembly.Generic.delta_small

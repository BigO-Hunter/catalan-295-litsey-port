module

public import CatalanMeasure.GenD.Analytic.ChebTailCount
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic
open Polynomial Finset Set
noncomputable section

/-- On a strictly monotone tail branch, the level map is injective even when
the full inverse image has many branches. Deleting roots can only reduce count. -/
theorem polynomial_node_tail_count {ι : Type*} [Fintype ι] {K : ℕ}
    (p : ℝ[X]) (τ : ι → ℝ) (level : ι → Fin K)
    (hτ : Function.Injective τ) (hτ1 : ∀ i, τ i ≤ 1)
    (heval : ∀ i, p.eval (τ i) = CatalanMeasure.chebX K (level i))
    {t0 t : ℝ} (hmono : StrictMonoOn p.eval (Icc t0 1)) (ht0 : t0 ≤ t) (ht1 : t ≤ 1) :
    ((Finset.univ.filter (fun i => t ≤ τ i)).card : ℝ) ≤
      (K : ℝ) * Real.arccos (p.eval t) / Real.pi + 1 := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => t ≤ τ i)
  let T : Finset (Fin K) := Finset.univ.filter (fun j => p.eval t ≤ CatalanMeasure.chebX K j)
  have hindex : Set.InjOn level (s : Set ι) := by
    intro i hi j hj he
    have hti : t ≤ τ i := (Finset.mem_filter.mp hi).2
    have htj : t ≤ τ j := (Finset.mem_filter.mp hj).2
    apply hτ
    apply hmono.injOn ⟨ht0.trans hti, hτ1 i⟩ ⟨ht0.trans htj, hτ1 j⟩
    change p.eval (τ i) = p.eval (τ j)
    rw [heval, heval, he]
  have hsub : s.image level ⊆ T := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hti : t ≤ τ i := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← heval]
    exact hmono.monotoneOn ⟨ht0, ht1⟩ ⟨ht0.trans hti, hτ1 i⟩ hti
  have hc : s.card ≤ T.card := by
    rw [← Finset.card_image_of_injOn hindex]
    exact Finset.card_le_card hsub
  have hcR : (s.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hc
  exact hcR.trans (chebX_tail_count (p.eval t))

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.polynomial_node_tail_count

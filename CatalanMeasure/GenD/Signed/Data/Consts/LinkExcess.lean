module

public import CatalanMeasure.GenD.Signed.Phase2Contract

/-!
# D2 constants: `Dtop`, `Dcap` of `LinkCert` (the excess is affine in `alpha`)

`excess target cost t0 c2 delta n0 alpha = (t0 - target + delta) + (cost - c2/n0) alpha`, so
* with `c2 = n0 * cost` it is the constant `t0 - target + delta` (`excess_const`);
* in general its supremum over an interval is attained at an endpoint (`excess_le_of_ends`).
-/

@[expose] public section

namespace CatalanMeasure.Signed.Consts

open Set CatalanMeasure.Signed

theorem excess_const {target cost t0 c2 δ n0 : ℝ} (α : ℝ) (hn0 : n0 ≠ 0) (hc2 : c2 = n0 * cost) :
    excess target cost t0 c2 δ n0 α = t0 - target + δ := by
  unfold excess
  rw [hc2]
  field_simp
  ring

theorem excess_le_of_ends {target cost t0 c2 δ n0 lo hi α D : ℝ} (hα : α ∈ Icc lo hi)
    (hlo : excess target cost t0 c2 δ n0 lo ≤ D) (hhi : excess target cost t0 c2 δ n0 hi ≤ D) :
    excess target cost t0 c2 δ n0 α ≤ D := by
  unfold excess at *
  obtain ⟨h1, h2⟩ := hα
  set s : ℝ := cost - c2 / n0 with hs
  have e : ∀ x : ℝ, (-target + Real.log 2 / 2 + cost * x + δ) - ((-t0 + Real.log 2 / 2) + c2 * x / n0)
      = (t0 - target + δ) + s * x := fun x => by rw [hs]; ring
  rw [e] at hlo hhi ⊢
  rcases le_total 0 s with hs0 | hs0
  · nlinarith [mul_le_mul_of_nonneg_left h2 hs0]
  · nlinarith [mul_le_mul_of_nonneg_left h1 (neg_nonneg.2 hs0)]

end CatalanMeasure.Signed.Consts

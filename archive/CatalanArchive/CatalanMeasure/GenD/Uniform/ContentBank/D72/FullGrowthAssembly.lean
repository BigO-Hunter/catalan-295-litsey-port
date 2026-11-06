module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.GrowthAssembly
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.ContentPriceBridge
public import CatalanMeasure.GenD.Signed.Davis.ScalarInstance72
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.LedgerW
open CatalanMeasure.GenD.Signed.Davis.ScalarInstance72 (price72 contentBeta72)
noncomputable section

/-- Consumer-facing growth statement from the exact full tape, with only the
nullity family list and its window bounds left as producer inputs. -/
theorem full_growth_from_kap72 (fams : List (NullityLB P72))
    (hkap : ∀ w ∈ windows72 fullWindowTape, ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
      w.a * N < p → (p : ℝ) ≤ w.b * N →
      (N : ℝ) * w.K.eval ((p : ℝ) / N) - 2 ≤ ((lb72 fams).kap N p : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop,
      Real.log ((canonicalNormalizer P72 Signed.dc72.admissible (lb72 fams) 98
        Signed.dc72_normalizer_cut).D N : ℝ) ≤ (price72 + ε) * (N : ℝ) ^ 2 := by
  filter_upwards [growth_from_kap72 fams fullWindowTape fullWindowTape_check
    full_band_check hkap hε] with N hN
  have hprice : gD P72 f72 kappa072 (windows72 fullWindowTape) ≤ price72 := by
    simpa only [price72, contentBeta72] using full_content_price72_le
  exact hN.trans (mul_le_mul_of_nonneg_right
    (add_le_add hprice le_rfl) (sq_nonneg (N : ℝ)))

#print axioms full_growth_from_kap72
end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

module
public import CatalanMeasure.GenD.Signed.Data.Trial72.NearEndpoint72
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16
@[expose] public section
set_option Elab.async false
namespace CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyTheorem72
open Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.Signed
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Uniform.Arithmetic
open Davis.ScalarInstance72
noncomputable section

/-- Internal assembly entry point. The remaining external inputs are the
content certificate and the exact field and spike-environment covers. -/
theorem of_covers (lb : NullityLB dc72.toParameters)
    (hcontent : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer dc72.toParameters dc72.admissible lb 98 dc72_normalizer_cut).D N) ≤
        (price72 + ε) * (N : ℝ) ^ 2)
    (F : Rows72.FieldRows)
    (E0 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T0.D N)))
    (E1 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T1.D N)))
    (E2 : ∀ᶠ N : ℕ in atTop, Nonempty (SpikeEnv (T2.D N))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(400 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  catalan_irrationalityMeasure_400_of_producer_data lb hcontent StandaloneEndpoints72.first
    (NearEndpoint72.hnear F NearEndpoint72.eventualRegions E0 E1 E2) StandaloneEndpoints72.large

end
end CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyTheorem72
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.AssemblyTheorem72.of_covers

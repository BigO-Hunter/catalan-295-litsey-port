module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FullHkap
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FullGrowthAssembly

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.Arithmetic
open CatalanMeasure.GenD.Uniform.W.TheoremC CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.GenD.Signed.Davis.ScalarInstance72 (price72)
noncomputable section

theorem hcontent (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop,
      Real.log ((canonicalNormalizer P72 Signed.dc72.admissible (lb72 fams72) 98
        Signed.dc72_normalizer_cut).D N : ℝ) ≤ (price72 + ε) * (N : ℝ)^2 :=
  full_growth_from_kap72 fams72 hkap72 ε hε

#print axioms hcontent
end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

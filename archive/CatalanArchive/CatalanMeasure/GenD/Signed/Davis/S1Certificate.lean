module
public import CatalanMeasure.GenD.Signed.Davis.S1CircleData
public import CatalanMeasure.GenD.Signed.Davis.S1RealSegments
public import CatalanMeasure.GenD.Signed.Davis.S1SelectorData
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 10
namespace CatalanMeasure.GenD.Signed.Davis.S1Certificate
open CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
noncomputable section

/-- Closed Davis72 S1 data, at the frozen strict exponent 108.754. -/
theorem hweights72 :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p m : ℕ, p+m=72*N →
      ∀ k : ℕ, k<72*N → ∀ i : Fin (66*N),
        |(rowCommonFactor dc72.toParameters N).eval (tau72 N i)| *
          |restrictedWeight dc72.toParameters N k (tau72 N) i| *
          (CatalanMeasure.binomBeta p m k : ℝ) ≤
            108000*(N : ℝ)*Real.exp ((54377/500 : ℝ)*N) :=
  hweights72_of_contour S1CircleData.circleG S1RealSegments.segmentPhi S1SelectorData.hPsi72

end
end CatalanMeasure.GenD.Signed.Davis.S1Certificate
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Certificate.hweights72

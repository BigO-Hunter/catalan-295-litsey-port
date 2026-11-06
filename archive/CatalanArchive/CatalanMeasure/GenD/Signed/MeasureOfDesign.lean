module

public import CatalanMeasure.GenD.Final
public import CatalanMeasure.GenD.Signed.DesignConst

@[expose] public section

namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD Filter CatalanMeasure.Parametric OAI.InternalCatalan
noncomputable section

namespace Generic

/-- Assemble a measure bound from matching certificates for one shared design.
`D` supplies the normalizer, growth, nonvanishing, decay and payment evidence.
No certificate output is inferred from the design choices alone. -/
theorem catalan_irrationalityMeasure_of_design (dc : DesignConst)
    (D : DesignData dc.toParameters) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(D.B : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| := by
  simpa [catalan] using measure_of_design dc.toParameters D

end Generic

end
end CatalanMeasure.GenD.Signed

#print axioms CatalanMeasure.GenD.Signed.Generic.catalan_irrationalityMeasure_of_design

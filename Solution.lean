module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.GenD.Signed.RouteI.Measure295

public section

/-!
Proof of the statement in `Challenge.lean`: the 295 bound of
`CatalanMeasure.GenD.Signed.RouteI.Measure295.catalan_irrationalityMeasure_295`.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_295 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(295 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.GenD.Signed.RouteI.Measure295.catalan_irrationalityMeasure_295

#print axioms catalan_irrationalityMeasure_295

end CatalanIrrationalityMeasure

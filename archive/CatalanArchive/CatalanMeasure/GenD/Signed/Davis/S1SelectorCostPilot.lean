module

public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10
namespace CatalanMeasure.GenD.Signed.Davis.S1SelectorCostPilot

/-! ONE frozen selector cell at the maximum Psi upper bound. Measures the exact
existing 124-bit log evaluator and rational inequalities, with no polynomial
reevaluation. This is not a continuum-selector soundness theorem. -/

def scalarOK (lo hi U Ψ : ℚ) : Bool :=
  match LogEval.logQ 12 (3/5) with
  | none => false
  | some (v,e) =>
    let a := 12 - 72*hi
    let contour := a*v + |a| * e + (24330011831893/549755813888 : ℚ)
    if lo ≤ 1/2 then
      match LogEval.logQ 12 2 with
      | none => false
      | some (v2,e2) => decide (contour ≤ U ∧ U+72*(v2+e2) ≤ Ψ)
    else
      match LogEval.logQ 12 lo, LogEval.logQ 12 (1-lo) with
      | some (v1,e1), some (v2,e2) =>
        decide (contour ≤ U ∧ U+72*(lo*(e1-v1)+(1-lo)*(e2-v2)) ≤ Ψ)
      | _, _ => false

def lo : ℚ := (1275 / 2048 : ℚ)
def hi : ℚ := (2551 / 4096 : ℚ)
def contourUpper : ℚ := (33552952516191 / 549755813888 : ℚ)
def psiUpper : ℚ := (119576174384707 / 1099511627776 : ℚ)

theorem representative_scalar : scalarOK lo hi contourUpper psiUpper = true := by
  -- kcost: 1 s estimated;three rational logQ12 evaluations and frozen affine/entropy comparisons.
  decide +kernel

end CatalanMeasure.GenD.Signed.Davis.S1SelectorCostPilot
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorCostPilot.representative_scalar

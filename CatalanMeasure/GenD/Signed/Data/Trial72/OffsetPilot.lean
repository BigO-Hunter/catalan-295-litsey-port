module

public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Data
public import CatalanMeasure.GenD.Signed.Data.Cells.Core

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.OffsetPilot
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Actual75-pole sV enclosure from frozen kappa-offset-map.json.
The generic EvalKappa sConst bridge is held; this checks the same Core
pole sum and exports its analytic absolute error directly. -/
def poles : List PoleR := T0.trial.v.tail.map fun t => ⟨-t.rr, -t.ri, t.zr, t.zi⟩
theorem sv_checked : poleSumI 56 0 poles = some (219958300254890109, 319) := by
  -- kcost: 1.050 s estimated;10500 integer operations,75 pole-log terms.
  decide +kernel

theorem sv_abs :
    |(poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      (219958300254890109 : ℝ) / 2 ^ 56| ≤ (319 : ℝ) / 2 ^ 56 := by
  simpa only [Rat.cast_zero, Int.cast_ofNat, Nat.cast_ofNat] using
    poleSumI_spec 56 (by norm_num) 0 poles 219958300254890109 319 sv_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.OffsetPilot
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.OffsetPilot.sv_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.OffsetPilot.sv_abs

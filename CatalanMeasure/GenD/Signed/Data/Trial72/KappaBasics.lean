module

public import CatalanMeasure.GenD.Signed.Data.Trial72.OffsetPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Cells
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Exact D72 shared P56 primitives. Source-only production pack; sV is reused, not recomputed. EvalKappa held semantic/affine bridge is not imported or claimed. -/
def sVPoles : List PoleR := OffsetPilot.poles
theorem sV_checked : poleSumI 56 0 sVPoles = some ((219958300254890109), 319) := by
  exact OffsetPilot.sv_checked
theorem sV_abs :
    |(sVPoles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((219958300254890109 : ℤ) : ℝ) / 2^56| ≤ (319 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 sVPoles (219958300254890109) 319 sV_checked

def tVPoles : List PoleR := T0.trial.v.tail.map (fun t => ⟨-t.rr/2, -t.ri/2, 2*t.zr, 2*t.zi⟩)
theorem tV_checked : poleSumI 56 0 tVPoles = some ((605944718502765539), 290) := by
  -- kcost: 1.0500 s estimated;75 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem tV_abs :
    |(tVPoles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((605944718502765539 : ℤ) : ℝ) / 2^56| ≤ (290 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 tVPoles (605944718502765539) 290 tV_checked

def tPPoles : List PoleR := T0.trial.p.tail.map (fun t => ⟨-t.rr/2, -t.ri/2, 2*t.zr, 2*t.zi⟩)
theorem tP_checked : poleSumI 56 0 tPPoles = some ((-374182068496652202), 281) := by
  -- kcost: 1.0500 s estimated;75 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem tP_abs :
    |(tPPoles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((-374182068496652202 : ℤ) : ℝ) / 2^56| ≤ (281 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 tPPoles (-374182068496652202) 281 tP_checked

def sA0Poles : List PoleR := T0.trial.a.tail.map (fun t => ⟨-t.rr, -t.ri, t.zr, t.zi⟩)
theorem sA0_checked : poleSumI 56 0 sA0Poles = some ((2781564582940640), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem sA0_abs :
    |(sA0Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((2781564582940640 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 sA0Poles (2781564582940640) 40 sA0_checked

def tA0Poles : List PoleR := T0.trial.a.tail.map (fun t => ⟨-t.rr/2, -t.ri/2, 2*t.zr, 2*t.zi⟩)
theorem tA0_checked : poleSumI 56 0 tA0Poles = some ((-3592953181869290), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem tA0_abs :
    |(tA0Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((-3592953181869290 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 tA0Poles (-3592953181869290) 40 tA0_checked

def sA1Poles : List PoleR := T1.trial.a.tail.map (fun t => ⟨-t.rr, -t.ri, t.zr, t.zi⟩)
theorem sA1_checked : poleSumI 56 0 sA1Poles = some ((3321757840045031), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem sA1_abs :
    |(sA1Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((3321757840045031 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 sA1Poles (3321757840045031) 40 sA1_checked

def tA1Poles : List PoleR := T1.trial.a.tail.map (fun t => ⟨-t.rr/2, -t.ri/2, 2*t.zr, 2*t.zi⟩)
theorem tA1_checked : poleSumI 56 0 tA1Poles = some ((-3173693578418126), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem tA1_abs :
    |(tA1Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((-3173693578418126 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 tA1Poles (-3173693578418126) 40 tA1_checked

def sA2Poles : List PoleR := T2.trial.a.tail.map (fun t => ⟨-t.rr, -t.ri, t.zr, t.zi⟩)
theorem sA2_checked : poleSumI 56 0 sA2Poles = some ((3225998431658358), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem sA2_abs :
    |(sA2Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((3225998431658358 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 sA2Poles (3225998431658358) 40 sA2_checked

def tA2Poles : List PoleR := T2.trial.a.tail.map (fun t => ⟨-t.rr/2, -t.ri/2, 2*t.zr, 2*t.zi⟩)
theorem tA2_checked : poleSumI 56 0 tA2Poles = some ((-2730056753377949), 40) := by
  -- kcost: 0.2800 s estimated;20 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem tA2_abs :
    |(tA2Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((-2730056753377949 : ℤ) : ℝ) / 2^56| ≤ (40 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 tA2Poles (-2730056753377949) 40 tA2_checked

def log2Poles : List PoleR := [⟨1, 0, -2, 0⟩]
theorem log2_checked : poleSumI 56 0 log2Poles = some ((49946518145322873), 3) := by
  -- kcost: 0.0140 s estimated;1 actual pole-log terms, P56 shared log tables.
  decide +kernel
theorem log2_abs :
    |(log2Poles.map (fun q => (q.rho * Complex.log (((0 : ℝ) : ℂ) - q.pc)).re)).sum -
      ((49946518145322873 : ℤ) : ℝ) / 2^56| ≤ (3 : ℝ) / 2^56 := by
  simpa only [Rat.cast_zero] using poleSumI_spec 56 (by norm_num) 0 log2Poles (49946518145322873) 3 log2_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.sV_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.tV_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.tP_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.sA0_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.tA0_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.sA1_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.tA1_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.sA2_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.tA2_abs
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.KappaBasics.log2_abs

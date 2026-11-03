module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalPerturbPilot
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section
/-! Actual largest exact-result-height four-tail perturb shard. The finite list is the existing frozen D72 object, with exact rational coefficients; no reinterpretation at2^-40 or assumed fixed denominator. -/
def f : List ℚ := T1.dpL
def tails : List TailQ := ReferenceData.secondPData.tail
def shard : List TailQ := (tails.drop 68).take 4
def crossUb : ℚ := (qlist (raw_ints% [8642633973327488963, 1208925819614629174706176])).headD 0
def sqUb : ℚ := (qlist (raw_ints% [225494025791451996297, 1208925819614629174706176])).headD 0
theorem cross_checked : qCross f shard ≤ crossUb := by
  -- kcost: 1.81 s measured earlier same-sized raw Horner class; 480 actual coefficient visits, exact rational variant.
  decide +kernel

theorem sq_checked : qSq f 0 ≤ sqUb := by
  -- kcost: 0.16 s measured raw finite-square class; 120 actual coefficients.
  decide +kernel
def dotUb : ℚ := (qlist (raw_ints% [-66689994389189931600657, 1208925819614629174706176])).headD 0
theorem dot_checked : qDot NormData.secondPInt f 0 ≤ dotUb := by
  -- kcost: 0.16 s estimated; 120 base/rational products and divisions.
  decide +kernel
end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalPerturbPilot
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalPerturbPilot.cross_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalPerturbPilot.sq_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalPerturbPilot.dot_checked

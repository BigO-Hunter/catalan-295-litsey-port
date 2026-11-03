module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalAPilot
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section
/-! Actual largest exact-result-height four-tail A shard. The finite list is the existing frozen D72 object, with exact rational coefficients; no reinterpretation at2^-40 or assumed fixed denominator. -/
def f : List ℚ := T2.aF
def tails : List TailQ := T2.trial.a.tail
def shard : List TailQ := (tails.drop 0).take 4
def crossUb : ℚ := (qlist (raw_ints% [86923276375113, 576460752303423488])).headD 0
def sqUb : ℚ := (qlist (raw_ints% [22900386759162411, 1152921504606846976])).headD 0
theorem cross_checked : qCross f shard ≤ crossUb := by
  -- kcost: 1.81 s measured earlier same-sized raw Horner class; 480 actual coefficient visits, exact rational variant.
  decide +kernel

theorem sq_checked : qSq f 0 ≤ sqUb := by
  -- kcost: 0.16 s measured raw finite-square class; 120 actual coefficients.
  decide +kernel
end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalAPilot
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalAPilot.cross_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RationalAPilot.sq_checked

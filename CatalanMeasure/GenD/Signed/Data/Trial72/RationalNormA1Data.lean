module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA1Data
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

def f : List ℚ := T1.aF
def tails : List TailQ := T1.trial.a.tail
def caps : List ℚ := qlist (raw_ints% [76591060910479, 1152921504606846976, 112410511582387, 1152921504606846976, 36351236333149, 1152921504606846976, 8563263264401, 4503599627370496, 9327966951498995, 576460752303423488])
def squareUb : ℚ := (qlist (raw_ints% [19449607902563667, 1152921504606846976])).headD 0
def normUb : ℚ := (qlist (raw_ints% [53898851543892489, 576460752303423488])).headD 0

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA1Data

module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Data
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

def f : List ℚ := T2.aF
def tails : List TailQ := T2.trial.a.tail
def caps : List ℚ := qlist (raw_ints% [86923276375113, 576460752303423488, 371961157433, 144115188075855872, 13427546166247, 1152921504606846976, 2478499005971125, 1152921504606846976, 19445572143063341, 1152921504606846976])
def squareUb : ℚ := (qlist (raw_ints% [22900386759162411, 1152921504606846976])).headD 0
def normUb : ℚ := (qlist (raw_ints% [101512338617548487, 1152921504606846976])).headD 0

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA2Data

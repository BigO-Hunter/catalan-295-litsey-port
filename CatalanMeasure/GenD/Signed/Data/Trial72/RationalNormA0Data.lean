module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
public import CatalanMeasure.GenD.Signed.Data.Trial72.NormData
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Data
open CatalanMeasure.Cert CatalanMeasure.CellCert OAI.InternalCatalan
open CatalanMeasure.Signed.FieldForm CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.TaylorCell (vecAdd)
open CatalanMeasure.GenD.Signed.Data.Consts.EvalNormCore
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

def f : List ℚ := T0.aF
def tails : List TailQ := T0.trial.a.tail
def caps : List ℚ := qlist (raw_ints% [-133878244702451, 1152921504606846976, 25158140019625, 576460752303423488, 45280060907621, 576460752303423488, 270707049867981, 288230376151711744, 463804880203271, 36028797018963968])
def squareUb : ℚ := (qlist (raw_ints% [17167164720504699, 1152921504606846976])).headD 0
def normUb : ℚ := (qlist (raw_ints% [54175492182958079, 576460752303423488])).headD 0

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RationalNormA0Data

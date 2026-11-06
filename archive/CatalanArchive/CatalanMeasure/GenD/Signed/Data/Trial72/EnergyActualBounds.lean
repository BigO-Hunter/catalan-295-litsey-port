module

public import CatalanMeasure.GenD.Signed.Data.Trial72.MergeOKPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds
open CatalanMeasure.Signed CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
noncomputable section

theorem merge0 : MergeOK MergeOKPilot.cutsT MergeOKPilot.cutsF MergeOKPilot.original EnergyCacheData.R0 :=
  MergeOKPilot.merge_checked

theorem bounds00 (N : ℕ) :
    (EnergyCacheTotal00.lower : ℝ) ≤ refEnergy (T0.D N).μ ∧ refEnergy (T0.D N).μ ≤ (EnergyCacheTotal00.upper : ℝ) := by
  have h := refEnergy_cached_enc_merged (T0.D N).μ MergeOKPilot.original EnergyCacheData.R0
    (MergeOKPilot.actual_ref N) MergeOKPilot.original_ok merge0
    EnergyCacheTotal00.cache_plan 7 EnergyCacheTotal00.enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal00.cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal00.cap_checked.2)⟩

theorem bounds01 (N M : ℕ) :
    (EnergyCacheTotal01.lower : ℝ) ≤ refBil (T0.D N).μ (T1.D M).μ ∧ refBil (T0.D N).μ (T1.D M).μ ≤ (EnergyCacheTotal01.upper : ℝ) := by
  have h := refBil_cached_enc_merged (T0.D N).μ (T1.D M).μ MergeOKPilot.original EnergyMerge1.original EnergyCacheData.R0 EnergyCacheData.R1
    (MergeOKPilot.actual_ref N) (EnergyMerge1.actual_ref M) MergeOKPilot.original_ok EnergyMerge1.original_ok merge0 EnergyMerge1.merge_checked
    EnergyCacheTotal01.cache_plan 7 EnergyCacheTotal01.enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal01.cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal01.cap_checked.2)⟩

theorem bounds11 (N : ℕ) :
    (EnergyCacheTotal11.lower : ℝ) ≤ refEnergy (T1.D N).μ ∧ refEnergy (T1.D N).μ ≤ (EnergyCacheTotal11.upper : ℝ) := by
  have h := refEnergy_cached_enc_merged (T1.D N).μ EnergyMerge1.original EnergyCacheData.R1
    (EnergyMerge1.actual_ref N) EnergyMerge1.original_ok EnergyMerge1.merge_checked
    EnergyCacheTotal11.cache_plan 7 EnergyCacheTotal11.enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal11.cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal11.cap_checked.2)⟩

theorem bounds12 (N M : ℕ) :
    (EnergyCacheTotal12.lower : ℝ) ≤ refBil (T1.D N).μ (T2.D M).μ ∧ refBil (T1.D N).μ (T2.D M).μ ≤ (EnergyCacheTotal12.upper : ℝ) := by
  have h := refBil_cached_enc_merged (T1.D N).μ (T2.D M).μ EnergyMerge1.original EnergyMerge2.original EnergyCacheData.R1 EnergyCacheData.R2
    (EnergyMerge1.actual_ref N) (EnergyMerge2.actual_ref M) EnergyMerge1.original_ok EnergyMerge2.original_ok EnergyMerge1.merge_checked EnergyMerge2.merge_checked
    EnergyCacheTotal12.cache_plan 7 EnergyCacheTotal12.enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal12.cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal12.cap_checked.2)⟩

theorem bounds22 (N : ℕ) :
    (EnergyCacheTotal22.lower : ℝ) ≤ refEnergy (T2.D N).μ ∧ refEnergy (T2.D N).μ ≤ (EnergyCacheTotal22.upper : ℝ) := by
  have h := refEnergy_cached_enc_merged (T2.D N).μ EnergyMerge2.original EnergyCacheData.R2
    (EnergyMerge2.actual_ref N) EnergyMerge2.original_ok EnergyMerge2.merge_checked
    EnergyCacheTotal22.cache_plan 7 EnergyCacheTotal22.enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal22.cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 EnergyCacheTotal22.cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds.bounds00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds.bounds01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds.bounds11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds.bounds12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyActualBounds.bounds22

module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache00_0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache00_0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache00_1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache00_1_1

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def cachedForms : List LF := [cache00_0_0, cache00_0_1, cache00_1_0, cache00_1_1]
theorem cache_plan : List.Forall₂ (fun (j : Job) (l : LF) => j.lf.normalize = l) (refPlan R0 R0) cachedForms := by
  exact (List.Forall₂.cons EnergyCache00_0_0.cache_checked (List.Forall₂.cons EnergyCache00_0_1.cache_checked (List.Forall₂.cons EnergyCache00_1_0.cache_checked (List.Forall₂.cons EnergyCache00_1_1.cache_checked List.Forall₂.nil))))
def literal : ℚ × ℚ := ((qlist (raw_ints% [1097970883028452058418418246758063436809839889619381019062200420529596410205228639557605160239014401, 1315443173671336107776658132860641428922113504304513209602017148472828766665379512603607025319936000])).headD 0, (qlist (raw_ints% [6496129532576866842859156202590603497543938982337025764221112356444940997, 11777426671643742968173586854939492169434995785715071468862815179764261426777071870776995873816576])).headD 0)
def lower : ℚ := (qlist (raw_ints% [481158847380187329, 576460752303423488])).headD 0
def upper : ℚ := (qlist (raw_ints% [962317694760374661, 1152921504606846976])).headD 0
theorem enclosure_checked : (LF.sumL cachedForms).enc 7 = some literal := by
  -- kcost: 0.126 s measured C32 largest aggregate; exact normalized LF sum then one enclosure.
  decide +kernel

theorem cap_checked : lower ≤ literal.1 - literal.2 ∧ literal.1 + literal.2 ≤ upper := by decide +kernel
theorem energy_bounds (μ : SRef) (hμ : IsRefQ μ R0) (hR : R0.OK) :
    (lower : ℝ) ≤ refEnergy μ ∧ refEnergy μ ≤ (upper : ℝ) := by
  have h := refEnergy_cached_enc μ R0 hμ hR cache_plan 7 enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00.cache_plan
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00.enclosure_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal00.energy_bounds

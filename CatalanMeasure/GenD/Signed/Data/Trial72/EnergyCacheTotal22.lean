module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_0_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_2_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_1_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_1_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_2_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache22_2_2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def cachedForms : List LF := [cache22_0_0, cache22_0_1, cache22_0_2, cache22_1_0, cache22_2_0, cache22_1_1, cache22_1_2, cache22_2_1, cache22_2_2]
theorem cache_plan : List.Forall₂ (fun (j : Job) (l : LF) => j.lf.normalize = l) (refPlan R2 R2) cachedForms := by
  exact (List.Forall₂.cons EnergyCache22_0_0.cache_checked (List.Forall₂.cons EnergyCache22_0_1.cache_checked (List.Forall₂.cons EnergyCache22_0_2.cache_checked (List.Forall₂.cons EnergyCache22_1_0.cache_checked (List.Forall₂.cons EnergyCache22_2_0.cache_checked (List.Forall₂.cons EnergyCache22_1_1.cache_checked (List.Forall₂.cons EnergyCache22_1_2.cache_checked (List.Forall₂.cons EnergyCache22_2_1.cache_checked (List.Forall₂.cons EnergyCache22_2_2.cache_checked List.Forall₂.nil)))))))))
def literal : ℚ × ℚ := ((qlist (raw_ints% [32089593466290225904063192324257900734183418327856968044777578261628156602034978003289130504747663844518790250919523000563586595376681742688566898210177069978076252253845069500441919996876152630705768594166623732776702195240689826187697280831827055880102064067150298878651901254632997414280165178102687443100594018949640247761472617619825036338830023151886887905308578934730571229419745141810185708706517017208555410298375281764159965859613251993, 41070996544618230622528376179754347062531292511524184038246208283273529240670886994719402635717739880799951889955549008131275720279257579391066619609850517670718479492226929752114109949570103874560944756325015036574061359784947818687813249873429813998363481421405373664984237987655752702333720954444412381155789773533568581881483215883531714560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0, (qlist (raw_ints% [58827773392573389492285749023303088138801939064123772134521417513795367901061585817651664292696606257042392553521272455611956053695814464192459114978558326752508083409960394367688486091441809833252634032384298808649063615612155424041043680649, 119643449179278621621060604448617031511881856471892994189927124052542813406541817767495010947736954430971644902266936686540294803658095347908522192687562636656640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0)
def lower : ℚ := (qlist (raw_ints% [900800698643512093, 1152921504606846976])).headD 0
def upper : ℚ := (qlist (raw_ints% [28150021832609753, 36028797018963968])).headD 0
theorem enclosure_checked : (LF.sumL cachedForms).enc 7 = some literal := by
  -- kcost: 0.126 s measured C32 largest aggregate; exact normalized LF sum then one enclosure.
  decide +kernel

theorem cap_checked : lower ≤ literal.1 - literal.2 ∧ literal.1 + literal.2 ≤ upper := by decide +kernel
theorem energy_bounds (μ : SRef) (hμ : IsRefQ μ R2) (hR : R2.OK) :
    (lower : ℝ) ≤ refEnergy μ ∧ refEnergy μ ≤ (upper : ℝ) := by
  have h := refEnergy_cached_enc μ R2 hμ hR cache_plan 7 enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22.cache_plan
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22.enclosure_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal22.energy_bounds

module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_0_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_2_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_1_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_1_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_2_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache11_2_2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def cachedForms : List LF := [cache11_0_0, cache11_0_1, cache11_0_2, cache11_1_0, cache11_2_0, cache11_1_1, cache11_1_2, cache11_2_1, cache11_2_2]
theorem cache_plan : List.Forall₂ (fun (j : Job) (l : LF) => j.lf.normalize = l) (refPlan R1 R1) cachedForms := by
  exact (List.Forall₂.cons EnergyCache11_0_0.cache_checked (List.Forall₂.cons EnergyCache11_0_1.cache_checked (List.Forall₂.cons EnergyCache11_0_2.cache_checked (List.Forall₂.cons EnergyCache11_1_0.cache_checked (List.Forall₂.cons EnergyCache11_2_0.cache_checked (List.Forall₂.cons EnergyCache11_1_1.cache_checked (List.Forall₂.cons EnergyCache11_1_2.cache_checked (List.Forall₂.cons EnergyCache11_2_1.cache_checked (List.Forall₂.cons EnergyCache11_2_2.cache_checked List.Forall₂.nil)))))))))
def literal : ℚ × ℚ := ((qlist (raw_ints% [386853002493011898540740494672792015901829990579900339448939631333085016800527350325556594094794826292818871983789666968344555992707256608618585422693715051563558522319621284045639566815245796536534991139886105797487921831741781256952676383513559099094208201597422668961354652836763331642053698595383441881197084852581307084510483891961605460567480141781987564245041573190900527746077142619725918002798101253830049071773701131333926952761969116219427, 465931473405332868406834519686288811213590293197963432366658665398481214074837793637573055111083603689747353373445303873758169935941157413259999466162169738281260061466439959372723096066551598576951894294443447893907418787476298783433175523774203772250342016125187012165787573809540051665130447802520644660170724321599307441512624718006452224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0, (qlist (raw_ints% [561816709883796900048547594349253908184630935713565536713393725026952422482618613518544117226031685541246191887640456856452335121634439377369143030022920956551643569126756257140063159118404877266979897169807613977566182199445356852375962410975581, 30998530014631279238183883879868958164442117358626821221935663959067910746240380057941889200095483648024471633769160868785440017311415612867208022650868501315584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0)
def lower : ℚ := (qlist (raw_ints% [957246228584168303, 1152921504606846976])).headD 0
def upper : ℚ := (qlist (raw_ints% [478623114292084153, 576460752303423488])).headD 0
theorem enclosure_checked : (LF.sumL cachedForms).enc 7 = some literal := by
  -- kcost: 0.126 s measured C32 largest aggregate; exact normalized LF sum then one enclosure.
  decide +kernel

theorem cap_checked : lower ≤ literal.1 - literal.2 ∧ literal.1 + literal.2 ≤ upper := by decide +kernel
theorem energy_bounds (μ : SRef) (hμ : IsRefQ μ R1) (hR : R1.OK) :
    (lower : ℝ) ≤ refEnergy μ ∧ refEnergy μ ≤ (upper : ℝ) := by
  have h := refEnergy_cached_enc μ R1 hμ hR cache_plan 7 enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11.cache_plan
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11.enclosure_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal11.energy_bounds

module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_0_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_1_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache01_1_2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def cachedForms : List LF := [cache01_0_0, cache01_0_1, cache01_0_2, cache01_1_0, cache01_1_1, cache01_1_2]
theorem cache_plan : List.Forall₂ (fun (j : Job) (l : LF) => j.lf.normalize = l) (refPlan R0 R1) cachedForms := by
  exact (List.Forall₂.cons EnergyCache01_0_0.cache_checked (List.Forall₂.cons EnergyCache01_0_1.cache_checked (List.Forall₂.cons EnergyCache01_0_2.cache_checked (List.Forall₂.cons EnergyCache01_1_0.cache_checked (List.Forall₂.cons EnergyCache01_1_1.cache_checked (List.Forall₂.cons EnergyCache01_1_2.cache_checked List.Forall₂.nil))))))
def literal : ℚ × ℚ := ((qlist (raw_ints% [27151328439306172540238915970595809888206841532251174898751004495499752522499508849749890863565282764184016869287327422892791178038089375530953648623221680201899450242933538075014853222158171030674360782372208204441779254275608923665533775273819516465481688739726953585263180939889083748704622729000186133284257205899316615581462818558082815743316569446234067028528549109245970343682397935436947165937927394857684000756242173349842244799348830043537, 32615203138373300788478416378040216784951320523857440265666106577893684985238645554630113857775852258282314736141171271163071895515881018928199962631351881679688204302650797156090616724658611900386632600611041352573519315123340914840322286664194264057523941128763090851605130166667803616559131346176445126211950702511951520905883730260451655680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0, (qlist (raw_ints% [3462190489378925621186929248478552769303913789928337429478522316826420388798443364053798754856185583104676593485052083954194560376348116231335060348724632563687209183675990145077734637207976483498362493417999452739126167718533000473118745359113, 368631167741561158508132673166009232225798152372859495612207895729456235901236952040390033730865210949480203212390021142313340746406023504366798107199517312942080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0)
def lower : ℚ := (qlist (raw_ints% [479888938657102851, 576460752303423488])).headD 0
def upper : ℚ := (qlist (raw_ints% [959777877314205705, 1152921504606846976])).headD 0
theorem enclosure_checked : (LF.sumL cachedForms).enc 7 = some literal := by
  -- kcost: 0.126 s measured C32 largest aggregate; exact normalized LF sum then one enclosure.
  decide +kernel

theorem cap_checked : lower ≤ literal.1 - literal.2 ∧ literal.1 + literal.2 ≤ upper := by decide +kernel
theorem bil_bounds (μ ν : SRef) (hμ : IsRefQ μ R0) (hν : IsRefQ ν R1)
    (hR : R0.OK) (hS : R1.OK) :
    (lower : ℝ) ≤ refBil μ ν ∧ refBil μ ν ≤ (upper : ℝ) := by
  have h := refBil_cached_enc μ ν R0 R1 hμ hν hR hS cache_plan 7 enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01.cache_plan
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01.enclosure_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal01.bil_bounds

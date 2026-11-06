module

public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_0_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_0_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_0_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_1_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_2_0
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_1_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_1_2
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_2_1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCache12_2_2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
open EnergyCacheData
def cachedForms : List LF := [cache12_0_0, cache12_0_1, cache12_0_2, cache12_1_0, cache12_2_0, cache12_1_1, cache12_1_2, cache12_2_1, cache12_2_2]
theorem cache_plan : List.Forall₂ (fun (j : Job) (l : LF) => j.lf.normalize = l) (refPlan R1 R2) cachedForms := by
  exact (List.Forall₂.cons EnergyCache12_0_0.cache_checked (List.Forall₂.cons EnergyCache12_0_1.cache_checked (List.Forall₂.cons EnergyCache12_0_2.cache_checked (List.Forall₂.cons EnergyCache12_1_0.cache_checked (List.Forall₂.cons EnergyCache12_2_0.cache_checked (List.Forall₂.cons EnergyCache12_1_1.cache_checked (List.Forall₂.cons EnergyCache12_1_2.cache_checked (List.Forall₂.cons EnergyCache12_2_1.cache_checked (List.Forall₂.cons EnergyCache12_2_2.cache_checked List.Forall₂.nil)))))))))
def literal : ℚ × ℚ := ((qlist (raw_ints% [223229667055446919766961484660915697258526613979268346998091360136570569747861137191664600501042727917349173463168059844078991401116064129002637034165394535858908407771951225809311150490603381070599346289916035320909466483767247146163126629392444137810998266213154043745399714371661387623118130746299121278110854663942449580675609644753631932105319702240234080697517313582855871200624713147303629991065653676462776543854320332043983834637411346733763, 277229226676173056702066539213341842672086224452788242258161905912096322374528487214355967791094744195399675257199955804886111111884988660889699682366490994277349736572531775826770242159598201153286377105193851496874914178548397776142739436645651244488953499594486272238643606416676330740752616442499783572801580971351587927700011707213839073280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0, (qlist (raw_ints% [128814292790924792246680786198256573933320984617846861082769427524809518030463946358570564242348171893274670413590403245132091413592285797380926693587527644943022177003901054505733338584984884928908740004937805534014911568676558549374775736062367, 470322524359922857406927893349735916977742470268820735781092832482409680287785076741187284415241820866578190305463130422951503710931823091778328619530418640650240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000])).headD 0)
def lower : ℚ := (qlist (raw_ints% [232087978872332899, 288230376151711744])).headD 0
def upper : ℚ := (qlist (raw_ints% [928351915489331599, 1152921504606846976])).headD 0
theorem enclosure_checked : (LF.sumL cachedForms).enc 7 = some literal := by
  -- kcost: 0.126 s measured C32 largest aggregate; exact normalized LF sum then one enclosure.
  decide +kernel

theorem cap_checked : lower ≤ literal.1 - literal.2 ∧ literal.1 + literal.2 ≤ upper := by decide +kernel
theorem bil_bounds (μ ν : SRef) (hμ : IsRefQ μ R1) (hν : IsRefQ ν R2)
    (hR : R1.OK) (hS : R2.OK) :
    (lower : ℝ) ≤ refBil μ ν ∧ refBil μ ν ≤ (upper : ℝ) := by
  have h := refBil_cached_enc μ ν R1 R2 hμ hν hR hS cache_plan 7 enclosure_checked
  exact ⟨((Rat.cast_le (K := ℝ)).2 cap_checked.1).trans h.ge_lower,
    h.le_upper.trans ((Rat.cast_le (K := ℝ)).2 cap_checked.2)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12.cache_plan
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12.enclosure_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyCacheTotal12.bil_bounds

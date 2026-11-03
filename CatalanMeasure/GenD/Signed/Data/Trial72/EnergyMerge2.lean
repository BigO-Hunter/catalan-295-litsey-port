module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMerge
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Binding

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Actual original signed D72 trial2, exact merged density with cuts from every original/merged endpoint. -/
def original : RefQ := ⟨T2.trial.qT, T2.trial.qF, T2.trial.qTn, T2.trial.qFn⟩
def merged : RefQ := EnergyCacheData.R2
def cutsT : List ℚ := qlist (raw_ints% [0, 1, 243, 65536, 165, 32768, 777, 32768, 1641, 65536, 4093, 65536, 4181, 65536, 1, 1])
def cutsF : List ℚ := qlist (raw_ints% [0, 1, 23, 1024, 1559, 65536, 4553, 65536, 2295, 32768, 401, 2500, 1, 1])
theorem merge_checked : MergeOK cutsT cutsF original merged := by
  -- kcost: 0.7705 s op model; endpoint/cut adjacency and 13 exact covering-poly comparisons.
  decide +kernel

theorem original_ok : original.OK := by
  have h := T2.dataOK (C := (T2.Cb : ℝ)) le_rfl
  exact ⟨h.pT, h.pF, h.pTn, h.pFn⟩

theorem actual_ref (N : ℕ) : IsRefQ (T2.D N).μ original := by
  have h := T2.specD N
  exact ⟨h.hμT, h.hμF, h.hμTn, h.hμFn⟩

theorem actual_energy_form (N : ℕ) : refEnergy (T2.D N).μ = (refBilLF merged merged).eval := by
  rw [refEnergy_eval _ original (actual_ref N) original_ok]
  exact refBilLF_merge original original merged merged merge_checked merge_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2.merge_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2.original_ok
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2.actual_ref
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2.actual_energy_form

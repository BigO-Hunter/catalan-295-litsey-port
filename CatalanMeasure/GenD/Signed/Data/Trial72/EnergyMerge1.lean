module

public import CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMerge
public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Binding

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm CatalanMeasure.Signed.ReflectionEnergy
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section
/-! Actual original signed D72 trial1, exact merged density with cuts from every original/merged endpoint. -/
def original : RefQ := ⟨T1.trial.qT, T1.trial.qF, T1.trial.qTn, T1.trial.qFn⟩
def merged : RefQ := EnergyCacheData.R1
def cutsT : List ℚ := qlist (raw_ints% [0, 1, 161, 65536, 31, 8192, 695, 32768, 739, 32768, 3929, 65536, 4017, 65536, 1, 1])
def cutsF : List ℚ := qlist (raw_ints% [0, 1, 777, 32768, 1569, 65536, 4585, 65536, 4671, 65536, 401, 2500, 1, 1])
theorem merge_checked : MergeOK cutsT cutsF original merged := by
  -- kcost: 0.7705 s op model; endpoint/cut adjacency and 13 exact covering-poly comparisons.
  decide +kernel

theorem original_ok : original.OK := by
  have h := T1.dataOK (C := (T1.Cb : ℝ)) le_rfl
  exact ⟨h.pT, h.pF, h.pTn, h.pFn⟩

theorem actual_ref (N : ℕ) : IsRefQ (T1.D N).μ original := by
  have h := T1.specD N
  exact ⟨h.hμT, h.hμF, h.hμTn, h.hμFn⟩

theorem actual_energy_form (N : ℕ) : refEnergy (T1.D N).μ = (refBilLF merged merged).eval := by
  rw [refEnergy_eval _ original (actual_ref N) original_ok]
  exact refBilLF_merge original original merged merged merge_checked merge_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1.merge_checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1.original_ok
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1.actual_ref
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1.actual_energy_form

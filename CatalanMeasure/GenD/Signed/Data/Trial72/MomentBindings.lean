module

public import CatalanMeasure.GenD.Signed.Data.Assembly.CurvFast
public import CatalanMeasure.GenD.Signed.Data.Consts.EvalRefMomMerge
public import CatalanMeasure.GenD.Signed.Data.Trial72.MergeOKPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge1
public import CatalanMeasure.GenD.Signed.Data.Trial72.EnergyMerge2
public import CatalanMeasure.GenD.Signed.Data.Trial72.RInstPilot
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentReduction1
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentReduction2
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentReduction01
public import CatalanMeasure.GenD.Signed.Data.Trial72.MomentDiffPilot

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000

namespace CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings
open CatalanMeasure.Signed.FieldForm
open CatalanMeasure.GenD.Signed.Data.Assembly
open CatalanMeasure.GenD.Signed.Data.Consts.EvalRef
open CatalanMeasure.Cert.Iv (mom1 dl mom1_dl)
noncomputable section

theorem merge0 : MergeOK MergeOKPilot.cutsT MergeOKPilot.cutsF MergeOKPilot.original EnergyCacheData.R0 :=
  MergeOKPilot.merge_checked

theorem actual_mpos0 (N n : ℕ) (τ : ℝ) :
    mpos (T0.D N).μ τ n = τ ^ (n + 1) * (mom1 EnergyCacheData.p0_0.p (n + 2) : ℝ) := by
  rw [mpos_eq _ MergeOKPilot.original (MergeOKPilot.actual_ref N) MergeOKPilot.original_ok,
    mposQ_merge merge0, mposQ_single EnergyCacheData.R0 EnergyCacheData.p0_0.p rfl rfl]

theorem actual_self0 (K : ℕ) :
    ipPartQ MergeOKPilot.original K = ∑ n ∈ Finset.range K,
      mom1 EnergyCacheData.p0_0.p (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  rw [ipPartQ_merge merge0]
  unfold ipPartQ
  exact Finset.sum_congr rfl (fun n _ => by rw [mposQ_single EnergyCacheData.R0 EnergyCacheData.p0_0.p rfl rfl])

theorem actual_mpos1 (N n : ℕ) (τ : ℝ) :
    mpos (T1.D N).μ τ n = τ ^ (n + 1) * (mom1 EnergyCacheData.p1_0.p (n + 2) : ℝ) := by
  rw [mpos_eq _ EnergyMerge1.original (EnergyMerge1.actual_ref N) EnergyMerge1.original_ok,
    mposQ_merge EnergyMerge1.merge_checked, mposQ_single EnergyCacheData.R1 EnergyCacheData.p1_0.p rfl rfl]

theorem actual_self1 (K : ℕ) :
    ipPartQ EnergyMerge1.original K = ∑ n ∈ Finset.range K,
      mom1 EnergyCacheData.p1_0.p (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  rw [ipPartQ_merge EnergyMerge1.merge_checked]
  unfold ipPartQ
  exact Finset.sum_congr rfl (fun n _ => by rw [mposQ_single EnergyCacheData.R1 EnergyCacheData.p1_0.p rfl rfl])

theorem actual_mpos2 (N n : ℕ) (τ : ℝ) :
    mpos (T2.D N).μ τ n = τ ^ (n + 1) * (mom1 EnergyCacheData.p2_0.p (n + 2) : ℝ) := by
  rw [mpos_eq _ EnergyMerge2.original (EnergyMerge2.actual_ref N) EnergyMerge2.original_ok,
    mposQ_merge EnergyMerge2.merge_checked, mposQ_single EnergyCacheData.R2 EnergyCacheData.p2_0.p rfl rfl]

theorem actual_self2 (K : ℕ) :
    ipPartQ EnergyMerge2.original K = ∑ n ∈ Finset.range K,
      mom1 EnergyCacheData.p2_0.p (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  rw [ipPartQ_merge EnergyMerge2.merge_checked]
  unfold ipPartQ
  exact Finset.sum_congr rfl (fun n _ => by rw [mposQ_single EnergyCacheData.R2 EnergyCacheData.p2_0.p rfl rfl])

theorem actual_diff01 (K : ℕ) :
    ipDiffRQ MergeOKPilot.original EnergyMerge1.original K = ∑ n ∈ Finset.range K,
      mom1 (dl EnergyCacheData.p0_0.p EnergyCacheData.p1_0.p) (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  rw [ipDiffRQ_merge merge0 EnergyMerge1.merge_checked]
  exact ipDiffRQ_single (R := EnergyCacheData.R0) (S := EnergyCacheData.R1) rfl rfl rfl rfl K

theorem actual_diff12 (K : ℕ) :
    ipDiffRQ EnergyMerge1.original EnergyMerge2.original K = ∑ n ∈ Finset.range K,
      mom1 (dl EnergyCacheData.p1_0.p EnergyCacheData.p2_0.p) (n + 2) ^ 2 / ((n : ℚ) + 1) := by
  rw [ipDiffRQ_merge EnergyMerge1.merge_checked EnergyMerge2.merge_checked]
  exact ipDiffRQ_single (R := EnergyCacheData.R1) (S := EnergyCacheData.R2) rfl rfl rfl rfl K

theorem density_eq0 : RInstPilot.density = EnergyCacheData.p0_0.p := by decide +kernel
theorem cap0 : RInstPilot.Lip ≤ ipPartQ MergeOKPilot.original 1000 := by
  rw [actual_self0, ← density_eq0]
  exact RInstPilot.hip0

theorem density_eq01 : MomentReduction01.density = dl EnergyCacheData.p0_0.p EnergyCacheData.p1_0.p := by decide +kernel
theorem cap01 : ipDiffRQ MergeOKPilot.original EnergyMerge1.original 1000 ≤ MomentReduction01.bound := by
  rw [actual_diff01, ← density_eq01]
  exact MomentReduction01.bound_checked

theorem density_eq1 : MomentReduction1.density = EnergyCacheData.p1_0.p := by decide +kernel
theorem cap1 : MomentReduction1.bound ≤ ipPartQ EnergyMerge1.original 1000 := by
  rw [actual_self1, ← density_eq1]
  exact MomentReduction1.bound_checked

theorem density_eq12 : MomentDiffPilot.density = dl EnergyCacheData.p1_0.p EnergyCacheData.p2_0.p := by decide +kernel
theorem cap12 : ipDiffRQ EnergyMerge1.original EnergyMerge2.original 1000 ≤ MomentDiffPilot.bound := by
  rw [actual_diff12, ← density_eq12]
  exact MomentDiffPilot.bound_checked

theorem density_eq2 : MomentReduction2.density = EnergyCacheData.p2_0.p := by decide +kernel
theorem cap2 : MomentReduction2.bound ≤ ipPartQ EnergyMerge2.original 1000 := by
  rw [actual_self2, ← density_eq2]
  exact MomentReduction2.bound_checked

end
end CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings.cap0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings.cap01
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings.cap1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings.cap12
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.MomentBindings.cap2

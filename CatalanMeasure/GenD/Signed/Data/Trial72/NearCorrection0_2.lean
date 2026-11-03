module

public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2
open CatalanMeasure.Signed CatalanMeasure.Refinement CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open NearCorrectionNodes
def capUpper : ℚ := (qlist (raw_ints% [467829, 604462909807314587353088000000])).headD 0
def cP : ℚ := (qlist (raw_ints% [-2104779873, 4294967296])).headD 0
def rP : ℚ := (qlist (raw_ints% [11, 6400])).headD 0
def bP : ℚ := (qlist (raw_ints% [1, 1208925819614629174706176])).headD 0
theorem capP_bound : capInt (cP : ℝ) (rP : ℝ) (1/1000) ≤ (bP : ℝ) := by
  apply NearCorrectionCore.whole (E := E) (F := exp0) (f := arg0) 60
    (by decide +kernel) (by decide +kernel) e_nonneg exp0_nonneg e_le exp0_le
  · decide +kernel
  · -- kcost: 0.2 s conservative TL small rational cap comparator.
    decide +kernel

def cS : ℚ := (qlist (raw_ints% [-6395645109, 17179869184])).headD 0
def rS : ℚ := (qlist (raw_ints% [6261, 11000000])).headD 0
def bS : ℚ := (qlist (raw_ints% [1, 1208925819614629174706176])).headD 0
theorem capS_bound : capInt (cS : ℝ) (rS : ℝ) (1/1000) ≤ (bS : ℝ) := by
  apply NearCorrectionCore.whole (E := E) (F := exp0) (f := arg0) 60
    (by decide +kernel) (by decide +kernel) e_nonneg exp0_nonneg e_le exp0_le
  · decide +kernel
  · -- kcost: 0.2 s conservative TL small rational cap comparator.
    decide +kernel

theorem combined : (467829 / 1000000 : ℝ) * (capInt (cP : ℝ) (rP : ℝ) (1/1000) +
    capInt (cS : ℝ) (rS : ℝ) (1/1000)) ≤ (capUpper : ℝ) := by
  have hq : (467829 / 1000000 : ℚ) * (bP + bS) ≤ capUpper := by decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at h
  exact (mul_le_mul_of_nonneg_left (add_le_add capP_bound capS_bound) (by norm_num)).trans h

end
end CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2.capP_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2.capS_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection0_2.combined

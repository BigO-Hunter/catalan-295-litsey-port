module

public import CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrectionNodes

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0
open CatalanMeasure.Signed CatalanMeasure.Refinement CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
noncomputable section

open NearCorrectionNodes
def capUpper : ℚ := (qlist (raw_ints% [10221608737238770342805697, 120892581961462917470617600000])).headD 0
def cP : ℚ := (qlist (raw_ints% [-1071482985, 2147483648])).headD 0
def rP : ℚ := (qlist (raw_ints% [11, 128])).headD 0
def bP : ℚ := (qlist (raw_ints% [109180855077469018641, 604462909807314587353088])).headD 0
theorem capP_bound : capInt (cP : ℝ) (rP : ℝ) (1/1000) ≤ (bP : ℝ) := by
  exact NearCorrectionCore.clipped (by decide +kernel) log_bounds.1 log_bounds.2
    (by decide +kernel) (by decide +kernel)

def cS : ℚ := (qlist (raw_ints% [-190588947, 536870912])).headD 0
def rS : ℚ := (qlist (raw_ints% [312511, 11000000])).headD 0
def bS : ℚ := (qlist (raw_ints% [251105339743179, 2361183241434822606848])).headD 0
theorem capS_bound : capInt (cS : ℝ) (rS : ℝ) (1/1000) ≤ (bS : ℝ) := by
  apply NearCorrectionCore.whole (E := E) (F := exp2) (f := arg2) 12
    (by decide +kernel) (by decide +kernel) e_nonneg exp2_nonneg e_le exp2_le
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
end CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0.capP_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0.capS_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.NearCorrection1_0.combined

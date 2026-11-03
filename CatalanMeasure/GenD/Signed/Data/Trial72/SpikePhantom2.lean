module

public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2
open CatalanMeasure.Signed.Consts CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def Aq : ℚ := 1257798236774585 / 1099511627776
def A1q : ℚ := 2007169413977 / 1099511627776
def B1q : ℚ := 386055281697 / 274877906944
def BRq : ℚ := 512126924357 / 549755813888
def Lθ : ℚ := 7

theorem log_bound : Real.log (1 / (1/1024 : ℝ)) ≤ (Lθ : ℝ) := by
  have hlog := Real.log_two_lt_d9
  have h := Real.log_le_log (by norm_num : 0 < (1/(1/1024) : ℝ))
    (by norm_num : (1/(1/1024) : ℝ) ≤ 2^10)
  rw [Real.log_pow] at h
  norm_num [Lθ] at h ⊢
  linarith

theorem tail_disk : tailZB T2.aTail = true := by decide +kernel
theorem abs_bound : absq T2.aF + tailMaj T2.aTail ≤ Aq := by decide +kernel
theorem a_bound : absSq T2.aF + Lθ * tailW T2.aTail ≤ A1q := by decide +kernel
theorem b_bound : absSq T2.bsL ≤ B1q := by decide +kernel
theorem ref_bound : brQ T2.RF ≤ BRq := by
  -- kcost: 2 s conservative TL model; 400 exact weighted coefficients.
  decide +kernel
theorem scalar : 72*(2*A1q+BRq+Lθ) + 40*B1q + 5/4 + Lθ ≤ 72*14 := by decide +kernel
theorem phantom_bound : (72 : ℝ)*(2*(A1q : ℝ)+BRq+Lθ) + 40*B1q + 5/4 + Lθ ≤ 72*14 := by
  exact_mod_cast scalar

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.log_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.abs_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.a_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.b_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.ref_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom2.phantom_bound

module

public import CatalanMeasure.GenD.Signed.Data.Consts.SpikeA
public import CatalanMeasure.GenD.Signed.Data.Trial72.T1Data

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1
open CatalanMeasure.Signed.Consts CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def Aq : ℚ := 35900711573119 / 68719476736
def A1q : ℚ := 1871506184617 / 1099511627776
def B1q : ℚ := 807993238195 / 549755813888
def BRq : ℚ := 265859991851 / 274877906944
def Lθ : ℚ := 7

theorem log_bound : Real.log (1 / (1/1000 : ℝ)) ≤ (Lθ : ℝ) := by
  have hlog := Real.log_two_lt_d9
  have h := Real.log_le_log (by norm_num : 0 < (1/(1/1000) : ℝ))
    (by norm_num : (1/(1/1000) : ℝ) ≤ 2^10)
  rw [Real.log_pow] at h
  norm_num [Lθ] at h ⊢
  linarith

theorem tail_disk : tailZB T1.aTail = true := by decide +kernel
theorem abs_bound : absq T1.aF + tailMaj T1.aTail ≤ Aq := by decide +kernel
theorem a_bound : absSq T1.aF + Lθ * tailW T1.aTail ≤ A1q := by decide +kernel
theorem b_bound : absSq T1.bsL ≤ B1q := by decide +kernel
theorem ref_bound : brQ T1.RF ≤ BRq := by
  -- kcost: 2 s conservative TL model; 400 exact weighted coefficients.
  decide +kernel
theorem scalar : 72*(2*A1q+BRq+Lθ) + 40*B1q + 5/4 + Lθ ≤ 72*14 := by decide +kernel
theorem phantom_bound : (72 : ℝ)*(2*(A1q : ℝ)+BRq+Lθ) + 40*B1q + 5/4 + Lθ ≤ 72*14 := by
  exact_mod_cast scalar

end
end CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.log_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.abs_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.a_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.b_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.ref_bound
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.SpikePhantom1.phantom_bound

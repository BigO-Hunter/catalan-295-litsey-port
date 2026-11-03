module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.WindowPrice
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic
noncomputable section

def bandCheck (ws : List WindowQ) : Bool :=
  ws.all fun w => decide (29 * w.b ≤ 954)

-- kcost: 0.178 s conservative; 148 exact rational multiplications and comparisons.
#time theorem full_band_check : bandCheck fullWindowTape = true := by decide +kernel
-- kcost: 0.178 s conservative; 148 exact rational multiplications and comparisons.
#time theorem fallback_band_check : bandCheck fallbackWindowTape = true := by decide +kernel

theorem window_pool_hcert72 {ws : List WindowQ} (hc : bandCheck ws = true)
    {w : KapWindow} (hw : w ∈ windows72 ws) {N p : Nat} (hN : 0 < N)
    (hp : (p : ℝ) ≤ w.b * N) :
    (N : ℝ) * w.G.eval ((p : ℝ) / N) - 2 ≤ (safeOddLoss P72 N p : ℝ) := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
  simp only [bandCheck, List.all_eq_true, decide_eq_true_eq] at hc
  have hb : (29 : ℝ) * (q.b : ℝ) ≤ 954 := by exact_mod_cast hc q hq
  have hNR : (0 : ℝ) ≤ N := by positivity
  have hbN := mul_le_mul_of_nonneg_right hb hNR
  change (p : ℝ) ≤ (q.b : ℝ) * N at hp
  have hcap : (p : ℝ) ≤ (954 / 29 : ℝ) * N := by nlinarith
  simpa [WindowQ.toKapWindow, PL.Prof.eval, PL.hinges, mul_comm] using g14472 hN hcap

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

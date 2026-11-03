module

public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable1

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RACached21
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def weights (k : ℕ) : ℚ := -(-1 : ℚ) ^ (k + 1) * T2.RF.getD k 0 / ((k : ℚ) + 1)
def interval : Iv := cachedLoop ivS (fun k I => mulC I (weights k)) 0 T1.aF (ATailTable1.table.take 400) zero
def lower : ℚ := (qlist (raw_ints% [82358120377076599548742203246682631810, 443426488243037769948249630619149892803])).headD 0
def upper : ℚ := (qlist (raw_ints% [82358120377076599548742203246682632277, 443426488243037769948249630619149892803])).headD 0
theorem checked : interval = ⟨(82358120377076599548742203246682631810), (82358120377076599548742203246682632277)⟩ := by
  -- kcost: 6.46 s measured same-shape C25 rate, 400 cached dot terms.
  decide +kernel
def exactDot : ℚ := ∑ k ∈ Finset.range 400, useq T1.aF ATailChunkData1.poles k * weights k
theorem enclosed : Enc (ivS : ℚ) interval exactDot := by
  have h := cachedLoop_enc (S := ivS) (S' := (ivS : ℚ)) ATailChunkData1.poles
    (fun k I => mulC I (weights k)) (fun k x => x * weights k)
    (fun k I x hx => enc_mulC hx _) T1.aF 400 0 _ (ATailTable1.table.take 400) zero 0
    ATailTable1.prefix_checked (polesEnc_init ivS _) (enc_zero _)
  simpa [interval, exactDot] using h
theorem bounds : lower ≤ exactDot ∧ exactDot ≤ upper :=
  ⟨le_of_enc ivS_pos enclosed lower (by rw [checked]; decide +kernel),
    le_of_enc' ivS_pos enclosed upper (by rw [checked]; decide +kernel)⟩

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RACached21
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached21.checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached21.bounds

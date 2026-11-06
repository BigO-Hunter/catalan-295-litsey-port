module

public import CatalanMeasure.GenD.Signed.Data.Trial72.T0Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable0

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RACached00
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def weights (k : ℕ) : ℚ := -(-1 : ℚ) ^ (k + 1) * T0.RF.getD k 0 / ((k : ℚ) + 1)
def interval : Iv := cachedLoop ivS (fun k I => mulC I (weights k)) 0 T0.aF (ATailTable0.table.take 400) zero
def lower : ℚ := (qlist (raw_ints% [1050111823383261270380018111638265879, 5474401089420219382077155933569751763])).headD 0
def upper : ℚ := (qlist (raw_ints% [85059057694044162900781467042699536672, 443426488243037769948249630619149892803])).headD 0
theorem checked : interval = ⟨(85059057694044162900781467042699536199), (85059057694044162900781467042699536672)⟩ := by
  -- kcost: 6.46 s measured same-shape C25 rate, 400 cached dot terms.
  decide +kernel
def exactDot : ℚ := ∑ k ∈ Finset.range 400, useq T0.aF ATailChunkData0.poles k * weights k
theorem enclosed : Enc (ivS : ℚ) interval exactDot := by
  have h := cachedLoop_enc (S := ivS) (S' := (ivS : ℚ)) ATailChunkData0.poles
    (fun k I => mulC I (weights k)) (fun k x => x * weights k)
    (fun k I x hx => enc_mulC hx _) T0.aF 400 0 _ (ATailTable0.table.take 400) zero 0
    ATailTable0.prefix_checked (polesEnc_init ivS _) (enc_zero _)
  simpa [interval, exactDot] using h
theorem bounds : lower ≤ exactDot ∧ exactDot ≤ upper :=
  ⟨le_of_enc ivS_pos enclosed lower (by rw [checked]; decide +kernel),
    le_of_enc' ivS_pos enclosed upper (by rw [checked]; decide +kernel)⟩

def frozenLower : ℚ := (qlist (raw_ints% [221155973711946465, 1152921504606846976])).headD 0
theorem frozen_lower : frozenLower ≤ exactDot :=
  le_trans (show frozenLower ≤ lower by decide +kernel) bounds.1

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RACached00
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached00.checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached00.bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached00.frozen_lower

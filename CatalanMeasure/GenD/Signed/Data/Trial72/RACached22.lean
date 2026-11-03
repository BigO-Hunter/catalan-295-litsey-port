module

public import CatalanMeasure.GenD.Signed.Data.Trial72.T2Data
public import CatalanMeasure.GenD.Signed.Data.Trial72.ATailTable2

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace CatalanMeasure.GenD.Signed.Data.Trial72.RACached22
open CatalanMeasure.Cert.Iv CatalanMeasure.CellCert
open CatalanMeasure.GenD.Signed.Data.Trial72 CatalanMeasure.GenD.Signed.Data.Trial
noncomputable section

def weights (k : ℕ) : ℚ := -(-1 : ℚ) ^ (k + 1) * T2.RF.getD k 0 / ((k : ℚ) + 1)
def interval : Iv := cachedLoop ivS (fun k I => mulC I (weights k)) 0 T2.aF (ATailTable2.table.take 400) zero
def lower : ℚ := (qlist (raw_ints% [26635165693660649184243154060973302933, 147808829414345923316083210206383297601])).headD 0
def upper : ℚ := (qlist (raw_ints% [79905497080981947552729462182919909280, 443426488243037769948249630619149892803])).headD 0
theorem checked : interval = ⟨(79905497080981947552729462182919908799), (79905497080981947552729462182919909280)⟩ := by
  -- kcost: 6.46 s measured same-shape C25 rate, 400 cached dot terms.
  decide +kernel
def exactDot : ℚ := ∑ k ∈ Finset.range 400, useq T2.aF ATailChunkData2.poles k * weights k
theorem enclosed : Enc (ivS : ℚ) interval exactDot := by
  have h := cachedLoop_enc (S := ivS) (S' := (ivS : ℚ)) ATailChunkData2.poles
    (fun k I => mulC I (weights k)) (fun k x => x * weights k)
    (fun k I x hx => enc_mulC hx _) T2.aF 400 0 _ (ATailTable2.table.take 400) zero 0
    ATailTable2.prefix_checked (polesEnc_init ivS _) (enc_zero _)
  simpa [interval, exactDot] using h
theorem bounds : lower ≤ exactDot ∧ exactDot ≤ upper :=
  ⟨le_of_enc ivS_pos enclosed lower (by rw [checked]; decide +kernel),
    le_of_enc' ivS_pos enclosed upper (by rw [checked]; decide +kernel)⟩

def frozenLower : ℚ := (qlist (raw_ints% [51939142317582431, 288230376151711744])).headD 0
theorem frozen_lower : frozenLower ≤ exactDot :=
  le_trans (show frozenLower ≤ lower by decide +kernel) bounds.1

end
end CatalanMeasure.GenD.Signed.Data.Trial72.RACached22
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached22.checked
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached22.bounds
#print axioms CatalanMeasure.GenD.Signed.Data.Trial72.RACached22.frozen_lower

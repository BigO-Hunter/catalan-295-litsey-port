module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1P0000
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT1CoverD0B0P000L000 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-6317608997077 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT1P0000Lo : ℝ) (ceSignedSpmTopT1P0000Hi : ℝ) := by
    norm_num [ceSignedSpmTopT1P0000Lo, ceSignedSpmTopT1P0000Hi, SignedSpmTopT1P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT1P0000Bound x h'
  norm_num [SignedSpmTopT1P0000Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT1CoverD0B0P000 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT1Fq (poleF ceSignedSpmTopT1Fq.poles) 0 x + lfieldTower ceSignedSpmTopT1Ts 0 x ≤ ((((-6317608997077 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  SignedSpmTopT1CoverD0B0P000L000
#print axioms SignedSpmTopT1CoverD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT1Cover

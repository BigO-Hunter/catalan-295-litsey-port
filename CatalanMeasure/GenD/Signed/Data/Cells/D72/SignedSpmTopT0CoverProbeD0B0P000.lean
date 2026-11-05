module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0P0000
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmTopT0CoverProbeD0B0P000L000 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmTopT0P0000Lo : ℝ) (ceSignedSpmTopT0P0000Hi : ℝ) := by
    norm_num [ceSignedSpmTopT0P0000Lo, ceSignedSpmTopT0P0000Hi, SignedSpmTopT0P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmTopT0P0000Bound x h'
  norm_num [SignedSpmTopT0P0000Literal.q2] at h ⊢
  exact h

theorem SignedSpmTopT0CoverProbeD0B0P000 : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmTopT0Fq (poleF ceSignedSpmTopT0Fq.poles) 0 x + lfieldTower ceSignedSpmTopT0Ts 0 x ≤ ((((-3151596717623 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  SignedSpmTopT0CoverProbeD0B0P000L000
#print axioms SignedSpmTopT0CoverProbeD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmTopT0Cover

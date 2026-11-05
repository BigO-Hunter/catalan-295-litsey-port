module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200P0001
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpmRT01200CoverProbeD0B0P000L000 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((23810019 : ℚ) / 232000000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0000Lo : ℝ) (ceSignedSpmRT01200P0000Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0000Lo, ceSignedSpmRT01200P0000Hi, SignedSpmRT01200P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0000Bound x h'
  norm_num [SignedSpmRT01200P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpmRT01200CoverProbeD0B0P000L001 : ∀ x ∈ Icc ((((23810019 : ℚ) / 232000000) : ℚ) : ℝ) ((((2471027 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpmRT01200P0001Lo : ℝ) (ceSignedSpmRT01200P0001Hi : ℝ) := by
    norm_num [ceSignedSpmRT01200P0001Lo, ceSignedSpmRT01200P0001Hi, SignedSpmRT01200P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpmRT01200P0001Bound x h'
  norm_num [SignedSpmRT01200P0001Literal.q2] at h ⊢
  exact h

theorem SignedSpmRT01200CoverProbeD0B0P000 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((2471027 : ℚ) / 23200000) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpmRT01200Fq (poleF ceSignedSpmRT01200Fq.poles) 0 x + lfieldTower ceSignedSpmRT01200Ts 0 x ≤ ((((-2882111069751 : ℚ) / 549755813888) : ℚ) : ℝ) :=
  (cover_union SignedSpmRT01200CoverProbeD0B0P000L000 SignedSpmRT01200CoverProbeD0B0P000L001)
#print axioms SignedSpmRT01200CoverProbeD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpmRT01200Cover

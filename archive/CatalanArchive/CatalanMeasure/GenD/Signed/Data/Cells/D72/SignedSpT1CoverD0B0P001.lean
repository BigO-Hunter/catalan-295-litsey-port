module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0017
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD0B0P001L016 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((7557 : ℚ) / 65536) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0015Lo : ℝ) (ceSignedSpT1P0015Hi : ℝ) := by
    norm_num [ceSignedSpT1P0015Lo, ceSignedSpT1P0015Hi, SignedSpT1P0015Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0015Bound x h'
  norm_num [SignedSpT1P0015Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P001L017 : ∀ x ∈ Icc ((((7557 : ℚ) / 65536) : ℚ) : ℝ) ((((3969 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0016Lo : ℝ) (ceSignedSpT1P0016Hi : ℝ) := by
    norm_num [ceSignedSpT1P0016Lo, ceSignedSpT1P0016Hi, SignedSpT1P0016Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0016Bound x h'
  norm_num [SignedSpT1P0016Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P001L018 : ∀ x ∈ Icc ((((3969 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0017Lo : ℝ) (ceSignedSpT1P0017Hi : ℝ) := by
    norm_num [ceSignedSpT1P0017Lo, ceSignedSpT1P0017Hi, SignedSpT1P0017Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0017Bound x h'
  norm_num [SignedSpT1P0017Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD0B0P001 : ∀ x ∈ Icc ((((3715 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 8) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) :=
  (cover_union SignedSpT1CoverD0B0P001L016 (cover_union SignedSpT1CoverD0B0P001L017 SignedSpT1CoverD0B0P001L018))
#print axioms SignedSpT1CoverD0B0P001

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Literal
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1P0014
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option profiler true


private theorem SignedSpT1CoverD0B0P000L000Field : fieldNFCheck ceSignedSpT1End00FullFq ceSignedSpT1ZeroPlain = true := by decide +kernel
private theorem SignedSpT1CoverD0B0P000L000Terms : laurentNF ceSignedSpT1End00FullTs = laurentNF [] := by decide +kernel

private theorem SignedSpT1CoverD0B0P000L000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1End00Lo : ℝ) (ceSignedSpT1End00Hi : ℝ) := by
    norm_num [ceSignedSpT1End00Lo, ceSignedSpT1End00Hi, SignedSpT1End00Literal.q2, ceSignedSpT1End00EndLiteral.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1End00Bound x h' (by norm_num [ceSignedSpT1End00Site, ceSignedSpT1End00EndLiteral.q2]; exact ne_of_gt hd.1)
  rw [fieldNFCheck_sound SignedSpT1CoverD0B0P000L000Field x, ← laurentNF_sound ceSignedSpT1End00FullTs x, SignedSpT1CoverD0B0P000L000Terms, laurentNF_sound [] x] at h
  norm_num [SignedSpT1End00Literal.q2, ceSignedSpT1End00EndLiteral.q2, ceSignedSpT1End00Target] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L001 : ∀ x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((143 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0000Lo : ℝ) (ceSignedSpT1P0000Hi : ℝ) := by
    norm_num [ceSignedSpT1P0000Lo, ceSignedSpT1P0000Hi, SignedSpT1P0000Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0000Bound x h'
  norm_num [SignedSpT1P0000Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L002 : ∀ x ∈ Icc ((((143 : ℚ) / 16384) : ℚ) : ℝ) ((((135 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0001Lo : ℝ) (ceSignedSpT1P0001Hi : ℝ) := by
    norm_num [ceSignedSpT1P0001Lo, ceSignedSpT1P0001Hi, SignedSpT1P0001Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0001Bound x h'
  norm_num [SignedSpT1P0001Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L003 : ∀ x ∈ Icc ((((135 : ℚ) / 8192) : ℚ) : ℝ) ((((397 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0002Lo : ℝ) (ceSignedSpT1P0002Hi : ℝ) := by
    norm_num [ceSignedSpT1P0002Lo, ceSignedSpT1P0002Hi, SignedSpT1P0002Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0002Bound x h'
  norm_num [SignedSpT1P0002Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L004 : ∀ x ∈ Icc ((((397 : ℚ) / 16384) : ℚ) : ℝ) ((((131 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0003Lo : ℝ) (ceSignedSpT1P0003Hi : ℝ) := by
    norm_num [ceSignedSpT1P0003Lo, ceSignedSpT1P0003Hi, SignedSpT1P0003Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0003Bound x h'
  norm_num [SignedSpT1P0003Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L005 : ∀ x ∈ Icc ((((131 : ℚ) / 4096) : ℚ) : ℝ) ((((651 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0004Lo : ℝ) (ceSignedSpT1P0004Hi : ℝ) := by
    norm_num [ceSignedSpT1P0004Lo, ceSignedSpT1P0004Hi, SignedSpT1P0004Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0004Bound x h'
  norm_num [SignedSpT1P0004Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L006 : ∀ x ∈ Icc ((((651 : ℚ) / 16384) : ℚ) : ℝ) ((((389 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0005Lo : ℝ) (ceSignedSpT1P0005Hi : ℝ) := by
    norm_num [ceSignedSpT1P0005Lo, ceSignedSpT1P0005Hi, SignedSpT1P0005Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0005Bound x h'
  norm_num [SignedSpT1P0005Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L007 : ∀ x ∈ Icc ((((389 : ℚ) / 8192) : ℚ) : ℝ) ((((905 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0006Lo : ℝ) (ceSignedSpT1P0006Hi : ℝ) := by
    norm_num [ceSignedSpT1P0006Lo, ceSignedSpT1P0006Hi, SignedSpT1P0006Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0006Bound x h'
  norm_num [SignedSpT1P0006Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L008 : ∀ x ∈ Icc ((((905 : ℚ) / 16384) : ℚ) : ℝ) ((((129 : ℚ) / 2048) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0007Lo : ℝ) (ceSignedSpT1P0007Hi : ℝ) := by
    norm_num [ceSignedSpT1P0007Lo, ceSignedSpT1P0007Hi, SignedSpT1P0007Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0007Bound x h'
  norm_num [SignedSpT1P0007Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L009 : ∀ x ∈ Icc ((((129 : ℚ) / 2048) : ℚ) : ℝ) ((((1159 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0008Lo : ℝ) (ceSignedSpT1P0008Hi : ℝ) := by
    norm_num [ceSignedSpT1P0008Lo, ceSignedSpT1P0008Hi, SignedSpT1P0008Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0008Bound x h'
  norm_num [SignedSpT1P0008Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L010 : ∀ x ∈ Icc ((((1159 : ℚ) / 16384) : ℚ) : ℝ) ((((643 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0009Lo : ℝ) (ceSignedSpT1P0009Hi : ℝ) := by
    norm_num [ceSignedSpT1P0009Lo, ceSignedSpT1P0009Hi, SignedSpT1P0009Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0009Bound x h'
  norm_num [SignedSpT1P0009Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L011 : ∀ x ∈ Icc ((((643 : ℚ) / 8192) : ℚ) : ℝ) ((((1413 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0010Lo : ℝ) (ceSignedSpT1P0010Hi : ℝ) := by
    norm_num [ceSignedSpT1P0010Lo, ceSignedSpT1P0010Hi, SignedSpT1P0010Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0010Bound x h'
  norm_num [SignedSpT1P0010Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L012 : ∀ x ∈ Icc ((((1413 : ℚ) / 16384) : ℚ) : ℝ) ((((385 : ℚ) / 4096) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0011Lo : ℝ) (ceSignedSpT1P0011Hi : ℝ) := by
    norm_num [ceSignedSpT1P0011Lo, ceSignedSpT1P0011Hi, SignedSpT1P0011Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0011Bound x h'
  norm_num [SignedSpT1P0011Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L013 : ∀ x ∈ Icc ((((385 : ℚ) / 4096) : ℚ) : ℝ) ((((1667 : ℚ) / 16384) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0012Lo : ℝ) (ceSignedSpT1P0012Hi : ℝ) := by
    norm_num [ceSignedSpT1P0012Lo, ceSignedSpT1P0012Hi, SignedSpT1P0012Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0012Bound x h'
  norm_num [SignedSpT1P0012Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L014 : ∀ x ∈ Icc ((((1667 : ℚ) / 16384) : ℚ) : ℝ) ((((897 : ℚ) / 8192) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0013Lo : ℝ) (ceSignedSpT1P0013Hi : ℝ) := by
    norm_num [ceSignedSpT1P0013Lo, ceSignedSpT1P0013Hi, SignedSpT1P0013Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0013Bound x h'
  norm_num [SignedSpT1P0013Literal.q2] at h ⊢
  exact h

private theorem SignedSpT1CoverD0B0P000L015 : ∀ x ∈ Icc ((((897 : ℚ) / 8192) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) := by
  intro x hx hd
  have h' : x ∈ Icc (ceSignedSpT1P0014Lo : ℝ) (ceSignedSpT1P0014Hi : ℝ) := by
    norm_num [ceSignedSpT1P0014Lo, ceSignedSpT1P0014Hi, SignedSpT1P0014Literal.q2, Set.mem_Icc] at hx ⊢
    exact hx
  have h := ceSignedSpT1P0014Bound x h'
  norm_num [SignedSpT1P0014Literal.q2] at h ⊢
  exact h

theorem SignedSpT1CoverD0B0P000 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((3715 : ℚ) / 32768) : ℚ) : ℝ), x ∈ Ioo (0 : ℝ) 1 → fieldTower ceSignedSpT1ZeroPlain (poleF ceSignedSpT1ZeroPlain.poles) 0 x + lfieldTower [] 0 x ≤ ((((-4125939391141837029615117735270763662606618314135092347322129305048042021968329 : ℚ) / 506590390413258354978123059413009596858056182912177467672626930034619942174720) : ℚ) : ℝ) :=
  (cover_union (cover_union (cover_union (cover_union SignedSpT1CoverD0B0P000L000 SignedSpT1CoverD0B0P000L001) (cover_union SignedSpT1CoverD0B0P000L002 SignedSpT1CoverD0B0P000L003)) (cover_union (cover_union SignedSpT1CoverD0B0P000L004 SignedSpT1CoverD0B0P000L005) (cover_union SignedSpT1CoverD0B0P000L006 SignedSpT1CoverD0B0P000L007))) (cover_union (cover_union (cover_union SignedSpT1CoverD0B0P000L008 SignedSpT1CoverD0B0P000L009) (cover_union SignedSpT1CoverD0B0P000L010 SignedSpT1CoverD0B0P000L011)) (cover_union (cover_union SignedSpT1CoverD0B0P000L012 SignedSpT1CoverD0B0P000L013) (cover_union SignedSpT1CoverD0B0P000L014 SignedSpT1CoverD0B0P000L015))))
#print axioms SignedSpT1CoverD0B0P000

end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSpT1Cover

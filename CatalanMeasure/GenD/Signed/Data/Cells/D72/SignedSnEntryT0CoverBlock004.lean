module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core063
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core064
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core065
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core066
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem cell064 : ∀ y ∈ Icc ((((-1132797624319 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((-3432752611325 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P063Lo : ℝ) (ceSignedSnEntryT0P063Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P063Lo, ceSignedSnEntryT0P063Hi, SignedSnEntryT0Core063Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P063Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core063Literal.q2] at h ⊢
  exact h

private theorem cell065 : ∀ y ∈ Icc ((((-3432752611325 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-1167157362687 : ℚ) / 70368744177664) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P064Lo : ℝ) (ceSignedSnEntryT0P064Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P064Lo, ceSignedSnEntryT0P064Hi, SignedSnEntryT0Core064Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P064Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core064Literal.q2] at h ⊢
  exact h

private theorem cell066 : ∀ y ∈ Icc ((((-1167157362687 : ℚ) / 70368744177664) : ℚ) : ℝ) ((((-1235876839423 : ℚ) / 140737488355328) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P065Lo : ℝ) (ceSignedSnEntryT0P065Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P065Lo, ceSignedSnEntryT0P065Hi, SignedSnEntryT0Core065Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P065Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core065Literal.q2] at h ⊢
  exact h

private theorem cell067 : ∀ y ∈ Icc ((((-1235876839423 : ℚ) / 140737488355328) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P066Lo : ℝ) (ceSignedSnEntryT0P066Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P066Lo, ceSignedSnEntryT0P066Hi, SignedSnEntryT0Core066Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P066Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core066Literal.q2] at h ⊢
  exact h

theorem endIdentity68 : fieldNFCheck ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0Fq = true := by decide +kernel
    
private theorem cell068 : ∀ y ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0E01Lo : ℝ) (ceSignedSnEntryT0E01Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0E01Lo, ceSignedSnEntryT0E01Hi, SignedSnEntryT0End01Literal.q2, ceSignedSnEntryT0E01EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0E01Bound y hx (by norm_num [ceSignedSnEntryT0E01Site, ceSignedSnEntryT0E01EndLiteral.q2]; exact ne_of_lt hd.2)
  rw [fieldNFCheck_sound endIdentity68 y] at h
  simp only [ceSignedSnEntryT0E01FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0End01Literal.q2, ceSignedSnEntryT0E01Target, ceSignedSnEntryT0E01EndLiteral.q2] at h ⊢
  exact h

theorem cover004 : ∀ y ∈ Icc ((((-1132797624319 : ℚ) / 35184372088832) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union (cover_union cell064 cell065) (cover_union cell066 (cover_union cell067 cell068)))
#print axioms cover004
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover

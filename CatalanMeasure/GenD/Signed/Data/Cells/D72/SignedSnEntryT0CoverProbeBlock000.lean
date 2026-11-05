module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0End00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Core001
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem endIdentity0 : fieldNFCheck ceSignedSnEntryT0E00FullFq ceSignedSnEntryT0Fq = true := by decide +kernel
    
private theorem cell000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0E00Lo : ℝ) (ceSignedSnEntryT0E00Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0E00Lo, ceSignedSnEntryT0E00Hi, SignedSnEntryT0End00Literal.q2, ceSignedSnEntryT0E00EndLiteral.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0E00Full y hx
  rw [fieldNFCheck_sound endIdentity0 y] at h
  simp only [ceSignedSnEntryT0E00FullTs, lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0End00Literal.q2, ceSignedSnEntryT0E00Target, ceSignedSnEntryT0E00EndLiteral.q2] at h ⊢
  exact h

private theorem cell001 : ∀ y ∈ Icc ((((-1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-4722366481766912360449 : ℚ) / 4722366482869645213696) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P000Lo : ℝ) (ceSignedSnEntryT0P000Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P000Lo, ceSignedSnEntryT0P000Hi, SignedSnEntryT0Core000Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P000Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core000Literal.q2] at h ⊢
  exact h

private theorem cell002 : ∀ y ∈ Icc ((((-4722366481766912360449 : ℚ) / 4722366482869645213696) : ℚ) : ℝ) ((((-1180591619617899675649 : ℚ) / 1180591620717411303424) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy hd
  have hx : y ∈ Icc (ceSignedSnEntryT0P001Lo : ℝ) (ceSignedSnEntryT0P001Hi : ℝ) := by
    norm_num [ceSignedSnEntryT0P001Lo, ceSignedSnEntryT0P001Hi, SignedSnEntryT0Core001Literal.q2, Set.mem_Icc] at hy ⊢
    exact hy
  have h := ceSignedSnEntryT0P001Bound y hx
  simp only [lfieldTower_nil_zero, add_zero] at h
  norm_num [SignedSnEntryT0Core001Literal.q2] at h ⊢
  exact h

theorem cover000 : ∀ y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-1180591619617899675649 : ℚ) / 1180591620717411303424) : ℚ) : ℝ),
    y ∈ Ioo (-1 : ℝ) 0 → fieldTower ceSignedSnEntryT0Fq (poleF ceSignedSnEntryT0Fq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) :=
  (cover_union cell000 (cover_union cell001 cell002))
#print axioms cover000
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover

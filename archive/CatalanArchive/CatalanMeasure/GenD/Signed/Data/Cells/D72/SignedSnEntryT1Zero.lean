module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1End02
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Zero
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem zeroField : fieldNFCheck ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1Fq = true := by decide +kernel

theorem zeroLog : ∀ y ∈ Icc (ceSignedSnEntryT1E02Lo : ℝ) 0, y ≠ 0 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T1.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T1.snFq.poles) 0 y ≤
      ((ceSignedSnEntryT1E02TR + ceSignedSnEntryT1E02U : ℚ) : ℝ) +
      (endC ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1E02FullTs ceSignedSnEntryT1E02Site : ℝ) * Real.log |y - 0| := by
  intro y hy _
  have hs : ceSignedSnEntryT1E02Site = 0 := by decide +kernel
  have hh : ceSignedSnEntryT1E02Hi = 0 := by decide +kernel
  have h := endOK_sound ceSignedSnEntryT1E02FullFq ceSignedSnEntryT1E02FullTs ceSignedSnEntryT1E02Site
    ceSignedSnEntryT1E02Lo ceSignedSnEntryT1E02Hi 10 ceSignedSnEntryT1E02U ceSignedSnEntryT1E02TR
    (endOK_of_endUOK ceSignedSnEntryT1E02Singular) ceSignedSnEntryT1E02Regular y
    (by simpa only [hh, Rat.cast_zero] using hy)
  rw [fieldNFCheck_sound zeroField y, ceSignedSnEntryT1FieldEq y] at h
  simpa only [ceSignedSnEntryT1E02FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
    show (ceSignedSnEntryT1E02Site : ℝ) = 0 by rw [hs, Rat.cast_zero]] using h
#print axioms zeroLog
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT1Zero

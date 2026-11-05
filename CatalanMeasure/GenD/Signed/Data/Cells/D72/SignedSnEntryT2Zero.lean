module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2End02
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Zero
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem zeroField : fieldNFCheck ceSignedSnEntryT2E02FullFq ceSignedSnEntryT2Fq = true := by decide +kernel

theorem zeroLog : ∀ y ∈ Icc (ceSignedSnEntryT2E02Lo : ℝ) 0, y ≠ 0 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq.poles) 0 y ≤
      ((ceSignedSnEntryT2E02TR + ceSignedSnEntryT2E02U : ℚ) : ℝ) +
      (endC ceSignedSnEntryT2E02FullFq ceSignedSnEntryT2E02FullTs ceSignedSnEntryT2E02Site : ℝ) * Real.log |y - 0| := by
  intro y hy _
  have hs : ceSignedSnEntryT2E02Site = 0 := by decide +kernel
  have hh : ceSignedSnEntryT2E02Hi = 0 := by decide +kernel
  have h := endOK_sound ceSignedSnEntryT2E02FullFq ceSignedSnEntryT2E02FullTs ceSignedSnEntryT2E02Site
    ceSignedSnEntryT2E02Lo ceSignedSnEntryT2E02Hi 10 ceSignedSnEntryT2E02U ceSignedSnEntryT2E02TR
    (endOK_of_endUOK ceSignedSnEntryT2E02Singular) ceSignedSnEntryT2E02Regular y
    (by simpa only [hh, Rat.cast_zero] using hy)
  rw [fieldNFCheck_sound zeroField y, ceSignedSnEntryT2FieldEq y] at h
  simpa only [ceSignedSnEntryT2E02FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
    show (ceSignedSnEntryT2E02Site : ℝ) = 0 by rw [hs, Rat.cast_zero]] using h
#print axioms zeroLog
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Zero

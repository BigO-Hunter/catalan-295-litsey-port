module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0End01
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Zero
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

private theorem zeroField : fieldNFCheck ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0Fq = true := by decide +kernel

theorem zeroLog : ∀ y ∈ Icc (ceSignedSnEntryT0E01Lo : ℝ) 0, y ≠ 0 →
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.snFq.poles) 0 y ≤
      ((ceSignedSnEntryT0E01TR + ceSignedSnEntryT0E01U : ℚ) : ℝ) +
      (endC ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0E01FullTs ceSignedSnEntryT0E01Site : ℝ) * Real.log |y - 0| := by
  intro y hy _
  have hs : ceSignedSnEntryT0E01Site = 0 := by decide +kernel
  have hh : ceSignedSnEntryT0E01Hi = 0 := by decide +kernel
  have h := endOK_sound ceSignedSnEntryT0E01FullFq ceSignedSnEntryT0E01FullTs ceSignedSnEntryT0E01Site
    ceSignedSnEntryT0E01Lo ceSignedSnEntryT0E01Hi 10 ceSignedSnEntryT0E01U ceSignedSnEntryT0E01TR
    (endOK_of_endUOK ceSignedSnEntryT0E01Singular) ceSignedSnEntryT0E01Regular y
    (by simpa only [hh, Rat.cast_zero] using hy)
  rw [fieldNFCheck_sound zeroField y, ceSignedSnEntryT0FieldEq y] at h
  simpa only [ceSignedSnEntryT0E01FullTs, lfieldTower_nil_zero, add_zero, Rat.cast_add,
    show (ceSignedSnEntryT0E01Site : ℝ) = 0 by rw [hs, Rat.cast_zero]] using h
#print axioms zeroLog
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Zero

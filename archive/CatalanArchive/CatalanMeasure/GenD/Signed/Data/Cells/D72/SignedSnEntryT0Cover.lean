module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0CoverBlock000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0CoverBlock001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0CoverBlock002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0CoverBlock003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0CoverBlock004
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem named : ∀ y ∈ Ioo (-1 : ℝ) 0,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T0.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T0.snFq.poles) 0 y ≤ ((((-8755850689279 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy
  have hx : y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) := by
    norm_num [Set.mem_Icc]
    exact ⟨hy.1.le, hy.2.le⟩
  have h := (cover_union (cover_union cover000 cover001) (cover_union cover002 (cover_union cover003 cover004))) y hx hy
  rw [ceSignedSnEntryT0FieldEq y] at h
  exact h

#print axioms named
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT0Cover

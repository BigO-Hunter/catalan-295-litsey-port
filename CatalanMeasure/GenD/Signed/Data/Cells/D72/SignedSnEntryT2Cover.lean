module
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Binding
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2CoverBlock008
@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover
open Set CatalanMeasure.GenD.Signed.Data.Cells CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.CellCert
set_option Elab.async false
set_option maxHeartbeats 0
set_option profiler true

theorem named : ∀ y ∈ Ioo (-1 : ℝ) 0,
    fieldTower CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq (poleF CatalanMeasure.GenD.Signed.Data.Trial72.T2.snFq.poles) 0 y ≤ ((((-8708350214367 : ℚ) / 1099511627776) : ℚ) : ℝ) := by
  intro y hy
  have hx : y ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ) := by
    norm_num [Set.mem_Icc]
    exact ⟨hy.1.le, hy.2.le⟩
  have h := (cover_union (cover_union (cover_union cover000 cover001) (cover_union cover002 cover003)) (cover_union (cover_union cover004 cover005) (cover_union cover006 (cover_union cover007 cover008)))) y hx hy
  rw [ceSignedSnEntryT2FieldEq y] at h
  exact h

#print axioms named
end CatalanMeasure.GenD.Signed.Data.Cells.D72.SignedSnEntryT2Cover

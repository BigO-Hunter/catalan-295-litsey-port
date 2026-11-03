module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached011
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached012
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached013
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached014
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached015
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached016
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached000
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneCoverFirstColumn
def valid (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1
theorem d2SAE003RawIdentity : fieldNFCheck d2SAE003FullFq D72.StandaloneFieldData.f1 = true := by decide +kernel
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE003Lo : ℝ) (d2SAE003Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE003Lo, d2SAE003Hi, d2SAE003EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE003Site : ℝ) := by
    simpa [d2SAE003Site, d2SAE003EndLiteral.q2] using hP.1
  have h := d2SAE003Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE003RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE003Target, d2SAE003EndLiteral.q2] : (d2SAE003Target : ℝ) ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [d2SAE003FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((654847 : ℚ) / 134217728) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P0Lift0 x (by norm_num [d2StandaloneCached011P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((654847 : ℚ) / 134217728) : ℚ) : ℝ) ((((1833469 : ℚ) / 268435456) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P1Lift0 x (by norm_num [d2StandaloneCached011P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((1833469 : ℚ) / 268435456) : ℚ) : ℝ) ((((589311 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P2Lift0 x (by norm_num [d2StandaloneCached011P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P2LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell4 (x : ℝ) (hx : x ∈ Icc ((((589311 : ℚ) / 67108864) : ℚ) : ℝ) ((((2881019 : ℚ) / 268435456) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P3Lift0 x (by norm_num [d2StandaloneCached011P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P3LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell5 (x : ℝ) (hx : x ∈ Icc ((((2881019 : ℚ) / 268435456) : ℚ) : ℝ) ((((556543 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P4Lift0 x (by norm_num [d2StandaloneCached011P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P4LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell6 (x : ℝ) (hx : x ∈ Icc ((((556543 : ℚ) / 33554432) : ℚ) : ℝ) ((((1636861 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P5Lift0 x (by norm_num [d2StandaloneCached011P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P5LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell7 (x : ℝ) (hx : x ∈ Icc ((((1636861 : ℚ) / 67108864) : ℚ) : ℝ) ((((540159 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached011P6Lift0 x (by norm_num [d2StandaloneCached011P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP010InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached011P6LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP010InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell8 (x : ℝ) (hx : x ∈ Icc ((((540159 : ℚ) / 16777216) : ℚ) : ℝ) ((((2684411 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P0Lift0 x (by norm_num [d2StandaloneCached012P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell9 (x : ℝ) (hx : x ∈ Icc ((((2684411 : ℚ) / 67108864) : ℚ) : ℝ) ((((1604093 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P1Lift0 x (by norm_num [d2StandaloneCached012P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell10 (x : ℝ) (hx : x ∈ Icc ((((1604093 : ℚ) / 33554432) : ℚ) : ℝ) ((((3731961 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P2Lift0 x (by norm_num [d2StandaloneCached012P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P2LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell11 (x : ℝ) (hx : x ∈ Icc ((((3731961 : ℚ) / 67108864) : ℚ) : ℝ) ((((531967 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P3Lift0 x (by norm_num [d2StandaloneCached012P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P3LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell12 (x : ℝ) (hx : x ∈ Icc ((((531967 : ℚ) / 8388608) : ℚ) : ℝ) ((((4779511 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P4Lift0 x (by norm_num [d2StandaloneCached012P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P4LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell13 (x : ℝ) (hx : x ∈ Icc ((((4779511 : ℚ) / 67108864) : ℚ) : ℝ) ((((2651643 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P5Lift0 x (by norm_num [d2StandaloneCached012P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P5LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell14 (x : ℝ) (hx : x ∈ Icc ((((2651643 : ℚ) / 33554432) : ℚ) : ℝ) ((((5827061 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P6Lift0 x (by norm_num [d2StandaloneCached012P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P6LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell15 (x : ℝ) (hx : x ∈ Icc ((((5827061 : ℚ) / 67108864) : ℚ) : ℝ) ((((1587709 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached012P7Lift0 x (by norm_num [d2StandaloneCached012P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP011InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached012P7LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP011InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell16 (x : ℝ) (hx : x ∈ Icc ((((1587709 : ℚ) / 16777216) : ℚ) : ℝ) ((((6874611 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P0Lift0 x (by norm_num [d2StandaloneCached013P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell17 (x : ℝ) (hx : x ∈ Icc ((((6874611 : ℚ) / 67108864) : ℚ) : ℝ) ((((3699193 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P1Lift0 x (by norm_num [d2StandaloneCached013P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell18 (x : ℝ) (hx : x ∈ Icc ((((3699193 : ℚ) / 33554432) : ℚ) : ℝ) ((((7922161 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P2Lift0 x (by norm_num [d2StandaloneCached013P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P2LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell19 (x : ℝ) (hx : x ∈ Icc ((((7922161 : ℚ) / 67108864) : ℚ) : ℝ) ((((527871 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P3Lift0 x (by norm_num [d2StandaloneCached013P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P3LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell20 (x : ℝ) (hx : x ∈ Icc ((((527871 : ℚ) / 4194304) : ℚ) : ℝ) ((((8969711 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P4Lift0 x (by norm_num [d2StandaloneCached013P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P4LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell21 (x : ℝ) (hx : x ∈ Icc ((((8969711 : ℚ) / 67108864) : ℚ) : ℝ) ((((4746743 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P5Lift0 x (by norm_num [d2StandaloneCached013P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P5LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell22 (x : ℝ) (hx : x ∈ Icc ((((4746743 : ℚ) / 33554432) : ℚ) : ℝ) ((((10017261 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P6Lift0 x (by norm_num [d2StandaloneCached013P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P6LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell23 (x : ℝ) (hx : x ∈ Icc ((((10017261 : ℚ) / 67108864) : ℚ) : ℝ) ((((2635259 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached013P7Lift0 x (by norm_num [d2StandaloneCached013P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP012InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached013P7LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP012InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell24 (x : ℝ) (hx : x ∈ Icc ((((2635259 : ℚ) / 16777216) : ℚ) : ℝ) ((((11064811 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached000P0Lo : ℝ) (d2StandaloneUncached000P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached000P0Lo, d2StandaloneUncached000P0Hi, d2StandaloneUncached000P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached000P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached000P0Literal.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell25 (x : ℝ) (hx : x ∈ Icc ((((11064811 : ℚ) / 67108864) : ℚ) : ℝ) ((((3682809 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached000P1Lo : ℝ) (d2StandaloneUncached000P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached000P1Lo, d2StandaloneUncached000P1Hi, d2StandaloneUncached000P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached000P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached000P1Literal.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell26 (x : ℝ) (hx : x ∈ Icc ((((3682809 : ℚ) / 16777216) : ℚ) : ℝ) ((((1575421 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached000P2Lo : ℝ) (d2StandaloneUncached000P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached000P2Lo, d2StandaloneUncached000P2Hi, d2StandaloneUncached000P2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached000P2Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached000P2Literal.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell27 (x : ℝ) (hx : x ∈ Icc ((((1575421 : ℚ) / 4194304) : ℚ) : ℝ) ((((2622971 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached000P3Lo : ℝ) (d2StandaloneUncached000P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached000P3Lo, d2StandaloneUncached000P3Hi, d2StandaloneUncached000P3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached000P3Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached000P3Literal.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell28 (x : ℝ) (hx : x ∈ Icc ((((2622971 : ℚ) / 4194304) : ℚ) : ℝ) ((((3670521 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached000P4Lo : ℝ) (d2StandaloneUncached000P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached000P4Lo, d2StandaloneUncached000P4Hi, d2StandaloneUncached000P4Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached000P4Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached000P4Literal.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell29 (x : ℝ) (hx : x ∈ Icc ((((3670521 : ℚ) / 4194304) : ℚ) : ℝ) ((((7864817 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached014P0Lift0 x (by norm_num [d2StandaloneCached014P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP013InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached014P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP013InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell30 (x : ℝ) (hx : x ∈ Icc ((((7864817 : ℚ) / 8388608) : ℚ) : ℝ) ((((16253409 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached014P1Lift0 x (by norm_num [d2StandaloneCached014P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP013InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached014P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP013InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell31 (x : ℝ) (hx : x ∈ Icc ((((16253409 : ℚ) / 16777216) : ℚ) : ℝ) ((((33030593 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P0Lift0 x (by norm_num [d2StandaloneCached015P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell32 (x : ℝ) (hx : x ∈ Icc ((((33030593 : ℚ) / 33554432) : ℚ) : ℝ) ((((66584961 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P1Lift0 x (by norm_num [d2StandaloneCached015P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell33 (x : ℝ) (hx : x ∈ Icc ((((66584961 : ℚ) / 67108864) : ℚ) : ℝ) ((((133693697 : ℚ) / 134217728) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P2Lift0 x (by norm_num [d2StandaloneCached015P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P2LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell34 (x : ℝ) (hx : x ∈ Icc ((((133693697 : ℚ) / 134217728) : ℚ) : ℝ) ((((267911169 : ℚ) / 268435456) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P3Lift0 x (by norm_num [d2StandaloneCached015P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P3LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell35 (x : ℝ) (hx : x ∈ Icc ((((267911169 : ℚ) / 268435456) : ℚ) : ℝ) ((((536346113 : ℚ) / 536870912) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P4Lift0 x (by norm_num [d2StandaloneCached015P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P4LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell36 (x : ℝ) (hx : x ∈ Icc ((((536346113 : ℚ) / 536870912) : ℚ) : ℝ) ((((2145908227 : ℚ) / 2147483648) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P5Lift0 x (by norm_num [d2StandaloneCached015P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P5LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell37 (x : ℝ) (hx : x ∈ Icc ((((2145908227 : ℚ) / 2147483648) : ℚ) : ℝ) ((((1073216001 : ℚ) / 1073741824) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P6Lift0 x (by norm_num [d2StandaloneCached015P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P6LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell38 (x : ℝ) (hx : x ∈ Icc ((((1073216001 : ℚ) / 1073741824) : ℚ) : ℝ) ((((2146955777 : ℚ) / 2147483648) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached015P7Lift0 x (by norm_num [d2StandaloneCached015P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached015P7LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell39 (x : ℝ) (hx : x ∈ Icc ((((2146955777 : ℚ) / 2147483648) : ℚ) : ℝ) ((((4294435329 : ℚ) / 4294967296) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached016P0Lift0 x (by norm_num [d2StandaloneCached016P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached016P0LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell40 (x : ℝ) (hx : x ∈ Icc ((((4294435329 : ℚ) / 4294967296) : ℚ) : ℝ) ((((8589394433 : ℚ) / 8589934592) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached016P1Lift0 x (by norm_num [d2StandaloneCached016P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached016P1LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell41 (x : ℝ) (hx : x ∈ Icc ((((8589394433 : ℚ) / 8589934592) : ℚ) : ℝ) ((((17179312641 : ℚ) / 17179869184) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached016P2Lift0 x (by norm_num [d2StandaloneCached016P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached016P2LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell42 (x : ℝ) (hx : x ∈ Icc ((((17179312641 : ℚ) / 17179869184) : ℚ) : ℝ) ((((68718821889 : ℚ) / 68719476736) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached016P3Lift0 x (by norm_num [d2StandaloneCached016P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached016P3LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell43 (x : ℝ) (hx : x ∈ Icc ((((68718821889 : ℚ) / 68719476736) : ℚ) : ℝ) ((((524287 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have h := d2StandaloneCached016P4Lift0 x (by norm_num [d2StandaloneCached016P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP014InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached016P4LiftLiteral.q2] : _ ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  have hnil : d2SAP014InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem d2SAE004RawIdentity : fieldNFCheck d2SAE004FullFq D72.StandaloneFieldData.f1 = true := by decide +kernel
theorem cell44 (x : ℝ) (hx : x ∈ Icc ((((524287 : ℚ) / 524288) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE004Lo : ℝ) (d2SAE004Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE004Lo, d2SAE004Hi, d2SAE004EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE004Site : ℝ) := by
    simpa [d2SAE004Site, d2SAE004EndLiteral.q2] using hP.2
  have h := d2SAE004Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE004RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE004Target, d2SAE004EndLiteral.q2] : (d2SAE004Target : ℝ) ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ))
  simpa only [d2SAE004FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
def domain0Block0Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((1 : ℚ) / 1024)), (((1 : ℚ) / 1024), ((654847 : ℚ) / 134217728)), (((654847 : ℚ) / 134217728), ((1833469 : ℚ) / 268435456)), (((1833469 : ℚ) / 268435456), ((589311 : ℚ) / 67108864)), (((589311 : ℚ) / 67108864), ((2881019 : ℚ) / 268435456)), (((2881019 : ℚ) / 268435456), ((556543 : ℚ) / 33554432)), (((556543 : ℚ) / 33554432), ((1636861 : ℚ) / 67108864)), (((1636861 : ℚ) / 67108864), ((540159 : ℚ) / 16777216)), (((540159 : ℚ) / 16777216), ((2684411 : ℚ) / 67108864)), (((2684411 : ℚ) / 67108864), ((1604093 : ℚ) / 33554432)), (((1604093 : ℚ) / 33554432), ((3731961 : ℚ) / 67108864)), (((3731961 : ℚ) / 67108864), ((531967 : ℚ) / 8388608)), (((531967 : ℚ) / 8388608), ((4779511 : ℚ) / 67108864)), (((4779511 : ℚ) / 67108864), ((2651643 : ℚ) / 33554432)), (((2651643 : ℚ) / 33554432), ((5827061 : ℚ) / 67108864)), (((5827061 : ℚ) / 67108864), ((1587709 : ℚ) / 16777216))]
theorem domain0Block0Cover : pieceCover ((1587709 : ℚ) / 16777216) ((0 : ℚ) / 1) domain0Block0Pieces = true := by decide +kernel
theorem domain0Block0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1587709 : ℚ) / 16777216) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f1) valid ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) ((0 : ℚ) / 1) ((1587709 : ℚ) / 16777216) domain0Block0Pieces (by decide +kernel) domain0Block0Cover
  intro p hp
  simp only [domain0Block0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell2 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell3 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell4 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell5 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell6 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell7 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell8 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell9 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell10 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell11 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell12 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell13 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell14 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell15 x hx hP).trans (by norm_num)
#print axioms domain0Block0Cover
#print axioms domain0Block0
def domain0Block1Pieces : List (ℚ × ℚ) := [(((1587709 : ℚ) / 16777216), ((6874611 : ℚ) / 67108864)), (((6874611 : ℚ) / 67108864), ((3699193 : ℚ) / 33554432)), (((3699193 : ℚ) / 33554432), ((7922161 : ℚ) / 67108864)), (((7922161 : ℚ) / 67108864), ((527871 : ℚ) / 4194304)), (((527871 : ℚ) / 4194304), ((8969711 : ℚ) / 67108864)), (((8969711 : ℚ) / 67108864), ((4746743 : ℚ) / 33554432)), (((4746743 : ℚ) / 33554432), ((10017261 : ℚ) / 67108864)), (((10017261 : ℚ) / 67108864), ((2635259 : ℚ) / 16777216)), (((2635259 : ℚ) / 16777216), ((11064811 : ℚ) / 67108864)), (((11064811 : ℚ) / 67108864), ((3682809 : ℚ) / 16777216)), (((3682809 : ℚ) / 16777216), ((1575421 : ℚ) / 4194304)), (((1575421 : ℚ) / 4194304), ((2622971 : ℚ) / 4194304)), (((2622971 : ℚ) / 4194304), ((3670521 : ℚ) / 4194304)), (((3670521 : ℚ) / 4194304), ((7864817 : ℚ) / 8388608)), (((7864817 : ℚ) / 8388608), ((16253409 : ℚ) / 16777216)), (((16253409 : ℚ) / 16777216), ((33030593 : ℚ) / 33554432))]
theorem domain0Block1Cover : pieceCover ((33030593 : ℚ) / 33554432) ((1587709 : ℚ) / 16777216) domain0Block1Pieces = true := by decide +kernel
theorem domain0Block1 : ∀ x ∈ Icc ((((1587709 : ℚ) / 16777216) : ℚ) : ℝ) ((((33030593 : ℚ) / 33554432) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f1) valid ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) ((1587709 : ℚ) / 16777216) ((33030593 : ℚ) / 33554432) domain0Block1Pieces (by decide +kernel) domain0Block1Cover
  intro p hp
  simp only [domain0Block1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell16 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell17 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell18 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell19 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell20 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell21 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell22 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell23 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell24 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell25 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell26 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell27 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell28 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell29 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell30 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell31 x hx hP).trans (by norm_num)
#print axioms domain0Block1Cover
#print axioms domain0Block1
def domain0Block2Pieces : List (ℚ × ℚ) := [(((33030593 : ℚ) / 33554432), ((66584961 : ℚ) / 67108864)), (((66584961 : ℚ) / 67108864), ((133693697 : ℚ) / 134217728)), (((133693697 : ℚ) / 134217728), ((267911169 : ℚ) / 268435456)), (((267911169 : ℚ) / 268435456), ((536346113 : ℚ) / 536870912)), (((536346113 : ℚ) / 536870912), ((2145908227 : ℚ) / 2147483648)), (((2145908227 : ℚ) / 2147483648), ((1073216001 : ℚ) / 1073741824)), (((1073216001 : ℚ) / 1073741824), ((2146955777 : ℚ) / 2147483648)), (((2146955777 : ℚ) / 2147483648), ((4294435329 : ℚ) / 4294967296)), (((4294435329 : ℚ) / 4294967296), ((8589394433 : ℚ) / 8589934592)), (((8589394433 : ℚ) / 8589934592), ((17179312641 : ℚ) / 17179869184)), (((17179312641 : ℚ) / 17179869184), ((68718821889 : ℚ) / 68719476736)), (((68718821889 : ℚ) / 68719476736), ((524287 : ℚ) / 524288)), (((524287 : ℚ) / 524288), ((1 : ℚ) / 1))]
theorem domain0Block2Cover : pieceCover ((1 : ℚ) / 1) ((33030593 : ℚ) / 33554432) domain0Block2Pieces = true := by decide +kernel
theorem domain0Block2 : ∀ x ∈ Icc ((((33030593 : ℚ) / 33554432) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f1) valid ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) ((33030593 : ℚ) / 33554432) ((1 : ℚ) / 1) domain0Block2Pieces (by decide +kernel) domain0Block2Cover
  intro p hp
  simp only [domain0Block2Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell32 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell33 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell34 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell35 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell36 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell37 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell38 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell39 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell40 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell41 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell42 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell43 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell44 x hx hP).trans (by norm_num)
#print axioms domain0Block2Cover
#print axioms domain0Block2
def domain0Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((1587709 : ℚ) / 16777216)), (((1587709 : ℚ) / 16777216), ((33030593 : ℚ) / 33554432)), (((33030593 : ℚ) / 33554432), ((1 : ℚ) / 1))]
theorem domain0Cover : pieceCover ((1 : ℚ) / 1) ((0 : ℚ) / 1) domain0Pieces = true := by decide +kernel
theorem domain0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f1 x ≤ ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f1) valid ((((540746234397773533 : ℚ) / 112589990684262400) : ℚ) : ℝ) ((0 : ℚ) / 1) ((1 : ℚ) / 1) domain0Pieces (by decide +kernel) domain0Cover
  intro p hp
  simp only [domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · intro x hx hP
    exact (domain0Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block2 x hx hP).trans (by norm_num)
#print axioms domain0Cover
#print axioms domain0
end D72.StandaloneCoverFirstColumn

end CatalanMeasure.GenD.Signed.Data.Cells

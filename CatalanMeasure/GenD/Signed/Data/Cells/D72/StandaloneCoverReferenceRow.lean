module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached017
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached018
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached019
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached020
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached021
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached022
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached023
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached024
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached025
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached026
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached027
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached028
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached029
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached030
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached031
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached032
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached033
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached034
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached035
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached036
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached037
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached038
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached039
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached040
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached041
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached042
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached043
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached044
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneCoverReferenceRow
def valid (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-4398046510081 : ℚ) / 4398046511104) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P0Lift0 x (by norm_num [d2StandaloneCached017P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((-4398046510081 : ℚ) / 4398046511104) : ℚ) : ℝ) ((((-1099511626753 : ℚ) / 1099511627776) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P1Lift0 x (by norm_num [d2StandaloneCached017P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((-1099511626753 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((-274877905921 : ℚ) / 274877906944) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P2Lift0 x (by norm_num [d2StandaloneCached017P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((-274877905921 : ℚ) / 274877906944) : ℚ) : ℝ) ((((-68719475713 : ℚ) / 68719476736) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P3Lift0 x (by norm_num [d2StandaloneCached017P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell4 (x : ℝ) (hx : x ∈ Icc ((((-68719475713 : ℚ) / 68719476736) : ℚ) : ℝ) ((((-34359737345 : ℚ) / 34359738368) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P4Lift0 x (by norm_num [d2StandaloneCached017P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell5 (x : ℝ) (hx : x ∈ Icc ((((-34359737345 : ℚ) / 34359738368) : ℚ) : ℝ) ((((-17179868161 : ℚ) / 17179869184) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P5Lift0 x (by norm_num [d2StandaloneCached017P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell6 (x : ℝ) (hx : x ∈ Icc ((((-17179868161 : ℚ) / 17179869184) : ℚ) : ℝ) ((((-8589933569 : ℚ) / 8589934592) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P6Lift0 x (by norm_num [d2StandaloneCached017P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell7 (x : ℝ) (hx : x ∈ Icc ((((-8589933569 : ℚ) / 8589934592) : ℚ) : ℝ) ((((-4294966273 : ℚ) / 4294967296) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached017P7Lift0 x (by norm_num [d2StandaloneCached017P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached017P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell8 (x : ℝ) (hx : x ∈ Icc ((((-4294966273 : ℚ) / 4294967296) : ℚ) : ℝ) ((((-2147482625 : ℚ) / 2147483648) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P0Lift0 x (by norm_num [d2StandaloneCached018P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell9 (x : ℝ) (hx : x ∈ Icc ((((-2147482625 : ℚ) / 2147483648) : ℚ) : ℝ) ((((-1073740801 : ℚ) / 1073741824) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P1Lift0 x (by norm_num [d2StandaloneCached018P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell10 (x : ℝ) (hx : x ∈ Icc ((((-1073740801 : ℚ) / 1073741824) : ℚ) : ℝ) ((((-536869889 : ℚ) / 536870912) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P2Lift0 x (by norm_num [d2StandaloneCached018P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell11 (x : ℝ) (hx : x ∈ Icc ((((-536869889 : ℚ) / 536870912) : ℚ) : ℝ) ((((-268434433 : ℚ) / 268435456) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P3Lift0 x (by norm_num [d2StandaloneCached018P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell12 (x : ℝ) (hx : x ∈ Icc ((((-268434433 : ℚ) / 268435456) : ℚ) : ℝ) ((((-134216705 : ℚ) / 134217728) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P4Lift0 x (by norm_num [d2StandaloneCached018P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell13 (x : ℝ) (hx : x ∈ Icc ((((-134216705 : ℚ) / 134217728) : ℚ) : ℝ) ((((-67107841 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P5Lift0 x (by norm_num [d2StandaloneCached018P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell14 (x : ℝ) (hx : x ∈ Icc ((((-67107841 : ℚ) / 67108864) : ℚ) : ℝ) ((((-33553409 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P6Lift0 x (by norm_num [d2StandaloneCached018P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell15 (x : ℝ) (hx : x ∈ Icc ((((-33553409 : ℚ) / 33554432) : ℚ) : ℝ) ((((-16776193 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached018P7Lift0 x (by norm_num [d2StandaloneCached018P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached018P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell16 (x : ℝ) (hx : x ∈ Icc ((((-16776193 : ℚ) / 16777216) : ℚ) : ℝ) ((((-8387585 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P0Lift0 x (by norm_num [d2StandaloneCached019P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell17 (x : ℝ) (hx : x ∈ Icc ((((-8387585 : ℚ) / 8388608) : ℚ) : ℝ) ((((-4193281 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P1Lift0 x (by norm_num [d2StandaloneCached019P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell18 (x : ℝ) (hx : x ∈ Icc ((((-4193281 : ℚ) / 4194304) : ℚ) : ℝ) ((((-16772101 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P2Lift0 x (by norm_num [d2StandaloneCached019P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell19 (x : ℝ) (hx : x ∈ Icc ((((-16772101 : ℚ) / 16777216) : ℚ) : ℝ) ((((-8385539 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P3Lift0 x (by norm_num [d2StandaloneCached019P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell20 (x : ℝ) (hx : x ∈ Icc ((((-8385539 : ℚ) / 8388608) : ℚ) : ℝ) ((((-16770055 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P4Lift0 x (by norm_num [d2StandaloneCached019P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell21 (x : ℝ) (hx : x ∈ Icc ((((-16770055 : ℚ) / 16777216) : ℚ) : ℝ) ((((-33539087 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P5Lift0 x (by norm_num [d2StandaloneCached019P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell22 (x : ℝ) (hx : x ∈ Icc ((((-33539087 : ℚ) / 33554432) : ℚ) : ℝ) ((((-2096129 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P6Lift0 x (by norm_num [d2StandaloneCached019P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell23 (x : ℝ) (hx : x ∈ Icc ((((-2096129 : ℚ) / 2097152) : ℚ) : ℝ) ((((-33537041 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached019P7Lift0 x (by norm_num [d2StandaloneCached019P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached019P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell24 (x : ℝ) (hx : x ∈ Icc ((((-33537041 : ℚ) / 33554432) : ℚ) : ℝ) ((((-1047553 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P0Lift0 x (by norm_num [d2StandaloneCached020P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell25 (x : ℝ) (hx : x ∈ Icc ((((-1047553 : ℚ) / 1048576) : ℚ) : ℝ) ((((-4189189 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P1Lift0 x (by norm_num [d2StandaloneCached020P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell26 (x : ℝ) (hx : x ∈ Icc ((((-4189189 : ℚ) / 4194304) : ℚ) : ℝ) ((((-2094083 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P2Lift0 x (by norm_num [d2StandaloneCached020P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell27 (x : ℝ) (hx : x ∈ Icc ((((-2094083 : ℚ) / 2097152) : ℚ) : ℝ) ((((-523265 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P3Lift0 x (by norm_num [d2StandaloneCached020P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell28 (x : ℝ) (hx : x ∈ Icc ((((-523265 : ℚ) / 524288) : ℚ) : ℝ) ((((-1045507 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P4Lift0 x (by norm_num [d2StandaloneCached020P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell29 (x : ℝ) (hx : x ∈ Icc ((((-1045507 : ℚ) / 1048576) : ℚ) : ℝ) ((((-2089991 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P5Lift0 x (by norm_num [d2StandaloneCached020P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell30 (x : ℝ) (hx : x ∈ Icc ((((-2089991 : ℚ) / 2097152) : ℚ) : ℝ) ((((-261121 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P6Lift0 x (by norm_num [d2StandaloneCached020P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell31 (x : ℝ) (hx : x ∈ Icc ((((-261121 : ℚ) / 262144) : ℚ) : ℝ) ((((-521219 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached020P7Lift0 x (by norm_num [d2StandaloneCached020P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached020P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell32 (x : ℝ) (hx : x ∈ Icc ((((-521219 : ℚ) / 524288) : ℚ) : ℝ) ((((-130049 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached021P0Lift0 x (by norm_num [d2StandaloneCached021P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached021P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell33 (x : ℝ) (hx : x ∈ Icc ((((-130049 : ℚ) / 131072) : ℚ) : ℝ) ((((-519173 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached021P1Lift0 x (by norm_num [d2StandaloneCached021P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached021P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell34 (x : ℝ) (hx : x ∈ Icc ((((-519173 : ℚ) / 524288) : ℚ) : ℝ) ((((-64513 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached021P2Lift0 x (by norm_num [d2StandaloneCached021P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached021P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell35 (x : ℝ) (hx : x ∈ Icc ((((-64513 : ℚ) / 65536) : ℚ) : ℝ) ((((-128003 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached021P3Lift0 x (by norm_num [d2StandaloneCached021P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached021P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell36 (x : ℝ) (hx : x ∈ Icc ((((-128003 : ℚ) / 131072) : ℚ) : ℝ) ((((-31745 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached021P4Lift0 x (by norm_num [d2StandaloneCached021P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP015InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached021P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP015InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell37 (x : ℝ) (hx : x ∈ Icc ((((-31745 : ℚ) / 32768) : ℚ) : ℝ) ((((-62467 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached022P0Lift0 x (by norm_num [d2StandaloneCached022P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP016InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached022P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP016InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell38 (x : ℝ) (hx : x ∈ Icc ((((-62467 : ℚ) / 65536) : ℚ) : ℝ) ((((-15361 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached022P1Lift0 x (by norm_num [d2StandaloneCached022P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP016InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached022P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP016InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell39 (x : ℝ) (hx : x ∈ Icc ((((-15361 : ℚ) / 16384) : ℚ) : ℝ) ((((-29699 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached022P2Lift0 x (by norm_num [d2StandaloneCached022P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP016InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached022P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP016InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell40 (x : ℝ) (hx : x ∈ Icc ((((-29699 : ℚ) / 32768) : ℚ) : ℝ) ((((-27653 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P0Lo : ℝ) (d2StandaloneUncached006P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P0Lo, d2StandaloneUncached006P0Hi, d2StandaloneUncached006P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P0Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell41 (x : ℝ) (hx : x ∈ Icc ((((-27653 : ℚ) / 32768) : ℚ) : ℝ) ((((-23561 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P1Lo : ℝ) (d2StandaloneUncached006P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P1Lo, d2StandaloneUncached006P1Hi, d2StandaloneUncached006P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P1Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell42 (x : ℝ) (hx : x ∈ Icc ((((-23561 : ℚ) / 32768) : ℚ) : ℝ) ((((-1025 : ℚ) / 2048) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P2Lo : ℝ) (d2StandaloneUncached006P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P2Lo, d2StandaloneUncached006P2Hi, d2StandaloneUncached006P2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P2Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P2Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell43 (x : ℝ) (hx : x ∈ Icc ((((-1025 : ℚ) / 2048) : ℚ) : ℝ) ((((-5131 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P3Lo : ℝ) (d2StandaloneUncached006P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P3Lo, d2StandaloneUncached006P3Hi, d2StandaloneUncached006P3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P3Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P3Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell44 (x : ℝ) (hx : x ∈ Icc ((((-5131 : ℚ) / 16384) : ℚ) : ℝ) ((((-7193 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P4Lo : ℝ) (d2StandaloneUncached006P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P4Lo, d2StandaloneUncached006P4Hi, d2StandaloneUncached006P4Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P4Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P4Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell45 (x : ℝ) (hx : x ∈ Icc ((((-7193 : ℚ) / 32768) : ℚ) : ℝ) ((((-3085 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached023P0Lift0 x (by norm_num [d2StandaloneCached023P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP017InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached023P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP017InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell46 (x : ℝ) (hx : x ∈ Icc ((((-3085 : ℚ) / 16384) : ℚ) : ℝ) ((((-11317 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached023P1Lift0 x (by norm_num [d2StandaloneCached023P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP017InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached023P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP017InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell47 (x : ℝ) (hx : x ∈ Icc ((((-11317 : ℚ) / 65536) : ℚ) : ℝ) ((((-21611 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached023P2Lift0 x (by norm_num [d2StandaloneCached023P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP017InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached023P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP017InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell48 (x : ℝ) (hx : x ∈ Icc ((((-21611 : ℚ) / 131072) : ℚ) : ℝ) ((((-5147 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached023P3Lift0 x (by norm_num [d2StandaloneCached023P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP017InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached023P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP017InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell49 (x : ℝ) (hx : x ∈ Icc ((((-5147 : ℚ) / 32768) : ℚ) : ℝ) ((((-19565 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P0Lift0 x (by norm_num [d2StandaloneCached024P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell50 (x : ℝ) (hx : x ∈ Icc ((((-19565 : ℚ) / 131072) : ℚ) : ℝ) ((((-9271 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P1Lift0 x (by norm_num [d2StandaloneCached024P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell51 (x : ℝ) (hx : x ∈ Icc ((((-9271 : ℚ) / 65536) : ℚ) : ℝ) ((((-17519 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P2Lift0 x (by norm_num [d2StandaloneCached024P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell52 (x : ℝ) (hx : x ∈ Icc ((((-17519 : ℚ) / 131072) : ℚ) : ℝ) ((((-1031 : ℚ) / 8192) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P3Lift0 x (by norm_num [d2StandaloneCached024P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell53 (x : ℝ) (hx : x ∈ Icc ((((-1031 : ℚ) / 8192) : ℚ) : ℝ) ((((-15473 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P4Lift0 x (by norm_num [d2StandaloneCached024P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell54 (x : ℝ) (hx : x ∈ Icc ((((-15473 : ℚ) / 131072) : ℚ) : ℝ) ((((-58823 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P5Lift0 x (by norm_num [d2StandaloneCached024P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell55 (x : ℝ) (hx : x ∈ Icc ((((-58823 : ℚ) / 524288) : ℚ) : ℝ) ((((-56777 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P6Lift0 x (by norm_num [d2StandaloneCached024P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell56 (x : ℝ) (hx : x ∈ Icc ((((-56777 : ℚ) / 524288) : ℚ) : ℝ) ((((-112531 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached024P7Lift0 x (by norm_num [d2StandaloneCached024P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached024P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell57 (x : ℝ) (hx : x ∈ Icc ((((-112531 : ℚ) / 1048576) : ℚ) : ℝ) ((((-27877 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P0Lift0 x (by norm_num [d2StandaloneCached025P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell58 (x : ℝ) (hx : x ∈ Icc ((((-27877 : ℚ) / 262144) : ℚ) : ℝ) ((((-13427 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P1Lift0 x (by norm_num [d2StandaloneCached025P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell59 (x : ℝ) (hx : x ∈ Icc ((((-13427 : ℚ) / 131072) : ℚ) : ℝ) ((((-428641 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P2Lift0 x (by norm_num [d2StandaloneCached025P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell60 (x : ℝ) (hx : x ∈ Icc ((((-428641 : ℚ) / 4194304) : ℚ) : ℝ) ((((-426595 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P3Lift0 x (by norm_num [d2StandaloneCached025P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell61 (x : ℝ) (hx : x ∈ Icc ((((-426595 : ℚ) / 4194304) : ℚ) : ℝ) ((((-106393 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P4Lift0 x (by norm_num [d2StandaloneCached025P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell62 (x : ℝ) (hx : x ∈ Icc ((((-106393 : ℚ) / 1048576) : ℚ) : ℝ) ((((-211763 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P5Lift0 x (by norm_num [d2StandaloneCached025P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell63 (x : ℝ) (hx : x ∈ Icc ((((-211763 : ℚ) / 2097152) : ℚ) : ℝ) ((((-52685 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P6Lift0 x (by norm_num [d2StandaloneCached025P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell64 (x : ℝ) (hx : x ∈ Icc ((((-52685 : ℚ) / 524288) : ℚ) : ℝ) ((((-104347 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached025P7Lift0 x (by norm_num [d2StandaloneCached025P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached025P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell65 (x : ℝ) (hx : x ∈ Icc ((((-104347 : ℚ) / 1048576) : ℚ) : ℝ) ((((-25831 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached026P0Lift0 x (by norm_num [d2StandaloneCached026P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached026P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell66 (x : ℝ) (hx : x ∈ Icc ((((-25831 : ℚ) / 262144) : ℚ) : ℝ) ((((-50639 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached026P1Lift0 x (by norm_num [d2StandaloneCached026P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached026P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell67 (x : ℝ) (hx : x ∈ Icc ((((-50639 : ℚ) / 524288) : ℚ) : ℝ) ((((-3101 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached026P2Lift0 x (by norm_num [d2StandaloneCached026P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP018InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached026P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP018InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell68 (x : ℝ) (hx : x ∈ Icc ((((-3101 : ℚ) / 32768) : ℚ) : ℝ) ((((-11381 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P0Lift0 x (by norm_num [d2StandaloneCached027P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell69 (x : ℝ) (hx : x ∈ Icc ((((-11381 : ℚ) / 131072) : ℚ) : ℝ) ((((-5179 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P1Lift0 x (by norm_num [d2StandaloneCached027P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell70 (x : ℝ) (hx : x ∈ Icc ((((-5179 : ℚ) / 65536) : ℚ) : ℝ) ((((-9335 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P2Lift0 x (by norm_num [d2StandaloneCached027P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell71 (x : ℝ) (hx : x ∈ Icc ((((-9335 : ℚ) / 131072) : ℚ) : ℝ) ((((-1039 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P3Lift0 x (by norm_num [d2StandaloneCached027P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell72 (x : ℝ) (hx : x ∈ Icc ((((-1039 : ℚ) / 16384) : ℚ) : ℝ) ((((-7289 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P4Lift0 x (by norm_num [d2StandaloneCached027P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell73 (x : ℝ) (hx : x ∈ Icc ((((-7289 : ℚ) / 131072) : ℚ) : ℝ) ((((-3133 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P5Lift0 x (by norm_num [d2StandaloneCached027P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell74 (x : ℝ) (hx : x ∈ Icc ((((-3133 : ℚ) / 65536) : ℚ) : ℝ) ((((-5243 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P6Lift0 x (by norm_num [d2StandaloneCached027P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell75 (x : ℝ) (hx : x ∈ Icc ((((-5243 : ℚ) / 131072) : ℚ) : ℝ) ((((-1055 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached027P7Lift0 x (by norm_num [d2StandaloneCached027P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP019InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached027P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP019InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell76 (x : ℝ) (hx : x ∈ Icc ((((-1055 : ℚ) / 32768) : ℚ) : ℝ) ((((-3197 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P0Lift0 x (by norm_num [d2StandaloneCached028P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell77 (x : ℝ) (hx : x ∈ Icc ((((-3197 : ℚ) / 131072) : ℚ) : ℝ) ((((-1087 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P1Lift0 x (by norm_num [d2StandaloneCached028P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell78 (x : ℝ) (hx : x ∈ Icc ((((-1087 : ℚ) / 65536) : ℚ) : ℝ) ((((-1151 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P2Lift0 x (by norm_num [d2StandaloneCached028P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell79 (x : ℝ) (hx : x ∈ Icc ((((-1151 : ℚ) / 131072) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P3Lift0 x (by norm_num [d2StandaloneCached028P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem d2SAE005RawIdentity : fieldNFCheck d2SAE005FullFq D72.StandaloneFieldData.f2 = true := by decide +kernel
theorem cell80 (x : ℝ) (hx : x ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE005Lo : ℝ) (d2SAE005Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE005Lo, d2SAE005Hi, d2SAE005EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE005Site : ℝ) := by
    simpa [d2SAE005Site, d2SAE005EndLiteral.q2] using hP.1
  have h := d2SAE005Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE005RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE005Target, d2SAE005EndLiteral.q2] : (d2SAE005Target : ℝ) ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [d2SAE005FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem d2SAE006RawIdentity : fieldNFCheck d2SAE006FullFq D72.StandaloneFieldData.f2 = true := by decide +kernel
theorem cell81 (x : ℝ) (hx : x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE006Lo : ℝ) (d2SAE006Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE006Lo, d2SAE006Hi, d2SAE006EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE006Site : ℝ) := by
    simpa [d2SAE006Site, d2SAE006EndLiteral.q2] using hP.1
  have h := d2SAE006Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE006RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE006Target, d2SAE006EndLiteral.q2] : (d2SAE006Target : ℝ) ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [d2SAE006FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell82 (x : ℝ) (hx : x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((4603 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P4Lift0 x (by norm_num [d2StandaloneCached028P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell83 (x : ℝ) (hx : x ∈ Icc ((((4603 : ℚ) / 524288) : ℚ) : ℝ) ((((4347 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P5Lift0 x (by norm_num [d2StandaloneCached028P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell84 (x : ℝ) (hx : x ∈ Icc ((((4347 : ℚ) / 262144) : ℚ) : ℝ) ((((12785 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P6Lift0 x (by norm_num [d2StandaloneCached028P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell85 (x : ℝ) (hx : x ∈ Icc ((((12785 : ℚ) / 524288) : ℚ) : ℝ) ((((4219 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached028P7Lift0 x (by norm_num [d2StandaloneCached028P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP020InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached028P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP020InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell86 (x : ℝ) (hx : x ∈ Icc ((((4219 : ℚ) / 131072) : ℚ) : ℝ) ((((20967 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P0Lift0 x (by norm_num [d2StandaloneCached029P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell87 (x : ℝ) (hx : x ∈ Icc ((((20967 : ℚ) / 524288) : ℚ) : ℝ) ((((12529 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P1Lift0 x (by norm_num [d2StandaloneCached029P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell88 (x : ℝ) (hx : x ∈ Icc ((((12529 : ℚ) / 262144) : ℚ) : ℝ) ((((29149 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P2Lift0 x (by norm_num [d2StandaloneCached029P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell89 (x : ℝ) (hx : x ∈ Icc ((((29149 : ℚ) / 524288) : ℚ) : ℝ) ((((4155 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P3Lift0 x (by norm_num [d2StandaloneCached029P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell90 (x : ℝ) (hx : x ∈ Icc ((((4155 : ℚ) / 65536) : ℚ) : ℝ) ((((37331 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P4Lift0 x (by norm_num [d2StandaloneCached029P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell91 (x : ℝ) (hx : x ∈ Icc ((((37331 : ℚ) / 524288) : ℚ) : ℝ) ((((20711 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P5Lift0 x (by norm_num [d2StandaloneCached029P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell92 (x : ℝ) (hx : x ∈ Icc ((((20711 : ℚ) / 262144) : ℚ) : ℝ) ((((45513 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P6Lift0 x (by norm_num [d2StandaloneCached029P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell93 (x : ℝ) (hx : x ∈ Icc ((((45513 : ℚ) / 524288) : ℚ) : ℝ) ((((95117 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached029P7Lift0 x (by norm_num [d2StandaloneCached029P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached029P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell94 (x : ℝ) (hx : x ∈ Icc ((((95117 : ℚ) / 1048576) : ℚ) : ℝ) ((((12401 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached030P0Lift0 x (by norm_num [d2StandaloneCached030P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP021InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached030P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP021InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell95 (x : ℝ) (hx : x ∈ Icc ((((12401 : ℚ) / 131072) : ℚ) : ℝ) ((((202507 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P0Lift0 x (by norm_num [d2StandaloneCached031P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell96 (x : ℝ) (hx : x ∈ Icc ((((202507 : ℚ) / 2097152) : ℚ) : ℝ) ((((409105 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P1Lift0 x (by norm_num [d2StandaloneCached031P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell97 (x : ℝ) (hx : x ∈ Icc ((((409105 : ℚ) / 4194304) : ℚ) : ℝ) ((((822301 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P2Lift0 x (by norm_num [d2StandaloneCached031P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell98 (x : ℝ) (hx : x ∈ Icc ((((822301 : ℚ) / 8388608) : ℚ) : ℝ) ((((103299 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P3Lift0 x (by norm_num [d2StandaloneCached031P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell99 (x : ℝ) (hx : x ∈ Icc ((((103299 : ℚ) / 1048576) : ℚ) : ℝ) ((((1656875 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P4Lift0 x (by norm_num [d2StandaloneCached031P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell100 (x : ℝ) (hx : x ∈ Icc ((((1656875 : ℚ) / 16777216) : ℚ) : ℝ) ((((1665057 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P5Lift0 x (by norm_num [d2StandaloneCached031P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell101 (x : ℝ) (hx : x ∈ Icc ((((1665057 : ℚ) / 16777216) : ℚ) : ℝ) ((((210689 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P6Lift0 x (by norm_num [d2StandaloneCached031P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell102 (x : ℝ) (hx : x ∈ Icc ((((210689 : ℚ) / 2097152) : ℚ) : ℝ) ((((433651 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached031P7Lift0 x (by norm_num [d2StandaloneCached031P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached031P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell103 (x : ℝ) (hx : x ∈ Icc ((((433651 : ℚ) / 4194304) : ℚ) : ℝ) ((((218871 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P0Lift0 x (by norm_num [d2StandaloneCached032P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell104 (x : ℝ) (hx : x ∈ Icc ((((218871 : ℚ) / 2097152) : ℚ) : ℝ) ((((441833 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P1Lift0 x (by norm_num [d2StandaloneCached032P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell105 (x : ℝ) (hx : x ∈ Icc ((((441833 : ℚ) / 4194304) : ℚ) : ℝ) ((((111481 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P2Lift0 x (by norm_num [d2StandaloneCached032P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell106 (x : ℝ) (hx : x ∈ Icc ((((111481 : ℚ) / 1048576) : ℚ) : ℝ) ((((28893 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P3Lift0 x (by norm_num [d2StandaloneCached032P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell107 (x : ℝ) (hx : x ∈ Icc ((((28893 : ℚ) / 262144) : ℚ) : ℝ) ((((119663 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P4Lift0 x (by norm_num [d2StandaloneCached032P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell108 (x : ℝ) (hx : x ∈ Icc ((((119663 : ℚ) / 1048576) : ℚ) : ℝ) ((((61877 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P5Lift0 x (by norm_num [d2StandaloneCached032P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell109 (x : ℝ) (hx : x ∈ Icc ((((61877 : ℚ) / 524288) : ℚ) : ℝ) ((((4123 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P6Lift0 x (by norm_num [d2StandaloneCached032P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell110 (x : ℝ) (hx : x ∈ Icc ((((4123 : ℚ) / 32768) : ℚ) : ℝ) ((((70059 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached032P7Lift0 x (by norm_num [d2StandaloneCached032P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached032P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell111 (x : ℝ) (hx : x ∈ Icc ((((70059 : ℚ) / 524288) : ℚ) : ℝ) ((((37075 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached033P0Lift0 x (by norm_num [d2StandaloneCached033P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached033P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell112 (x : ℝ) (hx : x ∈ Icc ((((37075 : ℚ) / 262144) : ℚ) : ℝ) ((((78241 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached033P1Lift0 x (by norm_num [d2StandaloneCached033P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached033P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell113 (x : ℝ) (hx : x ∈ Icc ((((78241 : ℚ) / 524288) : ℚ) : ℝ) ((((20583 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached033P2Lift0 x (by norm_num [d2StandaloneCached033P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP022InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached033P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP022InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell114 (x : ℝ) (hx : x ∈ Icc ((((20583 : ℚ) / 131072) : ℚ) : ℝ) ((((86423 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached034P0Lift0 x (by norm_num [d2StandaloneCached034P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP023InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached034P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP023InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell115 (x : ℝ) (hx : x ∈ Icc ((((86423 : ℚ) / 524288) : ℚ) : ℝ) ((((45257 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached034P1Lift0 x (by norm_num [d2StandaloneCached034P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP023InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached034P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP023InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell116 (x : ℝ) (hx : x ∈ Icc ((((45257 : ℚ) / 262144) : ℚ) : ℝ) ((((12337 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached034P2Lift0 x (by norm_num [d2StandaloneCached034P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP023InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached034P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP023InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell117 (x : ℝ) (hx : x ∈ Icc ((((12337 : ℚ) / 65536) : ℚ) : ℝ) ((((28765 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached034P3Lift0 x (by norm_num [d2StandaloneCached034P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP023InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached034P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP023InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell118 (x : ℝ) (hx : x ∈ Icc ((((28765 : ℚ) / 131072) : ℚ) : ℝ) ((((20519 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P5Lo : ℝ) (d2StandaloneUncached006P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P5Lo, d2StandaloneUncached006P5Hi, d2StandaloneUncached006P5Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P5Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P5Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell119 (x : ℝ) (hx : x ∈ Icc ((((20519 : ℚ) / 65536) : ℚ) : ℝ) ((((4099 : ℚ) / 8192) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached006P6Lo : ℝ) (d2StandaloneUncached006P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached006P6Lo, d2StandaloneUncached006P6Hi, d2StandaloneUncached006P6Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached006P6Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached006P6Literal.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell120 (x : ℝ) (hx : x ∈ Icc ((((4099 : ℚ) / 8192) : ℚ) : ℝ) ((((20487 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached035P0Lift0 x (by norm_num [d2StandaloneCached035P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP024InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached035P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP024InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell121 (x : ℝ) (hx : x ∈ Icc ((((20487 : ℚ) / 32768) : ℚ) : ℝ) ((((94221 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached035P1Lift0 x (by norm_num [d2StandaloneCached035P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP024InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached035P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP024InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell122 (x : ℝ) (hx : x ∈ Icc ((((94221 : ℚ) / 131072) : ℚ) : ℝ) ((((12289 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached036P0Lift0 x (by norm_num [d2StandaloneCached036P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP025InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached036P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP025InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell123 (x : ℝ) (hx : x ∈ Icc ((((12289 : ℚ) / 16384) : ℚ) : ℝ) ((((102403 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached036P1Lift0 x (by norm_num [d2StandaloneCached036P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP025InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached036P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP025InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell124 (x : ℝ) (hx : x ∈ Icc ((((102403 : ℚ) / 131072) : ℚ) : ℝ) ((((217079 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached037P0Lift0 x (by norm_num [d2StandaloneCached037P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP026InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached037P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP026InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell125 (x : ℝ) (hx : x ∈ Icc ((((217079 : ℚ) / 262144) : ℚ) : ℝ) ((((225261 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached037P1Lift0 x (by norm_num [d2StandaloneCached037P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP026InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached037P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP026InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell126 (x : ℝ) (hx : x ∈ Icc ((((225261 : ℚ) / 262144) : ℚ) : ℝ) ((((454613 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached038P0Lift0 x (by norm_num [d2StandaloneCached038P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP027InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached038P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP027InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell127 (x : ℝ) (hx : x ∈ Icc ((((454613 : ℚ) / 524288) : ℚ) : ℝ) ((((28669 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached038P1Lift0 x (by norm_num [d2StandaloneCached038P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP027InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached038P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP027InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell128 (x : ℝ) (hx : x ∈ Icc ((((28669 : ℚ) / 32768) : ℚ) : ℝ) ((((462795 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached038P2Lift0 x (by norm_num [d2StandaloneCached038P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP027InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached038P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP027InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell129 (x : ℝ) (hx : x ∈ Icc ((((462795 : ℚ) / 524288) : ℚ) : ℝ) ((((233443 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached038P3Lift0 x (by norm_num [d2StandaloneCached038P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP027InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached038P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP027InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell130 (x : ℝ) (hx : x ∈ Icc ((((233443 : ℚ) / 262144) : ℚ) : ℝ) ((((118767 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached038P4Lift0 x (by norm_num [d2StandaloneCached038P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP027InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached038P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP027InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell131 (x : ℝ) (hx : x ∈ Icc ((((118767 : ℚ) / 131072) : ℚ) : ℝ) ((((241625 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P0Lift0 x (by norm_num [d2StandaloneCached039P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell132 (x : ℝ) (hx : x ∈ Icc ((((241625 : ℚ) / 262144) : ℚ) : ℝ) ((((970591 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P1Lift0 x (by norm_num [d2StandaloneCached039P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell133 (x : ℝ) (hx : x ∈ Icc ((((970591 : ℚ) / 1048576) : ℚ) : ℝ) ((((487341 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P2Lift0 x (by norm_num [d2StandaloneCached039P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell134 (x : ℝ) (hx : x ∈ Icc ((((487341 : ℚ) / 524288) : ℚ) : ℝ) ((((978773 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P3Lift0 x (by norm_num [d2StandaloneCached039P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell135 (x : ℝ) (hx : x ∈ Icc ((((978773 : ℚ) / 1048576) : ℚ) : ℝ) ((((61429 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P4Lift0 x (by norm_num [d2StandaloneCached039P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell136 (x : ℝ) (hx : x ∈ Icc ((((61429 : ℚ) / 65536) : ℚ) : ℝ) ((((986955 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P5Lift0 x (by norm_num [d2StandaloneCached039P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell137 (x : ℝ) (hx : x ∈ Icc ((((986955 : ℚ) / 1048576) : ℚ) : ℝ) ((((1978001 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P6Lift0 x (by norm_num [d2StandaloneCached039P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell138 (x : ℝ) (hx : x ∈ Icc ((((1978001 : ℚ) / 2097152) : ℚ) : ℝ) ((((995137 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached039P7Lift0 x (by norm_num [d2StandaloneCached039P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached039P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell139 (x : ℝ) (hx : x ∈ Icc ((((995137 : ℚ) / 1048576) : ℚ) : ℝ) ((((249807 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P0Lift0 x (by norm_num [d2StandaloneCached040P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell140 (x : ℝ) (hx : x ∈ Icc ((((249807 : ℚ) / 262144) : ℚ) : ℝ) ((((2002547 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P1Lift0 x (by norm_num [d2StandaloneCached040P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell141 (x : ℝ) (hx : x ∈ Icc ((((2002547 : ℚ) / 2097152) : ℚ) : ℝ) ((((1003319 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P2Lift0 x (by norm_num [d2StandaloneCached040P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell142 (x : ℝ) (hx : x ∈ Icc ((((1003319 : ℚ) / 1048576) : ℚ) : ℝ) ((((2018911 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P3Lift0 x (by norm_num [d2StandaloneCached040P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell143 (x : ℝ) (hx : x ∈ Icc ((((2018911 : ℚ) / 2097152) : ℚ) : ℝ) ((((4041913 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P4Lift0 x (by norm_num [d2StandaloneCached040P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell144 (x : ℝ) (hx : x ∈ Icc ((((4041913 : ℚ) / 4194304) : ℚ) : ℝ) ((((1011501 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P5Lift0 x (by norm_num [d2StandaloneCached040P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell145 (x : ℝ) (hx : x ∈ Icc ((((1011501 : ℚ) / 1048576) : ℚ) : ℝ) ((((2027093 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P6Lift0 x (by norm_num [d2StandaloneCached040P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell146 (x : ℝ) (hx : x ∈ Icc ((((2027093 : ℚ) / 2097152) : ℚ) : ℝ) ((((2035275 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached040P7Lift0 x (by norm_num [d2StandaloneCached040P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP028InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached040P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP028InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell147 (x : ℝ) (hx : x ∈ Icc ((((2035275 : ℚ) / 2097152) : ℚ) : ℝ) ((((1019683 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P0Lift0 x (by norm_num [d2StandaloneCached041P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell148 (x : ℝ) (hx : x ∈ Icc ((((1019683 : ℚ) / 1048576) : ℚ) : ℝ) ((((4082823 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P1Lift0 x (by norm_num [d2StandaloneCached041P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell149 (x : ℝ) (hx : x ∈ Icc ((((4082823 : ℚ) / 4194304) : ℚ) : ℝ) ((((2043457 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P2Lift0 x (by norm_num [d2StandaloneCached041P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell150 (x : ℝ) (hx : x ∈ Icc ((((2043457 : ℚ) / 2097152) : ℚ) : ℝ) ((((8218829 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P3Lift0 x (by norm_num [d2StandaloneCached041P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell151 (x : ℝ) (hx : x ∈ Icc ((((8218829 : ℚ) / 8388608) : ℚ) : ℝ) ((((1027865 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P4Lift0 x (by norm_num [d2StandaloneCached041P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell152 (x : ℝ) (hx : x ∈ Icc ((((1027865 : ℚ) / 1048576) : ℚ) : ℝ) ((((8227011 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P5Lift0 x (by norm_num [d2StandaloneCached041P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell153 (x : ℝ) (hx : x ∈ Icc ((((8227011 : ℚ) / 8388608) : ℚ) : ℝ) ((((4115551 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P6Lift0 x (by norm_num [d2StandaloneCached041P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell154 (x : ℝ) (hx : x ∈ Icc ((((4115551 : ℚ) / 4194304) : ℚ) : ℝ) ((((257989 : ℚ) / 262144) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached041P7Lift0 x (by norm_num [d2StandaloneCached041P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached041P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell155 (x : ℝ) (hx : x ∈ Icc ((((257989 : ℚ) / 262144) : ℚ) : ℝ) ((((4131915 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P0Lift0 x (by norm_num [d2StandaloneCached042P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell156 (x : ℝ) (hx : x ∈ Icc ((((4131915 : ℚ) / 4194304) : ℚ) : ℝ) ((((2068003 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P1Lift0 x (by norm_num [d2StandaloneCached042P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell157 (x : ℝ) (hx : x ∈ Icc ((((2068003 : ℚ) / 2097152) : ℚ) : ℝ) ((((16548115 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P2Lift0 x (by norm_num [d2StandaloneCached042P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell158 (x : ℝ) (hx : x ∈ Icc ((((16548115 : ℚ) / 16777216) : ℚ) : ℝ) ((((8276103 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P3Lift0 x (by norm_num [d2StandaloneCached042P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell159 (x : ℝ) (hx : x ∈ Icc ((((8276103 : ℚ) / 8388608) : ℚ) : ℝ) ((((16556297 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P4Lift0 x (by norm_num [d2StandaloneCached042P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell160 (x : ℝ) (hx : x ∈ Icc ((((16556297 : ℚ) / 16777216) : ℚ) : ℝ) ((((4140097 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P5Lift0 x (by norm_num [d2StandaloneCached042P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell161 (x : ℝ) (hx : x ∈ Icc ((((4140097 : ℚ) / 4194304) : ℚ) : ℝ) ((((1036047 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P6Lift0 x (by norm_num [d2StandaloneCached042P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell162 (x : ℝ) (hx : x ∈ Icc ((((1036047 : ℚ) / 1048576) : ℚ) : ℝ) ((((8308831 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached042P7Lift0 x (by norm_num [d2StandaloneCached042P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached042P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell163 (x : ℝ) (hx : x ∈ Icc ((((8308831 : ℚ) / 8388608) : ℚ) : ℝ) ((((33239415 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P0Lift0 x (by norm_num [d2StandaloneCached043P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell164 (x : ℝ) (hx : x ∈ Icc ((((33239415 : ℚ) / 33554432) : ℚ) : ℝ) ((((16621753 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P1Lift0 x (by norm_num [d2StandaloneCached043P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell165 (x : ℝ) (hx : x ∈ Icc ((((16621753 : ℚ) / 16777216) : ℚ) : ℝ) ((((33247597 : ℚ) / 33554432) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P2Lift0 x (by norm_num [d2StandaloneCached043P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell166 (x : ℝ) (hx : x ∈ Icc ((((33247597 : ℚ) / 33554432) : ℚ) : ℝ) ((((66499285 : ℚ) / 67108864) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P3Lift0 x (by norm_num [d2StandaloneCached043P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell167 (x : ℝ) (hx : x ∈ Icc ((((66499285 : ℚ) / 67108864) : ℚ) : ℝ) ((((4156461 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P4Lift0 x (by norm_num [d2StandaloneCached043P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell168 (x : ℝ) (hx : x ∈ Icc ((((4156461 : ℚ) / 4194304) : ℚ) : ℝ) ((((16629935 : ℚ) / 16777216) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P5Lift0 x (by norm_num [d2StandaloneCached043P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell169 (x : ℝ) (hx : x ∈ Icc ((((16629935 : ℚ) / 16777216) : ℚ) : ℝ) ((((8317013 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P6Lift0 x (by norm_num [d2StandaloneCached043P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P6LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell170 (x : ℝ) (hx : x ∈ Icc ((((8317013 : ℚ) / 8388608) : ℚ) : ℝ) ((((520069 : ℚ) / 524288) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached043P7Lift0 x (by norm_num [d2StandaloneCached043P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached043P7LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell171 (x : ℝ) (hx : x ∈ Icc ((((520069 : ℚ) / 524288) : ℚ) : ℝ) ((((4164643 : ℚ) / 4194304) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P0Lift0 x (by norm_num [d2StandaloneCached044P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P0LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell172 (x : ℝ) (hx : x ∈ Icc ((((4164643 : ℚ) / 4194304) : ℚ) : ℝ) ((((2084367 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P1Lift0 x (by norm_num [d2StandaloneCached044P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P1LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell173 (x : ℝ) (hx : x ∈ Icc ((((2084367 : ℚ) / 2097152) : ℚ) : ℝ) ((((1044229 : ℚ) / 1048576) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P2Lift0 x (by norm_num [d2StandaloneCached044P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P2LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell174 (x : ℝ) (hx : x ∈ Icc ((((1044229 : ℚ) / 1048576) : ℚ) : ℝ) ((((2092549 : ℚ) / 2097152) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P3Lift0 x (by norm_num [d2StandaloneCached044P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P3LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell175 (x : ℝ) (hx : x ∈ Icc ((((2092549 : ℚ) / 2097152) : ℚ) : ℝ) ((((8382469 : ℚ) / 8388608) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P4Lift0 x (by norm_num [d2StandaloneCached044P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P4LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell176 (x : ℝ) (hx : x ∈ Icc ((((8382469 : ℚ) / 8388608) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached044P5Lift0 x (by norm_num [d2StandaloneCached044P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP029InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached044P5LiftLiteral.q2] : _ ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP029InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem d2SAE007RawIdentity : fieldNFCheck d2SAE007FullFq D72.StandaloneFieldData.f2 = true := by decide +kernel
theorem cell177 (x : ℝ) (hx : x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE007Lo : ℝ) (d2SAE007Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE007Lo, d2SAE007Hi, d2SAE007EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE007Site : ℝ) := by
    simpa [d2SAE007Site, d2SAE007EndLiteral.q2] using hP.2
  have h := d2SAE007Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE007RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE007Target, d2SAE007EndLiteral.q2] : (d2SAE007Target : ℝ) ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [d2SAE007FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
def domain0Block0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-4398046510081 : ℚ) / 4398046511104)), (((-4398046510081 : ℚ) / 4398046511104), ((-1099511626753 : ℚ) / 1099511627776)), (((-1099511626753 : ℚ) / 1099511627776), ((-274877905921 : ℚ) / 274877906944)), (((-274877905921 : ℚ) / 274877906944), ((-68719475713 : ℚ) / 68719476736)), (((-68719475713 : ℚ) / 68719476736), ((-34359737345 : ℚ) / 34359738368)), (((-34359737345 : ℚ) / 34359738368), ((-17179868161 : ℚ) / 17179869184)), (((-17179868161 : ℚ) / 17179869184), ((-8589933569 : ℚ) / 8589934592)), (((-8589933569 : ℚ) / 8589934592), ((-4294966273 : ℚ) / 4294967296)), (((-4294966273 : ℚ) / 4294967296), ((-2147482625 : ℚ) / 2147483648)), (((-2147482625 : ℚ) / 2147483648), ((-1073740801 : ℚ) / 1073741824)), (((-1073740801 : ℚ) / 1073741824), ((-536869889 : ℚ) / 536870912)), (((-536869889 : ℚ) / 536870912), ((-268434433 : ℚ) / 268435456)), (((-268434433 : ℚ) / 268435456), ((-134216705 : ℚ) / 134217728)), (((-134216705 : ℚ) / 134217728), ((-67107841 : ℚ) / 67108864)), (((-67107841 : ℚ) / 67108864), ((-33553409 : ℚ) / 33554432)), (((-33553409 : ℚ) / 33554432), ((-16776193 : ℚ) / 16777216))]
theorem domain0Block0Cover : pieceCover ((-16776193 : ℚ) / 16777216) ((-1 : ℚ) / 1) domain0Block0Pieces = true := by decide +kernel
theorem domain0Block0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-16776193 : ℚ) / 16777216) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((-16776193 : ℚ) / 16777216) domain0Block0Pieces (by decide +kernel) domain0Block0Cover
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
def domain0Block1Pieces : List (ℚ × ℚ) := [(((-16776193 : ℚ) / 16777216), ((-8387585 : ℚ) / 8388608)), (((-8387585 : ℚ) / 8388608), ((-4193281 : ℚ) / 4194304)), (((-4193281 : ℚ) / 4194304), ((-16772101 : ℚ) / 16777216)), (((-16772101 : ℚ) / 16777216), ((-8385539 : ℚ) / 8388608)), (((-8385539 : ℚ) / 8388608), ((-16770055 : ℚ) / 16777216)), (((-16770055 : ℚ) / 16777216), ((-33539087 : ℚ) / 33554432)), (((-33539087 : ℚ) / 33554432), ((-2096129 : ℚ) / 2097152)), (((-2096129 : ℚ) / 2097152), ((-33537041 : ℚ) / 33554432)), (((-33537041 : ℚ) / 33554432), ((-1047553 : ℚ) / 1048576)), (((-1047553 : ℚ) / 1048576), ((-4189189 : ℚ) / 4194304)), (((-4189189 : ℚ) / 4194304), ((-2094083 : ℚ) / 2097152)), (((-2094083 : ℚ) / 2097152), ((-523265 : ℚ) / 524288)), (((-523265 : ℚ) / 524288), ((-1045507 : ℚ) / 1048576)), (((-1045507 : ℚ) / 1048576), ((-2089991 : ℚ) / 2097152)), (((-2089991 : ℚ) / 2097152), ((-261121 : ℚ) / 262144)), (((-261121 : ℚ) / 262144), ((-521219 : ℚ) / 524288))]
theorem domain0Block1Cover : pieceCover ((-521219 : ℚ) / 524288) ((-16776193 : ℚ) / 16777216) domain0Block1Pieces = true := by decide +kernel
theorem domain0Block1 : ∀ x ∈ Icc ((((-16776193 : ℚ) / 16777216) : ℚ) : ℝ) ((((-521219 : ℚ) / 524288) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-16776193 : ℚ) / 16777216) ((-521219 : ℚ) / 524288) domain0Block1Pieces (by decide +kernel) domain0Block1Cover
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
def domain0Block2Pieces : List (ℚ × ℚ) := [(((-521219 : ℚ) / 524288), ((-130049 : ℚ) / 131072)), (((-130049 : ℚ) / 131072), ((-519173 : ℚ) / 524288)), (((-519173 : ℚ) / 524288), ((-64513 : ℚ) / 65536)), (((-64513 : ℚ) / 65536), ((-128003 : ℚ) / 131072)), (((-128003 : ℚ) / 131072), ((-31745 : ℚ) / 32768)), (((-31745 : ℚ) / 32768), ((-62467 : ℚ) / 65536)), (((-62467 : ℚ) / 65536), ((-15361 : ℚ) / 16384)), (((-15361 : ℚ) / 16384), ((-29699 : ℚ) / 32768)), (((-29699 : ℚ) / 32768), ((-27653 : ℚ) / 32768)), (((-27653 : ℚ) / 32768), ((-23561 : ℚ) / 32768)), (((-23561 : ℚ) / 32768), ((-1025 : ℚ) / 2048)), (((-1025 : ℚ) / 2048), ((-5131 : ℚ) / 16384)), (((-5131 : ℚ) / 16384), ((-7193 : ℚ) / 32768)), (((-7193 : ℚ) / 32768), ((-3085 : ℚ) / 16384)), (((-3085 : ℚ) / 16384), ((-11317 : ℚ) / 65536)), (((-11317 : ℚ) / 65536), ((-21611 : ℚ) / 131072))]
theorem domain0Block2Cover : pieceCover ((-21611 : ℚ) / 131072) ((-521219 : ℚ) / 524288) domain0Block2Pieces = true := by decide +kernel
theorem domain0Block2 : ∀ x ∈ Icc ((((-521219 : ℚ) / 524288) : ℚ) : ℝ) ((((-21611 : ℚ) / 131072) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-521219 : ℚ) / 524288) ((-21611 : ℚ) / 131072) domain0Block2Pieces (by decide +kernel) domain0Block2Cover
  intro p hp
  simp only [domain0Block2Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro x hx hP
    exact (cell45 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell46 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell47 x hx hP).trans (by norm_num)
#print axioms domain0Block2Cover
#print axioms domain0Block2
def domain0Block3Pieces : List (ℚ × ℚ) := [(((-21611 : ℚ) / 131072), ((-5147 : ℚ) / 32768)), (((-5147 : ℚ) / 32768), ((-19565 : ℚ) / 131072)), (((-19565 : ℚ) / 131072), ((-9271 : ℚ) / 65536)), (((-9271 : ℚ) / 65536), ((-17519 : ℚ) / 131072)), (((-17519 : ℚ) / 131072), ((-1031 : ℚ) / 8192)), (((-1031 : ℚ) / 8192), ((-15473 : ℚ) / 131072)), (((-15473 : ℚ) / 131072), ((-58823 : ℚ) / 524288)), (((-58823 : ℚ) / 524288), ((-56777 : ℚ) / 524288)), (((-56777 : ℚ) / 524288), ((-112531 : ℚ) / 1048576)), (((-112531 : ℚ) / 1048576), ((-27877 : ℚ) / 262144)), (((-27877 : ℚ) / 262144), ((-13427 : ℚ) / 131072)), (((-13427 : ℚ) / 131072), ((-428641 : ℚ) / 4194304)), (((-428641 : ℚ) / 4194304), ((-426595 : ℚ) / 4194304)), (((-426595 : ℚ) / 4194304), ((-106393 : ℚ) / 1048576)), (((-106393 : ℚ) / 1048576), ((-211763 : ℚ) / 2097152)), (((-211763 : ℚ) / 2097152), ((-52685 : ℚ) / 524288))]
theorem domain0Block3Cover : pieceCover ((-52685 : ℚ) / 524288) ((-21611 : ℚ) / 131072) domain0Block3Pieces = true := by decide +kernel
theorem domain0Block3 : ∀ x ∈ Icc ((((-21611 : ℚ) / 131072) : ℚ) : ℝ) ((((-52685 : ℚ) / 524288) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-21611 : ℚ) / 131072) ((-52685 : ℚ) / 524288) domain0Block3Pieces (by decide +kernel) domain0Block3Cover
  intro p hp
  simp only [domain0Block3Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell48 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell49 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell50 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell51 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell52 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell53 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell54 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell55 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell56 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell57 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell58 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell59 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell60 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell61 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell62 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell63 x hx hP).trans (by norm_num)
#print axioms domain0Block3Cover
#print axioms domain0Block3
def domain0Block4Pieces : List (ℚ × ℚ) := [(((-52685 : ℚ) / 524288), ((-104347 : ℚ) / 1048576)), (((-104347 : ℚ) / 1048576), ((-25831 : ℚ) / 262144)), (((-25831 : ℚ) / 262144), ((-50639 : ℚ) / 524288)), (((-50639 : ℚ) / 524288), ((-3101 : ℚ) / 32768)), (((-3101 : ℚ) / 32768), ((-11381 : ℚ) / 131072)), (((-11381 : ℚ) / 131072), ((-5179 : ℚ) / 65536)), (((-5179 : ℚ) / 65536), ((-9335 : ℚ) / 131072)), (((-9335 : ℚ) / 131072), ((-1039 : ℚ) / 16384)), (((-1039 : ℚ) / 16384), ((-7289 : ℚ) / 131072)), (((-7289 : ℚ) / 131072), ((-3133 : ℚ) / 65536)), (((-3133 : ℚ) / 65536), ((-5243 : ℚ) / 131072)), (((-5243 : ℚ) / 131072), ((-1055 : ℚ) / 32768)), (((-1055 : ℚ) / 32768), ((-3197 : ℚ) / 131072)), (((-3197 : ℚ) / 131072), ((-1087 : ℚ) / 65536)), (((-1087 : ℚ) / 65536), ((-1151 : ℚ) / 131072)), (((-1151 : ℚ) / 131072), ((-1 : ℚ) / 1024))]
theorem domain0Block4Cover : pieceCover ((-1 : ℚ) / 1024) ((-52685 : ℚ) / 524288) domain0Block4Pieces = true := by decide +kernel
theorem domain0Block4 : ∀ x ∈ Icc ((((-52685 : ℚ) / 524288) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-52685 : ℚ) / 524288) ((-1 : ℚ) / 1024) domain0Block4Pieces (by decide +kernel) domain0Block4Cover
  intro p hp
  simp only [domain0Block4Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell64 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell65 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell66 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell67 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell68 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell69 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell70 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell71 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell72 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell73 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell74 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell75 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell76 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell77 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell78 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell79 x hx hP).trans (by norm_num)
#print axioms domain0Block4Cover
#print axioms domain0Block4
def domain0Block5Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1024), ((0 : ℚ) / 1))]
theorem domain0Block5Cover : pieceCover ((0 : ℚ) / 1) ((-1 : ℚ) / 1024) domain0Block5Pieces = true := by decide +kernel
theorem domain0Block5 : ∀ x ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-1 : ℚ) / 1024) ((0 : ℚ) / 1) domain0Block5Pieces (by decide +kernel) domain0Block5Cover
  intro p hp
  simp only [domain0Block5Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst p
  intro x hx hP
  exact (cell80 x hx hP).trans (by norm_num)
#print axioms domain0Block5Cover
#print axioms domain0Block5
def domain0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-16776193 : ℚ) / 16777216)), (((-16776193 : ℚ) / 16777216), ((-521219 : ℚ) / 524288)), (((-521219 : ℚ) / 524288), ((-21611 : ℚ) / 131072)), (((-21611 : ℚ) / 131072), ((-52685 : ℚ) / 524288)), (((-52685 : ℚ) / 524288), ((-1 : ℚ) / 1024)), (((-1 : ℚ) / 1024), ((0 : ℚ) / 1))]
theorem domain0Cover : pieceCover ((0 : ℚ) / 1) ((-1 : ℚ) / 1) domain0Pieces = true := by decide +kernel
theorem domain0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((0 : ℚ) / 1) domain0Pieces (by decide +kernel) domain0Cover
  intro p hp
  simp only [domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (domain0Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block2 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block3 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block4 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block5 x hx hP).trans (by norm_num)
#print axioms domain0Cover
#print axioms domain0
def domain1Block0Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((1 : ℚ) / 1024)), (((1 : ℚ) / 1024), ((4603 : ℚ) / 524288)), (((4603 : ℚ) / 524288), ((4347 : ℚ) / 262144)), (((4347 : ℚ) / 262144), ((12785 : ℚ) / 524288)), (((12785 : ℚ) / 524288), ((4219 : ℚ) / 131072)), (((4219 : ℚ) / 131072), ((20967 : ℚ) / 524288)), (((20967 : ℚ) / 524288), ((12529 : ℚ) / 262144)), (((12529 : ℚ) / 262144), ((29149 : ℚ) / 524288)), (((29149 : ℚ) / 524288), ((4155 : ℚ) / 65536)), (((4155 : ℚ) / 65536), ((37331 : ℚ) / 524288)), (((37331 : ℚ) / 524288), ((20711 : ℚ) / 262144)), (((20711 : ℚ) / 262144), ((45513 : ℚ) / 524288)), (((45513 : ℚ) / 524288), ((95117 : ℚ) / 1048576)), (((95117 : ℚ) / 1048576), ((12401 : ℚ) / 131072)), (((12401 : ℚ) / 131072), ((202507 : ℚ) / 2097152)), (((202507 : ℚ) / 2097152), ((409105 : ℚ) / 4194304))]
theorem domain1Block0Cover : pieceCover ((409105 : ℚ) / 4194304) ((0 : ℚ) / 1) domain1Block0Pieces = true := by decide +kernel
theorem domain1Block0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((409105 : ℚ) / 4194304) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((0 : ℚ) / 1) ((409105 : ℚ) / 4194304) domain1Block0Pieces (by decide +kernel) domain1Block0Cover
  intro p hp
  simp only [domain1Block0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell81 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell82 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell83 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell84 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell85 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell86 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell87 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell88 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell89 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell90 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell91 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell92 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell93 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell94 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell95 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell96 x hx hP).trans (by norm_num)
#print axioms domain1Block0Cover
#print axioms domain1Block0
def domain1Block1Pieces : List (ℚ × ℚ) := [(((409105 : ℚ) / 4194304), ((822301 : ℚ) / 8388608)), (((822301 : ℚ) / 8388608), ((103299 : ℚ) / 1048576)), (((103299 : ℚ) / 1048576), ((1656875 : ℚ) / 16777216)), (((1656875 : ℚ) / 16777216), ((1665057 : ℚ) / 16777216)), (((1665057 : ℚ) / 16777216), ((210689 : ℚ) / 2097152)), (((210689 : ℚ) / 2097152), ((433651 : ℚ) / 4194304)), (((433651 : ℚ) / 4194304), ((218871 : ℚ) / 2097152)), (((218871 : ℚ) / 2097152), ((441833 : ℚ) / 4194304)), (((441833 : ℚ) / 4194304), ((111481 : ℚ) / 1048576)), (((111481 : ℚ) / 1048576), ((28893 : ℚ) / 262144)), (((28893 : ℚ) / 262144), ((119663 : ℚ) / 1048576)), (((119663 : ℚ) / 1048576), ((61877 : ℚ) / 524288)), (((61877 : ℚ) / 524288), ((4123 : ℚ) / 32768)), (((4123 : ℚ) / 32768), ((70059 : ℚ) / 524288)), (((70059 : ℚ) / 524288), ((37075 : ℚ) / 262144)), (((37075 : ℚ) / 262144), ((78241 : ℚ) / 524288))]
theorem domain1Block1Cover : pieceCover ((78241 : ℚ) / 524288) ((409105 : ℚ) / 4194304) domain1Block1Pieces = true := by decide +kernel
theorem domain1Block1 : ∀ x ∈ Icc ((((409105 : ℚ) / 4194304) : ℚ) : ℝ) ((((78241 : ℚ) / 524288) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((409105 : ℚ) / 4194304) ((78241 : ℚ) / 524288) domain1Block1Pieces (by decide +kernel) domain1Block1Cover
  intro p hp
  simp only [domain1Block1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell97 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell98 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell99 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell100 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell101 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell102 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell103 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell104 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell105 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell106 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell107 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell108 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell109 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell110 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell111 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell112 x hx hP).trans (by norm_num)
#print axioms domain1Block1Cover
#print axioms domain1Block1
def domain1Block2Pieces : List (ℚ × ℚ) := [(((78241 : ℚ) / 524288), ((20583 : ℚ) / 131072)), (((20583 : ℚ) / 131072), ((86423 : ℚ) / 524288)), (((86423 : ℚ) / 524288), ((45257 : ℚ) / 262144)), (((45257 : ℚ) / 262144), ((12337 : ℚ) / 65536)), (((12337 : ℚ) / 65536), ((28765 : ℚ) / 131072)), (((28765 : ℚ) / 131072), ((20519 : ℚ) / 65536)), (((20519 : ℚ) / 65536), ((4099 : ℚ) / 8192)), (((4099 : ℚ) / 8192), ((20487 : ℚ) / 32768)), (((20487 : ℚ) / 32768), ((94221 : ℚ) / 131072)), (((94221 : ℚ) / 131072), ((12289 : ℚ) / 16384)), (((12289 : ℚ) / 16384), ((102403 : ℚ) / 131072)), (((102403 : ℚ) / 131072), ((217079 : ℚ) / 262144)), (((217079 : ℚ) / 262144), ((225261 : ℚ) / 262144)), (((225261 : ℚ) / 262144), ((454613 : ℚ) / 524288)), (((454613 : ℚ) / 524288), ((28669 : ℚ) / 32768)), (((28669 : ℚ) / 32768), ((462795 : ℚ) / 524288))]
theorem domain1Block2Cover : pieceCover ((462795 : ℚ) / 524288) ((78241 : ℚ) / 524288) domain1Block2Pieces = true := by decide +kernel
theorem domain1Block2 : ∀ x ∈ Icc ((((78241 : ℚ) / 524288) : ℚ) : ℝ) ((((462795 : ℚ) / 524288) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((78241 : ℚ) / 524288) ((462795 : ℚ) / 524288) domain1Block2Pieces (by decide +kernel) domain1Block2Cover
  intro p hp
  simp only [domain1Block2Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell113 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell114 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell115 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell116 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell117 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell118 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell119 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell120 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell121 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell122 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell123 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell124 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell125 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell126 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell127 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell128 x hx hP).trans (by norm_num)
#print axioms domain1Block2Cover
#print axioms domain1Block2
def domain1Block3Pieces : List (ℚ × ℚ) := [(((462795 : ℚ) / 524288), ((233443 : ℚ) / 262144)), (((233443 : ℚ) / 262144), ((118767 : ℚ) / 131072)), (((118767 : ℚ) / 131072), ((241625 : ℚ) / 262144)), (((241625 : ℚ) / 262144), ((970591 : ℚ) / 1048576)), (((970591 : ℚ) / 1048576), ((487341 : ℚ) / 524288)), (((487341 : ℚ) / 524288), ((978773 : ℚ) / 1048576)), (((978773 : ℚ) / 1048576), ((61429 : ℚ) / 65536)), (((61429 : ℚ) / 65536), ((986955 : ℚ) / 1048576)), (((986955 : ℚ) / 1048576), ((1978001 : ℚ) / 2097152)), (((1978001 : ℚ) / 2097152), ((995137 : ℚ) / 1048576)), (((995137 : ℚ) / 1048576), ((249807 : ℚ) / 262144)), (((249807 : ℚ) / 262144), ((2002547 : ℚ) / 2097152)), (((2002547 : ℚ) / 2097152), ((1003319 : ℚ) / 1048576)), (((1003319 : ℚ) / 1048576), ((2018911 : ℚ) / 2097152)), (((2018911 : ℚ) / 2097152), ((4041913 : ℚ) / 4194304)), (((4041913 : ℚ) / 4194304), ((1011501 : ℚ) / 1048576))]
theorem domain1Block3Cover : pieceCover ((1011501 : ℚ) / 1048576) ((462795 : ℚ) / 524288) domain1Block3Pieces = true := by decide +kernel
theorem domain1Block3 : ∀ x ∈ Icc ((((462795 : ℚ) / 524288) : ℚ) : ℝ) ((((1011501 : ℚ) / 1048576) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((462795 : ℚ) / 524288) ((1011501 : ℚ) / 1048576) domain1Block3Pieces (by decide +kernel) domain1Block3Cover
  intro p hp
  simp only [domain1Block3Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell129 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell130 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell131 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell132 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell133 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell134 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell135 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell136 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell137 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell138 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell139 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell140 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell141 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell142 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell143 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell144 x hx hP).trans (by norm_num)
#print axioms domain1Block3Cover
#print axioms domain1Block3
def domain1Block4Pieces : List (ℚ × ℚ) := [(((1011501 : ℚ) / 1048576), ((2027093 : ℚ) / 2097152)), (((2027093 : ℚ) / 2097152), ((2035275 : ℚ) / 2097152)), (((2035275 : ℚ) / 2097152), ((1019683 : ℚ) / 1048576)), (((1019683 : ℚ) / 1048576), ((4082823 : ℚ) / 4194304)), (((4082823 : ℚ) / 4194304), ((2043457 : ℚ) / 2097152)), (((2043457 : ℚ) / 2097152), ((8218829 : ℚ) / 8388608)), (((8218829 : ℚ) / 8388608), ((1027865 : ℚ) / 1048576)), (((1027865 : ℚ) / 1048576), ((8227011 : ℚ) / 8388608)), (((8227011 : ℚ) / 8388608), ((4115551 : ℚ) / 4194304)), (((4115551 : ℚ) / 4194304), ((257989 : ℚ) / 262144)), (((257989 : ℚ) / 262144), ((4131915 : ℚ) / 4194304)), (((4131915 : ℚ) / 4194304), ((2068003 : ℚ) / 2097152)), (((2068003 : ℚ) / 2097152), ((16548115 : ℚ) / 16777216)), (((16548115 : ℚ) / 16777216), ((8276103 : ℚ) / 8388608)), (((8276103 : ℚ) / 8388608), ((16556297 : ℚ) / 16777216)), (((16556297 : ℚ) / 16777216), ((4140097 : ℚ) / 4194304))]
theorem domain1Block4Cover : pieceCover ((4140097 : ℚ) / 4194304) ((1011501 : ℚ) / 1048576) domain1Block4Pieces = true := by decide +kernel
theorem domain1Block4 : ∀ x ∈ Icc ((((1011501 : ℚ) / 1048576) : ℚ) : ℝ) ((((4140097 : ℚ) / 4194304) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((1011501 : ℚ) / 1048576) ((4140097 : ℚ) / 4194304) domain1Block4Pieces (by decide +kernel) domain1Block4Cover
  intro p hp
  simp only [domain1Block4Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell145 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell146 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell147 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell148 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell149 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell150 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell151 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell152 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell153 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell154 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell155 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell156 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell157 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell158 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell159 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell160 x hx hP).trans (by norm_num)
#print axioms domain1Block4Cover
#print axioms domain1Block4
def domain1Block5Pieces : List (ℚ × ℚ) := [(((4140097 : ℚ) / 4194304), ((1036047 : ℚ) / 1048576)), (((1036047 : ℚ) / 1048576), ((8308831 : ℚ) / 8388608)), (((8308831 : ℚ) / 8388608), ((33239415 : ℚ) / 33554432)), (((33239415 : ℚ) / 33554432), ((16621753 : ℚ) / 16777216)), (((16621753 : ℚ) / 16777216), ((33247597 : ℚ) / 33554432)), (((33247597 : ℚ) / 33554432), ((66499285 : ℚ) / 67108864)), (((66499285 : ℚ) / 67108864), ((4156461 : ℚ) / 4194304)), (((4156461 : ℚ) / 4194304), ((16629935 : ℚ) / 16777216)), (((16629935 : ℚ) / 16777216), ((8317013 : ℚ) / 8388608)), (((8317013 : ℚ) / 8388608), ((520069 : ℚ) / 524288)), (((520069 : ℚ) / 524288), ((4164643 : ℚ) / 4194304)), (((4164643 : ℚ) / 4194304), ((2084367 : ℚ) / 2097152)), (((2084367 : ℚ) / 2097152), ((1044229 : ℚ) / 1048576)), (((1044229 : ℚ) / 1048576), ((2092549 : ℚ) / 2097152)), (((2092549 : ℚ) / 2097152), ((8382469 : ℚ) / 8388608)), (((8382469 : ℚ) / 8388608), ((4095 : ℚ) / 4096))]
theorem domain1Block5Cover : pieceCover ((4095 : ℚ) / 4096) ((4140097 : ℚ) / 4194304) domain1Block5Pieces = true := by decide +kernel
theorem domain1Block5 : ∀ x ∈ Icc ((((4140097 : ℚ) / 4194304) : ℚ) : ℝ) ((((4095 : ℚ) / 4096) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((4140097 : ℚ) / 4194304) ((4095 : ℚ) / 4096) domain1Block5Pieces (by decide +kernel) domain1Block5Cover
  intro p hp
  simp only [domain1Block5Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell161 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell162 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell163 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell164 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell165 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell166 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell167 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell168 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell169 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell170 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell171 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell172 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell173 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell174 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell175 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell176 x hx hP).trans (by norm_num)
#print axioms domain1Block5Cover
#print axioms domain1Block5
def domain1Block6Pieces : List (ℚ × ℚ) := [(((4095 : ℚ) / 4096), ((1 : ℚ) / 1))]
theorem domain1Block6Cover : pieceCover ((1 : ℚ) / 1) ((4095 : ℚ) / 4096) domain1Block6Pieces = true := by decide +kernel
theorem domain1Block6 : ∀ x ∈ Icc ((((4095 : ℚ) / 4096) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((4095 : ℚ) / 4096) ((1 : ℚ) / 1) domain1Block6Pieces (by decide +kernel) domain1Block6Cover
  intro p hp
  simp only [domain1Block6Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  subst p
  intro x hx hP
  exact (cell177 x hx hP).trans (by norm_num)
#print axioms domain1Block6Cover
#print axioms domain1Block6
def domain1Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((409105 : ℚ) / 4194304)), (((409105 : ℚ) / 4194304), ((78241 : ℚ) / 524288)), (((78241 : ℚ) / 524288), ((462795 : ℚ) / 524288)), (((462795 : ℚ) / 524288), ((1011501 : ℚ) / 1048576)), (((1011501 : ℚ) / 1048576), ((4140097 : ℚ) / 4194304)), (((4140097 : ℚ) / 4194304), ((4095 : ℚ) / 4096)), (((4095 : ℚ) / 4096), ((1 : ℚ) / 1))]
theorem domain1Cover : pieceCover ((1 : ℚ) / 1) ((0 : ℚ) / 1) domain1Pieces = true := by decide +kernel
theorem domain1 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263019657569864829385479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((0 : ℚ) / 1) ((1 : ℚ) / 1) domain1Pieces (by decide +kernel) domain1Cover
  intro p hp
  simp only [domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (domain1Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block2 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block3 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block4 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block5 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block6 x hx hP).trans (by norm_num)
#print axioms domain1Cover
#print axioms domain1
end D72.StandaloneCoverReferenceRow

end CatalanMeasure.GenD.Signed.Data.Cells

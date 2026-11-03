module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneEnd002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached002
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneCoverFirstRow
def valid (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-130049 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P0Lo : ℝ) (d2StandaloneUncached001P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P0Lo, d2StandaloneUncached001P0Hi, d2StandaloneUncached001P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P0Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((-130049 : ℚ) / 131072) : ℚ) : ℝ) ((((-15361 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P1Lo : ℝ) (d2StandaloneUncached001P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P1Lo, d2StandaloneUncached001P1Hi, d2StandaloneUncached001P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P1Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((-15361 : ℚ) / 16384) : ℚ) : ℝ) ((((-25607 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P2Lo : ℝ) (d2StandaloneUncached001P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P2Lo, d2StandaloneUncached001P2Hi, d2StandaloneUncached001P2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P2Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P2Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((-25607 : ℚ) / 32768) : ℚ) : ℝ) ((((-17423 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P3Lo : ℝ) (d2StandaloneUncached001P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P3Lo, d2StandaloneUncached001P3Hi, d2StandaloneUncached001P3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P3Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P3Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell4 (x : ℝ) (hx : x ∈ Icc ((((-17423 : ℚ) / 32768) : ℚ) : ℝ) ((((-1025 : ℚ) / 2048) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached000P0Lift0 x (by norm_num [d2StandaloneCached000P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP000InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached000P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP000InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell5 (x : ℝ) (hx : x ∈ Icc ((((-1025 : ℚ) / 2048) : ℚ) : ℝ) ((((-31777 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached000P1Lift0 x (by norm_num [d2StandaloneCached000P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP000InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached000P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP000InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell6 (x : ℝ) (hx : x ∈ Icc ((((-31777 : ℚ) / 65536) : ℚ) : ℝ) ((((-9239 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P4Lo : ℝ) (d2StandaloneUncached001P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P4Lo, d2StandaloneUncached001P4Hi, d2StandaloneUncached001P4Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P4Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P4Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell7 (x : ℝ) (hx : x ∈ Icc ((((-9239 : ℚ) / 32768) : ℚ) : ℝ) ((((-3085 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P5Lo : ℝ) (d2StandaloneUncached001P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P5Lo, d2StandaloneUncached001P5Hi, d2StandaloneUncached001P5Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P5Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P5Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell8 (x : ℝ) (hx : x ∈ Icc ((((-3085 : ℚ) / 16384) : ℚ) : ℝ) ((((-21611 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached001P0Lift0 x (by norm_num [d2StandaloneCached001P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP001InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached001P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP001InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell9 (x : ℝ) (hx : x ∈ Icc ((((-21611 : ℚ) / 131072) : ℚ) : ℝ) ((((-5147 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached001P1Lift0 x (by norm_num [d2StandaloneCached001P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP001InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached001P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP001InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell10 (x : ℝ) (hx : x ∈ Icc ((((-5147 : ℚ) / 32768) : ℚ) : ℝ) ((((-19565 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P0Lift0 x (by norm_num [d2StandaloneCached002P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell11 (x : ℝ) (hx : x ∈ Icc ((((-19565 : ℚ) / 131072) : ℚ) : ℝ) ((((-9271 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P1Lift0 x (by norm_num [d2StandaloneCached002P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell12 (x : ℝ) (hx : x ∈ Icc ((((-9271 : ℚ) / 65536) : ℚ) : ℝ) ((((-17519 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P2Lift0 x (by norm_num [d2StandaloneCached002P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell13 (x : ℝ) (hx : x ∈ Icc ((((-17519 : ℚ) / 131072) : ℚ) : ℝ) ((((-1031 : ℚ) / 8192) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P3Lift0 x (by norm_num [d2StandaloneCached002P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P3LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell14 (x : ℝ) (hx : x ∈ Icc ((((-1031 : ℚ) / 8192) : ℚ) : ℝ) ((((-15473 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P4Lift0 x (by norm_num [d2StandaloneCached002P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P4LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell15 (x : ℝ) (hx : x ∈ Icc ((((-15473 : ℚ) / 131072) : ℚ) : ℝ) ((((-7225 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P5Lift0 x (by norm_num [d2StandaloneCached002P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P5LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell16 (x : ℝ) (hx : x ∈ Icc ((((-7225 : ℚ) / 65536) : ℚ) : ℝ) ((((-13427 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P6Lift0 x (by norm_num [d2StandaloneCached002P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P6LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell17 (x : ℝ) (hx : x ∈ Icc ((((-13427 : ℚ) / 131072) : ℚ) : ℝ) ((((-3101 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached002P7Lift0 x (by norm_num [d2StandaloneCached002P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP002InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached002P7LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP002InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell18 (x : ℝ) (hx : x ∈ Icc ((((-3101 : ℚ) / 32768) : ℚ) : ℝ) ((((-11381 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P0Lift0 x (by norm_num [d2StandaloneCached003P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell19 (x : ℝ) (hx : x ∈ Icc ((((-11381 : ℚ) / 131072) : ℚ) : ℝ) ((((-5179 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P1Lift0 x (by norm_num [d2StandaloneCached003P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell20 (x : ℝ) (hx : x ∈ Icc ((((-5179 : ℚ) / 65536) : ℚ) : ℝ) ((((-9335 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P2Lift0 x (by norm_num [d2StandaloneCached003P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell21 (x : ℝ) (hx : x ∈ Icc ((((-9335 : ℚ) / 131072) : ℚ) : ℝ) ((((-1039 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P3Lift0 x (by norm_num [d2StandaloneCached003P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P3LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell22 (x : ℝ) (hx : x ∈ Icc ((((-1039 : ℚ) / 16384) : ℚ) : ℝ) ((((-7289 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P4Lift0 x (by norm_num [d2StandaloneCached003P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P4LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell23 (x : ℝ) (hx : x ∈ Icc ((((-7289 : ℚ) / 131072) : ℚ) : ℝ) ((((-3133 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P5Lift0 x (by norm_num [d2StandaloneCached003P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P5LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell24 (x : ℝ) (hx : x ∈ Icc ((((-3133 : ℚ) / 65536) : ℚ) : ℝ) ((((-5243 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P6Lift0 x (by norm_num [d2StandaloneCached003P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P6LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell25 (x : ℝ) (hx : x ∈ Icc ((((-5243 : ℚ) / 131072) : ℚ) : ℝ) ((((-1055 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached003P7Lift0 x (by norm_num [d2StandaloneCached003P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP003InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached003P7LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP003InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell26 (x : ℝ) (hx : x ∈ Icc ((((-1055 : ℚ) / 32768) : ℚ) : ℝ) ((((-3197 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P0Lift0 x (by norm_num [d2StandaloneCached004P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell27 (x : ℝ) (hx : x ∈ Icc ((((-3197 : ℚ) / 131072) : ℚ) : ℝ) ((((-1087 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P1Lift0 x (by norm_num [d2StandaloneCached004P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell28 (x : ℝ) (hx : x ∈ Icc ((((-1087 : ℚ) / 65536) : ℚ) : ℝ) ((((-1151 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P2Lift0 x (by norm_num [d2StandaloneCached004P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell29 (x : ℝ) (hx : x ∈ Icc ((((-1151 : ℚ) / 131072) : ℚ) : ℝ) ((((-1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P3Lift0 x (by norm_num [d2StandaloneCached004P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P3LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem d2SAE000RawIdentity : fieldNFCheck d2SAE000FullFq D72.StandaloneFieldData.f0 = true := by decide +kernel
theorem cell30 (x : ℝ) (hx : x ∈ Icc ((((-1 : ℚ) / 1024) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE000Lo : ℝ) (d2SAE000Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE000Lo, d2SAE000Hi, d2SAE000EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE000Site : ℝ) := by
    simpa [d2SAE000Site, d2SAE000EndLiteral.q2] using hP.1
  have h := d2SAE000Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE000RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE000Target, d2SAE000EndLiteral.q2] : (d2SAE000Target : ℝ) ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [d2SAE000FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem d2SAE001RawIdentity : fieldNFCheck d2SAE001FullFq D72.StandaloneFieldData.f0 = true := by decide +kernel
theorem cell31 (x : ℝ) (hx : x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE001Lo : ℝ) (d2SAE001Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE001Lo, d2SAE001Hi, d2SAE001EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE001Site : ℝ) := by
    simpa [d2SAE001Site, d2SAE001EndLiteral.q2] using hP.1
  have h := d2SAE001Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE001RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE001Target, d2SAE001EndLiteral.q2] : (d2SAE001Target : ℝ) ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [d2SAE001FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell32 (x : ℝ) (hx : x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((575 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P4Lift0 x (by norm_num [d2StandaloneCached004P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P4LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell33 (x : ℝ) (hx : x ∈ Icc ((((575 : ℚ) / 65536) : ℚ) : ℝ) ((((543 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P5Lift0 x (by norm_num [d2StandaloneCached004P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P5LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell34 (x : ℝ) (hx : x ∈ Icc ((((543 : ℚ) / 32768) : ℚ) : ℝ) ((((1597 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P6Lift0 x (by norm_num [d2StandaloneCached004P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P6LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell35 (x : ℝ) (hx : x ∈ Icc ((((1597 : ℚ) / 65536) : ℚ) : ℝ) ((((527 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached004P7Lift0 x (by norm_num [d2StandaloneCached004P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP004InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached004P7LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP004InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell36 (x : ℝ) (hx : x ∈ Icc ((((527 : ℚ) / 16384) : ℚ) : ℝ) ((((2619 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P0Lift0 x (by norm_num [d2StandaloneCached005P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell37 (x : ℝ) (hx : x ∈ Icc ((((2619 : ℚ) / 65536) : ℚ) : ℝ) ((((1565 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P1Lift0 x (by norm_num [d2StandaloneCached005P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell38 (x : ℝ) (hx : x ∈ Icc ((((1565 : ℚ) / 32768) : ℚ) : ℝ) ((((3641 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P2Lift0 x (by norm_num [d2StandaloneCached005P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell39 (x : ℝ) (hx : x ∈ Icc ((((3641 : ℚ) / 65536) : ℚ) : ℝ) ((((519 : ℚ) / 8192) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P3Lift0 x (by norm_num [d2StandaloneCached005P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P3LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell40 (x : ℝ) (hx : x ∈ Icc ((((519 : ℚ) / 8192) : ℚ) : ℝ) ((((4663 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P4Lift0 x (by norm_num [d2StandaloneCached005P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P4LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell41 (x : ℝ) (hx : x ∈ Icc ((((4663 : ℚ) / 65536) : ℚ) : ℝ) ((((2587 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P5Lift0 x (by norm_num [d2StandaloneCached005P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P5LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell42 (x : ℝ) (hx : x ∈ Icc ((((2587 : ℚ) / 32768) : ℚ) : ℝ) ((((5685 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P6Lift0 x (by norm_num [d2StandaloneCached005P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P6LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell43 (x : ℝ) (hx : x ∈ Icc ((((5685 : ℚ) / 65536) : ℚ) : ℝ) ((((11881 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached005P7Lift0 x (by norm_num [d2StandaloneCached005P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached005P7LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell44 (x : ℝ) (hx : x ∈ Icc ((((11881 : ℚ) / 131072) : ℚ) : ℝ) ((((1549 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached006P0Lift0 x (by norm_num [d2StandaloneCached006P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP005InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached006P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP005InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell45 (x : ℝ) (hx : x ∈ Icc ((((1549 : ℚ) / 16384) : ℚ) : ℝ) ((((6707 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P0Lift0 x (by norm_num [d2StandaloneCached007P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell46 (x : ℝ) (hx : x ∈ Icc ((((6707 : ℚ) / 65536) : ℚ) : ℝ) ((((3609 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P1Lift0 x (by norm_num [d2StandaloneCached007P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell47 (x : ℝ) (hx : x ∈ Icc ((((3609 : ℚ) / 32768) : ℚ) : ℝ) ((((7729 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P2Lift0 x (by norm_num [d2StandaloneCached007P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell48 (x : ℝ) (hx : x ∈ Icc ((((7729 : ℚ) / 65536) : ℚ) : ℝ) ((((515 : ℚ) / 4096) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P3Lift0 x (by norm_num [d2StandaloneCached007P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P3LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell49 (x : ℝ) (hx : x ∈ Icc ((((515 : ℚ) / 4096) : ℚ) : ℝ) ((((8751 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P4Lift0 x (by norm_num [d2StandaloneCached007P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P4LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell50 (x : ℝ) (hx : x ∈ Icc ((((8751 : ℚ) / 65536) : ℚ) : ℝ) ((((4631 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P5Lift0 x (by norm_num [d2StandaloneCached007P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P5LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell51 (x : ℝ) (hx : x ∈ Icc ((((4631 : ℚ) / 32768) : ℚ) : ℝ) ((((9773 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P6Lift0 x (by norm_num [d2StandaloneCached007P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P6LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell52 (x : ℝ) (hx : x ∈ Icc ((((9773 : ℚ) / 65536) : ℚ) : ℝ) ((((2571 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached007P7Lift0 x (by norm_num [d2StandaloneCached007P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP006InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached007P7LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP006InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell53 (x : ℝ) (hx : x ∈ Icc ((((2571 : ℚ) / 16384) : ℚ) : ℝ) ((((10795 : ℚ) / 65536) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached008P0Lift0 x (by norm_num [d2StandaloneCached008P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP007InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached008P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP007InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell54 (x : ℝ) (hx : x ∈ Icc ((((10795 : ℚ) / 65536) : ℚ) : ℝ) ((((3593 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached008P1Lift0 x (by norm_num [d2StandaloneCached008P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP007InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached008P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP007InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell55 (x : ℝ) (hx : x ∈ Icc ((((3593 : ℚ) / 16384) : ℚ) : ℝ) ((((1537 : ℚ) / 4096) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P6Lo : ℝ) (d2StandaloneUncached001P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P6Lo, d2StandaloneUncached001P6Hi, d2StandaloneUncached001P6Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P6Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P6Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell56 (x : ℝ) (hx : x ∈ Icc ((((1537 : ℚ) / 4096) : ℚ) : ℝ) ((((2559 : ℚ) / 4096) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached001P7Lo : ℝ) (d2StandaloneUncached001P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached001P7Lo, d2StandaloneUncached001P7Hi, d2StandaloneUncached001P7Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached001P7Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached001P7Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell57 (x : ℝ) (hx : x ∈ Icc ((((2559 : ℚ) / 4096) : ℚ) : ℝ) ((((11769 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached002P0Lo : ℝ) (d2StandaloneUncached002P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached002P0Lo, d2StandaloneUncached002P0Hi, d2StandaloneUncached002P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached002P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached002P0Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell58 (x : ℝ) (hx : x ∈ Icc ((((11769 : ℚ) / 16384) : ℚ) : ℝ) ((((1535 : ℚ) / 2048) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached009P0Lift0 x (by norm_num [d2StandaloneCached009P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP008InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached009P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP008InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell59 (x : ℝ) (hx : x ∈ Icc ((((1535 : ℚ) / 2048) : ℚ) : ℝ) ((((12791 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached009P1Lift0 x (by norm_num [d2StandaloneCached009P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP008InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached009P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP008InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell60 (x : ℝ) (hx : x ∈ Icc ((((12791 : ℚ) / 16384) : ℚ) : ℝ) ((((14835 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached002P1Lo : ℝ) (d2StandaloneUncached002P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached002P1Lo, d2StandaloneUncached002P1Hi, d2StandaloneUncached002P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached002P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached002P1Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell61 (x : ℝ) (hx : x ∈ Icc ((((14835 : ℚ) / 16384) : ℚ) : ℝ) ((((15857 : ℚ) / 16384) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached002P2Lo : ℝ) (d2StandaloneUncached002P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached002P2Lo, d2StandaloneUncached002P2Hi, d2StandaloneUncached002P2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached002P2Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached002P2Literal.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
theorem cell62 (x : ℝ) (hx : x ∈ Icc ((((15857 : ℚ) / 16384) : ℚ) : ℝ) ((((32225 : ℚ) / 32768) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached010P0Lift0 x (by norm_num [d2StandaloneCached010P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP009InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached010P0LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP009InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell63 (x : ℝ) (hx : x ∈ Icc ((((32225 : ℚ) / 32768) : ℚ) : ℝ) ((((130433 : ℚ) / 131072) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached010P1Lift0 x (by norm_num [d2StandaloneCached010P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP009InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached010P1LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP009InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem cell64 (x : ℝ) (hx : x ∈ Icc ((((130433 : ℚ) / 131072) : ℚ) : ℝ) ((((1023 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached010P2Lift0 x (by norm_num [d2StandaloneCached010P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP009InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached010P2LiftLiteral.q2] : _ ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  have hnil : d2SAP009InputTs = [] := rfl
  simpa only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] using h'
theorem d2SAE002RawIdentity : fieldNFCheck d2SAE002FullFq D72.StandaloneFieldData.f0 = true := by decide +kernel
theorem cell65 (x : ℝ) (hx : x ∈ Icc ((((1023 : ℚ) / 1024) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2SAE002Lo : ℝ) (d2SAE002Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2SAE002Lo, d2SAE002Hi, d2SAE002EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2SAE002Site : ℝ) := by
    simpa [d2SAE002Site, d2SAE002EndLiteral.q2] using hP.2
  have h := d2SAE002Bound x hxE hne
  rw [fieldNFCheck_sound d2SAE002RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2SAE002Target, d2SAE002EndLiteral.q2] : (d2SAE002Target : ℝ) ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ))
  simpa only [d2SAE002FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero] using hBound
def domain0Block0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-130049 : ℚ) / 131072)), (((-130049 : ℚ) / 131072), ((-15361 : ℚ) / 16384)), (((-15361 : ℚ) / 16384), ((-25607 : ℚ) / 32768)), (((-25607 : ℚ) / 32768), ((-17423 : ℚ) / 32768)), (((-17423 : ℚ) / 32768), ((-1025 : ℚ) / 2048)), (((-1025 : ℚ) / 2048), ((-31777 : ℚ) / 65536)), (((-31777 : ℚ) / 65536), ((-9239 : ℚ) / 32768)), (((-9239 : ℚ) / 32768), ((-3085 : ℚ) / 16384)), (((-3085 : ℚ) / 16384), ((-21611 : ℚ) / 131072)), (((-21611 : ℚ) / 131072), ((-5147 : ℚ) / 32768)), (((-5147 : ℚ) / 32768), ((-19565 : ℚ) / 131072)), (((-19565 : ℚ) / 131072), ((-9271 : ℚ) / 65536)), (((-9271 : ℚ) / 65536), ((-17519 : ℚ) / 131072)), (((-17519 : ℚ) / 131072), ((-1031 : ℚ) / 8192)), (((-1031 : ℚ) / 8192), ((-15473 : ℚ) / 131072)), (((-15473 : ℚ) / 131072), ((-7225 : ℚ) / 65536))]
theorem domain0Block0Cover : pieceCover ((-7225 : ℚ) / 65536) ((-1 : ℚ) / 1) domain0Block0Pieces = true := by decide +kernel
theorem domain0Block0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-7225 : ℚ) / 65536) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((-7225 : ℚ) / 65536) domain0Block0Pieces (by decide +kernel) domain0Block0Cover
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
def domain0Block1Pieces : List (ℚ × ℚ) := [(((-7225 : ℚ) / 65536), ((-13427 : ℚ) / 131072)), (((-13427 : ℚ) / 131072), ((-3101 : ℚ) / 32768)), (((-3101 : ℚ) / 32768), ((-11381 : ℚ) / 131072)), (((-11381 : ℚ) / 131072), ((-5179 : ℚ) / 65536)), (((-5179 : ℚ) / 65536), ((-9335 : ℚ) / 131072)), (((-9335 : ℚ) / 131072), ((-1039 : ℚ) / 16384)), (((-1039 : ℚ) / 16384), ((-7289 : ℚ) / 131072)), (((-7289 : ℚ) / 131072), ((-3133 : ℚ) / 65536)), (((-3133 : ℚ) / 65536), ((-5243 : ℚ) / 131072)), (((-5243 : ℚ) / 131072), ((-1055 : ℚ) / 32768)), (((-1055 : ℚ) / 32768), ((-3197 : ℚ) / 131072)), (((-3197 : ℚ) / 131072), ((-1087 : ℚ) / 65536)), (((-1087 : ℚ) / 65536), ((-1151 : ℚ) / 131072)), (((-1151 : ℚ) / 131072), ((-1 : ℚ) / 1024)), (((-1 : ℚ) / 1024), ((0 : ℚ) / 1))]
theorem domain0Block1Cover : pieceCover ((0 : ℚ) / 1) ((-7225 : ℚ) / 65536) domain0Block1Pieces = true := by decide +kernel
theorem domain0Block1 : ∀ x ∈ Icc ((((-7225 : ℚ) / 65536) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((-7225 : ℚ) / 65536) ((0 : ℚ) / 1) domain0Block1Pieces (by decide +kernel) domain0Block1Cover
  intro p hp
  simp only [domain0Block1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms domain0Block1Cover
#print axioms domain0Block1
def domain0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-7225 : ℚ) / 65536)), (((-7225 : ℚ) / 65536), ((0 : ℚ) / 1))]
theorem domain0Cover : pieceCover ((0 : ℚ) / 1) ((-1 : ℚ) / 1) domain0Pieces = true := by decide +kernel
theorem domain0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((0 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((0 : ℚ) / 1) domain0Pieces (by decide +kernel) domain0Cover
  intro p hp
  simp only [domain0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · intro x hx hP
    exact (domain0Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain0Block1 x hx hP).trans (by norm_num)
#print axioms domain0Cover
#print axioms domain0
def domain1Block0Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((1 : ℚ) / 1024)), (((1 : ℚ) / 1024), ((575 : ℚ) / 65536)), (((575 : ℚ) / 65536), ((543 : ℚ) / 32768)), (((543 : ℚ) / 32768), ((1597 : ℚ) / 65536)), (((1597 : ℚ) / 65536), ((527 : ℚ) / 16384)), (((527 : ℚ) / 16384), ((2619 : ℚ) / 65536)), (((2619 : ℚ) / 65536), ((1565 : ℚ) / 32768)), (((1565 : ℚ) / 32768), ((3641 : ℚ) / 65536)), (((3641 : ℚ) / 65536), ((519 : ℚ) / 8192)), (((519 : ℚ) / 8192), ((4663 : ℚ) / 65536)), (((4663 : ℚ) / 65536), ((2587 : ℚ) / 32768)), (((2587 : ℚ) / 32768), ((5685 : ℚ) / 65536)), (((5685 : ℚ) / 65536), ((11881 : ℚ) / 131072)), (((11881 : ℚ) / 131072), ((1549 : ℚ) / 16384)), (((1549 : ℚ) / 16384), ((6707 : ℚ) / 65536)), (((6707 : ℚ) / 65536), ((3609 : ℚ) / 32768))]
theorem domain1Block0Cover : pieceCover ((3609 : ℚ) / 32768) ((0 : ℚ) / 1) domain1Block0Pieces = true := by decide +kernel
theorem domain1Block0 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((3609 : ℚ) / 32768) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((0 : ℚ) / 1) ((3609 : ℚ) / 32768) domain1Block0Pieces (by decide +kernel) domain1Block0Cover
  intro p hp
  simp only [domain1Block0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell31 x hx hP).trans (by norm_num)
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
#print axioms domain1Block0Cover
#print axioms domain1Block0
def domain1Block1Pieces : List (ℚ × ℚ) := [(((3609 : ℚ) / 32768), ((7729 : ℚ) / 65536)), (((7729 : ℚ) / 65536), ((515 : ℚ) / 4096)), (((515 : ℚ) / 4096), ((8751 : ℚ) / 65536)), (((8751 : ℚ) / 65536), ((4631 : ℚ) / 32768)), (((4631 : ℚ) / 32768), ((9773 : ℚ) / 65536)), (((9773 : ℚ) / 65536), ((2571 : ℚ) / 16384)), (((2571 : ℚ) / 16384), ((10795 : ℚ) / 65536)), (((10795 : ℚ) / 65536), ((3593 : ℚ) / 16384)), (((3593 : ℚ) / 16384), ((1537 : ℚ) / 4096)), (((1537 : ℚ) / 4096), ((2559 : ℚ) / 4096)), (((2559 : ℚ) / 4096), ((11769 : ℚ) / 16384)), (((11769 : ℚ) / 16384), ((1535 : ℚ) / 2048)), (((1535 : ℚ) / 2048), ((12791 : ℚ) / 16384)), (((12791 : ℚ) / 16384), ((14835 : ℚ) / 16384)), (((14835 : ℚ) / 16384), ((15857 : ℚ) / 16384)), (((15857 : ℚ) / 16384), ((32225 : ℚ) / 32768))]
theorem domain1Block1Cover : pieceCover ((32225 : ℚ) / 32768) ((3609 : ℚ) / 32768) domain1Block1Pieces = true := by decide +kernel
theorem domain1Block1 : ∀ x ∈ Icc ((((3609 : ℚ) / 32768) : ℚ) : ℝ) ((((32225 : ℚ) / 32768) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((3609 : ℚ) / 32768) ((32225 : ℚ) / 32768) domain1Block1Pieces (by decide +kernel) domain1Block1Cover
  intro p hp
  simp only [domain1Block1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell47 x hx hP).trans (by norm_num)
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
#print axioms domain1Block1Cover
#print axioms domain1Block1
def domain1Block2Pieces : List (ℚ × ℚ) := [(((32225 : ℚ) / 32768), ((130433 : ℚ) / 131072)), (((130433 : ℚ) / 131072), ((1023 : ℚ) / 1024)), (((1023 : ℚ) / 1024), ((1 : ℚ) / 1))]
theorem domain1Block2Cover : pieceCover ((1 : ℚ) / 1) ((32225 : ℚ) / 32768) domain1Block2Pieces = true := by decide +kernel
theorem domain1Block2 : ∀ x ∈ Icc ((((32225 : ℚ) / 32768) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((32225 : ℚ) / 32768) ((1 : ℚ) / 1) domain1Block2Pieces (by decide +kernel) domain1Block2Cover
  intro p hp
  simp only [domain1Block2Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · intro x hx hP
    exact (cell63 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell64 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell65 x hx hP).trans (by norm_num)
#print axioms domain1Block2Cover
#print axioms domain1Block2
def domain1Pieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((3609 : ℚ) / 32768)), (((3609 : ℚ) / 32768), ((32225 : ℚ) / 32768)), (((32225 : ℚ) / 32768), ((1 : ℚ) / 1))]
theorem domain1Cover : pieceCover ((1 : ℚ) / 1) ((0 : ℚ) / 1) domain1Pieces = true := by decide +kernel
theorem domain1 : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f0 x ≤ ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f0) valid ((((-33625206883788140229 : ℚ) / 4503599627370496000) : ℚ) : ℝ) ((0 : ℚ) / 1) ((1 : ℚ) / 1) domain1Pieces (by decide +kernel) domain1Cover
  intro p hp
  simp only [domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · intro x hx hP
    exact (domain1Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block2 x hx hP).trans (by norm_num)
#print axioms domain1Cover
#print axioms domain1
end D72.StandaloneCoverFirstRow

end CatalanMeasure.GenD.Signed.Data.Cells

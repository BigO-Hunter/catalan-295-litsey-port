module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached045
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached046
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached047
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached048
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCached049
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneResidualGap
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneUncached005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneCoverReferenceResidual
def valid (x : ℝ) : Prop := True
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-289910292477901 : ℚ) / 289910292480000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P0Lift0 x (by norm_num [d2StandaloneCached045P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P0LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((-289910292477901 : ℚ) / 289910292480000) : ℚ) : ℝ) ((((-72477573117901 : ℚ) / 72477573120000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P1Lift0 x (by norm_num [d2StandaloneCached045P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P1LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((-72477573117901 : ℚ) / 72477573120000) : ℚ) : ℝ) ((((-36238786557901 : ℚ) / 36238786560000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P2Lift0 x (by norm_num [d2StandaloneCached045P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P2LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((-36238786557901 : ℚ) / 36238786560000) : ℚ) : ℝ) ((((-18119393277901 : ℚ) / 18119393280000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P3Lift0 x (by norm_num [d2StandaloneCached045P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P3LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell4 (x : ℝ) (hx : x ∈ Icc ((((-18119393277901 : ℚ) / 18119393280000) : ℚ) : ℝ) ((((-9059696637901 : ℚ) / 9059696640000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P4Lift0 x (by norm_num [d2StandaloneCached045P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P4LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell5 (x : ℝ) (hx : x ∈ Icc ((((-9059696637901 : ℚ) / 9059696640000) : ℚ) : ℝ) ((((-4529848317901 : ℚ) / 4529848320000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P5Lift0 x (by norm_num [d2StandaloneCached045P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P5LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell6 (x : ℝ) (hx : x ∈ Icc ((((-4529848317901 : ℚ) / 4529848320000) : ℚ) : ℝ) ((((-2264924157901 : ℚ) / 2264924160000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P6Lift0 x (by norm_num [d2StandaloneCached045P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P6LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell7 (x : ℝ) (hx : x ∈ Icc ((((-2264924157901 : ℚ) / 2264924160000) : ℚ) : ℝ) ((((-1132462077901 : ℚ) / 1132462080000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached045P7Lift0 x (by norm_num [d2StandaloneCached045P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached045P7LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell8 (x : ℝ) (hx : x ∈ Icc ((((-1132462077901 : ℚ) / 1132462080000) : ℚ) : ℝ) ((((-566231037901 : ℚ) / 566231040000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P0Lift0 x (by norm_num [d2StandaloneCached046P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P0LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell9 (x : ℝ) (hx : x ∈ Icc ((((-566231037901 : ℚ) / 566231040000) : ℚ) : ℝ) ((((-283115517901 : ℚ) / 283115520000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P1Lift0 x (by norm_num [d2StandaloneCached046P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P1LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell10 (x : ℝ) (hx : x ∈ Icc ((((-283115517901 : ℚ) / 283115520000) : ℚ) : ℝ) ((((-141557757901 : ℚ) / 141557760000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P2Lift0 x (by norm_num [d2StandaloneCached046P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P2LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell11 (x : ℝ) (hx : x ∈ Icc ((((-141557757901 : ℚ) / 141557760000) : ℚ) : ℝ) ((((-70778877901 : ℚ) / 70778880000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P3Lift0 x (by norm_num [d2StandaloneCached046P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P3LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell12 (x : ℝ) (hx : x ∈ Icc ((((-70778877901 : ℚ) / 70778880000) : ℚ) : ℝ) ((((-35389437901 : ℚ) / 35389440000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P4Lift0 x (by norm_num [d2StandaloneCached046P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P4LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell13 (x : ℝ) (hx : x ∈ Icc ((((-35389437901 : ℚ) / 35389440000) : ℚ) : ℝ) ((((-17694717901 : ℚ) / 17694720000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P5Lift0 x (by norm_num [d2StandaloneCached046P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P5LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell14 (x : ℝ) (hx : x ∈ Icc ((((-17694717901 : ℚ) / 17694720000) : ℚ) : ℝ) ((((-8847357901 : ℚ) / 8847360000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P6Lift0 x (by norm_num [d2StandaloneCached046P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P6LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell15 (x : ℝ) (hx : x ∈ Icc ((((-8847357901 : ℚ) / 8847360000) : ℚ) : ℝ) ((((-4423677901 : ℚ) / 4423680000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached046P7Lift0 x (by norm_num [d2StandaloneCached046P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached046P7LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell16 (x : ℝ) (hx : x ∈ Icc ((((-4423677901 : ℚ) / 4423680000) : ℚ) : ℝ) ((((-2211837901 : ℚ) / 2211840000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P0Lift0 x (by norm_num [d2StandaloneCached047P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P0LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell17 (x : ℝ) (hx : x ∈ Icc ((((-2211837901 : ℚ) / 2211840000) : ℚ) : ℝ) ((((-1105917901 : ℚ) / 1105920000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P1Lift0 x (by norm_num [d2StandaloneCached047P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P1LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell18 (x : ℝ) (hx : x ∈ Icc ((((-1105917901 : ℚ) / 1105920000) : ℚ) : ℝ) ((((-552957901 : ℚ) / 552960000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P2Lift0 x (by norm_num [d2StandaloneCached047P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P2LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell19 (x : ℝ) (hx : x ∈ Icc ((((-552957901 : ℚ) / 552960000) : ℚ) : ℝ) ((((-276477901 : ℚ) / 276480000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P3Lift0 x (by norm_num [d2StandaloneCached047P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P3LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell20 (x : ℝ) (hx : x ∈ Icc ((((-276477901 : ℚ) / 276480000) : ℚ) : ℝ) ((((-138237901 : ℚ) / 138240000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P4Lift0 x (by norm_num [d2StandaloneCached047P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P4LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell21 (x : ℝ) (hx : x ∈ Icc ((((-138237901 : ℚ) / 138240000) : ℚ) : ℝ) ((((-69117901 : ℚ) / 69120000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P5Lift0 x (by norm_num [d2StandaloneCached047P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P5LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell22 (x : ℝ) (hx : x ∈ Icc ((((-69117901 : ℚ) / 69120000) : ℚ) : ℝ) ((((-34557901 : ℚ) / 34560000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P6Lift0 x (by norm_num [d2StandaloneCached047P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P6LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell23 (x : ℝ) (hx : x ∈ Icc ((((-34557901 : ℚ) / 34560000) : ℚ) : ℝ) ((((-11517901 : ℚ) / 11520000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached047P7Lift0 x (by norm_num [d2StandaloneCached047P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached047P7LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell24 (x : ℝ) (hx : x ∈ Icc ((((-11517901 : ℚ) / 11520000) : ℚ) : ℝ) ((((-8637901 : ℚ) / 8640000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P0Lift0 x (by norm_num [d2StandaloneCached048P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P0LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell25 (x : ℝ) (hx : x ∈ Icc ((((-8637901 : ℚ) / 8640000) : ℚ) : ℝ) ((((-4317901 : ℚ) / 4320000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P1Lift0 x (by norm_num [d2StandaloneCached048P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P1LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell26 (x : ℝ) (hx : x ∈ Icc ((((-4317901 : ℚ) / 4320000) : ℚ) : ℝ) ((((-2157901 : ℚ) / 2160000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P2Lift0 x (by norm_num [d2StandaloneCached048P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P2LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell27 (x : ℝ) (hx : x ∈ Icc ((((-2157901 : ℚ) / 2160000) : ℚ) : ℝ) ((((-1077901 : ℚ) / 1080000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P3Lift0 x (by norm_num [d2StandaloneCached048P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P3LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell28 (x : ℝ) (hx : x ∈ Icc ((((-1077901 : ℚ) / 1080000) : ℚ) : ℝ) ((((-537901 : ℚ) / 540000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P4Lift0 x (by norm_num [d2StandaloneCached048P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P4LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell29 (x : ℝ) (hx : x ∈ Icc ((((-537901 : ℚ) / 540000) : ℚ) : ℝ) ((((-267901 : ℚ) / 270000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P5Lift0 x (by norm_num [d2StandaloneCached048P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P5LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell30 (x : ℝ) (hx : x ∈ Icc ((((-267901 : ℚ) / 270000) : ℚ) : ℝ) ((((-132901 : ℚ) / 135000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P6Lift0 x (by norm_num [d2StandaloneCached048P6LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P6LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell31 (x : ℝ) (hx : x ∈ Icc ((((-132901 : ℚ) / 135000) : ℚ) : ℝ) ((((-65401 : ℚ) / 67500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached048P7Lift0 x (by norm_num [d2StandaloneCached048P7LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP030InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached048P7LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP030InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell32 (x : ℝ) (hx : x ∈ Icc ((((-65401 : ℚ) / 67500) : ℚ) : ℝ) ((((-20401 : ℚ) / 22500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P0Lo : ℝ) (d2StandaloneUncached004P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P0Lo, d2StandaloneUncached004P0Hi, d2StandaloneUncached004P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P0Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell33 (x : ℝ) (hx : x ∈ Icc ((((-20401 : ℚ) / 22500) : ℚ) : ℝ) ((((-5401 : ℚ) / 7500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P1Lo : ℝ) (d2StandaloneUncached004P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P1Lo, d2StandaloneUncached004P1Hi, d2StandaloneUncached004P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P1Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell34 (x : ℝ) (hx : x ∈ Icc ((((-5401 : ℚ) / 7500) : ℚ) : ℝ) ((((-31817 : ℚ) / 67500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P2Lo : ℝ) (d2StandaloneUncached004P2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P2Lo, d2StandaloneUncached004P2Hi, d2StandaloneUncached004P2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P2Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P2Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell35 (x : ℝ) (hx : x ∈ Icc ((((-31817 : ℚ) / 67500) : ℚ) : ℝ) ((((-601 : ℚ) / 2700) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P3Lo : ℝ) (d2StandaloneUncached004P3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P3Lo, d2StandaloneUncached004P3Hi, d2StandaloneUncached004P3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P3Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P3Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell36 (x : ℝ) (hx : x ∈ Icc ((((-601 : ℚ) / 2700) : ℚ) : ℝ) ((((-401 : ℚ) / 2500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P4Lo : ℝ) (d2StandaloneUncached004P4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P4Lo, d2StandaloneUncached004P4Hi, d2StandaloneUncached004P4Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P4Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P4Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell37 (x : ℝ) (hx : x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((851643 : ℚ) / 8000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap0Lo : ℝ) (d2ResidualGap0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap0Lo, d2ResidualGap0Hi, d2ResidualGap0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap0Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap0Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell38 (x : ℝ) (hx : x ∈ Icc ((((851643 : ℚ) / 8000000) : ℚ) : ℝ) ((((456647 : ℚ) / 4000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap1Lo : ℝ) (d2ResidualGap1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap1Lo, d2ResidualGap1Hi, d2ResidualGap1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap1Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap1Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell39 (x : ℝ) (hx : x ∈ Icc ((((456647 : ℚ) / 4000000) : ℚ) : ℝ) ((((194989 : ℚ) / 1600000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap2Lo : ℝ) (d2ResidualGap2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap2Lo, d2ResidualGap2Hi, d2ResidualGap2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap2Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap2Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell40 (x : ℝ) (hx : x ∈ Icc ((((194989 : ℚ) / 1600000) : ℚ) : ℝ) ((((259149 : ℚ) / 2000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap3Lo : ℝ) (d2ResidualGap3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap3Lo, d2ResidualGap3Hi, d2ResidualGap3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap3Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap3Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell41 (x : ℝ) (hx : x ∈ Icc ((((259149 : ℚ) / 2000000) : ℚ) : ℝ) ((((1098247 : ℚ) / 8000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap4Lo : ℝ) (d2ResidualGap4Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap4Lo, d2ResidualGap4Hi, d2ResidualGap4Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap4Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap4Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell42 (x : ℝ) (hx : x ∈ Icc ((((1098247 : ℚ) / 8000000) : ℚ) : ℝ) ((((579949 : ℚ) / 4000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap5Lo : ℝ) (d2ResidualGap5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap5Lo, d2ResidualGap5Hi, d2ResidualGap5Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap5Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap5Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell43 (x : ℝ) (hx : x ∈ Icc ((((579949 : ℚ) / 4000000) : ℚ) : ℝ) ((((1221549 : ℚ) / 8000000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap6Lo : ℝ) (d2ResidualGap6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap6Lo, d2ResidualGap6Hi, d2ResidualGap6Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap6Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap6Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell44 (x : ℝ) (hx : x ∈ Icc ((((1221549 : ℚ) / 8000000) : ℚ) : ℝ) ((((401 : ℚ) / 2500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2ResidualGap7Lo : ℝ) (d2ResidualGap7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2ResidualGap7Lo, d2ResidualGap7Hi, d2ResidualGap7Literal.q2] at hx ⊢ <;> exact hx
  have h := d2ResidualGap7Bound x hxC
  have hBound := h.trans (by norm_num [d2ResidualGap7Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell45 (x : ℝ) (hx : x ∈ Icc ((((401 : ℚ) / 2500) : ℚ) : ℝ) ((((10661 : ℚ) / 33750) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P5Lo : ℝ) (d2StandaloneUncached004P5Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P5Lo, d2StandaloneUncached004P5Hi, d2StandaloneUncached004P5Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P5Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P5Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell46 (x : ℝ) (hx : x ∈ Icc ((((10661 : ℚ) / 33750) : ℚ) : ℝ) ((((19057 : ℚ) / 33750) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P6Lo : ℝ) (d2StandaloneUncached004P6Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P6Lo, d2StandaloneUncached004P6Hi, d2StandaloneUncached004P6Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P6Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P6Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell47 (x : ℝ) (hx : x ∈ Icc ((((19057 : ℚ) / 33750) : ℚ) : ℝ) ((((9151 : ℚ) / 11250) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached004P7Lo : ℝ) (d2StandaloneUncached004P7Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached004P7Lo, d2StandaloneUncached004P7Hi, d2StandaloneUncached004P7Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached004P7Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached004P7Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell48 (x : ℝ) (hx : x ∈ Icc ((((9151 : ℚ) / 11250) : ℚ) : ℝ) ((((31651 : ℚ) / 33750) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached005P0Lo : ℝ) (d2StandaloneUncached005P0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached005P0Lo, d2StandaloneUncached005P0Hi, d2StandaloneUncached005P0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached005P0Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached005P0Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell49 (x : ℝ) (hx : x ∈ Icc ((((31651 : ℚ) / 33750) : ℚ) : ℝ) ((((65401 : ℚ) / 67500) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2StandaloneUncached005P1Lo : ℝ) (d2StandaloneUncached005P1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2StandaloneUncached005P1Lo, d2StandaloneUncached005P1Hi, d2StandaloneUncached005P1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2StandaloneUncached005P1Bound x hxC
  have hBound := h.trans (by norm_num [d2StandaloneUncached005P1Literal.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simp only [lfieldTower, List.map_nil, List.sum_nil, add_zero] at hBound
  first | exact hBound | exact le_of_le_of_eq hBound rfl
theorem cell50 (x : ℝ) (hx : x ∈ Icc ((((65401 : ℚ) / 67500) : ℚ) : ℝ) ((((132901 : ℚ) / 135000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P0Lift0 x (by norm_num [d2StandaloneCached049P0LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P0LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell51 (x : ℝ) (hx : x ∈ Icc ((((132901 : ℚ) / 135000) : ℚ) : ℝ) ((((267901 : ℚ) / 270000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P1Lift0 x (by norm_num [d2StandaloneCached049P1LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P1LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell52 (x : ℝ) (hx : x ∈ Icc ((((267901 : ℚ) / 270000) : ℚ) : ℝ) ((((537901 : ℚ) / 540000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P2Lift0 x (by norm_num [d2StandaloneCached049P2LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P2LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell53 (x : ℝ) (hx : x ∈ Icc ((((537901 : ℚ) / 540000) : ℚ) : ℝ) ((((1077901 : ℚ) / 1080000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P3Lift0 x (by norm_num [d2StandaloneCached049P3LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P3LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell54 (x : ℝ) (hx : x ∈ Icc ((((1077901 : ℚ) / 1080000) : ℚ) : ℝ) ((((4317901 : ℚ) / 4320000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P4Lift0 x (by norm_num [d2StandaloneCached049P4LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P4LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
theorem cell55 (x : ℝ) (hx : x ∈ Icc ((((4317901 : ℚ) / 4320000) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have h := d2StandaloneCached049P5Lift0 x (by norm_num [d2StandaloneCached049P5LiftLiteral.q2, Set.mem_Icc] at hx ⊢ <;> exact hx)
  rw [d2SAP031InputFq, fieldClean_sound] at h
  have h' := h.trans (by norm_num [d2StandaloneCached049P5LiftLiteral.q2] : _ ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  have hnil : d2SAP031InputTs = [] := rfl
  simp only [hnil, lfieldTower, List.map_nil, List.sum_nil, add_zero] at h'
  first | exact h' | exact le_of_le_of_eq h' rfl
def domain0Block0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-289910292477901 : ℚ) / 289910292480000)), (((-289910292477901 : ℚ) / 289910292480000), ((-72477573117901 : ℚ) / 72477573120000)), (((-72477573117901 : ℚ) / 72477573120000), ((-36238786557901 : ℚ) / 36238786560000)), (((-36238786557901 : ℚ) / 36238786560000), ((-18119393277901 : ℚ) / 18119393280000)), (((-18119393277901 : ℚ) / 18119393280000), ((-9059696637901 : ℚ) / 9059696640000)), (((-9059696637901 : ℚ) / 9059696640000), ((-4529848317901 : ℚ) / 4529848320000)), (((-4529848317901 : ℚ) / 4529848320000), ((-2264924157901 : ℚ) / 2264924160000)), (((-2264924157901 : ℚ) / 2264924160000), ((-1132462077901 : ℚ) / 1132462080000)), (((-1132462077901 : ℚ) / 1132462080000), ((-566231037901 : ℚ) / 566231040000)), (((-566231037901 : ℚ) / 566231040000), ((-283115517901 : ℚ) / 283115520000)), (((-283115517901 : ℚ) / 283115520000), ((-141557757901 : ℚ) / 141557760000)), (((-141557757901 : ℚ) / 141557760000), ((-70778877901 : ℚ) / 70778880000)), (((-70778877901 : ℚ) / 70778880000), ((-35389437901 : ℚ) / 35389440000)), (((-35389437901 : ℚ) / 35389440000), ((-17694717901 : ℚ) / 17694720000)), (((-17694717901 : ℚ) / 17694720000), ((-8847357901 : ℚ) / 8847360000)), (((-8847357901 : ℚ) / 8847360000), ((-4423677901 : ℚ) / 4423680000))]
theorem domain0Block0Cover : pieceCover ((-4423677901 : ℚ) / 4423680000) ((-1 : ℚ) / 1) domain0Block0Pieces = true := by decide +kernel
theorem domain0Block0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-4423677901 : ℚ) / 4423680000) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((-4423677901 : ℚ) / 4423680000) domain0Block0Pieces (by decide +kernel) domain0Block0Cover
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
def domain0Block1Pieces : List (ℚ × ℚ) := [(((-4423677901 : ℚ) / 4423680000), ((-2211837901 : ℚ) / 2211840000)), (((-2211837901 : ℚ) / 2211840000), ((-1105917901 : ℚ) / 1105920000)), (((-1105917901 : ℚ) / 1105920000), ((-552957901 : ℚ) / 552960000)), (((-552957901 : ℚ) / 552960000), ((-276477901 : ℚ) / 276480000)), (((-276477901 : ℚ) / 276480000), ((-138237901 : ℚ) / 138240000)), (((-138237901 : ℚ) / 138240000), ((-69117901 : ℚ) / 69120000)), (((-69117901 : ℚ) / 69120000), ((-34557901 : ℚ) / 34560000)), (((-34557901 : ℚ) / 34560000), ((-11517901 : ℚ) / 11520000)), (((-11517901 : ℚ) / 11520000), ((-8637901 : ℚ) / 8640000)), (((-8637901 : ℚ) / 8640000), ((-4317901 : ℚ) / 4320000)), (((-4317901 : ℚ) / 4320000), ((-2157901 : ℚ) / 2160000)), (((-2157901 : ℚ) / 2160000), ((-1077901 : ℚ) / 1080000)), (((-1077901 : ℚ) / 1080000), ((-537901 : ℚ) / 540000)), (((-537901 : ℚ) / 540000), ((-267901 : ℚ) / 270000)), (((-267901 : ℚ) / 270000), ((-132901 : ℚ) / 135000)), (((-132901 : ℚ) / 135000), ((-65401 : ℚ) / 67500))]
theorem domain0Block1Cover : pieceCover ((-65401 : ℚ) / 67500) ((-4423677901 : ℚ) / 4423680000) domain0Block1Pieces = true := by decide +kernel
theorem domain0Block1 : ∀ x ∈ Icc ((((-4423677901 : ℚ) / 4423680000) : ℚ) : ℝ) ((((-65401 : ℚ) / 67500) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-4423677901 : ℚ) / 4423680000) ((-65401 : ℚ) / 67500) domain0Block1Pieces (by decide +kernel) domain0Block1Cover
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
def domain0Block2Pieces : List (ℚ × ℚ) := [(((-65401 : ℚ) / 67500), ((-20401 : ℚ) / 22500)), (((-20401 : ℚ) / 22500), ((-5401 : ℚ) / 7500)), (((-5401 : ℚ) / 7500), ((-31817 : ℚ) / 67500)), (((-31817 : ℚ) / 67500), ((-601 : ℚ) / 2700)), (((-601 : ℚ) / 2700), ((-401 : ℚ) / 2500))]
theorem domain0Block2Cover : pieceCover ((-401 : ℚ) / 2500) ((-65401 : ℚ) / 67500) domain0Block2Pieces = true := by decide +kernel
theorem domain0Block2 : ∀ x ∈ Icc ((((-65401 : ℚ) / 67500) : ℚ) : ℝ) ((((-401 : ℚ) / 2500) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-65401 : ℚ) / 67500) ((-401 : ℚ) / 2500) domain0Block2Pieces (by decide +kernel) domain0Block2Cover
  intro p hp
  simp only [domain0Block2Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
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
#print axioms domain0Block2Cover
#print axioms domain0Block2
def domain0Pieces : List (ℚ × ℚ) := [(((-1 : ℚ) / 1), ((-4423677901 : ℚ) / 4423680000)), (((-4423677901 : ℚ) / 4423680000), ((-65401 : ℚ) / 67500)), (((-65401 : ℚ) / 67500), ((-401 : ℚ) / 2500))]
theorem domain0Cover : pieceCover ((-401 : ℚ) / 2500) ((-1 : ℚ) / 1) domain0Pieces = true := by decide +kernel
theorem domain0 : ∀ x ∈ Icc ((((-1 : ℚ) / 1) : ℚ) : ℝ) ((((-401 : ℚ) / 2500) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((-1 : ℚ) / 1) ((-401 : ℚ) / 2500) domain0Pieces (by decide +kernel) domain0Cover
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
def domain1Block0Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((851643 : ℚ) / 8000000)), (((851643 : ℚ) / 8000000), ((456647 : ℚ) / 4000000)), (((456647 : ℚ) / 4000000), ((194989 : ℚ) / 1600000)), (((194989 : ℚ) / 1600000), ((259149 : ℚ) / 2000000)), (((259149 : ℚ) / 2000000), ((1098247 : ℚ) / 8000000)), (((1098247 : ℚ) / 8000000), ((579949 : ℚ) / 4000000)), (((579949 : ℚ) / 4000000), ((1221549 : ℚ) / 8000000)), (((1221549 : ℚ) / 8000000), ((401 : ℚ) / 2500)), (((401 : ℚ) / 2500), ((10661 : ℚ) / 33750)), (((10661 : ℚ) / 33750), ((19057 : ℚ) / 33750)), (((19057 : ℚ) / 33750), ((9151 : ℚ) / 11250)), (((9151 : ℚ) / 11250), ((31651 : ℚ) / 33750)), (((31651 : ℚ) / 33750), ((65401 : ℚ) / 67500)), (((65401 : ℚ) / 67500), ((132901 : ℚ) / 135000)), (((132901 : ℚ) / 135000), ((267901 : ℚ) / 270000)), (((267901 : ℚ) / 270000), ((537901 : ℚ) / 540000))]
theorem domain1Block0Cover : pieceCover ((537901 : ℚ) / 540000) ((98749 : ℚ) / 1000000) domain1Block0Pieces = true := by decide +kernel
theorem domain1Block0 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((537901 : ℚ) / 540000) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) ((537901 : ℚ) / 540000) domain1Block0Pieces (by decide +kernel) domain1Block0Cover
  intro p hp
  simp only [domain1Block0Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
#print axioms domain1Block0Cover
#print axioms domain1Block0
def domain1Block1Pieces : List (ℚ × ℚ) := [(((537901 : ℚ) / 540000), ((1077901 : ℚ) / 1080000)), (((1077901 : ℚ) / 1080000), ((4317901 : ℚ) / 4320000)), (((4317901 : ℚ) / 4320000), ((1 : ℚ) / 1))]
theorem domain1Block1Cover : pieceCover ((1 : ℚ) / 1) ((537901 : ℚ) / 540000) domain1Block1Pieces = true := by decide +kernel
theorem domain1Block1 : ∀ x ∈ Icc ((((537901 : ℚ) / 540000) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((537901 : ℚ) / 540000) ((1 : ℚ) / 1) domain1Block1Pieces (by decide +kernel) domain1Block1Cover
  intro p hp
  simp only [domain1Block1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · intro x hx hP
    exact (cell53 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell54 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell55 x hx hP).trans (by norm_num)
#print axioms domain1Block1Cover
#print axioms domain1Block1
def domain1Pieces : List (ℚ × ℚ) := [(((98749 : ℚ) / 1000000), ((537901 : ℚ) / 540000)), (((537901 : ℚ) / 540000), ((1 : ℚ) / 1))]
theorem domain1Cover : pieceCover ((1 : ℚ) / 1) ((98749 : ℚ) / 1000000) domain1Pieces = true := by decide +kernel
theorem domain1 : ∀ x ∈ Icc ((((98749 : ℚ) / 1000000) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f3 x ≤ ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f3) valid ((((-147137254242524485100131 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((98749 : ℚ) / 1000000) ((1 : ℚ) / 1) domain1Pieces (by decide +kernel) domain1Cover
  intro p hp
  simp only [domain1Pieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · intro x hx hP
    exact (domain1Block0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (domain1Block1 x hx hP).trans (by norm_num)
#print axioms domain1Cover
#print axioms domain1
end D72.StandaloneCoverReferenceResidual

end CatalanMeasure.GenD.Signed.Data.Cells

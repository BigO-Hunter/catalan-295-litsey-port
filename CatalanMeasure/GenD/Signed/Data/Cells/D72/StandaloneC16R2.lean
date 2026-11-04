module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R2Packet00
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneC16R2
def valid (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((549343497027459 : ℚ) / 549755813888000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R2P1C0Lo : ℝ) (d2C16R2P1C0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R2P1C0Lo, d2C16R2P1C0Hi, d2C16R2P1C0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R2P1C0Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R2P1C0Literal.q2] : _ ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((549343497027459 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((549618374934153 : ℚ) / 549755813888000) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R2P1C1Lo : ℝ) (d2C16R2P1C1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R2P1C1Lo, d2C16R2P1C1Hi, d2C16R2P1C1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R2P1C1Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R2P1C1Literal.q2] : _ ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((549618374934153 : ℚ) / 549755813888000) : ℚ) : ℝ) ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R2P1C2Lo : ℝ) (d2C16R2P1C2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R2P1C2Lo, d2C16R2P1C2Hi, d2C16R2P1C2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R2P1C2Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R2P1C2Literal.q2] : _ ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem d2C16R2P1C3RawIdentity : fieldNFCheck d2C16R2P1C3FullFq D72.StandaloneFieldData.f2 = true := by decide +kernel
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((1099511627775 : ℚ) / 1099511627776) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2C16R2P1C3Lo : ℝ) (d2C16R2P1C3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R2P1C3Lo, d2C16R2P1C3Hi, d2C16R2P1C3EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2C16R2P1C3Site : ℝ) := by
    simpa [d2C16R2P1C3Site, d2C16R2P1C3EndLiteral.q2] using hP.2
  have h := d2C16R2P1C3Bound x hxE hne
  rw [fieldNFCheck_sound d2C16R2P1C3RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2C16R2P1C3Target, d2C16R2P1C3EndLiteral.q2] : (d2C16R2P1C3Target : ℝ) ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [d2C16R2P1C3FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
def boundPieces : List (ℚ × ℚ) := [(((999 : ℚ) / 1000), ((549343497027459 : ℚ) / 549755813888000)), (((549343497027459 : ℚ) / 549755813888000), ((549618374934153 : ℚ) / 549755813888000)), (((549618374934153 : ℚ) / 549755813888000), ((1099511627775 : ℚ) / 1099511627776)), (((1099511627775 : ℚ) / 1099511627776), ((1 : ℚ) / 1))]
theorem boundCover : pieceCover ((1 : ℚ) / 1) ((999 : ℚ) / 1000) boundPieces = true := by decide +kernel
theorem bound : ∀ x ∈ Icc ((((999 : ℚ) / 1000) : ℚ) : ℝ) ((((1 : ℚ) / 1) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-265413602246788958665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((999 : ℚ) / 1000) ((1 : ℚ) / 1) boundPieces (by decide +kernel) boundCover
  intro p hp
  simp only [boundPieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell0 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell1 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell2 x hx hP).trans (by norm_num)
  · intro x hx hP
    exact (cell3 x hx hP).trans (by norm_num)
#print axioms boundCover
#print axioms bound
end D72.StandaloneC16R2

end CatalanMeasure.GenD.Signed.Data.Cells

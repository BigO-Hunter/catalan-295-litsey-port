module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Trial.Hid
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverTools
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldData
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1pPacket00
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1pPacket01
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1pPacket02
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1pPacket03
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
namespace D72.StandaloneC16R1p
def valid (x : ℝ) : Prop := x ≠ 0 ∧ x ≠ 1
theorem cell0 (x : ℝ) (hx : x ∈ Icc ((((1 : ℚ) / 1024) : ℚ) : ℝ) ((((689 : ℚ) / 102400) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP1C0Lo : ℝ) (d2C16R1pP1C0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP1C0Lo, d2C16R1pP1C0Hi, d2C16R1pP1C0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP1C0Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP1C0Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell1 (x : ℝ) (hx : x ∈ Icc ((((689 : ℚ) / 102400) : ℚ) : ℝ) ((((639 : ℚ) / 51200) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP1C1Lo : ℝ) (d2C16R1pP1C1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP1C1Lo, d2C16R1pP1C1Hi, d2C16R1pP1C1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP1C1Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP1C1Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell2 (x : ℝ) (hx : x ∈ Icc ((((639 : ℚ) / 51200) : ℚ) : ℝ) ((((1867 : ℚ) / 102400) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP1C2Lo : ℝ) (d2C16R1pP1C2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP1C2Lo, d2C16R1pP1C2Hi, d2C16R1pP1C2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP1C2Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP1C2Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell3 (x : ℝ) (hx : x ∈ Icc ((((1867 : ℚ) / 102400) : ℚ) : ℝ) ((((307 : ℚ) / 12800) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP1C3Lo : ℝ) (d2C16R1pP1C3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP1C3Lo, d2C16R1pP1C3Hi, d2C16R1pP1C3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP1C3Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP1C3Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell4 (x : ℝ) (hx : x ∈ Icc ((((307 : ℚ) / 12800) : ℚ) : ℝ) ((((609 : ℚ) / 20480) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP2C0Lo : ℝ) (d2C16R1pP2C0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP2C0Lo, d2C16R1pP2C0Hi, d2C16R1pP2C0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP2C0Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP2C0Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell5 (x : ℝ) (hx : x ∈ Icc ((((609 : ℚ) / 20480) : ℚ) : ℝ) ((((1817 : ℚ) / 51200) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP2C1Lo : ℝ) (d2C16R1pP2C1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP2C1Lo, d2C16R1pP2C1Hi, d2C16R1pP2C1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP2C1Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP2C1Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell6 (x : ℝ) (hx : x ∈ Icc ((((1817 : ℚ) / 51200) : ℚ) : ℝ) ((((4223 : ℚ) / 102400) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP2C2Lo : ℝ) (d2C16R1pP2C2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP2C2Lo, d2C16R1pP2C2Hi, d2C16R1pP2C2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP2C2Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP2C2Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell7 (x : ℝ) (hx : x ∈ Icc ((((4223 : ℚ) / 102400) : ℚ) : ℝ) ((((1203 : ℚ) / 25600) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP2C3Lo : ℝ) (d2C16R1pP2C3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP2C3Lo, d2C16R1pP2C3Hi, d2C16R1pP2C3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP2C3Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP2C3Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell8 (x : ℝ) (hx : x ∈ Icc ((((1203 : ℚ) / 25600) : ℚ) : ℝ) ((((5401 : ℚ) / 102400) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP3C0Lo : ℝ) (d2C16R1pP3C0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP3C0Lo, d2C16R1pP3C0Hi, d2C16R1pP3C0Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP3C0Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP3C0Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell9 (x : ℝ) (hx : x ∈ Icc ((((5401 : ℚ) / 102400) : ℚ) : ℝ) ((((599 : ℚ) / 10240) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP3C1Lo : ℝ) (d2C16R1pP3C1Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP3C1Lo, d2C16R1pP3C1Hi, d2C16R1pP3C1Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP3C1Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP3C1Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell10 (x : ℝ) (hx : x ∈ Icc ((((599 : ℚ) / 10240) : ℚ) : ℝ) ((((6579 : ℚ) / 102400) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP3C2Lo : ℝ) (d2C16R1pP3C2Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP3C2Lo, d2C16R1pP3C2Hi, d2C16R1pP3C2Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP3C2Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP3C2Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem cell11 (x : ℝ) (hx : x ∈ Icc ((((6579 : ℚ) / 102400) : ℚ) : ℝ) ((((7 : ℚ) / 100) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxC : x ∈ Icc (d2C16R1pP3C3Lo : ℝ) (d2C16R1pP3C3Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP3C3Lo, d2C16R1pP3C3Hi, d2C16R1pP3C3Literal.q2] at hx ⊢ <;> exact hx
  have h := d2C16R1pP3C3Bound x hxC
  have hBound := h.trans (by norm_num [d2C16R1pP3C3Literal.q2] : _ ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
theorem d2C16R1pP4C0RawIdentity : fieldNFCheck d2C16R1pP4C0FullFq D72.StandaloneFieldData.f2 = true := by decide +kernel
theorem cell12 (x : ℝ) (hx : x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((1 : ℚ) / 1024) : ℚ) : ℝ)) (hP : valid x) : fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  have hxE : x ∈ Icc (d2C16R1pP4C0Lo : ℝ) (d2C16R1pP4C0Hi : ℝ) := by
    norm_num [Set.mem_Icc, d2C16R1pP4C0Lo, d2C16R1pP4C0Hi, d2C16R1pP4C0EndLiteral.q2] at hx ⊢ <;> exact hx
  have hne : x ≠ (d2C16R1pP4C0Site : ℝ) := by
    simpa [d2C16R1pP4C0Site, d2C16R1pP4C0EndLiteral.q2] using hP.1
  have h := d2C16R1pP4C0Bound x hxE hne
  rw [fieldNFCheck_sound d2C16R1pP4C0RawIdentity x] at h
  have hBound := h.trans (by norm_num [d2C16R1pP4C0Target, d2C16R1pP4C0EndLiteral.q2] : (d2C16R1pP4C0Target : ℝ) ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ))
  simpa only [d2C16R1pP4C0FullTs, lfieldTower, List.map_nil, List.sum_nil, add_zero, fieldTower, poleTower_zero, fval, poleF, poleFn] using hBound
def boundPieces : List (ℚ × ℚ) := [(((0 : ℚ) / 1), ((1 : ℚ) / 1024)), (((1 : ℚ) / 1024), ((689 : ℚ) / 102400)), (((689 : ℚ) / 102400), ((639 : ℚ) / 51200)), (((639 : ℚ) / 51200), ((1867 : ℚ) / 102400)), (((1867 : ℚ) / 102400), ((307 : ℚ) / 12800)), (((307 : ℚ) / 12800), ((609 : ℚ) / 20480)), (((609 : ℚ) / 20480), ((1817 : ℚ) / 51200)), (((1817 : ℚ) / 51200), ((4223 : ℚ) / 102400)), (((4223 : ℚ) / 102400), ((1203 : ℚ) / 25600)), (((1203 : ℚ) / 25600), ((5401 : ℚ) / 102400)), (((5401 : ℚ) / 102400), ((599 : ℚ) / 10240)), (((599 : ℚ) / 10240), ((6579 : ℚ) / 102400)), (((6579 : ℚ) / 102400), ((7 : ℚ) / 100))]
theorem boundCover : pieceCover ((7 : ℚ) / 100) ((0 : ℚ) / 1) boundPieces = true := by decide +kernel
theorem bound : ∀ x ∈ Icc ((((0 : ℚ) / 1) : ℚ) : ℝ) ((((7 : ℚ) / 100) : ℚ) : ℝ), valid x → fval D72.StandaloneFieldData.f2 x ≤ ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) := by
  apply D72.StandaloneCoverTools.coverOn (fval D72.StandaloneFieldData.f2) valid ((((-263584014898169694665479 : ℚ) / 14073748835532800000000) : ℚ) : ℝ) ((0 : ℚ) / 1) ((7 : ℚ) / 100) boundPieces (by decide +kernel) boundCover
  intro p hp
  simp only [boundPieces, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x hx hP
    exact (cell12 x hx hP).trans (by norm_num)
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
#print axioms boundCover
#print axioms bound
end D72.StandaloneC16R1p

end CatalanMeasure.GenD.Signed.Data.Cells

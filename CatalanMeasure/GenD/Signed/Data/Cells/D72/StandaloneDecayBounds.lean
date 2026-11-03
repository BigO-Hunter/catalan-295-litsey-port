module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AnchoredLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverFirstRow
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverFirstColumn
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverReferenceRow
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverReferenceResidual
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneCoverJointSC
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneConstantsGate
public import CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
public import CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceNear
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
open CatalanMeasure.GenD.Signed.Data.Trial
open CatalanMeasure.GenD.Signed.Data.Trial72
open CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
open CatalanMeasure.GenD.Signed.Data.Trial72.SheetBindings
open CatalanMeasure.GenD.Signed.Davis.ScalarInstance72
open CatalanMeasure.GenD.Analytic CatalanMeasure.GenD
namespace D72.StandaloneDecayBounds
open D72.StandaloneAdapter
open D72.StandaloneFieldData
open D72.StandaloneFieldsGate
open D72.StandaloneConstantsGate

private theorem rowMem {x : ℝ} (hx : x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1) :
    |x| ≤ 1 ∧ x ≠ 0 ∧ x ≠ 1 := by
  rcases hx with h | h
  · exact ⟨abs_le.mpr ⟨h.1, by linarith [h.2]⟩, ne_of_lt h.2, by linarith [h.2]⟩
  · exact ⟨abs_le.mpr ⟨by linarith [h.1], h.2.le⟩, ne_of_gt h.1, ne_of_lt h.2⟩

theorem first : FirstDecayBounds where
  row := by
    intro x hx
    have ⟨ha,h0,h1⟩ := rowMem hx
    have hb := (show fval f0 x ≤ _ from by
      rcases hx with h | h
      · exact D72.StandaloneCoverFirstRow.domain0 x
          (by simpa [Set.mem_Icc] using (show -1 ≤ x ∧ x ≤ 0 from ⟨h.1,h.2.le⟩)) ⟨h0,h1⟩
      · exact D72.StandaloneCoverFirstRow.domain1 x
          (by simpa [Set.mem_Icc] using (show 0 ≤ x ∧ x ≤ 1 from ⟨h.1.le,h.2.le⟩)) ⟨h0,h1⟩)
    have he := firstRowValue x
    change fval f0 x = _ at he
    rw [he] at hb
    apply firstRow_lift firstPData firstVData (tailOK_of _ firstP_tail) (tailOK_of _ firstV_tail)
      firstMX _ firstRowUpper ha
    exact hb.trans (by norm_num [firstMX, d2LitsConstantsGate.q2])
  column := by
    intro x hx
    have ha : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1],hx.2.le⟩
    change colFieldG (11/72) (1/18) (sequence firstVData) x ≤ firstMY
    rw [columnIdentity firstVData (tailOK_of _ firstV_tail) ha]
    have hb := D72.StandaloneCoverFirstColumn.domain0 x
      (by simpa [Set.mem_Icc] using (show 0 ≤ x ∧ x ≤ 1 from ⟨hx.1.le,hx.2.le⟩))
      ⟨ne_of_gt hx.1,ne_of_lt hx.2⟩
    have he := firstColumnValue x
    change fval f1 x = _ at he
    rw [he] at hb
    exact (add_le_add hb firstColUpper).trans (by norm_num [firstMY, d2LitsConstantsGate.q2])

theorem reference : SecondDecayBounds (-96992793/100000000) (-158005012/100000000)
    (-6909202/100000000) (-77/100) where
  row := by
    intro x hx
    have ⟨ha,h0,h1⟩ := rowMem hx
    change rowFieldG (3/8) (1/9) (97/72) (sequence secondPData) (sequence secondVData) x ≤ _
    rw [referenceRowIdentity secondPData secondVData (tailOK_of _ secondP_tail) (tailOK_of _ secondV_tail) ha]
    have hb := (show fval f2 x ≤ _ from by
      rcases hx with h | h
      · exact D72.StandaloneCoverReferenceRow.domain0 x
          (by simpa [Set.mem_Icc] using (show -1 ≤ x ∧ x ≤ 0 from ⟨h.1,h.2.le⟩)) ⟨h0,h1⟩
      · exact D72.StandaloneCoverReferenceRow.domain1 x
          (by simpa [Set.mem_Icc] using (show 0 ≤ x ∧ x ≤ 1 from ⟨h.1.le,h.2.le⟩)) ⟨h0,h1⟩)
    have he := referenceRowValue x
    change fval f2 x = _ at he
    rw [he] at hb
    exact (add_le_add hb refRowUpper).trans (by norm_num [d2LitsConstantsGate.q2])
  column := by
    intro x hx
    have ha : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1],hx.2.le⟩
    change colFieldG (11/72) (1/18) (sequence secondVData) x ≤ _
    rw [columnIdentity secondVData (tailOK_of _ secondV_tail) ha]
    have hb := D72.StandaloneCoverJointSC.referenceColumn x
      (by simpa [Set.mem_Icc] using (show 0 ≤ x ∧ x ≤ 1 from ⟨hx.1.le,hx.2.le⟩))
      ⟨ne_of_gt hx.1,ne_of_lt hx.2⟩
    have he := referenceColumnValue x
    change fval referenceColumnLiteral x = _ at he
    rw [he] at hb
    exact (add_le_add hb refColUpper).trans (by norm_num [d2LitsConstantsGate.q2])
  residual := by
    intro x hx hg
    change x ≤ -(19501/100000 : ℝ) ∨ (98749/1000000 : ℝ) ≤ x at hg
    have ha : |x| ≤ 1 := abs_le.mpr hx
    change resFieldGen (gRes dc72.toParameters) (sequence secondPData) x ≤ _
    have hRes : gRes dc72.toParameters = (11/12 : ℝ) := by norm_num [gRes, dc72]
    rw [hRes, residualIdentity secondPData (tailOK_of _ secondP_tail) ha]
    have hb := (show fval f3 x ≤ _ from by
      rcases hg with h | h
      · exact D72.StandaloneCoverReferenceResidual.domain0 x
          ⟨by simpa using hx.1, by norm_num at h ⊢; linarith⟩ trivial
      · exact D72.StandaloneCoverReferenceResidual.domain1 x
          ⟨by norm_num at h ⊢; linarith, by simpa using hx.2⟩ trivial)
    have he := referenceResidualValue x
    change fval f3 x = _ at he
    rw [he] at hb
    exact (add_le_add hb residualUpper).trans (by norm_num [d2LitsConstantsGate.q2])
  near := by
    intro y hy
    exact (ReferenceNear.secondDecay_near y hy).trans (by norm_num)

#print axioms first
#print axioms reference
end D72.StandaloneDecayBounds

end CatalanMeasure.GenD.Signed.Data.Cells

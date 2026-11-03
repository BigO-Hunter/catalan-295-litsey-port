module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1n
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R1p
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16R2
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneConstantsGate
public import CatalanMeasure.GenD.Signed.Data.Consts.LinkSupLim
public import CatalanMeasure.GenD.Signed.DesignConst

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16
open Set Filter OAI.InternalCatalan CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
open CatalanMeasure.Signed.Consts CatalanMeasure.GenD.Signed.DesignConst
open CatalanMeasure.GenD.Signed.Data.Trial CatalanMeasure.GenD.Signed.Data.Trial72.ReferenceData
open CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneAdapter
open CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneFieldsGate
open CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneConstantsGate

private theorem rowOfBound {x T : ℝ} (hx : |x| ≤ 1)
    (h : fval D72.StandaloneFieldData.f2 x ≤ T) :
    rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤
      T + (((638384986865860071 : ℚ) / 36028797018963968) : ℝ) := by
  change rowFieldG (3/8) (1/9) (97/72) (sequence secondPData) (sequence secondVData) x ≤ _
  rw [referenceRowIdentity secondPData secondVData (tailOK_of _ secondP_tail) (tailOK_of _ secondV_tail) hx]
  have he := referenceRowValue x
  change fval D72.StandaloneFieldData.f2 x = _ at he
  rw [he] at h
  exact add_le_add h (refRowUpper.trans (by norm_num [d2LitsConstantsGate.q2]))

private theorem gapSubset : {x : ℝ | 0 < |x| ∧ |x| < 7/100} ⊆
    Ico (-1 : ℝ) 0 ∪ Ioo 0 1 := by
  rintro x ⟨h0,h1⟩
  rcases lt_or_gt_of_ne (abs_pos.mp h0) with h | h
  · left
    rw [abs_of_neg h] at h1
    exact ⟨by linarith, h⟩
  · right
    rw [abs_of_pos h] at h1
    exact ⟨h, by linarith⟩

theorem gapLimit (x : ℝ) (h0 : 0 < |x|) (h1 : |x| < 7/100) :
    rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤
      (-96992793/100000000 : ℝ) - (1/25 + 1/10000) := by
  have hx : |x| ≤ 1 := by linarith
  have hvalid : x ≠ 0 ∧ x ≠ 1 := ⟨abs_pos.mp h0, by
    intro he
    subst x
    norm_num at h1⟩
  rcases lt_or_gt_of_ne hvalid.1 with h | h
  · rw [abs_of_neg h] at h1
    have hb := D72.StandaloneC16R1n.bound x (by
      constructor <;> push_cast <;> linarith) hvalid
    exact (rowOfBound hx hb).trans (by norm_num)
  · rw [abs_of_pos h] at h1
    have hb := D72.StandaloneC16R1p.bound x (by
      constructor <;> push_cast <;> linarith) hvalid
    exact (rowOfBound hx hb).trans (by norm_num)

theorem supLimit (x : ℝ) (hx : x ∈ Ioo (1-1/1000 : ℝ) 1) :
    rowFieldG (3/8) (1/9) (97/72) secondP secondV x ≤
      (-96992793/100000000 : ℝ) - (17/100 + 1/10000) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have ha : |x| ≤ 1 := by rw [abs_of_pos hx0]; exact hx.2.le
  have hb := D72.StandaloneC16R2.bound x (by
    constructor <;> push_cast <;> linarith [hx.1, hx.2]) ⟨ne_of_gt hx0, ne_of_lt hx.2⟩
  exact (rowOfBound ha hb).trans (by norm_num)

theorem hgap : ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, 0 < |x| → |x| < 7/100 →
    freeRowX dc72.toParameters N secondP secondV x ≤
      (-96992793/100000000 : ℝ) + (13/100000)/4 - 1/25 := by
  have h := link_cap_of_region dc72.admissible secondP_summable secondV_summable
    (α := 3/8) (β := 1/9) (γ := 97/72)
    (by norm_num [dc72]) (by norm_num [dc72]) (by norm_num [dc72])
    gapSubset (fun x hx => gapLimit x hx.1 hx.2) (d := 1/25) (δ := 13/100000)
    (by norm_num) (by norm_num)
  filter_upwards [h] with N hN x h0 h1 using hN x ⟨h0,h1⟩

theorem hsup : ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (1-1/1000 : ℝ) 1,
    freeRowX dc72.toParameters N secondP secondV x ≤
      (-96992793/100000000 : ℝ) + (13/100000)/4 - 17/100 := by
  exact link_cap_of_region dc72.admissible secondP_summable secondV_summable
    (α := 3/8) (β := 1/9) (γ := 97/72)
    (by norm_num [dc72]) (by norm_num [dc72]) (by norm_num [dc72])
    (fun x hx => Or.inr ⟨by linarith [hx.1], hx.2⟩) supLimit (by norm_num) (by norm_num)

#print axioms hgap
#print axioms hsup
end CatalanMeasure.GenD.Signed.Data.Cells.D72.StandaloneC16


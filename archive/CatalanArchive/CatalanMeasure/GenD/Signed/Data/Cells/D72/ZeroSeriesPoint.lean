module
public import CatalanMeasure.GenD.Signed.Data.Cells.Core

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Data.Cells.D72
open Set CatalanMeasure.GenD.Signed.TaylorCell

/-- Apply the checked zero series to a pointwise real upper bound, including a
logarithmic endpoint bound. Rational density reuses the existing certificate. -/
theorem zeroSeries_point (fq fq' : FieldQ) (ts : List LTerm) (hi : ℚ) (n : ℕ) (δ : ℚ)
    (h : l0OK ts hi n = true) (hc : l0C ts = 0)
    (hpl : fq'.plogs = fq.plogs) (hpo : fq'.poles = fq.poles)
    (hD : polyAB (vecAdd (vecAdd fq.poly (l0P ts n)) (fq'.poly.map (fun t => (-1 : ℚ) * t))) 0 hi ≤ δ)
    {x : ℝ} (hx : x ∈ Ioc 0 (hi : ℝ)) :
    fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x ≤
      fieldTower fq' (poleF fq'.poles) 0 x + ((δ + l0Err hi n ts : ℚ) : ℝ) := by
  by_contra! hn
  have hgap : fieldTower fq' (poleF fq'.poles) 0 x <
      fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x -
        ((δ + l0Err hi n ts : ℚ) : ℝ) := by linarith
  obtain ⟨T, hT, hT'⟩ := exists_rat_btwn hgap
  have hs : ∀ y ∈ ({x} : Set ℝ), 0 < y ∧ y ≤ (hi : ℝ) := by
    intro y hy
    have hxy := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨hx.1, hx.2⟩
  have hcell : ∀ y ∈ ({x} : Set ℝ), fieldTower fq' (poleF fq'.poles) 0 y ≤ (T : ℝ) := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using hT.le
  have hbound := l0_series_sound fq fq' ts hi n δ T h hc hpl hpo hD {x} hs hcell x (by simp)
  push_cast at hT' hbound
  linarith

#print axioms zeroSeries_point
end CatalanMeasure.GenD.Signed.Data.Cells.D72

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace D72.StandaloneCoverTools
theorem coverOn (f : ℝ → ℝ) (P : ℝ → Prop) (T : ℝ) (lo hi : ℚ)
    (ps : List (ℚ × ℚ)) (hn : ps ≠ []) (hc : pieceCover hi lo ps = true)
    (hp : ∀ p ∈ ps, ∀ x ∈ Icc (p.1 : ℝ) (p.2 : ℝ), P x → f x ≤ T) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ), P x → f x ≤ T := by
  classical
  have h := pieceCover_bound hi (fun x => if P x then f x else T) T lo ps hn hc
    (by
      intro p hmem x hx
      by_cases hP : P x
      · simpa [hP] using hp p hmem x hx hP
      · simp [hP])
  intro x hx hP
  simpa [hP] using h x hx
#print axioms coverOn
end D72.StandaloneCoverTools

end CatalanMeasure.GenD.Signed.Data.Cells

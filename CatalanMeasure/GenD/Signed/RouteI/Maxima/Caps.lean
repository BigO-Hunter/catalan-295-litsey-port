module
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCap
public import CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCap
@[expose] public section
set_option Elab.async false

/-!
# Route-I maxima caps: `row_sup_S'` and `column_sup_S'`

The K590 second-population caps of `PositiveCert.XCover.row_sup_S` / `YCover.column_sup_S`, with the
same statements over the same `PositiveCert.Data` names, proved by the derivative-root cover:
exact rational derivative identity, Descartes root count saturated by 81-bit sign brackets, one
global Lipschitz bound per bracket and the endpoint wrapper (no Taylor-block cover).
-/
namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert OAI.InternalCatalan Set

theorem row_sup_S' : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ (MX : ℝ) :=
  CatalanMeasure.GenD.Signed.RouteI.Maxima.RowCap.xmAvoidX

theorem column_sup_S' : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ (MY : ℝ) :=
  CatalanMeasure.GenD.Signed.RouteI.Maxima.ColCap.xmAvoidY

#print axioms row_sup_S'
#print axioms column_sup_S'
end CatalanMeasure.GenD.D58.Cert590

module

public import CatalanMeasure.GenD.Signed.Count.Ledger
public import CatalanMeasure.GenD.Uniform.ContentBank.Table

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! The content bound of the ledger: `baseRows` is `W13`, certified against `fams13`. -/

namespace CatalanMeasure.GenD.Signed.Count.LedgerContent
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank535.Ledger10 CatalanMeasure.GenD.Uniform.Bank532
  CatalanMeasure.GenD.Signed.Count.ContentAssembly CatalanMeasure.GenD.Signed.Count.Ledger D58
noncomputable section

theorem W13_rows : W13 = baseRows.map Row.win := by
  simp only [W13, baseRows, List.map_cons, List.map_nil, Row.win]
  norm_num

/-- **`hcontent` of `RouteI.catalan_irrationalityMeasure_295`** for `lb := famLB (lbC :: fams13)`,
with `gain ≥ 220607/10000`. -/
theorem content : ∃ (lbC : NullityLB design) (gain : ℝ), (220607 / 10000 : ℝ) ≤ gain ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer Signed.dc58.toParameters Signed.dc58.admissible
        (famLB (lbC :: fams13)) 79 Signed.RouteI.dc58_normalizer_cut).D N : ℝ) ≤
        (gDg gain + ε) * (N : ℝ) ^ 2 :=
  CatalanMeasure.GenD.Signed.Count.Ledger.content fams13 fun o ho => W13_cert _ (W13_rows ▸ List.mem_map_of_mem ho)

end
end CatalanMeasure.GenD.Signed.Count.LedgerContent
#print axioms CatalanMeasure.GenD.Signed.Count.LedgerContent.content

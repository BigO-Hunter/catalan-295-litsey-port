module

public import Submission.CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

@[expose] public section

/-! # The full-prefix checker branches of a Level3 bank

`prefixBranches N = [brPrefix 1, ..., brPrefix N]`: the full closed price of the original prefix strips
`n p ≤ m < (n+1) p`, each valid by `WrapPrefixCheck.catValid_prefix_full`.  Pure bookkeeping for the bank
catalogues (data modules append `prefixBranches N` after `brWrap`); no new mathematics. -/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.UFMoments CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.BankShared.Check

namespace CatalanCore.Uniform.Content.UFSimple

open CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck in
/-- The checker branches `brPrefix 1, ..., brPrefix N`. -/
def prefixBranches (N : ℕ) : List Branch := (List.range N).map (fun i => brPrefix (i + 1))

/-- Every branch of `prefixBranches N` is valid, from `catValid_prefix_full`. -/
theorem catValid_prefixBranches (c : ℚ) (hc : 0 < c) {Fr : Frame} {q o : ℕ}
    (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm = (nm : ℚ))
    (depth Pbad N0 N : ℕ)
    (hP : ∀ p : ℕ, p.Prime → Pbad < p → ¬ p ∣ nm ∧ q < p) :
    CatValid c hc Fr depth q o Pbad N0 (prefixBranches N) := by
  intro b hb
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
  exact CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck.catValid_prefix_full c hc T hnorm depth Pbad N0
    (i + 1) (by omega) hP _ (List.mem_singleton_self _)

end CatalanCore.Uniform.Content.UFSimple

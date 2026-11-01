module

public import CatalanCore.Uniform.Content.UFMember.Layer

@[expose] public section

/-! # Transfer of mixed-chain Smith witnesses

Wrapped and prefix elimination order the row and column chains separately.
A witness in those actual mixed coordinates prices the original deletion
members. The row and column equivalences need not agree.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Uniform CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFSimple.WrapSource

open CatalanCore.Uniform.Content.UFMember

variable {p : ℕ} [Fact p.Prime]

/-- Transfer a mixed-coordinate witness directly to any original-coordinate minor. -/
theorem gle_minor_reindex {ι τ κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]
    [Fintype κ] [DecidableEq κ]
    (M : Matrix ι ι ℚ[X]) (er ec : τ ≃ ι) {b : ℕ}
    (W : ThreeLevelWit p (M.submatrix er ec) b) (eR eC : κ → ι)
    (hk : Fintype.card κ ≤ Fintype.card ι) :
    GLE p (W.price + (Fintype.card ι - Fintype.card κ))
      (M.submatrix eR eC).det := by
  have hc : Fintype.card τ = Fintype.card ι := Fintype.card_congr er
  have h := W.gle_submatrix_debit (fun i => er.symm (eR i))
    (fun i => ec.symm (eC i)) (by omega)
  simpa only [hc, Matrix.submatrix_submatrix, Function.comp_def,
    Equiv.apply_symm_apply] using h


end CatalanCore.Uniform.Content.UFSimple.WrapSource

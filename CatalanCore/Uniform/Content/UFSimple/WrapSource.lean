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

/-- Original-gauge deletion price from a scaled witness with independent
row and column chain orderings. -/
theorem member_gle_scaled_reindex {ι κ τ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype τ] [DecidableEq τ]
    (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    (er ec : τ ≃ (ι ⊕ κ)) {b : ℕ}
    (W : ThreeLevelWit p
      (((FullN Fr common xs ys (X : ℚ[X])).map (scaleU p)).submatrix er ec) b) :
    GLE p (W.price + (Fintype.card ι - S.card))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_member_eq_submatrix]
  apply gle_submatrix_of_scaleU
  have hS : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
  have h := gle_minor_reindex _ er ec W (memberEmbedding S) (memberEmbedding S)
    (by simp only [Fintype.card_sum, Fintype.card_coe]; omega)
  refine h.mono ?_
  simp only [Fintype.card_sum, Fintype.card_coe]
  omega

/-- Actual mixed-coordinate data; no symmetry of the augmented core is required. -/
structure MixedDatum (G : BlockGeom) (Fr : Frame) (r p : ℕ) [Fact p.Prime] where
  n : ℕ
  b : ℕ
  row : Fin n ≃ ((G.geometry r).C ⊕ Fin (G.geometry r).k)
  col : Fin n ≃ ((G.geometry r).C ⊕ Fin (G.geometry r).k)
  W : ThreeLevelWit p (((fullMat G Fr r).map (scaleU p)).submatrix row col) b

/-- Assemble mixed-coordinate data through the existing debit-layer interface. -/
noncomputable def mixedLayer {G : BlockGeom} {Fr : Frame} {depth : ℕ}
    (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (D : ∀ r p : ℕ, [Fact p.Prime] → valid r p → MixedDatum G Fr r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p,
      (D r p h).W.price ≤ base r p) : DebitLayer G Fr depth where
  base := base
  debit := 1
  valid := valid
  gle := by
    intro i _ p hp hv
    have h := member_gle_scaled_reindex Fr (fun a : (G.geometry i.1).C => (a : ℕ))
      (G.geometry i.1).xs (G.geometry i.1).ys i.2
      (D i.1 p hv).row (D i.1 p hv).col (D i.1 p hv).W
    have hc : Fintype.card (G.geometry i.1).C = (G.geometry i.1).C.card :=
      Fintype.card_coe _
    rw [hc] at h
    refine h.mono ?_
    rw [one_mul]
    have := hbase i.1 p hv
    unfold delCount
    omega

end CatalanCore.Uniform.Content.UFSimple.WrapSource

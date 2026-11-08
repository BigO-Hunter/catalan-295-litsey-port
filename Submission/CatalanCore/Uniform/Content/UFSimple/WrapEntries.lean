module

public import Submission.CatalanCore.Uniform.Content.UFMoments.SLiftInst
public import Submission.CatalanCore.Uniform.Content.UFMember.FiberMom

@[expose] public section

/-! # Actual scaled entries for independently reordered wrapped chains

The full lift satisfies the Loewner commutator at every pair of indices.
Its cross-residue reduction vanishes before and after independent reorderings.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Rect
  CatalanCore.Uniform.Content.UFMember CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFSimple.WrapEntries

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Exact full-entry commutator, including all common spectral diagonals. -/
theorem sLift_commutator (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a<N)
    (hx : ∀ i, xs i<N) (hy : ∀ i, ys i<N) (i j : ι ⊕ κ) :
    nL p Fr * (nd p (colNode c ys j) - nd p (rowNode c xs i)) *
      sLift c xs ys (hint_of_poleData D hN hc hx hy) i j =
        PF p Fr (colNode c ys j) - PF p Fr (rowNode c xs i) := by
  rcases i with a | a <;> rcases j with b | b
  · by_cases hab : a=b
    · subst b
      simp [rowNode, colNode]
    · have hh := const_commutator D (hc a) (hc b)
        (hint_of_poleData D hN hc hx hy (Sum.inl a) (Sum.inl b))
      simpa [sLift, sConst, rowNode, colNode, Matrix.one_apply, hab] using hh
  · have hh := const_commutator D (hc a) (hy b)
      (hint_of_poleData D hN hc hx hy (Sum.inl a) (Sum.inr b))
    simpa [sLift, sConst, rowNode, colNode] using hh
  · have hh := const_commutator D (hx a) (hc b)
      (hint_of_poleData D hN hc hx hy (Sum.inr a) (Sum.inl b))
    simpa [sLift, sConst, rowNode, colNode] using hh
  · have hh := const_commutator D (hx a) (hy b)
      (hint_of_poleData D hN hc hx hy (Sum.inr a) (Sum.inr b))
    simpa [sLift, sConst, rowNode, colNode] using hh

/-- Full scaled entries across distinct residues vanish after reduction. -/
theorem sLift_cross_zero (D : PoleData Fr p N) (hN : N<p*p)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a<N)
    (hx : ∀ i, xs i<N) (hy : ∀ i, ys i<N) (i j : ι ⊕ κ)
    (hij : ((rowNode c xs i : ℕ) : ZMod p) ≠ ((colNode c ys j : ℕ) : ZMod p)) :
    phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy) i j) = 0 := by
  have hz := phiP_sConst_eq_zero D hN hc hx hy i j hij
  rcases i with a | a <;> rcases j with b | b
  · have hab : a≠b := by
      intro he
      apply hij
      simp [rowNode, colNode, he]
    simpa [sLift, Matrix.one_apply, hab] using hz
  · simpa [sLift] using hz
  · simpa [sLift] using hz
  · simpa [sLift] using hz

end CatalanCore.Uniform.Content.UFSimple.WrapEntries

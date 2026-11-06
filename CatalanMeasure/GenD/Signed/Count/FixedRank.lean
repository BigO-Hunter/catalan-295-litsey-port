module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option Elab.async false

/-!
# Count layer: rank caps from small fixed integer matrices, and the gauge cap

Two groups of statements, both independent of any literal matrix.

**Int-native finite matrices (decoder, cast, product).**  A sparse integer matrix is a flat list
`k₀ v₀ k₁ v₁ …` per row (`unpack`), read into `Fin n × ℤ` pairs with the column index reduced
modulo `n` (the range check is a separate boolean over the unreduced literals,
`validPairs`).  `leftInverse_of_rows` turns row-wise product identities (one tiny `decide +kernel`
each) into `L * A = 1` over `ℤ`; `rank_eq_of_leftInverse` and `injective_of_leftInverse` transfer it
to EVERY field by any ring hom (so the cast is a generic lemma, and good for every prime);
`rank_le_of_factor` is the matching upper-rank certificate `M = X * Y`.

**Gauge cap.**  If the raw rows of a map vanish on `ker G`, then `rank (F, raw) ≤ rank (F, G)` and
`rank (F, raw) ≤ rank F + #raw`.
-/

namespace CatalanMeasure.GenD.Signed.Count.FixedRank
open Module Matrix

section IntDecoder

/-- Flat sparse row `k₀ v₀ k₁ v₁ …` → pairs, column index reduced mod `n`. -/
def unpack (n : ℕ) (hn : 0 < n) : List ℤ → List (Fin n × ℤ)
  | k :: v :: tail => (⟨k.toNat % n, Nat.mod_lt _ hn⟩, v) :: unpack n hn tail
  | _ => []

/-- Range check of the unreduced literal indices. -/
def validPairs (n : ℕ) : List ℤ → Bool
  | k :: _ :: tail => decide (0 ≤ k) && decide (k < (n : ℤ)) && validPairs n tail
  | [] => true
  | [_] => false

/-- The dense entry of a sparse row. -/
def rowVal {n : ℕ} (s : List (Fin n × ℤ)) (j : Fin n) : ℤ :=
  (s.map fun rc => if rc.1 = j then rc.2 else 0).sum

/-- Generic soundness of sparse left multiplication. -/
theorem sum_exchange {n : ℕ} (s : List (Fin n × ℤ)) (v : Fin n → ℤ) :
    (∑ r, rowVal s r * v r) = (s.map fun rc => rc.2 * v rc.1).sum := by
  induction s with
  | nil => simp [rowVal]
  | cons rc tail ih =>
    simp only [rowVal, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    simp [ite_mul]

/-- Row-wise product identities give the matrix identity `L * A = 1`. -/
theorem leftInverse_of_rows {a m : ℕ} (lrow : Fin a → List (Fin m × ℤ)) (A : Matrix (Fin m) (Fin a) ℤ)
    (h : ∀ i col : Fin a, ((lrow i).map fun rc => rc.2 * A rc.1 col).sum = if i = col then 1 else 0) :
    (Matrix.of fun i r => rowVal (lrow i) r) * A = (1 : Matrix (Fin a) (Fin a) ℤ) := by
  ext i col
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [sum_exchange]
  rw [h i col]
  simp [Matrix.one_apply]

variable {K : Type*} [Field K]

/-- An integer left inverse gives full column rank over EVERY field. -/
theorem rank_eq_of_leftInverse {a m : ℕ} (L : Matrix (Fin a) (Fin m) ℤ) (A : Matrix (Fin m) (Fin a) ℤ)
    (h : L * A = 1) (f : ℤ →+* K) : (A.map f).rank = a := by
  have hc : L.map f * A.map f = (1 : Matrix (Fin a) (Fin a) K) := by
    have := congrArg (fun M : Matrix (Fin a) (Fin a) ℤ => M.map f) h
    rw [Matrix.map_mul] at this
    simpa using this
  apply le_antisymm (Matrix.rank_le_width _)
  have h2 := Matrix.rank_mul_le_right (L.map f) (A.map f)
  simpa only [hc, Matrix.rank_one, Fintype.card_fin] using h2

/-- The same left inverse makes the cast matrix injective on vectors (every prime). -/
theorem injective_of_leftInverse {a m : ℕ} (L : Matrix (Fin a) (Fin m) ℤ) (A : Matrix (Fin m) (Fin a) ℤ)
    (h : L * A = 1) (f : ℤ →+* K) : Function.Injective (A.map f).mulVec := by
  intro x y hxy
  have hc : L.map f * A.map f = (1 : Matrix (Fin a) (Fin a) K) := by
    have := congrArg (fun M : Matrix (Fin a) (Fin a) ℤ => M.map f) h
    rw [Matrix.map_mul] at this
    simpa using this
  have := congrArg (L.map f).mulVec hxy
  simpa [Matrix.mulVec_mulVec, hc] using this

/-- Upper rank certificate: a factorization through `r` columns, valid in every field. -/
theorem rank_le_of_factor {n m r : ℕ} (X : Matrix (Fin n) (Fin r) ℤ) (Y : Matrix (Fin r) (Fin m) ℤ)
    (f : ℤ →+* K) : ((X * Y).map f).rank ≤ r := by
  rw [Matrix.map_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_width (X.map f))

end IntDecoder

section Gauge
variable {K V W₁ W₂ : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]

/-- A smaller kernel means a larger rank. -/
theorem finrank_range_le_of_ker_le {W₃ : Type*} [AddCommGroup W₃] [Module K W₃]
    (f : V →ₗ[K] W₁) (g : V →ₗ[K] W₃) (h : LinearMap.ker f ≤ LinearMap.ker g) :
    finrank K (LinearMap.range g) ≤ finrank K (LinearMap.range f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := V) (V₂ := W₁) f
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := V) (V₂ := W₃) g
  have h3 := Submodule.finrank_mono h
  omega

/-- **Gauge cap (P3).**  If every raw row vanishes on `ker G`, the stacked map `(F, raw)` has rank at
most that of `(F, G)`. -/
theorem rank_stack_le_gauge {t : ℕ} (F : V →ₗ[K] W₁) (G : V →ₗ[K] W₂)
    (raw : V →ₗ[K] (Fin t → K)) (hraw : LinearMap.ker G ≤ LinearMap.ker raw) :
    finrank K (LinearMap.range (F.prod raw)) ≤ finrank K (LinearMap.range (F.prod G)) := by
  apply finrank_range_le_of_ker_le
  rw [LinearMap.ker_prod, LinearMap.ker_prod]
  exact inf_le_inf_left _ hraw

/-- **Row-count cap (P2).**  `rank (F, raw) ≤ rank F + #raw`. -/
theorem rank_stack_le_count {t : ℕ} (F : V →ₗ[K] W₁) (raw : V →ₗ[K] (Fin t → K)) :
    finrank K (LinearMap.range (F.prod raw)) ≤ finrank K (LinearMap.range F) + t := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := V) (V₂ := W₁ × (Fin t → K))
    (F.prod raw)
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := V) (V₂ := W₁) F
  have h3 := LinearMap.finrank_range_add_finrank_ker (K := K) (V := V) (V₂ := Fin t → K) raw
  have h4 : finrank K (LinearMap.range raw) ≤ t := by
    have := Submodule.finrank_le (LinearMap.range raw)
    simpa using this
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker F) (LinearMap.ker raw)
  have h6 : finrank K (↥(LinearMap.ker F ⊔ LinearMap.ker raw)) ≤ finrank K V :=
    Submodule.finrank_le _
  rw [LinearMap.ker_prod] at h1
  omega

/-- Restriction to a subspace preserves the gauge hypothesis (precomposition with the inclusion). -/
theorem ker_le_comp_subtype {W₃ : Type*} [AddCommGroup W₃] [Module K W₃] (G : V →ₗ[K] W₂)
    (raw : V →ₗ[K] W₃) (hraw : LinearMap.ker G ≤ LinearMap.ker raw) (U : Submodule K V) :
    LinearMap.ker (G.comp U.subtype) ≤ LinearMap.ker (raw.comp U.subtype) := by
  intro x hx
  exact hraw hx

end Gauge

end CatalanMeasure.GenD.Signed.Count.FixedRank
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.leftInverse_of_rows
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.rank_eq_of_leftInverse
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.injective_of_leftInverse
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.rank_le_of_factor
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.rank_stack_le_gauge
#print axioms CatalanMeasure.GenD.Signed.Count.FixedRank.rank_stack_le_count

module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
set_option Elab.async false

/-!
# Count layer: the coefficient-pair gauge

The actual tiling coefficient pairs (physical-prefix theorem, section 4) are

    T+_k = (T_k, U_{k-1}),
    H+_k = ((1+Y)(U_k - U_{k-1}), U_k + U_{k-1}),
    H-_k = ((Y-1)(U_k + U_{k-1}), U_k - U_{k-1}).

The Chebyshev recurrence gives `H+_k = T+_k + T+_{k+1}` and `H-_k = T+_{k+1} - T+_k` for ALL integer `k`
(`pairA_eq`, `pairC_eq`).  Consequently any block combination of the slot coordinates is a combination
of the node vectors `T+_m` with explicit node coefficients (`gauge_sum`), so the combined pair, and
hence EVERY linear functional of it (all raw rows, their h-differences, the p-step and the F/E shift
difference are linear in the pair), depends on the coordinates only through the node vector `G`:
`ker G ≤ ker φ` (`ker_le_of_factor`).  No moment table, log, rank oracle or raw rational value occurs.
-/

namespace CatalanMeasure.GenD.Signed.Count.SlotGauge
open Polynomial Polynomial.Chebyshev Finset

section Chebyshev
variable (R : Type*) [CommRing R]

/-- The node pair `T+_k = (T_k, U_{k-1})`. -/
noncomputable def nodePair (k : ℤ) : R[X] × R[X] := (T R k, U R (k - 1))
/-- The `H+` pair. -/
noncomputable def pairA (k : ℤ) : R[X] × R[X] :=
  ((1 + X) * (U R k - U R (k - 1)), U R k + U R (k - 1))
/-- The `H-` pair. -/
noncomputable def pairC (k : ℤ) : R[X] × R[X] :=
  ((X - 1) * (U R k + U R (k - 1)), U R k - U R (k - 1))

theorem T_add_T (k : ℤ) : T R k + T R (k + 1) = (1 + X) * (U R k - U R (k - 1)) := by
  have h1 := T_eq_U_sub_X_mul_U R k
  have h2 := T_eq_U_sub_X_mul_U R (k + 1)
  have h3 := U_add_two R (k - 1)
  simp only [show k - 1 + 2 = k + 1 by ring, show k + 1 - 1 = k by ring, show k - 1 + 1 = k by ring] at h2 h3
  linear_combination h1 + h2 + h3

theorem T_sub_T (k : ℤ) : T R (k + 1) - T R k = (X - 1) * (U R k + U R (k - 1)) := by
  have h1 := T_eq_U_sub_X_mul_U R k
  have h2 := T_eq_U_sub_X_mul_U R (k + 1)
  have h3 := U_add_two R (k - 1)
  simp only [show k - 1 + 2 = k + 1 by ring, show k + 1 - 1 = k by ring, show k - 1 + 1 = k by ring] at h2 h3
  linear_combination h2 - h1 + h3

/-- **`H+_k = T+_k + T+_{k+1}`** (both components), for all integer `k`. -/
theorem pairA_eq (k : ℤ) : pairA R k = nodePair R k + nodePair R (k + 1) := by
  refine Prod.ext ?_ ?_
  · simp only [pairA, nodePair, Prod.fst_add]; exact (T_add_T R k).symm
  · simp only [pairA, nodePair, Prod.snd_add, show k + 1 - 1 = k by ring]; try ring

/-- **`H-_k = T+_{k+1} - T+_k`** (both components), for all integer `k`. -/
theorem pairC_eq (k : ℤ) : pairC R k = nodePair R (k + 1) - nodePair R k := by
  refine Prod.ext ?_ ?_
  · simp only [pairC, nodePair, Prod.fst_sub]; exact (T_sub_T R k).symm
  · simp only [pairC, nodePair, Prod.snd_sub, show k + 1 - 1 = k by ring]; try ring

end Chebyshev

section Formal
variable {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]

/-- Node coefficient of the node `m` in a block combination `Σ_k a_k(e_k+e_{k+1}) + c_k(e_{k+1}-e_k)`
with `b` blocks. -/
def nodeCoef (a c : ℕ → R) (b m : ℕ) : R :=
  (if m < b then a m - c m else 0) + (if 0 < m then a (m - 1) + c (m - 1) else 0)

/-- **Block sum = node sum** (formal telescoping, valid in any module). -/
theorem gauge_sum (a c : ℕ → R) (e : ℕ → X) (b : ℕ) :
    ∑ k ∈ range b, (a k • (e k + e (k + 1)) + c k • (e (k + 1) - e k)) =
      ∑ m ∈ range (b + 1), nodeCoef a c b m • e m := by
  induction b with
  | zero => simp [nodeCoef]
  | succ b ih =>
    rw [sum_range_succ, ih]
    have hlow : ∀ m ∈ range b, nodeCoef a c (b + 1) m = nodeCoef a c b m := by
      intro m hm
      have : m < b := mem_range.mp hm
      simp [nodeCoef, this, Nat.lt_succ_of_lt this]
    have e1 : ∑ m ∈ range (b + 1), nodeCoef a c b m • e m =
        ∑ m ∈ range b, nodeCoef a c b m • e m + nodeCoef a c b b • e b := sum_range_succ _ _
    have e2 : ∑ m ∈ range (b + 1 + 1), nodeCoef a c (b + 1) m • e m =
        ∑ m ∈ range b, nodeCoef a c (b + 1) m • e m + nodeCoef a c (b + 1) b • e b +
          nodeCoef a c (b + 1) (b + 1) • e (b + 1) := by rw [sum_range_succ, sum_range_succ]
    have e3 : ∑ m ∈ range b, nodeCoef a c (b + 1) m • e m =
        ∑ m ∈ range b, nodeCoef a c b m • e m := sum_congr rfl fun m hm => by rw [hlow m hm]
    have hb : nodeCoef a c (b + 1) b = nodeCoef a c b b + (a b - c b) := by
      simp [nodeCoef]; ring
    have hb1 : nodeCoef a c (b + 1) (b + 1) = a b + c b := by simp [nodeCoef]
    rw [e1, e2, e3, hb, hb1]
    simp only [add_smul, smul_add, smul_sub, sub_smul]
    abel

/-- Any functional that factors through the node vector kills the gauge kernel. -/
theorem ker_le_of_factor {V N Y : Type*} [AddCommGroup V] [Module R V] [AddCommGroup N] [Module R N]
    [AddCommGroup Y] [Module R Y] (G : V →ₗ[R] N) (Λ : N →ₗ[R] Y) :
    LinearMap.ker G ≤ LinearMap.ker (Λ ∘ₗ G) := by
  intro x hx
  simp [LinearMap.mem_ker.mp hx]

end Formal

end CatalanMeasure.GenD.Signed.Count.SlotGauge
#print axioms CatalanMeasure.GenD.Signed.Count.SlotGauge.pairA_eq
#print axioms CatalanMeasure.GenD.Signed.Count.SlotGauge.pairC_eq
#print axioms CatalanMeasure.GenD.Signed.Count.SlotGauge.gauge_sum

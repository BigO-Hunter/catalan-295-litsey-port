module

public import CatalanMeasure.GenD.Signed.MarkedExpansion
public import CatalanMeasure.GenD.Signed.RealPlace
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

/-!
# Selected-sheet comparison (PROOF-RI 12.23), finite algebra

For `Y = K + D_-` and `P = D_+` with `Y + P ⪰ 0` and `Y - cP ⪰ 0`, every principal block of
`Y - 5P` has determinant at most `r^card` times that of `Y`.  Selected rows of the Laurent matrix
give the same full-node diagonal and a principal minor, so the bound passes to the selected
determinant with the original row scalars.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Matrix CatalanMeasure.Signed CatalanMeasure.GenD.Signed
open scoped ComplexOrder

noncomputable section

section Compressed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Relative determinant comparison.** `Y + P ⪰ 0`, `Y - cP ⪰ 0`, with `6 ≤ r` and
`5 ≤ c (r + 1)`, give `‖det (Y - 5P)‖ ≤ r^card det Y`.  `Y` may be singular. -/
theorem norm_det_sub_five_le {Y P : Matrix ι ι ℂ} (hYh : Y.IsHermitian) {c r : ℝ} (hc : 0 < c)
    (hr : 6 ≤ r) (hcr : 5 ≤ c * (r + 1))
    (h1 : (Y + P).PosSemidef) (h2 : (Y - (c : ℂ) • P).PosSemidef) :
    ‖(Y - (5 : ℂ) • P).det‖ ≤ r ^ Fintype.card ι * Y.det.re := by
  have hc0 : (0 : ℂ) ≤ (c : ℂ) := Complex.zero_le_real.mpr hc.le
  have hc1 : (0 : ℂ) ≤ ((1 + c)⁻¹ : ℝ) := Complex.zero_le_real.mpr (by positivity)
  have hcC : ((1 + c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + c : ℝ) ≠ 0)
  have hY : Y.PosSemidef := by
    have h := (h2.add (h1.smul hc0)).smul hc1
    have e : (((1 + c)⁻¹ : ℝ) : ℂ) • (Y - (c : ℂ) • P + (c : ℂ) • (Y + P)) = Y := by
      have : Y - (c : ℂ) • P + (c : ℂ) • (Y + P) = ((1 + c : ℝ) : ℂ) • Y := by
        push_cast
        module
      rw [this, smul_smul]
      push_cast at hcC ⊢
      rw [inv_mul_cancel₀ hcC, one_smul]
    rwa [e] at h
  have hPh : P.IsHermitian := by
    have := h1.1.sub hYh
    simpa using this
  have hZh : (Y - (5 : ℂ) • P).IsHermitian :=
    hYh.sub (hPh.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))
  -- regularised inequality
  have hreg : ∀ t : ℝ, 0 < t →
      ‖(Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P).det‖ ≤
        r ^ Fintype.card ι * (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re := by
    intro t ht
    have ht0 : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.mpr ht.le
    have hYt : (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef := by
      have hh : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
        Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr ht)
      rw [add_comm]; exact hh.add_posSemidef hY
    have hsm : ((t : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := PosSemidef.one.smul ht0
    have hZt : (Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P).IsHermitian := by
      have hs : ((t : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := hsm.1
      have := hZh.add hs
      have e : Y - (5 : ℂ) • P + (t : ℂ) • (1 : Matrix ι ι ℂ) =
          Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P := by abel
      rwa [e] at this
    have q1 : ((r : ℂ) • (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)) -
        (Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P)).PosSemidef := by
      have hA := h1.smul (show (0 : ℂ) ≤ (5 : ℂ) by norm_num)
      have hB := hY.smul (Complex.zero_le_real.mpr (by linarith : (0 : ℝ) ≤ r - 6))
      have hC := hsm.smul (Complex.zero_le_real.mpr (by linarith : (0 : ℝ) ≤ r - 1))
      have e : (r : ℂ) • (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)) -
          (Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P) =
          (5 : ℂ) • (Y + P) + ((r - 6 : ℝ) : ℂ) • Y +
            ((r - 1 : ℝ) : ℂ) • ((t : ℂ) • (1 : Matrix ι ι ℂ)) := by
        push_cast
        module
      rw [e]
      exact (hA.add hB).add hC
    have q2 : ((r : ℂ) • (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)) +
        (Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P)).PosSemidef := by
      have hk : (0 : ℝ) ≤ 5 / c := by positivity
      have hrest : (0 : ℝ) ≤ r + 1 - 5 / c := by
        rw [sub_nonneg, div_le_iff₀ hc]
        linarith
      have hA := h2.smul (Complex.zero_le_real.mpr hk)
      have hB := hY.smul (Complex.zero_le_real.mpr hrest)
      have hC := hsm.smul (Complex.zero_le_real.mpr (by linarith : (0 : ℝ) ≤ r + 1))
      have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      have e : (r : ℂ) • (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)) +
          (Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P) =
          ((5 / c : ℝ) : ℂ) • (Y - (c : ℂ) • P) + ((r + 1 - 5 / c : ℝ) : ℂ) • Y +
            ((r + 1 : ℝ) : ℂ) • ((t : ℂ) • (1 : Matrix ι ι ℂ)) := by
        have hcc : ((5 / c : ℝ) : ℂ) * (c : ℂ) = 5 := by
          push_cast
          field_simp
        rw [smul_sub, smul_smul, hcc]
        push_cast
        module
      rw [e]
      exact (hA.add hB).add hC
    exact norm_det_le_of_loewner_gram hYt hZt q1 q2
  -- limit `t → 0⁺`
  have hcontZ : Continuous fun t : ℝ =>
      ‖(Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P).det‖ := by
    have : Continuous fun t : ℝ => Y + (t : ℂ) • (1 : Matrix ι ι ℂ) - (5 : ℂ) • P := by
      fun_prop
    exact (this.matrix_det).norm
  have hcontY : Continuous fun t : ℝ =>
      r ^ Fintype.card ι * (Y + (t : ℂ) • (1 : Matrix ι ι ℂ)).det.re := by
    have : Continuous fun t : ℝ => Y + (t : ℂ) • (1 : Matrix ι ι ℂ) := by fun_prop
    exact continuous_const.mul (Complex.continuous_re.comp this.matrix_det)
  have hZ0 := (hcontZ.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hY0 := (hcontY.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hle := le_of_tendsto_of_tendsto hZ0 hY0
    (Filter.eventually_of_mem self_mem_nhdsWithin fun t ht => hreg t ht)
  simpa using hle

end Compressed

section Transfer

/-- The diagonal coefficient `δ_a = B_-'(x_a) x_a^e` computed from the full node list. -/
def nodeDelta {k : ℕ} (e : ℕ) (x : Fin k → ℝ) (a : Fin k) : ℝ :=
  negBlaschkeDeriv x a * x a ^ e

/-- Rows of `S` carry the diagonal alone; the other rows carry `K + D_ω`. -/
def gramSel {k : ℕ} (S : Finset (Fin k)) (ω : Fin k → ℝ) (e : ℕ) (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a j => if a ∈ S then Matrix.diagonal (nodeDelta e x) a j
    else (kMat x + dW ω e x) a j

/-- Rows of `S` carry `x^(m-j)`; the other rows carry `x^j + ω x^(m-j)`. -/
def laurentSel {k : ℕ} (S : Finset (Fin k)) (ω : Fin k → ℝ) (m : ℕ) (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a j => if a ∈ S then x a ^ (m - (j : ℕ))
    else x a ^ (j : ℕ) + ω a * x a ^ (m - (j : ℕ))

theorem kMat_det_ne_zero {k : ℕ} {x : Fin k → ℝ} (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1) : (kMat x).det ≠ 0 := by
  have h := kR_det_pos hinj hx0 hx1
  have e : kMat x = kR x := rfl
  rw [e]
  exact h.ne'

/-- Selected form of `lemma51_weighted`, by multilinearity in the selected rows. -/
theorem gramSel_det_mul {k : ℕ} (e : ℕ) (x : Fin k → ℝ)
    (hinj : Function.Injective x) (hx0 : ∀ b, x b ≠ 0) (hx1 : ∀ b, |x b| < 1)
    (S : Finset (Fin k)) (ω : Fin k → ℝ) :
    (gramSel S ω e x).det * (Matrix.vandermonde x).det =
      (kMat x).det * (laurentSel S ω (e + k - 1) x).det := by
  classical
  induction S using Finset.induction_on generalizing ω with
  | empty =>
    have h := lemma51_weighted ω e x hinj hx0 hx1
    have hK := kMat_det_ne_zero hinj hx0 hx1
    have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
    rw [div_eq_div_iff hK hV] at h
    have e1 : gramSel ∅ ω e x = kMat x + dW ω e x := by
      ext a j; simp [gramSel]
    have e2 : laurentSel ∅ ω (e + k - 1) x = dMatW ω (e + k - 1) x := by
      ext a j; simp [laurentSel, dMatW]
    rw [e1, e2, h]
    ring
  | insert i S hi ih =>
    set ω1 := Function.update ω i 1 with hω1
    set ω0 := Function.update ω i 0 with hω0
    have hrowG : (gramSel S ω1 e x).det =
        (gramSel S ω0 e x).det + (gramSel (insert i S) ω e x).det := by
      have e1 : gramSel S ω1 e x = (gramSel S ω e x).updateRow i
          ((gramSel S ω0 e x) i + (gramSel (insert i S) ω e x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha
          simp only [Matrix.updateRow_self, Pi.add_apply, gramSel, Matrix.of_apply, hi, if_false,
            Finset.mem_insert, true_or, if_true, Matrix.add_apply, dW, Matrix.diagonal_apply, hω1,
            hω0, Function.update_self, nodeDelta]
          split_ifs <;> simp
        · rw [Matrix.updateRow_ne ha]
          simp only [gramSel, Matrix.of_apply, Matrix.add_apply, dW, Matrix.diagonal_apply, hω1,
            Function.update_of_ne ha]
      have e2 : gramSel S ω0 e x = (gramSel S ω e x).updateRow i ((gramSel S ω0 e x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha; simp
        · rw [Matrix.updateRow_ne ha]
          simp only [gramSel, Matrix.of_apply, Matrix.add_apply, dW, Matrix.diagonal_apply, hω0,
            Function.update_of_ne ha]
      have e3 : gramSel (insert i S) ω e x =
          (gramSel S ω e x).updateRow i ((gramSel (insert i S) ω e x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha; simp
        · rw [Matrix.updateRow_ne ha]
          simp only [gramSel, Matrix.of_apply, Finset.mem_insert, ha, false_or]
      rw [e1, Matrix.det_updateRow_add, ← e2, ← e3]
    have hrowL : (laurentSel S ω1 (e + k - 1) x).det =
        (laurentSel S ω0 (e + k - 1) x).det + (laurentSel (insert i S) ω (e + k - 1) x).det := by
      have e1 : laurentSel S ω1 (e + k - 1) x = (laurentSel S ω (e + k - 1) x).updateRow i
          ((laurentSel S ω0 (e + k - 1) x) i + (laurentSel (insert i S) ω (e + k - 1) x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha
          simp [laurentSel, hi, hω1, hω0]
        · rw [Matrix.updateRow_ne ha]
          simp only [laurentSel, Matrix.of_apply, hω1, Function.update_of_ne ha]
      have e2 : laurentSel S ω0 (e + k - 1) x =
          (laurentSel S ω (e + k - 1) x).updateRow i ((laurentSel S ω0 (e + k - 1) x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha; simp
        · rw [Matrix.updateRow_ne ha]
          simp only [laurentSel, Matrix.of_apply, hω0, Function.update_of_ne ha]
      have e3 : laurentSel (insert i S) ω (e + k - 1) x =
          (laurentSel S ω (e + k - 1) x).updateRow i
            ((laurentSel (insert i S) ω (e + k - 1) x) i) := by
        ext a j
        by_cases ha : a = i
        · subst ha; simp
        · rw [Matrix.updateRow_ne ha]
          simp only [laurentSel, Matrix.of_apply, Finset.mem_insert, ha, false_or]
      rw [e1, Matrix.det_updateRow_add, ← e2, ← e3]
    have h1 := ih ω1
    have h0 := ih ω0
    rw [hrowG, hrowL] at h1
    linear_combination h1 - h0

/-- `gramSel` determinant: the selected diagonal times the complementary principal minor. -/
theorem gramSel_det {k : ℕ} (S : Finset (Fin k)) (ω : Fin k → ℝ) (e : ℕ) (x : Fin k → ℝ) :
    (gramSel S ω e x).det = (∏ a ∈ S, nodeDelta e x a) *
      ((kMat x + dW ω e x).submatrix (fun a : {a // a ∉ S} => a.1)
        (fun a : {a // a ∉ S} => a.1)).det := by
  have h := det_piecewise_diag (kMat x + dW ω e x) (nodeDelta e x) S
  have e1 : gramSel S ω e x = pwMat Sᶜ (kMat x + dW ω e x) (Matrix.diagonal (nodeDelta e x)) := by
    ext a j
    rw [pwMat_apply]
    by_cases ha : a ∈ S <;> simp [gramSel, ha]
  rw [e1, h]

end Transfer

section Selected

open CatalanMeasure.Parametric

variable {n : ℕ}

/-- Comparison weights: `1` on negatives, `0` on positives. -/
def omegaCmp (z : Fin n → ℝ) (i : Fin n) : ℝ := if z i < 0 then 1 else 0
/-- Indicator of the positive rows. -/
def omegaPos (z : Fin n → ℝ) (i : Fin n) : ℝ := if z i < 0 then 0 else 1

/-- `Y = K + D_-` on the full physical list. -/
def pickY (e : ℕ) (z : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := kMat z + dW (omegaCmp z) e z
/-- `P = D_+` on the full physical list. -/
def pickP (e : ℕ) (z : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := dW (omegaPos z) e z

/-- The physical Pick window at `c`: the two real quadratic forms `Y + P`, `Y - cP` are
nonnegative on the original node list. -/
def PickWindow (c : ℝ) (e : ℕ) (z : Fin n → ℝ) : Prop :=
  (∀ u : Fin n → ℝ, 0 ≤ ∑ a, ∑ b, u a * (pickY e z + pickP e z) a b * u b) ∧
  (∀ u : Fin n → ℝ, 0 ≤ ∑ a, ∑ b, u a * (pickY e z - c • pickP e z) a b * u b)

/-- The Laurent matrix with the rows of `S` on the second sheet. -/
def selectedLaurent (g : ℕ) (z : Fin n → ℝ) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i r => if i ∈ S then z i ^ ((r : ℤ) - g) else actualLaurentEntry g r (z i)

/-- The `w = 0` comparison matrix: the same selected rows and negative rows, ordinary positive
rows evaluated at `z`. -/
def comparisonLaurent (g : ℕ) (z : Fin n → ℝ) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i r => if i ∈ S then z i ^ ((r : ℤ) - g)
    else if z i < 0 then actualLaurentEntry g r (z i) else z i ^ ((g : ℤ) - r)

theorem second_laurent_factor {g : ℕ} (hg : 2 * g + 1 ≤ n) (r : Fin n) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g : ℤ) - (n - 1 : ℕ)) * x ^ ((n - 1 - 2 * g) + n - 1 - (r.rev : ℕ)) =
      x ^ ((r : ℤ) - g) := by
  first
    | rw [← zpow_natCast x _, ← zpow_add₀ hx]
    | rw [← zpow_add₀ hx]
  congr 1
  have := r.isLt
  simp only [Fin.val_rev]
  omega

theorem selectedLaurent_factor {g : ℕ} (hg : 2 * g + 1 ≤ n) (z : Fin n → ℝ)
    (hz0 : ∀ i, z i ≠ 0) (S : Finset (Fin n)) :
    selectedLaurent g z S =
      Matrix.diagonal (fun i => (if i ∈ S then 1 else lamOf (z i)) *
          z i ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (laurentSel S (fun i => omegaOf (z i)) ((n - 1 - 2 * g) + n - 1) z).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin n)) := by
  ext i r
  simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id, laurentSel, Matrix.of_apply,
    Fin.revPerm_apply, selectedLaurent]
  by_cases hi : i ∈ S
  · simp only [hi, if_true, one_mul]
    exact (second_laurent_factor hg r (hz0 i)).symm
  · simp only [hi, if_false]
    rw [actualLaurentEntry_eq hg (hz0 i) r]

theorem comparisonLaurent_factor {g : ℕ} (hg : 2 * g + 1 ≤ n) (z : Fin n → ℝ)
    (hz0 : ∀ i, z i ≠ 0) (S : Finset (Fin n)) :
    comparisonLaurent g z S =
      Matrix.diagonal (fun i => (if i ∈ S then 1 else if z i < 0 then 1 / 2 else 1) *
          z i ^ ((g : ℤ) - (n - 1 : ℕ))) *
        (laurentSel S (omegaCmp z) ((n - 1 - 2 * g) + n - 1) z).submatrix id
          (Fin.revPerm : Equiv.Perm (Fin n)) := by
  ext i r
  simp only [Matrix.diagonal_mul, Matrix.submatrix_apply, id, laurentSel, Matrix.of_apply,
    Fin.revPerm_apply, comparisonLaurent]
  by_cases hi : i ∈ S
  · simp only [hi, if_true, one_mul]
    exact (second_laurent_factor hg r (hz0 i)).symm
  · simp only [hi, if_false]
    by_cases hneg : z i < 0
    · rw [actualLaurentEntry_eq hg (hz0 i) r]
      simp only [hneg, if_true, omegaCmp, lamOf, omegaOf]
    · simp only [hneg, if_false, omegaCmp, one_mul, zero_mul, add_zero]
      exact (far_laurent_factor r (hz0 i)).symm

theorem abs_det_diag_mul_rev (l : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ) :
    |(Matrix.diagonal l * L.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))).det| =
      (∏ i, |l i|) * |L.det| := by
  rw [Matrix.det_mul, Matrix.det_diagonal, abs_mul, Finset.abs_prod]
  congr 1
  simpa using Matrix.abs_det_submatrix_equiv_equiv (Equiv.refl (Fin n))
    (Fin.revPerm : Equiv.Perm (Fin n)) L

theorem kMat_symm (z : Fin n → ℝ) (a b : Fin n) : kMat z a b = kMat z b a := by
  simp only [kMat, Matrix.of_apply, mul_comm]

theorem dW_symm (ω : Fin n → ℝ) (e : ℕ) (z : Fin n → ℝ) (a b : Fin n) :
    dW ω e z a b = dW ω e z b a := by
  simp only [dW, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- **Selected-sheet comparison.** On a physical list in the Pick window at `1/100`, every
second-sheet selection has determinant at most `499^n` times its `w = 0` comparison determinant,
with all original row scalars and full-node diagonal coefficients. -/
theorem selected_laurent_comparison {g : ℕ} (hg : 2 * g + 1 ≤ n) (z : Fin n → ℝ)
    (hinj : Function.Injective z) (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, |z i| < 1)
    (hpick : PickWindow (1 / 100) (n - 1 - 2 * g) z) (S : Finset (Fin n)) :
    |(selectedLaurent g z S).det| ≤ 499 ^ n * |(comparisonLaurent g z S).det| := by
  classical
  set e := n - 1 - 2 * g with he
  let f : {a // a ∉ S} → Fin n := fun a => a.1
  let ofR : ℝ → ℂ := fun r => (r : ℂ)
  have hYs : ∀ a b, pickY e z a b = pickY e z b a := fun a b => by
    simp only [pickY, Matrix.add_apply, kMat_symm z a b, dW_symm _ e z a b]
  have hPs : ∀ a b, pickP e z a b = pickP e z b a := fun a b => dW_symm _ e z a b
  have h1 : (((pickY e z + pickP e z).map ofR).submatrix f f).PosSemidef :=
    (posSemidef_map_ofReal _ (fun a b => by simp only [Matrix.add_apply, hYs a b, hPs a b])
      hpick.1).submatrix f
  have h2 : (((pickY e z - (1 / 100 : ℝ) • pickP e z).map ofR).submatrix f f).PosSemidef :=
    (posSemidef_map_ofReal _ (fun a b => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, hYs a b, hPs a b]) hpick.2).submatrix f
  set Y : Matrix {a // a ∉ S} {a // a ∉ S} ℂ := ((pickY e z).map ofR).submatrix f f with hY
  set P : Matrix {a // a ∉ S} {a // a ∉ S} ℂ := ((pickP e z).map ofR).submatrix f f with hP
  have hYh : Y.IsHermitian := by
    ext a b
    simp only [Y, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.map_apply, ofR,
      Complex.star_def, Complex.conj_ofReal, hYs (f b) (f a)]
  have e1 : ((pickY e z + pickP e z).map ofR).submatrix f f = Y + P := by
    ext a b
    simp [Y, P, ofR]
  have e2 : ((pickY e z - (1 / 100 : ℝ) • pickP e z).map ofR).submatrix f f =
      Y - (((1 / 100 : ℝ)) : ℂ) • P := by
    ext a b
    simp [Y, P, ofR]
  rw [e1] at h1
  rw [e2] at h2
  have hcmp := norm_det_sub_five_le hYh (c := 1 / 100) (r := 499) (by norm_num) (by norm_num)
    (by norm_num) h1 h2
  have hZ : Y - (5 : ℂ) • P =
      (((kMat z + dW (fun i => omegaOf (z i)) e z).submatrix f f).map ofR) := by
    ext a b
    simp only [Y, P, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply,
      pickY, pickP, Matrix.add_apply, dW, Matrix.diagonal_apply, ofR, smul_eq_mul]
    by_cases hab : f a = f b
    · simp only [hab, if_true, omegaCmp, omegaPos, omegaOf]
      split_ifs <;> push_cast <;> ring
    · simp only [hab, if_false]
      push_cast
      ring
  have hYdet : Y = (((kMat z + dW (omegaCmp z) e z).submatrix f f).map ofR) := by
    ext a b
    simp [Y, ofR, pickY]
  rw [hZ, det_map_ofReal, hYdet, det_map_ofReal] at hcmp
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs] at hcmp
  set dZ := ((kMat z + dW (fun i => omegaOf (z i)) e z).submatrix f f).det with hdZ
  set dY := ((kMat z + dW (omegaCmp z) e z).submatrix f f).det with hdY
  have hcard : (499 : ℝ) ^ Fintype.card {a // a ∉ S} ≤ 499 ^ n := by
    apply pow_le_pow_right₀ (by norm_num)
    have := Fintype.card_subtype_le (fun a : Fin n => a ∉ S)
    simpa using this
  have hZY : |dZ| ≤ 499 ^ n * |dY| := by
    have hp : (0 : ℝ) < 499 ^ Fintype.card {a // a ∉ S} := by positivity
    calc |dZ| ≤ 499 ^ Fintype.card {a // a ∉ S} * dY := hcmp
      _ ≤ 499 ^ Fintype.card {a // a ∉ S} * |dY| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hp.le
      _ ≤ 499 ^ n * |dY| := mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
  have hK := kMat_det_ne_zero hinj hz0 hz1
  have hV : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hKpos : 0 < |(kMat z).det| := abs_pos.mpr hK
  have hVpos : 0 < |(Matrix.vandermonde z).det| := abs_pos.mpr hV
  have hL : ∀ ω : Fin n → ℝ,
      |(laurentSel S ω (e + n - 1) z).det| * |(kMat z).det| =
        (∏ a ∈ S, |nodeDelta e z a|) *
          |((kMat z + dW ω e z).submatrix f f).det| * |(Matrix.vandermonde z).det| := by
    intro ω
    have h := congrArg abs (gramSel_det_mul e z hinj hz0 hz1 S ω)
    rw [gramSel_det, abs_mul, abs_mul, abs_mul, Finset.abs_prod] at h
    linarith only [h]
  have hsel := selectedLaurent_factor hg z hz0 S
  have hc := comparisonLaurent_factor hg z hz0 S
  rw [hsel, hc, abs_det_diag_mul_rev, abs_det_diag_mul_rev]
  have hl : (∏ i, |(if i ∈ S then 1 else lamOf (z i)) * z i ^ ((g : ℤ) - (n - 1 : ℕ))|) ≤
      ∏ i, |(if i ∈ S then 1 else if z i < 0 then 1 / 2 else 1) *
        z i ^ ((g : ℤ) - (n - 1 : ℕ))| := by
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => ?_)
    rw [abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    by_cases hi : i ∈ S
    · simp [hi]
    · simp only [hi, if_false, lamOf]
      split_ifs <;> norm_num [abs_of_pos, abs_of_neg]
  set A := ∏ i, |(if i ∈ S then 1 else lamOf (z i)) * z i ^ ((g : ℤ) - (n - 1 : ℕ))|
  set B := ∏ i, |(if i ∈ S then 1 else if z i < 0 then 1 / 2 else 1) *
        z i ^ ((g : ℤ) - (n - 1 : ℕ))|
  have hA0 : 0 ≤ A := Finset.prod_nonneg fun i _ => abs_nonneg _
  have hLZ := hL (fun i => omegaOf (z i))
  have hLY := hL (omegaCmp z)
  have hD : 0 ≤ ∏ a ∈ S, |nodeDelta e z a| := Finset.prod_nonneg fun i _ => abs_nonneg _
  set LZ := |(laurentSel S (fun i => omegaOf (z i)) (e + n - 1) z).det|
  set LY := |(laurentSel S (omegaCmp z) (e + n - 1) z).det|
  have hLZY : LZ ≤ 499 ^ n * LY := by
    have h3 : LZ * |(kMat z).det| ≤ (499 ^ n * LY) * |(kMat z).det| := by
      rw [hLZ, mul_assoc (499 ^ n : ℝ), hLY]
      have h4 := mul_le_mul_of_nonneg_left hZY hD
      have h5 := mul_le_mul_of_nonneg_right h4 hVpos.le
      calc _ ≤ _ := h5
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hKpos
  have hLY0 : 0 ≤ LY := abs_nonneg _
  calc A * LZ ≤ A * (499 ^ n * LY) := mul_le_mul_of_nonneg_left hLZY hA0
    _ ≤ B * (499 ^ n * LY) := mul_le_mul_of_nonneg_right hl (by positivity)
    _ = _ := by ring

end Selected

end
end CatalanMeasure.GenD.Signed.PhysicalPick

#print axioms CatalanMeasure.GenD.Signed.PhysicalPick.selected_laurent_comparison

#print axioms CatalanMeasure.GenD.Signed.PhysicalPick.norm_det_sub_five_le
#print axioms CatalanMeasure.GenD.Signed.PhysicalPick.gramSel_det_mul
#print axioms CatalanMeasure.GenD.Signed.PhysicalPick.gramSel_det

/-!
# R1: from a positive semidefinite Pick matrix to the physical Pick window

For real nodes `z` (injective, nonzero, in the open unit interval) and real values `f`, the Pick matrix
`P(f) = [(1 - f_a f_b)/(1 - z_a z_b)]` being positive semidefinite gives
`K + diag (B'(z_a) f_a) ⪰ 0` (the congruence `A* K A = K + 2 H F + F K F`, `A = I + H⁻¹ K F`).
With `f_a = g_a z_a ^ e`, `g = 1` on negative nodes and `g = -c` on positive nodes, this is the
second half of `PickWindow c e z`; the first half is the classical Pick inequality (`g ≡ 1`).
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Matrix CatalanMeasure.Signed CatalanMeasure.GenD.Signed CatalanMeasure.Parametric
open scoped ComplexOrder

noncomputable section

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Pick matrix `K - F K F` of the data `f` at the nodes `x`, over `ℂ`. -/
theorem pickMat_entry (x f : ι → ℝ) (a b : ι) :
    (kC x - diagC f * kC x * diagC f) a b = (((1 - f a * f b) / (1 - x a * x b) : ℝ) : ℂ) := by
  simp only [kC, diagC, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_apply]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  push_cast
  ring

/-- **Pick matrix to Loewner form.** If `K - F K F ⪰ 0` then `K + diag (B'(x_a) f_a) ⪰ 0`. -/
theorem posSemidef_kC_add_of_pick {x : ι → ℝ} (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hx : ∀ a, |x a| < 1) (f : ι → ℝ)
    (hP : (kC x - diagC f * kC x * diagC f).PosSemidef) :
    (kC x + diagC (fun a => bdr x a * f a)).PosSemidef := by
  set K := kC x with hK
  set H := diagC (bdr x) with hH
  set Hi := diagC (fun a => (bdr x a)⁻¹) with hHi
  set X := diagC f with hX
  set T := Hi * K * X with hT
  have rK : K * Hi * K = H := kC_mul_inv_mul hinj hx0 hx
  have rHHi : H * Hi = 1 := by
    rw [hH, hHi, diagC_mul]
    unfold diagC
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    simp [mul_inv_cancel₀ (bdr_ne_zero hinj hx a)]
  have rHX : H * X = diagC (fun a => bdr x a * f a) := by
    rw [hH, hX, diagC_mul]
  have rXH : X * H = diagC (fun a => bdr x a * f a) := by
    rw [hH, hX, diagC_mul]
    unfold diagC
    congr 1
    funext a
    push_cast
    ring
  have hKh : Kᴴ = K := kC_conjTranspose x
  have hHih : Hiᴴ = Hi := diagC_conjTranspose _
  have hXh : Xᴴ = X := diagC_conjTranspose _
  have hTh : Tᴴ = X * K * Hi := by
    rw [hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hKh, hHih, hXh]
    simp only [Matrix.mul_assoc]
  have e1 : K * T = diagC (fun a => bdr x a * f a) := by
    calc K * T = (K * Hi * K) * X := by simp only [hT, Matrix.mul_assoc]
      _ = _ := by rw [rK, rHX]
  have e2 : Tᴴ * K = diagC (fun a => bdr x a * f a) := by
    calc Tᴴ * K = X * (K * Hi * K) := by rw [hTh]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [rK, rXH]
  have e3 : Tᴴ * K * T = X * K * X := by
    calc Tᴴ * K * T = (X * H) * (Hi * K * X) := by rw [e2, ← rXH, hT]
      _ = X * (H * Hi) * K * X := by simp only [Matrix.mul_assoc]
      _ = X * K * X := by rw [rHHi]; simp only [Matrix.mul_one]
  set A : Matrix ι ι ℂ := 1 + T with hA
  have hAh : Aᴴ = 1 + Tᴴ := by
    rw [hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
  have hQ : (Aᴴ * K * A).PosSemidef := (posSemidef_kC hx).conjTranspose_mul_mul_same A
  have hexp : Aᴴ * K * A = K + K * T + Tᴴ * K + Tᴴ * K * T := by
    rw [hAh, hA]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hfin : K + diagC (fun a => bdr x a * f a) =
      (1 / 2 : ℂ) • (Aᴴ * K * A + (K - X * K * X)) := by
    rw [hexp, e3, e1, e2]
    module
  rw [hfin]
  have h2 : (0 : ℂ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.zero_le_real.mpr (by norm_num)
  have hP' : (K - X * K * X).PosSemidef := hP
  exact (hQ.add hP').smul h2

/-- A positive semidefinite complexification has a nonnegative real quadratic form. -/
theorem realForm_nonneg_of_posSemidef (Mr : Matrix ι ι ℝ) (hs : ∀ a b, Mr a b = Mr b a)
    (h : (Mr.map (fun r : ℝ => (r : ℂ))).PosSemidef) (u : ι → ℝ) :
    0 ≤ ∑ a, ∑ b, u a * Mr a b * u b := by
  have h1 := h.dotProduct_mulVec_nonneg (fun a => (u a : ℂ))
  have h2 := form_map_ofReal Mr hs (fun a => (u a : ℂ))
  rw [h2] at h1
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at h1
  exact Complex.zero_le_real.mp h1

/-- **R1, general form.** A nonnegative real Pick form gives the Loewner form `K + diag (B' f) ⪰ 0`
as a real quadratic form. -/
theorem loewnerForm_of_pickForm {x : ι → ℝ} (hinj : Function.Injective x)
    (hx0 : ∀ b, x b ≠ 0) (hx : ∀ a, |x a| < 1) (f : ι → ℝ)
    (hP : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * u b * ((1 - f a * f b) / (1 - x a * x b)))
    (u : ι → ℝ) :
    0 ≤ ∑ a, ∑ b, u a * (kR x + Matrix.diagonal (fun a => bdr x a * f a)) a b * u b := by
  have hsym : ∀ a b : ι, (Matrix.of fun a b => (1 - f a * f b) / (1 - x a * x b)) a b =
      (Matrix.of fun a b => (1 - f a * f b) / (1 - x a * x b)) b a := by
    intro a b
    simp only [Matrix.of_apply]
    rw [mul_comm (f a) (f b), mul_comm (x a) (x b)]
  have hpsd : (kC x - diagC f * kC x * diagC f).PosSemidef := by
    have e : kC x - diagC f * kC x * diagC f =
        (Matrix.of fun a b => (1 - f a * f b) / (1 - x a * x b)).map
          (fun r : ℝ => (r : ℂ)) := by
      ext a b
      rw [pickMat_entry]
      simp
    rw [e]
    refine posSemidef_map_ofReal _ hsym (fun w => ?_)
    have := hP w
    simpa [Matrix.of_apply, mul_assoc, mul_comm, mul_left_comm] using this
  have hl := posSemidef_kC_add_of_pick hinj hx0 hx f hpsd
  have e2 : kC x + diagC (fun a => bdr x a * f a) =
      (kR x + Matrix.diagonal (fun a => bdr x a * f a)).map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    simp only [kC, kR, diagC, Matrix.add_apply, Matrix.of_apply, Matrix.map_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [e2] at hl
  refine realForm_nonneg_of_posSemidef _ (fun a b => ?_) hl u
  simp only [Matrix.add_apply, kR, Matrix.of_apply, Matrix.diagonal_apply]
  rw [mul_comm (x a) (x b)]
  by_cases hab : a = b
  · subst hab; rfl
  · rw [if_neg hab, if_neg (Ne.symm hab)]

end General

section Window

variable {n : ℕ}

/-- The Pick data of the physical window: `z_i ^ e` at negative nodes, `-c z_i ^ e` at positive
nodes. -/
def winData (c : ℝ) (e : ℕ) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  (if z i < 0 then 1 else -c) * z i ^ e

/-- The Pick form of the physical window data. -/
def winPickForm (c : ℝ) (e : ℕ) (z : Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  ∑ a, ∑ b, u a * u b *
    ((1 - winData c e z a * winData c e z b) / (1 - z a * z b))

theorem negBlaschkeDeriv_eq_bdr (z : Fin n → ℝ) (b : Fin n) :
    negBlaschkeDeriv z b = bdr z b := by
  unfold negBlaschkeDeriv nodalProd wFun bdr
  rfl

theorem dW_eq_diagonal (ω : Fin n → ℝ) (e : ℕ) (z : Fin n → ℝ) :
    dW ω e z = Matrix.diagonal (fun a => bdr z a * (ω a * z a ^ e)) := by
  unfold dW
  congr 1
  funext b
  rw [negBlaschkeDeriv_eq_bdr]
  ring

/-- **R1.** A nonnegative Pick form for the physical data gives the second Loewner inequality of
`PickWindow`; the first inequality is the classical Pick inequality. -/
theorem pickWindow_of_pickForm {z : Fin n → ℝ} (hinj : Function.Injective z)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, |z i| < 1) (c : ℝ) (e : ℕ)
    (hP : ∀ u, 0 ≤ winPickForm c e z u) : PickWindow c e z := by
  have hK : kMat z = kR z := rfl
  refine ⟨fun u => ?_, fun u => ?_⟩
  · -- classical Pick: data `z ^ e`
    have hf : ∀ w : Fin n → ℝ, 0 ≤ ∑ a, ∑ b, w a * w b *
        ((1 - z a ^ e * z b ^ e) / (1 - z a * z b)) := by
      intro w
      have hsym : ∀ a b : Fin n, (Matrix.of fun a b =>
          (1 - z a ^ e * z b ^ e) / (1 - z a * z b)) a b =
          (Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)) b a := by
        intro a b
        simp only [Matrix.of_apply]
        rw [mul_comm (z a ^ e) (z b ^ e), mul_comm (z a) (z b)]
      have hps : ((Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)).map
          (fun r : ℝ => (r : ℂ))).PosSemidef := by
        have h := posSemidef_kC_sub hz1 e
        have e1 : (kC z - diagC (fun a => z a ^ e) * kC z * diagC (fun a => z a ^ e)) =
            (Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)).map
              (fun r : ℝ => (r : ℂ)) := by
          ext a b
          rw [pickMat_entry]
          simp
        rw [e1] at h
        exact h
      have := realForm_nonneg_of_posSemidef _ hsym hps w
      simpa [Matrix.of_apply, mul_assoc, mul_comm, mul_left_comm] using this
    have := loewnerForm_of_pickForm hinj hz0 hz1 (fun a => z a ^ e) hf u
    have e2 : pickY e z + pickP e z = kR z + Matrix.diagonal (fun a => bdr z a * z a ^ e) := by
      unfold pickY pickP
      rw [hK, dW_eq_diagonal, dW_eq_diagonal]
      ext a b
      simp only [Matrix.add_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        simp only [if_true, omegaCmp, omegaPos]
        split_ifs <;> ring
      · simp [hab]
    rw [e2]
    exact this
  · have := loewnerForm_of_pickForm hinj hz0 hz1 (winData c e z) hP u
    have e2 : pickY e z - c • pickP e z =
        kR z + Matrix.diagonal (fun a => bdr z a * winData c e z a) := by
      unfold pickY pickP
      rw [hK, dW_eq_diagonal, dW_eq_diagonal]
      ext a b
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        simp only [if_true, omegaCmp, omegaPos, winData, smul_eq_mul]
        split_ifs <;> ring
      · simp [hab]
    rw [e2]
    exact this

end Window

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R2, R3: seed and first exit for a one-parameter family of quadratic forms

`exists_null_of_exit`: a continuous family of symmetric real quadratic forms `Q_γ`, positive definite at
`γ₀ ≤ γ₁`, is either positive semidefinite at `γ₁` or has a parameter `γ ∈ (γ₀, γ₁)` where it is
positive semidefinite with a nonzero null vector (`W v = 0`).  No monotonicity, no concavity.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Matrix Filter Topology Set CatalanMeasure.Signed CatalanMeasure.GenD.Signed
open CatalanMeasure.Parametric
open scoped ComplexOrder

noncomputable section

section Exit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quadratic form of the family of matrices `w γ`. -/
def Qf (w : ℝ → ι → ι → ℝ) (γ : ℝ) (u : ι → ℝ) : ℝ := ∑ a, ∑ b, u a * w γ a b * u b

theorem Qf_smul (w : ℝ → ι → ι → ℝ) (γ s : ℝ) (u : ι → ℝ) :
    Qf w γ (s • u) = s ^ 2 * Qf w γ u := by
  unfold Qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_Qf_pair (w : ℝ → ι → ι → ℝ) (hc : ∀ a b, Continuous fun γ => w γ a b) :
    Continuous fun p : ℝ × (ι → ℝ) => Qf w p.1 p.2 := by
  unfold Qf
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  have h1 : Continuous fun p : ℝ × (ι → ℝ) => p.2 a := (continuous_apply a).comp continuous_snd
  have h2 : Continuous fun p : ℝ × (ι → ℝ) => p.2 b := (continuous_apply b).comp continuous_snd
  have h3 : Continuous fun p : ℝ × (ι → ℝ) => w p.1 a b := (hc a b).comp continuous_fst
  exact (h1.mul h3).mul h2

/-- The unit sphere of `ι → ℝ`. -/
def sph (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {u | ∑ a, u a ^ 2 = 1}

theorem isCompact_sph : IsCompact (sph ι) := by
  have hcl : IsClosed (sph ι) :=
    isClosed_eq (continuous_finset_sum _ fun a _ => (continuous_apply a).pow 2) continuous_const
  have hb : Bornology.IsBounded (sph ι) := by
    refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset ?_
    intro u hu
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro a
    have h1 : u a ^ 2 ≤ ∑ b, u b ^ 2 :=
      Finset.single_le_sum (f := fun b => u b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
    have h2 : ∑ b, u b ^ 2 = 1 := hu
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (u a), sq_abs (u a)]
  exact Metric.isCompact_of_isClosed_isBounded hcl hb

/-- Positive definiteness is an open condition in the parameter. -/
theorem eventually_pd (w : ℝ → ι → ι → ℝ) (hc : ∀ a b, Continuous fun γ => w γ a b)
    {γ₁ : ℝ} (h : ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ₁ u) :
    ∀ᶠ γ in 𝓝 γ₁, ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ u := by
  have hS : ∀ᶠ γ in 𝓝 γ₁, ∀ u ∈ sph ι, 0 < Qf w γ u := by
    refine isCompact_sph.eventually_forall_of_forall_eventually (P := fun γ u => 0 < Qf w γ u) ?_
    intro u hu
    have hne : u ≠ 0 := by
      rintro rfl
      simp [sph] at hu
    have hcont := (continuous_Qf_pair w hc).continuousAt (x := (γ₁, u))
    exact hcont.eventually (lt_mem_nhds (h u hne))
  filter_upwards [hS] with γ hγ u hu
  have hpos : 0 < ∑ a, u a ^ 2 := by
    by_contra hneg
    push_neg at hneg
    apply hu
    funext a
    have h0 : ∑ a, u a ^ 2 = 0 :=
      le_antisymm hneg (Finset.sum_nonneg fun a _ => sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (u a))).mp h0 a
      (Finset.mem_univ a)
    simpa using this
  set s := Real.sqrt (∑ a, u a ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hs2 : s ^ 2 = ∑ a, u a ^ 2 := Real.sq_sqrt hpos.le
  have hmem : s⁻¹ • u ∈ sph ι := by
    show ∑ a, (s⁻¹ • u) a ^ 2 = 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← hs2]
    field_simp
  have this := hγ _ hmem
  have hu' : u = s • (s⁻¹ • u) := by
    rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  rw [hu', Qf_smul]
  exact mul_pos (by positivity) this

/-- Expansion of the form at `v + t e_a`. -/
theorem form_add_single (W : ι → ι → ℝ) (hs : ∀ a b, W a b = W b a) (v : ι → ℝ) (a : ι)
    (t : ℝ) :
    ∑ x, ∑ y, (v + t • (Pi.single a (1 : ℝ) : ι → ℝ)) x * W x y * (v + t • (Pi.single a (1 : ℝ) : ι → ℝ)) y =
      (∑ x, ∑ y, v x * W x y * v y) + 2 * t * (∑ b, W a b * v b) + t ^ 2 * W a a := by
  have h1 : ∑ x, ∑ y, v x * W x y * (t * (Pi.single a (1 : ℝ) : ι → ℝ) y) =
      t * ∑ x, v x * W x a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single a]
    · simp [Pi.single_apply]; ring
    · intro y _ hy; simp [Pi.single_apply, hy]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ x, ∑ y, (t * (Pi.single a (1 : ℝ) : ι → ℝ) x) * W x y * v y =
      t * ∑ y, W a y * v y := by
    rw [Finset.sum_eq_single a]
    · simp [Pi.single_apply, Finset.mul_sum, mul_assoc]
    · intro x _ hx; simp [Pi.single_apply, hx]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h3 : ∑ x, ∑ y, (t * (Pi.single a (1 : ℝ) : ι → ℝ) x) * W x y *
      (t * (Pi.single a (1 : ℝ) : ι → ℝ) y) = t ^ 2 * W a a := by
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single a]
      · simp [Pi.single_apply]; ring
      · intro y _ hy; simp [Pi.single_apply, hy]
      · intro h; exact absurd (Finset.mem_univ a) h
    · intro x _ hx; simp [Pi.single_apply, hx]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h4 : ∑ x, v x * W x a = ∑ b, W a b * v b := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hs x a, mul_comm]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, Finset.sum_add_distrib]
  rw [h1, h2, h3, h4]
  ring

/-- A positive semidefinite form vanishing at `v` has `W v = 0` (symmetric `W`). -/
theorem null_of_psd (W : ι → ι → ℝ) (hs : ∀ a b, W a b = W b a)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * W a b * u b) (v : ι → ℝ)
    (hv : ∑ a, ∑ b, v a * W a b * v b = 0) (a : ι) : ∑ b, W a b * v b = 0 := by
  set g : ℝ := ∑ b, W a b * v b with hg
  set A : ℝ := W a a with hA
  have key : ∀ t : ℝ, 0 ≤ 2 * t * g + t ^ 2 * A := by
    intro t
    have h := hpsd (v + t • (Pi.single a (1 : ℝ) : ι → ℝ))
    rw [form_add_single W hs v a t, hv] at h
    linarith
  set D : ℝ := |A| + 1 with hD
  have hD0 : 0 < D := by positivity
  have h := key (-g / D)
  have e : 2 * (-g / D) * g + (-g / D) ^ 2 * A = g ^ 2 * (A - 2 * D) / D ^ 2 := by
    field_simp
    ring
  rw [e] at h
  have h2 : 0 ≤ g ^ 2 * (A - 2 * D) := by
    by_contra hneg
    push_neg at hneg
    have : g ^ 2 * (A - 2 * D) / D ^ 2 < 0 := div_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hA2 : A - 2 * D < 0 := by
    have := le_abs_self A
    rw [hD]; linarith
  have : g ^ 2 ≤ 0 := by nlinarith [sq_nonneg g]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg g))

/-- **R3, first exit.** -/
theorem exists_null_of_exit (w : ℝ → ι → ι → ℝ) (hc : ∀ a b, Continuous fun γ => w γ a b)
    (hs : ∀ γ a b, w γ a b = w γ b a) {γ₀ γ₁ : ℝ} (h01 : γ₀ ≤ γ₁)
    (h0 : ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ₀ u) :
    (∀ u : ι → ℝ, 0 ≤ Qf w γ₁ u) ∨
      ∃ γ, γ₀ < γ ∧ γ < γ₁ ∧ (∀ u : ι → ℝ, 0 ≤ Qf w γ u) ∧
        ∃ v : ι → ℝ, v ≠ 0 ∧ ∀ a, ∑ b, w γ a b * v b = 0 := by
  classical
  -- the bad set
  set T : Set ℝ := {γ | γ ∈ Icc γ₀ γ₁ ∧ ¬ ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ u} with hT
  by_cases hTe : T = ∅
  · left
    have h1 : ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ₁ u := by
      by_contra hneg
      have : γ₁ ∈ T := ⟨⟨h01, le_rfl⟩, hneg⟩
      rw [hTe] at this
      exact this
    intro u
    by_cases hu : u = 0
    · subst hu
      simp [Qf]
    · exact (h1 u hu).le
  · have hTn : T.Nonempty := Set.nonempty_iff_ne_empty.mpr hTe
    have hTcl : IsClosed T := by
      have hop : IsOpen {γ : ℝ | ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ u} := by
        rw [isOpen_iff_mem_nhds]
        intro γ hγ
        exact eventually_pd w hc hγ
      have : T = Icc γ₀ γ₁ ∩ {γ : ℝ | ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γ u}ᶜ := by
        ext γ; simp [hT]
      rw [this]
      exact isClosed_Icc.inter hop.isClosed_compl
    have hTb : BddBelow T := ⟨γ₀, fun γ hγ => hγ.1.1⟩
    set γs := sInf T with hγs
    have hγsT : γs ∈ T := hTcl.csInf_mem hTn hTb
    have hγs0 : γ₀ ≤ γs := hγsT.1.1
    have hγs1 : γs ≤ γ₁ := hγsT.1.2
    have hnot : ¬ ∀ u : ι → ℝ, u ≠ 0 → 0 < Qf w γs u := hγsT.2
    have hne0 : γ₀ ≠ γs := by
      intro h
      apply hnot
      rw [← h]; exact h0
    have hlt : γ₀ < γs := lt_of_le_of_ne hγs0 hne0
    -- positive semidefinite at γs by continuity from the left
    have hpsd : ∀ u : ι → ℝ, 0 ≤ Qf w γs u := by
      intro u
      have hpos : ∀ γ, γ₀ ≤ γ → γ < γs → 0 < Qf w γ u ∨ u = 0 := by
        intro γ hγ0 hγ
        by_cases hu : u = 0
        · exact Or.inr hu
        · left
          by_contra hneg
          have hmem : γ ∈ T := ⟨⟨hγ0, by linarith⟩, fun hall => hneg (hall u hu)⟩
          have := csInf_le hTb hmem
          linarith
      by_cases hu : u = 0
      · subst hu; simp [Qf]
      · have hcont : Continuous fun γ => Qf w γ u := by
          unfold Qf
          exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
            ((continuous_const.mul (hc a b)).mul continuous_const)
        have hcl : IsClosed {γ : ℝ | 0 ≤ Qf w γ u} := isClosed_le continuous_const hcont
        have hsub : Ico γ₀ γs ⊆ {γ : ℝ | 0 ≤ Qf w γ u} := by
          intro γ hγ
          rcases hpos γ hγ.1 hγ.2 with h | h
          · exact h.le
          · exact absurd h hu
        have hcls : closure (Ico γ₀ γs) ⊆ {γ : ℝ | 0 ≤ Qf w γ u} := closure_minimal hsub hcl
        have hmem : γs ∈ closure (Ico γ₀ γs) := by
          rw [closure_Ico (ne_of_lt hlt)]
          exact ⟨hlt.le, le_rfl⟩
        exact hcls hmem
    -- a non-positive-definite semidefinite form has a nonzero zero
    obtain ⟨v, hv0, hvle⟩ : ∃ v : ι → ℝ, v ≠ 0 ∧ Qf w γs v ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hnot fun u hu => hcon u hu
    have hv : Qf w γs v = 0 := le_antisymm hvle (hpsd v)
    have hsym : ∀ a b, w γs a b = w γs b a := hs γs
    have hnull := null_of_psd (w γs) hsym hpsd v hv
    by_cases hγe : γs = γ₁
    · left
      rw [← hγe]
      exact hpsd
    · right
      exact ⟨γs, hlt, lt_of_le_of_ne hγs1 hγe, hpsd, v, hv0, hnull⟩

end Exit

section WindowFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data of the one-parameter family: `-c z^e` at positive nodes, `γ z^e` at negative nodes. -/
def gData (c : ℝ) (e : ℕ) (z : ι → ℝ) (γ : ℝ) (a : ι) : ℝ :=
  (if z a < 0 then γ else -c) * z a ^ e

/-- Matrix entries of the Pick matrix of `gData`. -/
def wFam (c : ℝ) (e : ℕ) (z : ι → ℝ) (γ : ℝ) (a b : ι) : ℝ :=
  (1 - gData c e z γ a * gData c e z γ b) / (1 - z a * z b)

theorem continuous_gData (c : ℝ) (e : ℕ) (z : ι → ℝ) (a : ι) :
    Continuous fun γ => gData c e z γ a := by
  unfold gData
  by_cases h : z a < 0
  · simp only [h, if_true]; fun_prop
  · simp only [h, if_false]; fun_prop

theorem continuous_wFam {c : ℝ} {e : ℕ} {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (a b : ι) :
    Continuous fun γ => wFam c e z γ a b := by
  unfold wFam
  have hne : 1 - z a * z b ≠ 0 := by
    have h1 := hz1 a
    have h2 := hz1 b
    rw [abs_lt] at h1 h2
    intro h
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  exact ((continuous_const.sub ((continuous_gData c e z a).mul (continuous_gData c e z b))).div
    continuous_const fun _ => hne)

theorem wFam_symm (c : ℝ) (e : ℕ) (z : ι → ℝ) (γ : ℝ) (a b : ι) :
    wFam c e z γ a b = wFam c e z γ b a := by
  unfold wFam
  rw [mul_comm (gData c e z γ a), mul_comm (z a)]

/-- `K` is positive definite as a real quadratic form. -/
theorem kForm_pos {z : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ b, z b ≠ 0)
    (hz1 : ∀ a, |z a| < 1) {u : ι → ℝ} (hu : u ≠ 0) :
    0 < ∑ a, ∑ b, u a * (1 / (1 - z a * z b)) * u b := by
  have hK := kC_posDef hinj hz0 hz1
  have hv : (fun a => (u a : ℂ)) ≠ 0 := by
    intro h
    apply hu
    funext a
    have := congrFun h a
    simpa using this
  have h1 := hK.dotProduct_mulVec_pos hv
  have hsym : ∀ a b : ι, kR z a b = kR z b a := by
    intro a b
    simp only [kR, Matrix.of_apply]
    rw [mul_comm (z a) (z b)]
  have h2 := form_map_ofReal (kR z) hsym (fun a => (u a : ℂ))
  rw [← kC_eq_map] at h2
  rw [h2] at h1
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at h1
  have h3 := Complex.zero_lt_real.mp h1
  simpa [kR, Matrix.of_apply] using h3

/-- The geometric part: `[(1 - (z_a z_b)^e)/(1 - z_a z_b)]` is positive semidefinite. -/
theorem geomForm_nonneg {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (e : ℕ) (u : ι → ℝ) :
    0 ≤ ∑ a, ∑ b, u a * ((1 - z a ^ e * z b ^ e) / (1 - z a * z b)) * u b := by
  have hsym : ∀ a b : ι, (Matrix.of fun a b =>
      (1 - z a ^ e * z b ^ e) / (1 - z a * z b)) a b =
      (Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)) b a := by
    intro a b
    simp only [Matrix.of_apply]
    rw [mul_comm (z a ^ e) (z b ^ e), mul_comm (z a) (z b)]
  have hps : ((Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)).map
      (fun r : ℝ => (r : ℂ))).PosSemidef := by
    have h := posSemidef_kC_sub hz1 e
    have e1 : (kC z - diagC (fun a => z a ^ e) * kC z * diagC (fun a => z a ^ e)) =
        (Matrix.of fun a b => (1 - z a ^ e * z b ^ e) / (1 - z a * z b)).map
          (fun r : ℝ => (r : ℂ)) := by
      ext a b
      rw [pickMat_entry]
      simp
    rw [e1] at h
    exact h
  have := realForm_nonneg_of_posSemidef _ hsym hps u
  simpa [Matrix.of_apply] using this

/-- **R2, the seed.** At `γ = -c` the form is positive definite (`0 ≤ c < 1`). -/
theorem seed_pos {z : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ b, z b ≠ 0)
    (hz1 : ∀ a, |z a| < 1) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (e : ℕ) {u : ι → ℝ}
    (hu : u ≠ 0) : 0 < Qf (wFam c e z) (-c) u := by
  have hK := kForm_pos hinj hz0 hz1 hu
  have hG := geomForm_nonneg hz1 e u
  have key : Qf (wFam c e z) (-c) u =
      (1 - c ^ 2) * (∑ a, ∑ b, u a * (1 / (1 - z a * z b)) * u b) +
        c ^ 2 * ∑ a, ∑ b, u a * ((1 - z a ^ e * z b ^ e) / (1 - z a * z b)) * u b := by
    unfold Qf wFam gData
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hne : 1 - z a * z b ≠ 0 := by
      have h1 := hz1 a
      have h2 := hz1 b
      rw [abs_lt] at h1 h2
      intro h
      nlinarith [h1.1, h1.2, h2.1, h2.2]
    have e1 : ∀ x : ℝ, (if x < 0 then -c else -c) = -c := fun x => by split_ifs <;> rfl
    simp only [e1]
    field_simp
    ring
  rw [key]
  have h1 : 0 < 1 - c ^ 2 := by nlinarith
  have h2 : 0 ≤ c ^ 2 := sq_nonneg c
  positivity

/-- **R2+R3 for the physical window.** Either the physical Pick form is nonnegative, or there is a
`γ ∈ (-c,1)` at which the Pick form of `gData γ` is positive semidefinite with a nonzero real
null vector. -/
theorem pick_or_singular {z : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ b, z b ≠ 0)
    (hz1 : ∀ a, |z a| < 1) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (e : ℕ) :
    (∀ u : ι → ℝ, 0 ≤ Qf (wFam c e z) 1 u) ∨
      ∃ γ, -c < γ ∧ γ < 1 ∧ (∀ u : ι → ℝ, 0 ≤ Qf (wFam c e z) γ u) ∧
        ∃ v : ι → ℝ, v ≠ 0 ∧ ∀ a, ∑ b, wFam c e z γ a b * v b = 0 := by
  refine exists_null_of_exit (wFam c e z) (fun a b => continuous_wFam hz1 a b)
    (fun γ a b => wFam_symm c e z γ a b) (by linarith) (fun u hu => ?_)
  exact seed_pos hinj hz0 hz1 hc0 hc1 e hu

end WindowFamily

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R4: the interpolant of a singular positive semidefinite Pick matrix

For nodes `z_a` (`|z_a| < 1`), data `f_a` and a real vector `v` with `W v = 0`, `W = [(1 - f_a f_b)/(1 - z_a z_b)]`
positive semidefinite, put `φ(ζ) = ∑ v_a/(1 - z_a ζ)`, `ψ(ζ) = ∑ v_a f_a/(1 - z_a ζ)`.  Then
* `φ(z_b) - f_b ψ(z_b) = (W v)_b = 0` (interpolation: `φ/ψ = f_b` at the nodes);
* `|φ(ζ)| ≤ |ψ(ζ)|` for `|ζ| < 1`;
* `|φ(ζ)| = |ψ(ζ)|` for `|ζ| = 1`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Matrix Finset CatalanMeasure.Signed CatalanMeasure.GenD.Signed CatalanMeasure.Parametric
open scoped ComplexOrder

noncomputable section

section Kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Pick matrix of data `f` at nodes `z`. -/
def pickW (z f : ι → ℝ) (a b : ι) : ℝ := (1 - f a * f b) / (1 - z a * z b)

theorem pickW_symm (z f : ι → ℝ) (a b : ι) : pickW z f a b = pickW z f b a := by
  unfold pickW
  rw [mul_comm (f a), mul_comm (z a)]

theorem wFam_eq_pickW (c : ℝ) (e : ℕ) (z : ι → ℝ) (γ : ℝ) :
    wFam c e z γ = pickW z (gData c e z γ) := rfl

/-- The simple pole `1/(1 - z_a ζ)`. -/
def kapp (z : ι → ℝ) (a : ι) (ζ : ℂ) : ℂ := 1 / (1 - (z a : ℂ) * ζ)

/-- `φ(ζ) = ∑ v_a / (1 - z_a ζ)`. -/
def phiK (z v : ι → ℝ) (ζ : ℂ) : ℂ := ∑ a, (v a : ℂ) * kapp z a ζ

/-- `ψ(ζ) = ∑ v_a f_a / (1 - z_a ζ)`. -/
def psiK (z f v : ι → ℝ) (ζ : ℂ) : ℂ := ∑ a, ((v a * f a : ℝ) : ℂ) * kapp z a ζ

theorem one_sub_ne_zero_of_norm {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    (a : ι) : (1 : ℂ) - (z a : ℂ) * ζ ≠ 0 := by
  intro h
  have h1 : (z a : ℂ) * ζ = 1 := by linear_combination -h
  have h2 : ‖(z a : ℂ) * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |z a| * ‖ζ‖ ≤ |z a| * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hz1 a
  rw [h1] at h2
  simp at h2

/-- Interpolation at the nodes: `φ(z_b) - f_b ψ(z_b) = (W v)_b`. -/
theorem phi_node {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ) (b : ι) :
    phiK z v (z b) - (f b : ℂ) * psiK z f v (z b) =
      (((∑ a, pickW z f b a * v a : ℝ)) : ℂ) := by
  unfold phiK psiK
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  have hne : (1 : ℂ) - (z a : ℂ) * (z b : ℂ) ≠ 0 := by
    have := one_sub_ne_zero_of_norm hz1 (ζ := (z b : ℂ)) (by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact (hz1 b).le) a
    exact this
  have hne' : (1 : ℂ) - (z b : ℂ) * (z a : ℂ) ≠ 0 := by
    rw [mul_comm]; exact hne
  unfold kapp pickW
  push_cast
  field_simp

/-- Pure algebra of the per-term identity inside the disc. -/
theorem alg_inside (za zb fa fb ζ ζb κa κb : ℂ) (hab : 1 - za * zb ≠ 0)
    (hk1 : κa * (1 - za * ζ) = 1) (hk2 : κb * (1 - zb * ζb) = 1) :
    (1 - ζb * ζ) * (1 - fa * fb) * κa * κb =
      ((1 - fa * fb) / (1 - za * zb)) * (1 - ((za - ζb) * κa) * ((zb - ζ) * κb)) := by
  rw [div_mul_eq_mul_div, eq_div_iff hab]
  linear_combination (1 - fa * fb) * ((κb * (1 - zb * ζb)) * hk1 + hk2)

/-- Pure algebra of the per-term identity on the circle. -/
theorem alg_circle (za zb ζ ζb κa κb : ℂ) (hζ : ζ * ζb = 1)
    (hk1 : κa * (1 - za * ζ) = 1) (hk2 : κb * (1 - zb * ζb) = 1) :
    (1 - za * zb) * κa * κb = κa + zb * ζb * κb := by
  linear_combination κa * hk2 + (zb * ζb * κb) * hk1 + (κa * κb * za * zb) * hζ

theorem kapp_mul {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (a : ι) :
    kapp z a ζ * (1 - (z a : ℂ) * ζ) = 1 := by
  unfold kapp
  exact one_div_mul_cancel (one_sub_ne_zero_of_norm hz1 hζ a)

theorem conj_kapp {z : ι → ℝ} (a : ι) (ζ : ℂ) :
    (starRingEnd ℂ) (kapp z a ζ) = 1 / (1 - (z a : ℂ) * (starRingEnd ℂ) ζ) := by
  unfold kapp
  simp [map_div₀, map_sub, map_mul, Complex.conj_ofReal]

theorem conj_kapp_mul {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (a : ι) :
    (starRingEnd ℂ) (kapp z a ζ) * (1 - (z a : ℂ) * (starRingEnd ℂ) ζ) = 1 := by
  have h := congrArg (starRingEnd ℂ) (kapp_mul hz1 hζ a)
  simpa [map_mul, map_sub, Complex.conj_ofReal] using h

theorem one_sub_mul_nodes_ne {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (a b : ι) :
    (1 : ℂ) - (z a : ℂ) * (z b : ℂ) ≠ 0 := by
  have := one_sub_ne_zero_of_norm hz1 (ζ := (z b : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact (hz1 b).le) a
  exact this

/-- `β_a = (z_a - conj ζ) κ_a`. -/
def betaK (z : ι → ℝ) (ζ : ℂ) (a : ι) : ℂ := ((z a : ℂ) - (starRingEnd ℂ) ζ) * kapp z a ζ

/-- The expansion of `|φ|² - |ψ|²` as a double sum. -/
theorem normSq_sub_expand (z f v : ι → ℝ) (ζ : ℂ) :
    ((Complex.normSq (phiK z v ζ) : ℝ) : ℂ) - ((Complex.normSq (psiK z f v ζ) : ℝ) : ℂ) =
      ∑ a, ∑ b, ((v a * v b * (1 - f a * f b) : ℝ) : ℂ) * kapp z a ζ *
        (starRingEnd ℂ) (kapp z b ζ) := by
  rw [← Complex.mul_conj, ← Complex.mul_conj]
  unfold phiK psiK
  rw [map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The identity inside the disc: `(1 - |ζ|²)(|φ|² - |ψ|²) = ∑∑ v_a v_b W_ab (1 - β_a conj β_b)`. -/
theorem normSq_sub_inside {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) :
    ((1 - Complex.normSq ζ : ℝ) : ℂ) *
        (((Complex.normSq (phiK z v ζ) : ℝ) : ℂ) - ((Complex.normSq (psiK z f v ζ) : ℝ) : ℂ)) =
      ∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) *
        (1 - betaK z ζ a * (starRingEnd ℂ) (betaK z ζ b)) := by
  rw [normSq_sub_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hk1 := kapp_mul hz1 hζ.le a
  have hk2 := conj_kapp_mul hz1 hζ.le b
  have hab := one_sub_mul_nodes_ne hz1 a b
  have key := alg_inside (z a : ℂ) (z b : ℂ) (f a : ℂ) (f b : ℂ) ζ ((starRingEnd ℂ) ζ)
    (kapp z a ζ) ((starRingEnd ℂ) (kapp z b ζ)) hab hk1 hk2
  have hnsq : ((1 - Complex.normSq ζ : ℝ) : ℂ) = 1 - (starRingEnd ℂ) ζ * ζ := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
  unfold betaK pickW
  simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_conj]
  rw [hnsq]
  push_cast
  have h2 : ((1 - starRingEnd ℂ ζ * ζ) * (1 - (f a : ℂ) * f b) * kapp z a ζ *
      (starRingEnd ℂ) (kapp z b ζ)) =
      ((1 - (f a : ℂ) * f b) / (1 - (z a : ℂ) * z b)) *
        (1 - ((z a - (starRingEnd ℂ) ζ) * kapp z a ζ) *
          ((z b - ζ) * (starRingEnd ℂ) (kapp z b ζ))) := key
  calc (1 - starRingEnd ℂ ζ * ζ) * ((v a : ℂ) * v b * (1 - (f a : ℂ) * f b) * kapp z a ζ *
          (starRingEnd ℂ) (kapp z b ζ))
      = (v a : ℂ) * v b * ((1 - starRingEnd ℂ ζ * ζ) * (1 - (f a : ℂ) * f b) * kapp z a ζ *
          (starRingEnd ℂ) (kapp z b ζ)) := by ring
    _ = _ := by rw [h2]; ring

/-- The complex Hermitian form of a real symmetric positive semidefinite form is nonnegative. -/
theorem cform_nonneg (W : ι → ι → ℝ) (hs : ∀ a b, W a b = W b a)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * W a b * u b) (x : ι → ℂ) :
    0 ≤ (∑ a, ∑ b, x a * (W a b : ℂ) * (starRingEnd ℂ) (x b)).re := by
  set y : ι → ℂ := fun b => (starRingEnd ℂ) (x b) with hy
  have hsM : ∀ a b, (Matrix.of W) a b = (Matrix.of W) b a := fun a b => hs a b
  have h2 := form_map_ofReal (Matrix.of W) hsM y
  have e1 : ∑ a, ∑ b, x a * (W a b : ℂ) * (starRingEnd ℂ) (x b) =
      star y ⬝ᵥ (((Matrix.of W).map (fun r : ℝ => (r : ℂ))) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Pi.star_apply, hy,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [e1, h2]
  rw [Complex.ofReal_re]
  have h3 := hpsd (fun a => (y a).re)
  have h4 := hpsd (fun a => (y a).im)
  simp only [Matrix.of_apply]
  linarith

/-- Inside the disc, for a kernel vector: `(1 - |ζ|²)(|φ|² - |ψ|²) = -∑∑ x_a W_ab conj x_b`,
`x_a = v_a β_a`. -/
theorem normSq_sub_inside_neg {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ)
    (hv : ∀ a, v a * ∑ b, pickW z f a b * v b = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ((1 - Complex.normSq ζ : ℝ) : ℂ) *
        (((Complex.normSq (phiK z v ζ) : ℝ) : ℂ) - ((Complex.normSq (psiK z f v ζ) : ℝ) : ℂ)) =
      -∑ a, ∑ b, ((v a : ℂ) * betaK z ζ a) * (pickW z f a b : ℂ) *
          (starRingEnd ℂ) ((v b : ℂ) * betaK z ζ b) := by
  have key := normSq_sub_inside hz1 f v hζ
  have hsplit : ∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) *
        (1 - betaK z ζ a * (starRingEnd ℂ) (betaK z ζ b)) =
      (∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ)) -
        ∑ a, ∑ b, ((v a : ℂ) * betaK z ζ a) * (pickW z f a b : ℂ) *
          (starRingEnd ℂ) ((v b : ℂ) * betaK z ζ b) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hzero : ∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) = 0 := by
    have h1 : ∀ a, ∑ b, v a * v b * pickW z f a b = v a * ∑ b, pickW z f a b * v b := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have h2 : ∑ a, ∑ b, v a * v b * pickW z f a b = 0 := by
      simp only [h1, hv, Finset.sum_const_zero]
    have := congrArg (fun r : ℝ => (r : ℂ)) h2
    simpa [Complex.ofReal_sum] using this
  rw [hsplit, hzero, zero_sub] at key
  exact key

/-- **Inside the disc**, for a kernel vector of a positive semidefinite Pick matrix:
`|φ(ζ)| ≤ |ψ(ζ)|`. -/
theorem normSq_phi_le_psi {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * pickW z f a b * u b)
    (hv : ∀ a, v a * ∑ b, pickW z f a b * v b = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Complex.normSq (phiK z v ζ) ≤ Complex.normSq (psiK z f v ζ) := by
  have key := normSq_sub_inside_neg hz1 f v hv hζ
  have hS := cform_nonneg (pickW z f) (pickW_symm z f) hpsd (fun a => (v a : ℂ) * betaK z ζ a)
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul, Complex.neg_re] at hre
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  have hpos : 0 < 1 - Complex.normSq ζ := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  have hle : (1 - Complex.normSq ζ) * (Complex.normSq (phiK z v ζ) -
      Complex.normSq (psiK z f v ζ)) ≤ 0 := by
    rw [hre]; linarith
  have h3 : Complex.normSq (phiK z v ζ) - Complex.normSq (psiK z f v ζ) ≤ 0 := by
    by_contra hh
    push_neg at hh
    have := mul_pos hpos hh
    linarith
  linarith

/-- **On the circle**, for a kernel vector: `|φ(ζ)| = |ψ(ζ)|`. -/
theorem normSq_phi_eq_psi {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ)
    (hv : ∀ a, v a * ∑ b, pickW z f a b * v b = 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    Complex.normSq (phiK z v ζ) = Complex.normSq (psiK z f v ζ) := by
  have hexp := normSq_sub_expand z f v ζ
  have hζc : ζ * (starRingEnd ℂ) ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
  have hterm : ∀ a b, ((v a * v b * (1 - f a * f b) : ℝ) : ℂ) * kapp z a ζ *
        (starRingEnd ℂ) (kapp z b ζ) =
      ((v a * v b * pickW z f a b : ℝ) : ℂ) * kapp z a ζ +
        ((v a * v b * pickW z f a b : ℝ) : ℂ) * ((z b : ℂ) * (starRingEnd ℂ) ζ *
          (starRingEnd ℂ) (kapp z b ζ)) := by
    intro a b
    have hk1 := kapp_mul hz1 hζ.le a
    have hk2 := conj_kapp_mul hz1 hζ.le b
    have hab := one_sub_mul_nodes_ne hz1 a b
    have key := alg_circle (z a : ℂ) (z b : ℂ) ζ ((starRingEnd ℂ) ζ) (kapp z a ζ)
      ((starRingEnd ℂ) (kapp z b ζ)) hζc hk1 hk2
    have hW : (((1 - f a * f b : ℝ)) : ℂ) = (pickW z f a b : ℂ) * (1 - (z a : ℂ) * z b) := by
      unfold pickW
      push_cast
      field_simp
    have e1 : ((v a * v b * (1 - f a * f b) : ℝ) : ℂ) =
        ((v a * v b : ℝ) : ℂ) * (pickW z f a b : ℂ) * (1 - (z a : ℂ) * z b) := by
      push_cast at hW ⊢
      rw [mul_assoc, hW]; ring
    have e2 : ((v a * v b * pickW z f a b : ℝ) : ℂ) =
        ((v a * v b : ℝ) : ℂ) * (pickW z f a b : ℂ) := by push_cast; ring
    rw [e1, e2]
    calc ((v a * v b : ℝ) : ℂ) * (pickW z f a b : ℂ) * (1 - (z a : ℂ) * z b) * kapp z a ζ *
          (starRingEnd ℂ) (kapp z b ζ)
        = ((v a * v b : ℝ) : ℂ) * (pickW z f a b : ℂ) *
            ((1 - (z a : ℂ) * z b) * kapp z a ζ * (starRingEnd ℂ) (kapp z b ζ)) := by ring
      _ = _ := by rw [key]; ring
  have hsum : ∑ a, ∑ b, ((v a * v b * (1 - f a * f b) : ℝ) : ℂ) * kapp z a ζ *
        (starRingEnd ℂ) (kapp z b ζ) = 0 := by
    simp only [hterm, Finset.sum_add_distrib]
    have h1 : ∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) * kapp z a ζ = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ∑ b, v a * v b * pickW z f a b = v a * ∑ b, pickW z f a b * v b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
      have h0 : ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) = 0 := by
        have := congrArg (fun r : ℝ => (r : ℂ)) (this.trans (hv a))
        simpa [Complex.ofReal_sum] using this
      rw [← Finset.sum_mul, h0, zero_mul]
    have h2 : ∑ a, ∑ b, ((v a * v b * pickW z f a b : ℝ) : ℂ) * ((z b : ℂ) *
        (starRingEnd ℂ) ζ * (starRingEnd ℂ) (kapp z b ζ)) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : ∑ a, v a * v b * pickW z f a b = v b * ∑ a, pickW z f b a * v a := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [pickW_symm z f b a]; ring
      have h0 : ∑ a, ((v a * v b * pickW z f a b : ℝ) : ℂ) = 0 := by
        have := congrArg (fun r : ℝ => (r : ℂ)) (this.trans (hv b))
        simpa [Complex.ofReal_sum] using this
      rw [← Finset.sum_mul, h0, zero_mul]
    rw [h1, h2, add_zero]
  rw [hsum] at hexp
  have := sub_eq_zero.mp hexp
  exact_mod_cast this

end Kernel

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5a: minimal singular sub-collections

If a positive semidefinite `W` has a kernel vector, some sub-collection `S` of the nodes is minimal
singular: it carries a kernel vector and no proper subset does.  On such an `S` the kernel vector has no
zero entry and `φ`, `ψ` have no common zero at a node of `S`.  So the reduced quotient `φ/ψ` (common
factors removed) still interpolates at every node of `S`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Matrix Finset CatalanMeasure.Signed CatalanMeasure.GenD.Signed CatalanMeasure.Parametric
open scoped ComplexOrder

noncomputable section

section Minimal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `S` carries a nonzero vector supported on `S` with `(W v)_c = 0` for `c ∈ S`. -/
def HasKer (W : ι → ι → ℝ) (S : Finset ι) : Prop :=
  ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ a, a ∉ S → v a = 0) ∧ ∀ c ∈ S, ∑ b, W c b * v b = 0

/-- `S` is minimal singular: it carries a kernel vector and no proper subset does. -/
def MinKer (W : ι → ι → ℝ) (S : Finset ι) : Prop :=
  HasKer W S ∧ ∀ T, T ⊂ S → ¬ HasKer W T

theorem exists_minKer (W : ι → ι → ℝ) (h : HasKer W Finset.univ) :
    ∃ S, MinKer W S := by
  classical
  have hex : ∃ n, ∃ S : Finset ι, S.card = n ∧ HasKer W S := ⟨_, _, rfl, h⟩
  obtain ⟨S, hSc, hS⟩ := Nat.find_spec hex
  refine ⟨S, hS, fun T hT hTk => ?_⟩
  have h1 : T.card < S.card := Finset.card_lt_card hT
  have h2 : Nat.find hex ≤ T.card := Nat.find_min' hex ⟨T, rfl, hTk⟩
  omega

/-- The kernel vector of a minimal singular set has no zero entry on `S`. -/
theorem minKer_entries_ne_zero {W : ι → ι → ℝ} {S : Finset ι} (hS : MinKer W S) {v : ι → ℝ}
    (hv0 : v ≠ 0) (hvs : ∀ a, a ∉ S → v a = 0) (hvk : ∀ c ∈ S, ∑ b, W c b * v b = 0) :
    ∀ a ∈ S, v a ≠ 0 := by
  intro a haS hva
  apply hS.2 (S.erase a) (Finset.erase_ssubset haS)
  refine ⟨v, hv0, fun b hb => ?_, fun c hc => hvk c (Finset.mem_of_mem_erase hc)⟩
  by_cases hba : b = a
  · rw [hba]; exact hva
  · exact hvs b (fun hbS => hb (Finset.mem_erase.mpr ⟨hba, hbS⟩))

/-- On a minimal singular set, no nonzero vector supported on a proper subset is a kernel vector of
the restricted matrix. -/
theorem minKer_proper {W : ι → ι → ℝ} {S : Finset ι} (hS : MinKer W S) {T : Finset ι}
    (hT : T ⊂ S) {u : ι → ℝ} (hus : ∀ a, a ∉ T → u a = 0)
    (huk : ∀ c ∈ T, ∑ b, W c b * u b = 0) : u = 0 := by
  by_contra hne
  exact hS.2 T hT ⟨u, hne, hus, huk⟩

/-- The real part of the Hermitian form of a real symmetric matrix. -/
theorem cform_re_eq (W : ι → ι → ℝ) (hs : ∀ a b, W a b = W b a) (x : ι → ℂ) :
    (∑ a, ∑ b, x a * (W a b : ℂ) * (starRingEnd ℂ) (x b)).re =
      (∑ a, ∑ b, (x a).re * W a b * (x b).re) + ∑ a, ∑ b, (x a).im * W a b * (x b).im := by
  set y : ι → ℂ := fun b => (starRingEnd ℂ) (x b) with hy
  have hsM : ∀ a b, (Matrix.of W) a b = (Matrix.of W) b a := fun a b => hs a b
  have h2 := form_map_ofReal (Matrix.of W) hsM y
  have e1 : ∑ a, ∑ b, x a * (W a b : ℂ) * (starRingEnd ℂ) (x b) =
      star y ⬝ᵥ (((Matrix.of W).map (fun r : ℝ => (r : ℂ))) *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Pi.star_apply, hy,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring
  rw [e1, h2, Complex.ofReal_re]
  simp only [Matrix.of_apply, hy, Complex.conj_re, Complex.conj_im, neg_mul, mul_neg, neg_neg]

/-- A vanishing Hermitian form of a positive semidefinite real form gives a complex kernel vector. -/
theorem cform_zero_kernel (W : ι → ι → ℝ) (hs : ∀ a b, W a b = W b a)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * W a b * u b) (x : ι → ℂ)
    (h0 : ∑ a, ∑ b, x a * (W a b : ℂ) * (starRingEnd ℂ) (x b) = 0) :
    ∀ a, ∑ b, (W a b : ℂ) * x b = 0 := by
  have hre := congrArg Complex.re h0
  rw [cform_re_eq W hs x, Complex.zero_re] at hre
  have h1 := hpsd (fun a => (x a).re)
  have h2 := hpsd (fun a => (x a).im)
  have e1 : ∑ a, ∑ b, (x a).re * W a b * (x b).re = 0 := by linarith
  have e2 : ∑ a, ∑ b, (x a).im * W a b * (x b).im = 0 := by linarith
  intro a
  have k1 := null_of_psd W hs hpsd (fun a => (x a).re) e1 a
  have k2 := null_of_psd W hs hpsd (fun a => (x a).im) e2 a
  have : ∑ b, (W a b : ℂ) * x b = ((∑ b, W a b * (x b).re : ℝ) : ℂ) +
      Complex.I * ((∑ b, W a b * (x b).im : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    conv_lhs => rw [← Complex.re_add_im (x b)]
    ring
  rw [this, k1, k2]
  simp

/-- A common zero of `φ` and `ψ` inside the disc gives a complex kernel vector `v_b β_b(ζ)`. -/
theorem common_zero_kernel {z : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (f v : ι → ℝ)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * pickW z f a b * u b)
    (hv : ∀ a, v a * ∑ b, pickW z f a b * v b = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1)
    (hφ : phiK z v ζ = 0) (hψ : psiK z f v ζ = 0) :
    ∀ a, ∑ b, (pickW z f a b : ℂ) * ((v b : ℂ) * betaK z ζ b) = 0 := by
  have key := normSq_sub_inside_neg hz1 f v hv hζ
  rw [hφ, hψ] at key
  simp only [map_zero, Complex.normSq_zero, Complex.ofReal_zero, sub_zero, mul_zero] at key
  have h0 : ∑ a, ∑ b, ((v a : ℂ) * betaK z ζ a) * (pickW z f a b : ℂ) *
      (starRingEnd ℂ) ((v b : ℂ) * betaK z ζ b) = 0 := by
    have := neg_eq_zero.mp key.symm
    exact this
  exact cform_zero_kernel (pickW z f) (pickW_symm z f) hpsd (fun a => (v a : ℂ) * betaK z ζ a) h0

/-- On a minimal singular set the kernel is one dimensional. -/
theorem minKer_ker_unique {W : ι → ι → ℝ} {S : Finset ι} (hS : MinKer W S) {v u : ι → ℝ}
    (hv0 : v ≠ 0) (hvs : ∀ a, a ∉ S → v a = 0) (hvk : ∀ c ∈ S, ∑ b, W c b * v b = 0)
    (hus : ∀ a, a ∉ S → u a = 0) (huk : ∀ c ∈ S, ∑ b, W c b * u b = 0) :
    ∃ κ : ℝ, ∀ b, u b = κ * v b := by
  have hvne := minKer_entries_ne_zero hS hv0 hvs hvk
  obtain ⟨a, ha⟩ : ∃ a, a ∈ S := by
    by_contra hne
    push_neg at hne
    apply hv0
    funext b
    exact hvs b (hne b)
  refine ⟨u a / v a, fun b => ?_⟩
  set w : ι → ℝ := fun b => u b - (u a / v a) * v b with hw
  have hws : ∀ b, b ∉ S.erase a → w b = 0 := by
    intro b hb
    by_cases hba : b = a
    · rw [hba]; simp only [hw]; field_simp [hvne a ha]; ring
    · have hbS : b ∉ S := fun h => hb (Finset.mem_erase.mpr ⟨hba, h⟩)
      simp [hw, hus b hbS, hvs b hbS]
  have hwk : ∀ c ∈ S.erase a, ∑ b, W c b * w b = 0 := by
    intro c hc
    have hcS := Finset.mem_of_mem_erase hc
    have : ∑ b, W c b * w b = ∑ b, W c b * u b - (u a / v a) * ∑ b, W c b * v b := by
      simp only [hw, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun b _ => by ring
    rw [this, huk c hcS, hvk c hcS]; ring
  have := minKer_proper hS (Finset.erase_ssubset ha) hws hwk
  have h2 := congrFun this b
  simp only [hw, Pi.zero_apply] at h2
  linarith

/-- `S` has at least two elements. -/
theorem minKer_two {z f : ι → ℝ} (hz1 : ∀ a, |z a| < 1) (hf : ∀ a, |f a| < 1) {S : Finset ι}
    (hS : MinKer (pickW z f) S) {v : ι → ℝ} (hv0 : v ≠ 0) (hvs : ∀ a, a ∉ S → v a = 0)
    (hvk : ∀ c ∈ S, ∑ b, pickW z f c b * v b = 0) : ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  have hvne := minKer_entries_ne_zero hS hv0 hvs hvk
  obtain ⟨a, ha⟩ : ∃ a, a ∈ S := by
    by_contra hne
    push_neg at hne
    apply hv0
    funext b
    exact hvs b (hne b)
  by_contra hcon
  push_neg at hcon
  have hsupp : ∀ b, b ≠ a → v b = 0 := by
    intro b hb
    apply hvs b
    intro hbS
    exact hb (hcon b hbS a ha)
  have hva := hvk a ha
  have hsum : ∑ b, pickW z f a b * v b = pickW z f a a * v a := by
    rw [Finset.sum_eq_single a]
    · intro b _ hb; rw [hsupp b hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hsum] at hva
  have hWa : 0 < pickW z f a a := by
    unfold pickW
    have h1 : 0 < 1 - f a * f a := by
      have := hf a
      rw [abs_lt] at this
      nlinarith [this.1, this.2]
    have h2 : 0 < 1 - z a * z a := by
      have := hz1 a
      rw [abs_lt] at this
      nlinarith [this.1, this.2]
    positivity
  exact absurd hva (mul_ne_zero hWa.ne' (hvne a ha))

/-- On a minimal singular set `φ` and `ψ` have no common zero in the open unit disc. -/
theorem no_common_zero_disc {z : ι → ℝ} (hinj : Function.Injective z) (hz1 : ∀ a, |z a| < 1)
    (f v : ι → ℝ) (hf : ∀ a, |f a| < 1)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * pickW z f a b * u b)
    {S : Finset ι} (hS : MinKer (pickW z f) S) (hv0 : v ≠ 0) (hvs : ∀ a, a ∉ S → v a = 0)
    (hvk : ∀ c ∈ S, ∑ b, pickW z f c b * v b = 0) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    ¬ (phiK z v ζ = 0 ∧ psiK z f v ζ = 0) := by
  rintro ⟨hφ, hψ⟩
  have hvall : ∀ c, v c * ∑ b, pickW z f c b * v b = 0 := by
    intro c
    by_cases hc : c ∈ S
    · rw [hvk c hc, mul_zero]
    · rw [hvs c hc, zero_mul]
  have hker := common_zero_kernel hz1 f v hpsd hvall hζ hφ hψ
  have hvne := minKer_entries_ne_zero hS hv0 hvs hvk
  set x : ι → ℂ := fun b => (v b : ℂ) * betaK z ζ b with hx
  have hre : ∀ c, ∑ b, pickW z f c b * (x b).re = 0 := by
    intro c
    have := congrArg Complex.re (hker c)
    simpa [Complex.re_sum, hx] using this
  have him : ∀ c, ∑ b, pickW z f c b * (x b).im = 0 := by
    intro c
    have := congrArg Complex.im (hker c)
    simpa [Complex.im_sum, hx] using this
  have hxs : ∀ a, a ∉ S → x a = 0 := by
    intro a ha; simp [hx, hvs a ha]
  obtain ⟨κ1, hκ1⟩ := minKer_ker_unique hS hv0 hvs hvk (u := fun b => (x b).re)
    (fun a ha => by simp [hxs a ha]) (fun c _ => hre c)
  obtain ⟨κ2, hκ2⟩ := minKer_ker_unique hS hv0 hvs hvk (u := fun b => (x b).im)
    (fun a ha => by simp [hxs a ha]) (fun c _ => him c)
  obtain ⟨a, ha, b, hb, hab⟩ := minKer_two hz1 hf hS hv0 hvs hvk
  have hxa : x a = ((κ1 : ℂ) + (κ2 : ℂ) * Complex.I) * (v a : ℂ) := by
    apply Complex.ext <;> simp [hκ1 a, hκ2 a] <;> ring
  have hxb : x b = ((κ1 : ℂ) + (κ2 : ℂ) * Complex.I) * (v b : ℂ) := by
    apply Complex.ext <;> simp [hκ1 b, hκ2 b] <;> ring
  have hβa : betaK z ζ a = (κ1 : ℂ) + (κ2 : ℂ) * Complex.I := by
    have h1 : (v a : ℂ) * betaK z ζ a = ((κ1 : ℂ) + (κ2 : ℂ) * Complex.I) * (v a : ℂ) := hxa
    have h2 : (v a : ℂ) ≠ 0 := by exact_mod_cast hvne a ha
    apply mul_left_cancel₀ h2
    rw [h1]; ring
  have hβb : betaK z ζ b = (κ1 : ℂ) + (κ2 : ℂ) * Complex.I := by
    have h1 : (v b : ℂ) * betaK z ζ b = ((κ1 : ℂ) + (κ2 : ℂ) * Complex.I) * (v b : ℂ) := hxb
    have h2 : (v b : ℂ) ≠ 0 := by exact_mod_cast hvne b hb
    apply mul_left_cancel₀ h2
    rw [h1]; ring
  have heq : betaK z ζ a = betaK z ζ b := by rw [hβa, hβb]
  have hna := one_sub_ne_zero_of_norm hz1 hζ.le a
  have hnb := one_sub_ne_zero_of_norm hz1 hζ.le b
  unfold betaK kapp at heq
  rw [mul_one_div, mul_one_div, div_eq_div_iff hna hnb] at heq
  have h3 : ((z a : ℂ) - (z b : ℂ)) * (1 - (starRingEnd ℂ) ζ * ζ) = 0 := by
    linear_combination heq
  have h4 : (1 : ℂ) - (starRingEnd ℂ) ζ * ζ ≠ 0 := by
    have : ((1 - Complex.normSq ζ : ℝ) : ℂ) = 1 - (starRingEnd ℂ) ζ * ζ := by
      push_cast; rw [Complex.normSq_eq_conj_mul_self]
    rw [← this]
    have hpos : 0 < 1 - Complex.normSq ζ := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
    exact_mod_cast hpos.ne'
  rcases mul_eq_zero.mp h3 with h | h
  · exact hab (hinj (by exact_mod_cast sub_eq_zero.mp h))
  · exact h4 h

end Minimal

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5b: unimodular real rational functions are Blaschke quotients

For coprime real polynomials `A`, `B` with `A A* X^{deg B} = B B* X^{deg A}` (the polynomial form of
`|A| = |B|` on the unit circle) and `B ≠ 0` on the open unit disc we prove `A = X^s P`,
`B = ε P*` with `ε = ±1`, `P(0) ≠ 0` and all roots of `P` in the open disc.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial

noncomputable section

/-- Unit circle points `(1 + t i)/(1 - t i)`. -/
def cayleyPt (t : ℝ) : ℂ := (1 + t * Complex.I) / (1 - t * Complex.I)

theorem norm_cayleyPt (t : ℝ) : ‖cayleyPt t‖ = 1 := by
  unfold cayleyPt
  rw [norm_div]
  have h1 : ‖(1 : ℂ) + t * Complex.I‖ = ‖(1 : ℂ) - t * Complex.I‖ := by
    rw [← Complex.norm_conj]
    congr 1
    simp [map_add, map_mul, Complex.conj_ofReal]
    ring
  have h2 : ‖(1 : ℂ) - t * Complex.I‖ ≠ 0 := by
    intro h
    have := norm_eq_zero.mp h
    have h3 := congrArg Complex.re this
    simp at h3
  rw [h1]
  exact div_self h2

theorem cayleyPt_injective : Function.Injective cayleyPt := by
  intro t t' h
  unfold cayleyPt at h
  have h1 : (1 : ℂ) - t * Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have h2 : (1 : ℂ) - t' * Complex.I ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  rw [div_eq_div_iff h1 h2] at h
  have h3 : (2 * Complex.I) * ((t : ℂ) - t') = 0 := by linear_combination h
  have h4 : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have h5 : (t : ℂ) - t' = 0 := (mul_eq_zero.mp h3).resolve_left h4
  exact_mod_cast sub_eq_zero.mp h5

theorem circle_infinite : {ζ : ℂ | ‖ζ‖ = 1}.Infinite :=
  Set.infinite_of_injective_forall_mem cayleyPt_injective norm_cayleyPt

/-- On the unit circle `f* (ζ) = ζ^{deg f} conj (f ζ)`. -/
theorem reverse_circle (f : ℝ[X]) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    aeval ζ f.reverse = ζ ^ f.natDegree * (starRingEnd ℂ) (aeval ζ f) := by
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h] at hζ; simp at hζ
  have hcz : (starRingEnd ℂ) ζ * ζ = 1 := by
    have := Complex.normSq_eq_conj_mul_self (z := ζ)
    rw [Complex.normSq_eq_norm_sq, hζ] at this
    simpa using this.symm
  have hinvz_dummy : True := trivial
  haveI hinvz : Invertible ((starRingEnd ℂ) ζ) :=
    invertibleOfNonzero (by simpa using hζ0)
  have hrec : ⅟((starRingEnd ℂ) ζ) = ζ := by
    exact invOf_eq_right_inv hcz
  have h1 := eval₂_reverse_mul_pow (algebraMap ℝ ℂ) ((starRingEnd ℂ) ζ) f
  rw [hrec] at h1
  have e1 : eval₂ (algebraMap ℝ ℂ) ((starRingEnd ℂ) ζ) f = (starRingEnd ℂ) (aeval ζ f) := by
    rw [← Polynomial.aeval_def]
    exact aeval_conj f ζ
  rw [e1] at h1
  have h2 : aeval ζ f.reverse * ((starRingEnd ℂ) ζ) ^ f.natDegree = (starRingEnd ℂ) (aeval ζ f) := by
    rw [← h1, Polynomial.aeval_def]
  calc aeval ζ f.reverse = aeval ζ f.reverse * ((starRingEnd ℂ) ζ * ζ) ^ f.natDegree := by
        rw [hcz, one_pow, mul_one]
    _ = (aeval ζ f.reverse * ((starRingEnd ℂ) ζ) ^ f.natDegree) * ζ ^ f.natDegree := by
        rw [mul_pow]; ring
    _ = _ := by rw [h2]; ring

/-- On the unit circle `f f* = ζ^{deg f} |f|²`. -/
theorem mul_reverse_circle (f : ℝ[X]) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    aeval ζ (f * f.reverse) = ζ ^ f.natDegree * ((‖aeval ζ f‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, reverse_circle f hζ]
  have : aeval ζ f * (starRingEnd ℂ) (aeval ζ f) = ((‖aeval ζ f‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc aeval ζ f * (ζ ^ f.natDegree * (starRingEnd ℂ) (aeval ζ f))
      = ζ ^ f.natDegree * (aeval ζ f * (starRingEnd ℂ) (aeval ζ f)) := by ring
    _ = _ := by rw [this]

/-- **Polynomial form of `|f| = |g|` on the circle.** -/
theorem poly_identity_of_circle (f g : ℝ[X]) (h : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖aeval ζ f‖ = ‖aeval ζ g‖) :
    f * f.reverse * X ^ g.natDegree = g * g.reverse * X ^ f.natDegree := by
  have hinj : Function.Injective (Polynomial.map (algebraMap ℝ ℂ)) :=
    Polynomial.map_injective _ (RingHom.injective _)
  apply hinj
  apply Polynomial.eq_of_infinite_eval_eq
  refine circle_infinite.mono fun ζ hζ => ?_
  have hζ' : ‖ζ‖ = 1 := hζ
  simp only [Set.mem_setOf_eq]
  have e : ∀ p : ℝ[X], eval ζ (p.map (algebraMap ℝ ℂ)) = aeval ζ p := by
    intro p; rw [Polynomial.aeval_def, Polynomial.eval_map]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, e]
  have h1 := mul_reverse_circle f hζ'
  have h2 := mul_reverse_circle g hζ'
  rw [map_mul] at h1 h2
  rw [h1, h2, h ζ hζ']
  ring

/-- The evaluation of the identity at a circle point gives `‖A‖ = ‖B‖`. -/
theorem norm_eq_of_identity {A B : ℝ[X]}
    (hid : A * A.reverse * X ^ B.natDegree = B * B.reverse * X ^ A.natDegree) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) : ‖aeval ζ A‖ = ‖aeval ζ B‖ := by
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h] at hζ; simp at hζ
  have h := congrArg (aeval ζ) hid
  simp only [map_mul, map_pow, aeval_X] at h
  have h1 := mul_reverse_circle A hζ
  have h2 := mul_reverse_circle B hζ
  rw [map_mul] at h1 h2
  rw [h1, h2] at h
  have h3 : ζ ^ (A.natDegree + B.natDegree) *
      (((‖aeval ζ A‖ ^ 2 : ℝ) : ℂ) - ((‖aeval ζ B‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    rw [pow_add]; linear_combination h
  have h4 : ζ ^ (A.natDegree + B.natDegree) ≠ 0 := pow_ne_zero _ hζ0
  have h5 := (mul_eq_zero.mp h3).resolve_left h4
  have h6 : ‖aeval ζ A‖ ^ 2 = ‖aeval ζ B‖ ^ 2 := by
    have := sub_eq_zero.mp h5
    exact_mod_cast this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h6

/-- **Blaschke form.**  Coprime real polynomials `A`, `B` with `|A| = |B|` on the circle (polynomial
identity) and `B ≠ 0` in the open disc are `A = X^s P`, `B = ε P*` with `ε = ±1`, `P(0) ≠ 0` and all
roots of `P` in the open disc. -/
theorem blaschke_form (A B : ℝ[X]) (hA : A ≠ 0) (hB0 : B ≠ 0) (hcop : IsCoprime A B)
    (hid : A * A.reverse * X ^ B.natDegree = B * B.reverse * X ^ A.natDegree)
    (hBd : ∀ ζ : ℂ, ‖ζ‖ < 1 → aeval ζ B ≠ 0) :
    ∃ (s : ℕ) (P : ℝ[X]) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ P.coeff 0 ≠ 0 ∧ A = X ^ s * P ∧
      B = C ε * P.reverse ∧ ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1 := by
  have hb0 : B.coeff 0 ≠ 0 := by
    have := hBd 0 (by simp)
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at this
    intro h
    apply this
    rw [h]; simp
  obtain ⟨P, hAP, hPX⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd A hA 0
  set s := Polynomial.rootMultiplicity 0 A with hs
  simp only [map_zero, sub_zero] at hAP hPX
  have hP0 : P.coeff 0 ≠ 0 := fun h => hPX (Polynomial.X_dvd_iff.mpr h)
  have hPne : P ≠ 0 := by rintro rfl; simp at hP0
  have hArev : A.reverse = P.reverse := by rw [hAP]; exact reverse_X_pow_mul P s
  have hXB : IsCoprime X B :=
    (Irreducible.coprime_iff_not_dvd Polynomial.irreducible_X).mpr
      (fun h => hb0 (Polynomial.X_dvd_iff.mp h))
  have hXP : IsCoprime X P :=
    (Irreducible.coprime_iff_not_dvd Polynomial.irreducible_X).mpr
      (fun h => hP0 (Polynomial.X_dvd_iff.mp h))
  -- B ∣ A.reverse
  have hdvd1 : B ∣ A * (A.reverse * X ^ B.natDegree) := by
    have : A * (A.reverse * X ^ B.natDegree) = B * (B.reverse * X ^ A.natDegree) := by
      rw [← mul_assoc, hid]; ring
    rw [this]; exact dvd_mul_right _ _
  have hBA : B ∣ A.reverse * X ^ B.natDegree := hcop.symm.dvd_of_dvd_mul_left hdvd1
  have hBA' : B ∣ A.reverse := (hXB.pow_left.symm).dvd_of_dvd_mul_right hBA
  -- P ∣ B.reverse
  have hdvd2 : A ∣ B * (B.reverse * X ^ A.natDegree) := by
    have : B * (B.reverse * X ^ A.natDegree) = A * (A.reverse * X ^ B.natDegree) := by
      rw [← mul_assoc, ← hid]; ring
    rw [this]; exact dvd_mul_right _ _
  have hAB : A ∣ B.reverse * X ^ A.natDegree := hcop.dvd_of_dvd_mul_left hdvd2
  have hPA : P ∣ A := ⟨X ^ s, by rw [hAP]; ring⟩
  have hPB : P ∣ B.reverse * X ^ A.natDegree := hPA.trans hAB
  have hPB' : P ∣ B.reverse := (hXP.pow_left.symm).dvd_of_dvd_mul_right hPB
  -- degrees
  have hPrev_ne : P.reverse ≠ 0 := fun h => hPne (Polynomial.reverse_eq_zero.mp h)
  have hBrev_ne : B.reverse ≠ 0 := fun h => hB0 (Polynomial.reverse_eq_zero.mp h)
  have hdegP : P.reverse.natDegree = P.natDegree := by
    rw [Polynomial.reverse_natDegree, (Polynomial.natTrailingDegree_eq_zero).mpr (Or.inr hP0)]
    simp
  have hdegB : B.reverse.natDegree = B.natDegree := by
    rw [Polynomial.reverse_natDegree, (Polynomial.natTrailingDegree_eq_zero).mpr (Or.inr hb0)]
    simp
  have hle1 : B.natDegree ≤ P.natDegree := by
    have := Polynomial.natDegree_le_of_dvd hBA' (by rw [hArev]; exact hPrev_ne)
    rw [hArev, hdegP] at this; exact this
  have hle2 : P.natDegree ≤ B.natDegree := by
    have := Polynomial.natDegree_le_of_dvd hPB' hBrev_ne
    rw [hdegB] at this; exact this
  have hdeg : B.natDegree = P.natDegree := le_antisymm hle1 hle2
  -- P.reverse = B * C λ
  obtain ⟨w, hw⟩ := hBA'
  rw [hArev] at hw
  have hwne : w ≠ 0 := by
    rintro rfl; apply hPrev_ne; rw [hw]; simp
  have hwdeg : w.natDegree = 0 := by
    have := congrArg Polynomial.natDegree hw
    rw [hdegP, Polynomial.natDegree_mul hB0 hwne, hdeg] at this
    omega
  have hwC : w = C (w.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hwdeg
  have hl : w.coeff 0 ≠ 0 := by
    intro h; apply hwne; rw [hwC, h]; simp
  set ε : ℝ := (w.coeff 0)⁻¹ with hε
  have hBε : B = C ε * P.reverse := by
    rw [hw, hwC]
    have : C ε * (B * C (w.coeff 0)) = B * C (ε * w.coeff 0) := by
      rw [C_mul]; ring
    rw [this, hε, inv_mul_cancel₀ hl]; simp
  -- ε = ±1
  have hnorm1 : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖aeval ζ A‖ = ‖aeval ζ B‖ := fun ζ hζ =>
    norm_eq_of_identity hid hζ
  obtain ⟨ζ, hζ, hPζ⟩ : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ aeval ζ P ≠ 0 := by
    have hmap : P.map (algebraMap ℝ ℂ) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hPne
    have hfin : ((P.map (algebraMap ℝ ℂ)).roots.toFinset : Set ℂ).Finite :=
      Finset.finite_toSet _
    obtain ⟨ζ, hζmem, hζnot⟩ := (circle_infinite.diff hfin).nonempty
    refine ⟨ζ, hζmem, fun h => hζnot ?_⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hmap, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact h
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
  have hAζ : ‖aeval ζ A‖ = ‖aeval ζ P‖ := by
    rw [hAP]; simp [norm_pow, hζ]
  have hBζ : ‖aeval ζ B‖ = |ε| * ‖aeval ζ P‖ := by
    rw [hBε, map_mul, aeval_C, reverse_circle P hζ, norm_mul, norm_mul, norm_pow, hζ]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hε1 : |ε| = 1 := by
    have h1 := hnorm1 ζ hζ
    rw [hAζ, hBζ] at h1
    have hPpos : 0 < ‖aeval ζ P‖ := norm_pos_iff.mpr hPζ
    have : (1 - |ε|) * ‖aeval ζ P‖ = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hPpos.ne'
  have hε2 : ε = 1 ∨ ε = -1 := by
    rcases abs_cases ε with ⟨h, _⟩ | ⟨h, _⟩
    · left; rw [h] at hε1; exact hε1
    · right; rw [h] at hε1; linarith
  refine ⟨s, P, ε, hε2, hP0, hAP, hBε, ?_⟩
  -- roots of P in the open disc
  intro ρ hρ
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hρ
    apply hP0
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at hρ
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp hρ
  haveI : Invertible ρ := invertibleOfNonzero hρ0
  have hBρ : aeval ρ⁻¹ B = 0 := by
    rw [hBε, map_mul, aeval_C]
    have h1 := (eval₂_reverse_eq_zero_iff (algebraMap ℝ ℂ) ρ P).mpr
      (by rw [← Polynomial.aeval_def]; exact hρ)
    rw [invOf_eq_inv] at h1
    rw [Polynomial.aeval_def, h1, mul_zero]
  by_contra hge
  push_neg at hge
  have hinv : ‖ρ⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ hge
  rcases hinv.lt_or_eq with hlt | heq
  · exact hBd _ hlt hBρ
  · -- on the circle: A vanishes at `ρ⁻¹`, contradicting coprimality
    have hA0 : aeval ρ⁻¹ A = 0 := by
      have h := congrArg (aeval ρ⁻¹) hid
      simp only [map_mul, map_pow, aeval_X, hBρ, zero_mul] at h
      have hζ0' : ρ⁻¹ ≠ 0 := inv_ne_zero hρ0
      have h2 := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hζ0')
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · rw [reverse_circle A heq, mul_eq_zero] at h3
        rcases h3 with h4 | h4
        · exact absurd h4 (pow_ne_zero _ hζ0')
        · simpa using h4
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (aeval ρ⁻¹) huv
    simp only [map_add, map_mul, hA0, hBρ, mul_zero, add_zero, map_one] at this
    exact zero_ne_one this

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5c: Chebyshev reduction of a palindromic polynomial

A real polynomial `C` of degree `≤ 2n` with symmetric coefficients is `z^n R(z + 1/z)` with `R` real of
degree `≤ n`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial

noncomputable section

/-- `chebS n (z + 1/z) = z^n + z^{-n}`. -/
def chebS : ℕ → ℝ[X]
  | 0 => 2
  | 1 => X
  | (n + 2) => X * chebS (n + 1) - chebS n

theorem chebS_natDegree_le : ∀ n : ℕ, (chebS n).natDegree ≤ n
  | 0 => by simp [chebS]
  | 1 => by simp [chebS]
  | (n + 2) => by
    have h1 := chebS_natDegree_le (n + 1)
    have h2 := chebS_natDegree_le n
    unfold chebS
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by omega))
    refine (natDegree_mul_le).trans ?_
    simp only [natDegree_X]
    omega

theorem chebS_eval (z : ℝ) (hz : z ≠ 0) : ∀ n : ℕ, (chebS n).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n
  | 0 => by simp [chebS]; norm_num
  | 1 => by simp [chebS]
  | (n + 2) => by
    have h1 := chebS_eval z hz (n + 1)
    have h2 := chebS_eval z hz n
    have hzw : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    simp only [chebS, eval_sub, eval_mul, eval_X, h1, h2]
    linear_combination ((z⁻¹) ^ n + z ^ n) * hzw

/-- The Chebyshev reduction of a palindromic polynomial. -/
theorem palindromic_reduction (n : ℕ) (C : ℝ[X]) (hdeg : C.natDegree ≤ 2 * n)
    (hsym : ∀ j, j ≤ 2 * n → C.coeff (2 * n - j) = C.coeff j) :
    ∃ R : ℝ[X], R.natDegree ≤ n ∧ ∀ z : ℝ, z ≠ 0 → C.eval z = z ^ n * R.eval (z + z⁻¹) := by
  refine ⟨Polynomial.C (C.coeff n) +
    ∑ k ∈ Finset.range n, Polynomial.C (C.coeff (n - 1 - k)) * chebS (k + 1), ?_, ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (chebS_natDegree_le _).trans (by omega)
  · intro z hz
    have hz' : z ≠ 0 := hz
    have hlt : C.natDegree < 2 * n + 1 := by omega
    rw [Polynomial.eval_eq_sum_range' hlt]
    simp only [eval_add, eval_C, eval_finsetSum, eval_mul, chebS_eval z hz']
    rw [show 2 * n + 1 = n + (n + 1) by ring, Finset.sum_range_add, Finset.sum_range_succ']
    have hL : ∑ x ∈ Finset.range n, C.coeff x * z ^ x =
        ∑ k ∈ Finset.range n, C.coeff (n - 1 - k) * z ^ (n - 1 - k) := by
      exact (Finset.sum_range_reflect (fun x => C.coeff x * z ^ x) n).symm
    have hU : ∑ x ∈ Finset.range n, C.coeff (n + (x + 1)) * z ^ (n + (x + 1)) =
        ∑ k ∈ Finset.range n, C.coeff (n - 1 - k) * z ^ (n + k + 1) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      have := hsym (n - 1 - k) (by omega)
      have e1 : 2 * n - (n - 1 - k) = n + (k + 1) := by omega
      rw [e1] at this
      rw [this]
      congr 2
    rw [hL, hU]
    have hR : ∀ k ∈ Finset.range n, z ^ n * (C.coeff (n - 1 - k) * (z ^ (k + 1) + z⁻¹ ^ (k + 1))) =
        C.coeff (n - 1 - k) * z ^ (n + k + 1) + C.coeff (n - 1 - k) * z ^ (n - 1 - k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hinv : z⁻¹ ^ (k + 1) * z ^ (k + 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hz', one_pow]
      have hn : z ^ n = z ^ (n - 1 - k) * z ^ (k + 1) := by
        rw [← pow_add]; congr 1; omega
      have e2 : z ^ n * z⁻¹ ^ (k + 1) = z ^ (n - 1 - k) := by
        rw [hn]
        calc z ^ (n - 1 - k) * z ^ (k + 1) * z⁻¹ ^ (k + 1)
            = z ^ (n - 1 - k) * (z⁻¹ ^ (k + 1) * z ^ (k + 1)) := by ring
          _ = z ^ (n - 1 - k) := by rw [hinv, mul_one]
      have e3 : z ^ n * z ^ (k + 1) = z ^ (n + k + 1) := by rw [← pow_add]; congr 1
      calc z ^ n * (C.coeff (n - 1 - k) * (z ^ (k + 1) + z⁻¹ ^ (k + 1)))
          = C.coeff (n - 1 - k) * (z ^ n * z ^ (k + 1)) +
            C.coeff (n - 1 - k) * (z ^ n * z⁻¹ ^ (k + 1)) := by ring
        _ = _ := by rw [e2, e3]
    rw [mul_add, Finset.mul_sum, Finset.sum_congr rfl hR, Finset.sum_add_distrib,
      mul_comm (z ^ n) (C.coeff n)]
    abel

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5d: the critical polynomial of `r = ε P / (x^T P*)`

`critPoly P T = X (P' P* - P P*') - T P P*` is the numerator of `r'`.  It is palindromic of degree `≤ 2v`
(`v = deg P`), so `critPoly P T (z) = z^v R(z + 1/z)` with `R` of degree `≤ v`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology

noncomputable section

/-- The numerator of the logarithmic derivative `x r'/r`, times `P P*`. -/
def critPoly (P : ℝ[X]) (T : ℕ) : ℝ[X] :=
  X * (derivative P * P.reverse - P * derivative P.reverse) - Polynomial.C (T : ℝ) * (P * P.reverse)

theorem reverse_eval_real (P : ℝ[X]) {x : ℝ} (hx : x ≠ 0) :
    P.reverse.eval x = x ^ P.natDegree * P.eval x⁻¹ := by
  haveI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reverse_mul_pow (RingHom.id ℝ) x⁻¹ P
  simp only [eval₂_id, invOf_eq_inv, inv_inv] at h
  have hxv : x ^ P.natDegree * (x⁻¹) ^ P.natDegree = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
  calc P.reverse.eval x = P.reverse.eval x * (x ^ P.natDegree * (x⁻¹) ^ P.natDegree) := by
        rw [hxv, mul_one]
    _ = x ^ P.natDegree * (P.reverse.eval x * (x⁻¹) ^ P.natDegree) := by ring
    _ = _ := by rw [h]

theorem deriv_reverse_eval (P : ℝ[X]) {x : ℝ} (hx : x ≠ 0) :
    x ^ 2 * (derivative P.reverse).eval x =
      (P.natDegree : ℝ) * x * P.reverse.eval x - x ^ P.natDegree * (derivative P).eval x⁻¹ := by
  set v := P.natDegree with hv
  have hf : HasDerivAt (fun y : ℝ => y ^ v * P.eval y⁻¹)
      ((v : ℝ) * x ^ (v - 1) * P.eval x⁻¹ + x ^ v * ((derivative P).eval x⁻¹ * (-(x ^ 2)⁻¹))) x := by
    have h1 := hasDerivAt_pow v x
    have h2 : HasDerivAt (fun y : ℝ => P.eval y⁻¹) ((derivative P).eval x⁻¹ * (-(x ^ 2)⁻¹)) x := by
      exact HasDerivAt.comp x (Polynomial.hasDerivAt P x⁻¹) (hasDerivAt_inv hx)
    exact h1.mul h2
  have hQ : HasDerivAt (fun y : ℝ => P.reverse.eval y) ((derivative P.reverse).eval x) x :=
    Polynomial.hasDerivAt _ x
  have hev : ∀ᶠ y in 𝓝 x, y ≠ 0 := eventually_ne_nhds hx
  have heq : (fun y : ℝ => y ^ v * P.eval y⁻¹) =ᶠ[𝓝 x] (fun y : ℝ => P.reverse.eval y) := by
    filter_upwards [hev] with y hy
    exact (reverse_eval_real P hy).symm
  have hf' := hf.congr_of_eventuallyEq heq.symm
  have hu := hQ.unique hf'
  rw [hu, reverse_eval_real P hx, ← hv]
  rcases Nat.eq_zero_or_pos v with h0 | hpos
  · rw [h0]; simp; field_simp
  · obtain ⟨w, hw⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    rw [hw]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
    ring

theorem crit_reciprocal (P : ℝ[X]) (T : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (critPoly P T).eval x = x ^ (2 * P.natDegree) * (critPoly P T).eval x⁻¹ := by
  set v := P.natDegree with hv
  have hu : x⁻¹ ≠ 0 := inv_ne_zero hx
  have eQx := reverse_eval_real P hx
  have eQu := reverse_eval_real P hu
  rw [inv_inv] at eQu
  have dQx := deriv_reverse_eval P hx
  have dQu := deriv_reverse_eval P hu
  rw [inv_inv] at dQu
  simp only [critPoly, eval_sub, eval_mul, eval_X, eval_C]
  set a := P.eval x⁻¹
  set b := (derivative P).eval x⁻¹
  set c0 := P.eval x
  set c1 := (derivative P).eval x
  set q1 := (derivative P.reverse).eval x
  set q2 := (derivative P.reverse).eval x⁻¹
  have hq1 : q1 = ((v : ℝ) * x * (x ^ v * a) - x ^ v * b) / x ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hx)]
    rw [mul_comm]; rw [dQx, eQx]
  have hq2 : q2 = ((v : ℝ) * x⁻¹ * ((x⁻¹) ^ v * c0) - (x⁻¹) ^ v * c1) / (x⁻¹) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hu)]
    rw [mul_comm]; rw [dQu, eQu]
  rw [hq1, hq2, eQx, eQu]
  have hxv : (x⁻¹) ^ v = (x ^ v)⁻¹ := inv_pow x v
  rw [hxv, pow_mul']
  have hxv0 : x ^ v ≠ 0 := pow_ne_zero v hx
  field_simp
  ring

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5e: counting lemmas for the contact argument

* `R_nonneg_of_counts`: a nonzero real polynomial `R` of degree `≤ v` with many real roots outside
  `[-2,2]` is nonnegative on `[-2,2]`.
* `rolle_finite`: a differentiable function vanishing on `N` points has `N - 1` critical points between them.
* `bonus_right`: if `F(ρ) = 0`, `F ≠ 0` on `(ρ,1]` and `F(1) F'(1) < 0` there is a critical point in `(ρ,1)`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology Set

noncomputable section

section Counting

theorem R_nonneg_of_counts (R : ℝ[X]) (v m k : ℕ) (hR0 : R ≠ 0) (hdeg : R.natDegree ≤ v)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hv : v + 1 ≤ m + k)
    (Yp Ym : Finset ℝ) (hYp : ∀ y ∈ Yp, 2 < y ∧ R.eval y = 0)
    (hYm : ∀ y ∈ Ym, y < -2 ∧ R.eval y = 0) (hcp : m - 1 ≤ Yp.card) (hcm : k - 1 ≤ Ym.card)
    (bp : R.eval 2 < 0 → ∃ y, 2 < y ∧ R.eval y = 0 ∧ y ∉ Yp)
    (bm : R.eval (-2) < 0 → ∃ y, y < -2 ∧ R.eval y = 0 ∧ y ∉ Ym) :
    ∀ x : ℝ, -2 ≤ x → x ≤ 2 → 0 ≤ R.eval x := by
  classical
  set Z : Finset ℝ := R.roots.toFinset with hZ
  have hmemZ : ∀ y, y ∈ Z ↔ R.eval y = 0 := by
    intro y
    simp only [hZ, Multiset.mem_toFinset, Polynomial.mem_roots hR0, Polynomial.IsRoot]
  have hZcard : Z.card ≤ v :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' R).trans hdeg)
  set Zin : Finset ℝ := Z.filter (fun y => -2 ≤ y ∧ y ≤ 2) with hZin
  have key : ∀ A B : Finset ℝ, (∀ y ∈ A, 2 < y ∧ R.eval y = 0) →
      (∀ y ∈ B, y < -2 ∧ R.eval y = 0) → A.card + B.card + Zin.card ≤ v := by
    intro A B hA hB
    have hAZ : A ⊆ Z := fun y hy => (hmemZ y).mpr (hA y hy).2
    have hBZ : B ⊆ Z := fun y hy => (hmemZ y).mpr (hB y hy).2
    have hZinZ : Zin ⊆ Z := Finset.filter_subset _ _
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro y hyA hyB
      have := (hA y hyA).1; have := (hB y hyB).1; linarith
    have hABZ : Disjoint (A ∪ B) Zin := by
      rw [Finset.disjoint_left]
      intro y hy hyZ
      have hyin := (Finset.mem_filter.mp hyZ).2
      rcases Finset.mem_union.mp hy with h | h
      · have := (hA y h).1; linarith [hyin.2]
      · have := (hB y h).1; linarith [hyin.1]
    have hsub : A ∪ B ∪ Zin ⊆ Z := Finset.union_subset (Finset.union_subset hAZ hBZ) hZinZ
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hABZ, Finset.card_union_of_disjoint hAB] at this
    omega
  have hZin0 : ∀ y, -2 ≤ y → y ≤ 2 → R.eval y = 0 → y ∈ Zin := by
    intro y h1 h2 h3
    exact Finset.mem_filter.mpr ⟨(hmemZ y).mpr h3, h1, h2⟩
  have hcont : Continuous fun y : ℝ => R.eval y := Polynomial.continuous R
  intro x hx1 hx2
  by_contra hneg
  push_neg at hneg
  -- the endpoint at 2 is nonnegative
  have h2 : 0 ≤ R.eval 2 := by
    by_contra h2neg
    push_neg at h2neg
    obtain ⟨y, hy, hRy, hyn⟩ := bp h2neg
    have h1 := key (insert y Yp) Ym (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hy, hRy⟩
      · exact hYp w hw) hYm
    rw [Finset.card_insert_of_notMem hyn] at h1
    have hZin0' : Zin.card = 0 := by omega
    by_cases hm2 : 0 ≤ R.eval (-2)
    · -- root in [-2, x]
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hx1 (hcont.continuousOn)
        (show (0 : ℝ) ∈ Icc (R.eval x) (R.eval (-2)) from ⟨hneg.le, hm2⟩)
      have := hZin0 r hr.1 (hr.2.trans hx2) hr0
      rw [Finset.card_eq_zero] at hZin0'
      rw [hZin0'] at this; simp at this
    · push_neg at hm2
      obtain ⟨y', hy', hRy', hyn'⟩ := bm hm2
      have h3 := key (insert y Yp) (insert y' Ym) (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ⟨hy, hRy⟩
        · exact hYp w hw) (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact ⟨hy', hRy'⟩
        · exact hYm w hw)
      rw [Finset.card_insert_of_notMem hyn, Finset.card_insert_of_notMem hyn'] at h3
      omega
  have hm2 : 0 ≤ R.eval (-2) := by
    by_contra hm2neg
    push_neg at hm2neg
    obtain ⟨y', hy', hRy', hyn'⟩ := bm hm2neg
    have h1 := key Yp (insert y' Ym) hYp (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hy', hRy'⟩
      · exact hYm w hw)
    rw [Finset.card_insert_of_notMem hyn'] at h1
    have hZin0' : Zin.card = 0 := by omega
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hx2 (hcont.continuousOn)
      (show (0 : ℝ) ∈ Icc (R.eval x) (R.eval 2) from ⟨hneg.le, h2⟩)
    have := hZin0 r (hx1.trans hr.1) hr.2 hr0
    rw [Finset.card_eq_zero] at hZin0'
    rw [hZin0'] at this; simp at this
  -- two roots in [-2, 2]
  obtain ⟨r1, hr1, hr10⟩ := intermediate_value_Icc' hx1 (hcont.continuousOn)
    (show (0 : ℝ) ∈ Icc (R.eval x) (R.eval (-2)) from ⟨hneg.le, hm2⟩)
  obtain ⟨r2, hr2, hr20⟩ := intermediate_value_Icc hx2 (hcont.continuousOn)
    (show (0 : ℝ) ∈ Icc (R.eval x) (R.eval 2) from ⟨hneg.le, h2⟩)
  have hr1x : r1 < x := lt_of_le_of_ne hr1.2 (fun h => by rw [h] at hr10; linarith)
  have hr2x : x < r2 := lt_of_le_of_ne hr2.1 (fun h => by rw [← h] at hr20; linarith)
  have hin1 := hZin0 r1 hr1.1 (hr1.2.trans hx2) hr10
  have hin2 := hZin0 r2 (hx1.trans hr2.1) hr2.2 hr20
  have hpair : ({r1, r2} : Finset ℝ) ⊆ Zin := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hin1
    · rw [Finset.mem_singleton] at hw; rw [hw]; exact hin2
  have hne : r1 ≠ r2 := by intro h; rw [h] at hr1x; linarith
  have hc2 : ({r1, r2} : Finset ℝ).card = 2 := Finset.card_pair hne
  have h4 := Finset.card_le_card hpair
  have h5 := key Yp Ym hYp hYm
  omega

end Counting

section Rolle

/-- A function vanishing at `N` points of `[a,b]`, differentiable on `[a,b]`, has `N - 1` critical points
between them. -/
theorem rolle_finite (F F' : ℝ → ℝ) {a b : ℝ} (Z : Finset ℝ)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F' x) x)
    (hZ : ∀ z ∈ Z, z ∈ Icc a b ∧ F z = 0) :
    ∃ D : Finset ℝ, (∀ d ∈ D, (∃ z ∈ Z, z < d) ∧ (∃ z ∈ Z, d < z) ∧ F' d = 0) ∧
      Z.card - 1 ≤ D.card := by
  classical
  induction Z using Finset.induction_on_max with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a' Z hlt ih =>
    obtain ⟨D, hD, hcard⟩ := ih (fun z hz => hZ z (Finset.mem_insert_of_mem hz))
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, by simp, by simp⟩
    · set z0 := Z.max' hne with hz0
      have hz0Z : z0 ∈ Z := Finset.max'_mem Z hne
      have hz0a : z0 < a' := hlt z0 hz0Z
      have hz0I := (hZ z0 (Finset.mem_insert_of_mem hz0Z))
      have ha'I := (hZ a' (Finset.mem_insert_self a' Z))
      obtain ⟨d, hd, hF'd⟩ := exists_hasDerivAt_eq_zero hz0a
        (fun x hx => (hF x ⟨hz0I.1.1.trans hx.1, hx.2.trans ha'I.1.2⟩).continuousAt.continuousWithinAt)
        (by rw [hz0I.2, ha'I.2])
        (fun x hx => hF x ⟨hz0I.1.1.trans hx.1.le, hx.2.le.trans ha'I.1.2⟩)
      have hdnot : d ∉ D := by
        intro hdD
        obtain ⟨_, ⟨z', hz', hdz'⟩, _⟩ := hD d hdD
        have h1 : z' ≤ z0 := Finset.le_max' Z z' hz'
        have h2 := hd.1
        linarith
      refine ⟨insert d D, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact ⟨⟨z0, Finset.mem_insert_of_mem hz0Z, hd.1⟩,
            ⟨a', Finset.mem_insert_self a' Z, hd.2⟩, hF'd⟩
        · obtain ⟨⟨z, hz, hze⟩, ⟨z', hz', hez'⟩, hF'e⟩ := hD e he
          exact ⟨⟨z, Finset.mem_insert_of_mem hz, hze⟩,
            ⟨z', Finset.mem_insert_of_mem hz', hez'⟩, hF'e⟩
      · rw [Finset.card_insert_of_notMem hdnot, Finset.card_insert_of_notMem (by
          intro h; exact absurd (hlt a' h) (lt_irrefl a'))]
        have : 1 ≤ Z.card := Finset.card_pos.mpr hne
        omega

end Rolle

section Bonus

/-- Positive version: `F(ρ) = 0`, `F > 0` on `(ρ,b]`... derived inside. -/
theorem bonus_right_pos (F F' : ℝ → ℝ) {ρ b : ℝ} (hρ : ρ < b)
    (hF : ∀ x ∈ Icc ρ b, HasDerivAt F (F' x) x) (hFρ : F ρ = 0)
    (hFne : ∀ x ∈ Ioc ρ b, F x ≠ 0) (hb : 0 < F b) (hd : F' b < 0) :
    ∃ y, ρ < y ∧ y < b ∧ F' y = 0 := by
  have hcont : ContinuousOn F (Icc ρ b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  -- positivity on `(ρ, b]`
  have hposx : ∀ x ∈ Ioc ρ b, 0 < F x := by
    intro x hx
    by_contra hle
    push_neg at hle
    have hxlt : F x < 0 := lt_of_le_of_ne hle (hFne x hx)
    have hsub : Icc x b ⊆ Icc ρ b := Icc_subset_Icc hx.1.le le_rfl
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hx.2 (hcont.mono hsub)
      (show (0 : ℝ) ∈ Icc (F x) (F b) from ⟨hxlt.le, hb.le⟩)
    exact hFne r ⟨lt_of_lt_of_le hx.1 hr.1, hr.2⟩ hr0
  -- a point to the left of `b` with a larger value
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hF b ⟨hρ.le, le_rfl⟩))
  have hev : ∀ᶠ x in 𝓝[<] b, slope F b x < 0 := by
    have h1 : ∀ᶠ x in 𝓝[≠] b, slope F b x < 0 :=
      hslope.eventually (Iio_mem_nhds hd)
    exact (nhdsWithin_mono b (fun x hx => ne_of_lt hx)) h1
  obtain ⟨x0, hx0s, hx0I⟩ := (hev.and (Ioo_mem_nhdsLT hρ)).exists
  have hx0lt : x0 < b := hx0I.2
  have hF0 : F b < F x0 := by
    have h := hx0s
    rw [slope_def_field] at h
    have hneg : x0 - b < 0 := by linarith
    have := (div_neg_iff.mp h)
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  -- maximum on `[ρ, b]`
  obtain ⟨y, hyI, hymax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hρ.le) hcont
  have hFy : F x0 ≤ F y := hymax ⟨hx0I.1.le, hx0lt.le⟩
  have hyρ : y ≠ ρ := by
    intro h
    have := hposx x0 ⟨hx0I.1, hx0lt.le⟩
    rw [h, hFρ] at hFy; linarith
  have hyb : y ≠ b := by
    intro h; rw [h] at hFy; linarith
  have hyIoo : y ∈ Ioo ρ b := ⟨lt_of_le_of_ne hyI.1 (Ne.symm hyρ), lt_of_le_of_ne hyI.2 hyb⟩
  have hloc : IsLocalMax F y := hymax.isLocalMax (Icc_mem_nhds hyIoo.1 hyIoo.2)
  exact ⟨y, hyIoo.1, hyIoo.2, hloc.hasDerivAt_eq_zero (hF y ⟨hyIoo.1.le, hyIoo.2.le⟩)⟩

/-- **Endpoint bonus (right).**  `F(ρ) = 0`, `F ≠ 0` on `(ρ,b]` and `F(b) F'(b) < 0` give a critical point
in `(ρ,b)`. -/
theorem bonus_right (F F' : ℝ → ℝ) {ρ b : ℝ} (hρ : ρ < b)
    (hF : ∀ x ∈ Icc ρ b, HasDerivAt F (F' x) x) (hFρ : F ρ = 0)
    (hFne : ∀ x ∈ Ioc ρ b, F x ≠ 0) (hsign : F b * F' b < 0) :
    ∃ y, ρ < y ∧ y < b ∧ F' y = 0 := by
  have hbne : F b ≠ 0 := hFne b ⟨hρ, le_rfl⟩
  rcases lt_or_gt_of_ne hbne with hneg | hpos
  · -- use `-F`
    have hd : 0 < F' b := by nlinarith
    obtain ⟨y, h1, h2, h3⟩ := bonus_right_pos (fun x => -F x) (fun x => -F' x) hρ
      (fun x hx => (hF x hx).neg) (by simp [hFρ]) (fun x hx => by simpa using hFne x hx)
      (by simpa using hneg) (by simpa using hd)
    exact ⟨y, h1, h2, by simpa using h3⟩
  · have hd : F' b < 0 := by nlinarith
    exact bonus_right_pos F F' hρ hF hFρ hFne hpos hd

/-- **Endpoint bonus (left).**  `F(ρ) = 0`, `F ≠ 0` on `[a,ρ)` and `F(a) F'(a) > 0` give a critical point
in `(a,ρ)`. -/
theorem bonus_left (F F' : ℝ → ℝ) {a ρ : ℝ} (hρ : a < ρ)
    (hF : ∀ x ∈ Icc a ρ, HasDerivAt F (F' x) x) (hFρ : F ρ = 0)
    (hFne : ∀ x ∈ Ico a ρ, F x ≠ 0) (hsign : 0 < F a * F' a) :
    ∃ y, a < y ∧ y < ρ ∧ F' y = 0 := by
  obtain ⟨y, h1, h2, h3⟩ := bonus_right (fun x => F (-x)) (fun x => -F' (-x)) (ρ := -ρ) (b := -a)
    (by linarith)
    (fun x hx => by
      have := HasDerivAt.comp x (hF (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩) (hasDerivAt_neg x)
      have h2 : HasDerivAt (fun y => F (-y)) (F' (-x) * -1) x := this
      simpa using h2)
    (by simpa using hFρ)
    (fun x hx => hFne (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (by simp only [neg_neg]; nlinarith)
  exact ⟨-y, by linarith, by linarith, by simpa using h3⟩

end Bonus

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5f: facts about the critical polynomial

degree `≤ 2v`, palindromic coefficients, the real polynomial `R` with `critPoly(z) = z^v R(z + 1/z)`,
`R ≠ 0`, `Q = P*` has no real zero in `[-1,1]`, and the derivative of `r = ε P/(x^T P*)`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology Set

noncomputable section

theorem critPoly_natDegree_le (P : ℝ[X]) (T : ℕ) :
    (critPoly P T).natDegree ≤ 2 * P.natDegree := by
  have hQd : P.reverse.natDegree ≤ P.natDegree := reverse_natDegree_le P
  have hPd : (derivative P).natDegree ≤ P.natDegree - 1 := natDegree_derivative_le P
  have hQd' : (derivative P.reverse).natDegree ≤ P.natDegree - 1 :=
    (natDegree_derivative_le _).trans (by omega)
  unfold critPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases hv : P.natDegree = 0
    · have hP : derivative P = 0 := derivative_of_natDegree_zero hv
      have hQ0 : P.reverse.natDegree = 0 := by omega
      have hQ' : derivative P.reverse = 0 := derivative_of_natDegree_zero hQ0
      rw [hP, hQ']; simp
    · refine natDegree_mul_le.trans ?_
      rw [natDegree_X]
      have h1 : (derivative P * P.reverse - P * derivative P.reverse).natDegree ≤
          2 * P.natDegree - 1 := by
        refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · exact natDegree_mul_le.trans (by omega)
        · exact natDegree_mul_le.trans (by omega)
      omega
  · refine (natDegree_C_mul_le _ _).trans ?_
    exact natDegree_mul_le.trans (by omega)

theorem critPoly_reflect (P : ℝ[X]) (T : ℕ) :
    reflect (2 * P.natDegree) (critPoly P T) = critPoly P T := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite {y : ℝ | y ≠ 0} := by
    have : {y : ℝ | y ≠ 0} = ({0} : Set ℝ)ᶜ := by ext y; simp
    rw [this]; exact (Set.finite_singleton (0 : ℝ)).infinite_compl
  refine hinf.mono fun y hy => ?_
  have hy0 : y ≠ 0 := hy
  have hx : y⁻¹ ≠ 0 := inv_ne_zero hy0
  haveI : Invertible y⁻¹ := invertibleOfNonzero hx
  have h1 := eval₂_reflect_mul_pow (RingHom.id ℝ) y⁻¹ (2 * P.natDegree) (critPoly P T)
    (critPoly_natDegree_le P T)
  simp only [eval₂_id, invOf_eq_inv, inv_inv] at h1
  have h2 := crit_reciprocal P T hx
  rw [inv_inv] at h2
  have hpow : (y⁻¹) ^ (2 * P.natDegree) ≠ 0 := pow_ne_zero _ hx
  show eval y (reflect (2 * P.natDegree) (critPoly P T)) = eval y (critPoly P T)
  have : eval y (reflect (2 * P.natDegree) (critPoly P T)) * (y⁻¹) ^ (2 * P.natDegree) =
      eval y (critPoly P T) * (y⁻¹) ^ (2 * P.natDegree) := by
    rw [h1, h2]; ring
  exact mul_right_cancel₀ hpow this

theorem critPoly_hsym (P : ℝ[X]) (T : ℕ) :
    ∀ j, j ≤ 2 * P.natDegree →
      (critPoly P T).coeff (2 * P.natDegree - j) = (critPoly P T).coeff j := by
  intro j hj
  have h := congrArg (fun q => q.coeff j) (critPoly_reflect P T)
  simp only [coeff_reflect, revAt_le hj] at h
  exact h

theorem exists_R (P : ℝ[X]) (T : ℕ) :
    ∃ R : ℝ[X], R.natDegree ≤ P.natDegree ∧
      ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹) :=
  palindromic_reduction P.natDegree (critPoly P T) (critPoly_natDegree_le P T)
    (critPoly_hsym P T)

theorem critPoly_coeff_zero (P : ℝ[X]) (T : ℕ) :
    (critPoly P T).coeff 0 = -((T : ℝ) * (P.coeff 0 * P.leadingCoeff)) := by
  unfold critPoly
  rw [coeff_sub, coeff_X_mul_zero, coeff_C_mul, mul_coeff_zero, coeff_zero_reverse]
  ring

theorem critPoly_ne_zero (P : ℝ[X]) (hP0 : P.coeff 0 ≠ 0) {T : ℕ} (hT : 1 ≤ T) :
    critPoly P T ≠ 0 := by
  intro h
  have h0 := critPoly_coeff_zero P T
  rw [h, coeff_zero] at h0
  have hPne : P ≠ 0 := fun hp => hP0 (by simp [hp])
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hPne
  have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have : (T : ℝ) * (P.coeff 0 * P.leadingCoeff) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact hT' h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hP0 h2
    · exact hlc h2

theorem R_ne_zero_of {P : ℝ[X]} {T : ℕ} (hC : critPoly P T ≠ 0) {R : ℝ[X]}
    (hR : ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) :
    R ≠ 0 := by
  intro hR0
  apply hC
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinf : Set.Infinite {y : ℝ | y ≠ 0} := by
    have : {y : ℝ | y ≠ 0} = ({0} : Set ℝ)ᶜ := by ext y; simp
    rw [this]; exact (Set.finite_singleton (0 : ℝ)).infinite_compl
  refine hinf.mono fun y hy => ?_
  have hy0 : y ≠ 0 := hy
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
  rw [hR y hy0, hR0]
  simp

theorem reverse_eval_ne (P : ℝ[X]) (hP0 : P.coeff 0 ≠ 0)
    (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) {y : ℝ} (hy : |y| ≤ 1) :
    P.reverse.eval y ≠ 0 := by
  by_cases hy0 : y = 0
  · subst hy0
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr (fun h => hP0 (by simp [h]))
  · rw [reverse_eval_real P hy0]
    refine mul_ne_zero (pow_ne_zero _ hy0) ?_
    intro h
    have h1 : aeval (((y⁻¹ : ℝ)) : ℂ) P = 0 := by
      rw [show (((y⁻¹ : ℝ)) : ℂ) = algebraMap ℝ ℂ y⁻¹ from rfl,
        aeval_algebraMap_apply_eq_algebraMap_eval, h]
      simp
    have h2 := hroots _ h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_inv] at h2
    have : 0 < |y| := abs_pos.mpr hy0
    rw [inv_lt_one_iff₀] at h2
    rcases h2 with h2 | h2
    · linarith
    · linarith

/-- The real function `r(x) = ε P(x) / (x^T P*(x))`. -/
def rfun (ε : ℝ) (P : ℝ[X]) (T : ℕ) (y : ℝ) : ℝ :=
  ε * P.eval y / (y ^ T * P.reverse.eval y)

theorem rfun_hasDerivAt (ε : ℝ) (P : ℝ[X]) {T : ℕ} (hT : 1 ≤ T) {y : ℝ} (hy : y ≠ 0)
    (hQ : P.reverse.eval y ≠ 0) :
    HasDerivAt (rfun ε P T)
      (ε * (critPoly P T).eval y / (y ^ (T + 1) * (P.reverse.eval y) ^ 2)) y := by
  have hc : HasDerivAt (fun y => ε * P.eval y) (ε * (derivative P).eval y) y :=
    (Polynomial.hasDerivAt P y).const_mul ε
  have hd : HasDerivAt (fun y => y ^ T * P.reverse.eval y)
      (((T : ℝ) * y ^ (T - 1)) * P.reverse.eval y + y ^ T * (derivative P.reverse).eval y) y :=
    (hasDerivAt_pow T y).mul (Polynomial.hasDerivAt P.reverse y)
  have hne : y ^ T * P.reverse.eval y ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) hQ
  have h := hc.div hd hne
  show HasDerivAt (fun y => ε * P.eval y / (y ^ T * P.reverse.eval y)) _ y
  convert h using 1
  obtain ⟨w, hw⟩ : ∃ w, T = w + 1 := ⟨T - 1, by omega⟩
  subst hw
  simp only [critPoly, eval_sub, eval_mul, eval_X, eval_C, Nat.add_sub_cancel]
  field_simp
  ring

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5g: sign computations and endpoint bonuses for `r = ε P / (x^T P*)`
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology Set

noncomputable section

section Helpers

theorem inv_add_inj {d d' : ℝ} (hd0 : d ≠ 0) (hd0' : d' ≠ 0) (hd : |d| < 1) (hd' : |d'| < 1)
    (h : d + d⁻¹ = d' + d'⁻¹) : d = d' := by
  have key : (d - d') * (d * d' - 1) = d * d' * (d + d⁻¹ - (d' + d'⁻¹)) := by
    field_simp; ring
  rw [h, sub_self, mul_zero] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · linarith
  · exfalso
    have : |d * d'| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg d, abs_nonneg d']
    have h2 : d * d' = 1 := by linarith
    rw [h2] at this; simp at this

theorem two_lt_add_inv {d : ℝ} (hd : 0 < d) (hd1 : d < 1) : 2 < d + d⁻¹ := by
  have h : d + d⁻¹ - 2 = (d - 1) ^ 2 / d := by field_simp; ring
  have h2 : 0 < (d - 1) ^ 2 / d := div_pos (by nlinarith) hd
  linarith

theorem add_inv_lt_neg_two {d : ℝ} (hd : d < 0) (hd1 : -1 < d) : d + d⁻¹ < -2 := by
  have hd0 : d ≠ 0 := ne_of_lt hd
  have h : d + d⁻¹ + 2 = (d + 1) ^ 2 / d := by field_simp; ring
  have h2 : (d + 1) ^ 2 / d < 0 := div_neg_of_pos_of_neg (by nlinarith) hd
  linarith

theorem right_sign (ε c0 R2 Q1 : ℝ) (hε : ε = 1 ∨ ε = -1) (hc0 : |c0| < 1) (hR2 : R2 < 0)
    (hQ : Q1 ≠ 0) : (ε + c0) * (ε * R2 / Q1 ^ 2) < 0 := by
  have hQ2 : 0 < Q1 ^ 2 := by positivity
  rw [abs_lt] at hc0
  have e : (ε + c0) * (ε * R2 / Q1 ^ 2) = (1 + ε * c0) * R2 / Q1 ^ 2 := by
    rcases hε with rfl | rfl <;> ring
  rw [e]
  have hpos : 0 < 1 + ε * c0 := by
    rcases hε with rfl | rfl <;> linarith [hc0.1, hc0.2]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpos hR2) hQ2

theorem left_sign (ε q R2 P1 s1 s2 : ℝ) (hε : ε = 1 ∨ ε = -1) (hs1 : s1 = 1 ∨ s1 = -1)
    (hs2 : s2 = 1 ∨ s2 = -1) (hq : |q| < 1) (hR2 : R2 < 0) (hP : P1 ≠ 0) :
    0 < (ε * s1 * s2 - q) * (ε * (s2 * R2) / ((-s1) * (s2 * P1) ^ 2)) := by
  have hP2 : 0 < P1 ^ 2 := by positivity
  rw [abs_lt] at hq
  have e : (ε * s1 * s2 - q) * (ε * (s2 * R2) / ((-s1) * (s2 * P1) ^ 2)) =
      -(1 - q * (ε * s1 * s2)) * R2 / P1 ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      field_simp <;> ring
  rw [e]
  have hpos : 0 < 1 - q * (ε * s1 * s2) := by
    rcases hε with rfl | rfl <;> rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      linarith [hq.1, hq.2]
  have : 0 < -(1 - q * (ε * s1 * s2)) * R2 := by nlinarith
  exact div_pos this hP2

end Helpers

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5h: endpoint bonuses for `r`
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology Set

noncomputable section

section Bonus

variable {P : ℝ[X]}

theorem real_root_abs_lt (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) {y : ℝ} (h : P.eval y = 0) :
    |y| < 1 := by
  have h1 : aeval ((y : ℝ) : ℂ) P = 0 := by
    rw [show ((y : ℝ) : ℂ) = algebraMap ℝ ℂ y from rfl,
      aeval_algebraMap_apply_eq_algebraMap_eval, h]
    simp
  have := hroots _ h1
  rwa [Complex.norm_real, Real.norm_eq_abs] at this

theorem eval_one_ne (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) : P.eval 1 ≠ 0 := by
  intro h
  have := real_root_abs_lt hroots h
  simp at this

theorem eval_neg_one_ne (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) : P.eval (-1) ≠ 0 := by
  intro h
  have := real_root_abs_lt hroots h
  simp at this

theorem reverse_eval_one (P : ℝ[X]) : P.reverse.eval 1 = P.eval 1 := by
  rw [reverse_eval_real P one_ne_zero]; simp

theorem reverse_eval_neg_one (P : ℝ[X]) :
    P.reverse.eval (-1) = (-1) ^ P.natDegree * P.eval (-1) := by
  rw [reverse_eval_real P (by norm_num)]
  norm_num

theorem rfun_one (ε : ℝ) (T : ℕ) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) :
    rfun ε P T 1 = ε := by
  unfold rfun
  rw [reverse_eval_one, one_pow, one_mul]
  have := eval_one_ne hroots
  field_simp

theorem rfun_neg_one (ε : ℝ) (T : ℕ) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) :
    rfun ε P T (-1) = ε * (-1) ^ T * (-1) ^ P.natDegree := by
  unfold rfun
  rw [reverse_eval_neg_one]
  have hP := eval_neg_one_ne hroots
  rcases neg_one_pow_eq_or ℝ T with h1 | h1 <;> rcases neg_one_pow_eq_or ℝ P.natDegree with h2 | h2 <;>
    rw [h1, h2] <;> field_simp <;> ring

/-- The derivative of `rfun`. -/
def drf (ε : ℝ) (P : ℝ[X]) (T : ℕ) (y : ℝ) : ℝ :=
  ε * (critPoly P T).eval y / (y ^ (T + 1) * (P.reverse.eval y) ^ 2)

theorem rfun_hasDerivAt' (ε : ℝ) (P : ℝ[X]) {T : ℕ} (hT : 1 ≤ T) {y : ℝ} (hy : y ≠ 0)
    (hQ : P.reverse.eval y ≠ 0) : HasDerivAt (rfun ε P T) (drf ε P T y) y :=
  rfun_hasDerivAt ε P hT hy hQ

theorem rfun_add_iff (ε c0 : ℝ) (P : ℝ[X]) (T : ℕ) {y : ℝ} (hy : y ≠ 0)
    (hQ : P.reverse.eval y ≠ 0) :
    rfun ε P T y + c0 =
      (ε * P.eval y + c0 * (y ^ T * P.reverse.eval y)) / (y ^ T * P.reverse.eval y) := by
  have hd : y ^ T * P.reverse.eval y ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) hQ
  unfold rfun
  field_simp

theorem rfun_sub_iff (ε q : ℝ) (P : ℝ[X]) (T : ℕ) {y : ℝ} (hy : y ≠ 0)
    (hQ : P.reverse.eval y ≠ 0) :
    rfun ε P T y - q =
      (ε * P.eval y - q * (y ^ T * P.reverse.eval y)) / (y ^ T * P.reverse.eval y) := by
  have hd : y ^ T * P.reverse.eval y ≠ 0 := mul_ne_zero (pow_ne_zero _ hy) hQ
  unfold rfun
  field_simp

theorem bonus_pos (hP0 : P.coeff 0 ≠ 0) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1)
    {T : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c0 : ℝ} (hc0 : |c0| < 1) {R : ℝ[X]}
    (hRC : ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹))
    (hR2 : R.eval 2 < 0) {p0 : ℝ} (hp0 : 0 < p0 ∧ p0 < 1) (hp0v : rfun ε P T p0 = -c0) :
    ∃ ρ y0 : ℝ, (∀ pt : ℝ, 0 < pt → pt < 1 → rfun ε P T pt = -c0 → pt ≤ ρ) ∧ ρ < y0 ∧
      y0 < 1 ∧ drf ε P T y0 = 0 := by
  classical
  have hQne : ∀ y : ℝ, |y| ≤ 1 → P.reverse.eval y ≠ 0 :=
    fun y hy => reverse_eval_ne P hP0 hroots hy
  have hc0' := abs_lt.mp hc0
  set N1 : ℝ[X] := C ε * P + C c0 * (X ^ T * P.reverse) with hN1
  have hN1eval : ∀ y : ℝ, N1.eval y = ε * P.eval y + c0 * (y ^ T * P.reverse.eval y) := by
    intro y; simp [hN1]
  have hiff : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → (rfun ε P T y + c0 = 0 ↔ N1.eval y = 0) := by
    intro y hy0 hy1
    have hd : y ^ T * P.reverse.eval y ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0) (hQne y hy1)
    rw [rfun_add_iff ε c0 P T hy0 (hQne y hy1), hN1eval, div_eq_zero_iff]
    simp [hd]
  have hN1ne : N1 ≠ 0 := by
    intro h
    have h1 : N1.eval 1 = 0 := by rw [h]; simp
    rw [hN1eval, reverse_eval_one] at h1
    have e : ε * P.eval 1 + c0 * (1 ^ T * P.eval 1) = (ε + c0) * P.eval 1 := by ring
    rw [e] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases hε with rfl | rfl <;> linarith
    · exact eval_one_ne hroots h2
  set S : Finset ℝ := N1.roots.toFinset.filter (fun y => 0 < y ∧ y < 1) with hS
  have hmemS : ∀ y, y ∈ S ↔ 0 < y ∧ y < 1 ∧ N1.eval y = 0 := by
    intro y
    simp only [hS, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hN1ne,
      Polynomial.IsRoot.def]
    tauto
  have hp0S : p0 ∈ S := (hmemS p0).mpr ⟨hp0.1, hp0.2,
    (hiff p0 hp0.1.ne' (by rw [abs_le]; constructor <;> linarith [hp0.1, hp0.2])).mp
      (by rw [hp0v]; ring)⟩
  have hne : S.Nonempty := ⟨p0, hp0S⟩
  set ρ := S.max' hne with hρ
  have hρS : ρ ∈ S := Finset.max'_mem S hne
  obtain ⟨hρ0, hρ1, hρN⟩ := (hmemS ρ).mp hρS
  have hF : ∀ y ∈ Icc ρ 1, HasDerivAt (fun y => rfun ε P T y + c0) (drf ε P T y) y := by
    intro y hy
    have hy0 : y ≠ 0 := by have := hy.1; exact (lt_of_lt_of_le hρ0 this).ne'
    have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    exact (rfun_hasDerivAt' ε P hT hy0 (hQne y hy1)).add_const c0
  have hFρ : rfun ε P T ρ + c0 = 0 :=
    (hiff ρ hρ0.ne' (by rw [abs_le]; constructor <;> linarith)).mpr hρN
  have hFne : ∀ y ∈ Ioc ρ 1, rfun ε P T y + c0 ≠ 0 := by
    intro y hy h0
    by_cases hy1 : y = 1
    · subst hy1
      rw [rfun_one ε T hroots] at h0
      rcases hε with rfl | rfl <;> linarith
    · have hylt : y < 1 := lt_of_le_of_ne hy.2 hy1
      have hy0 : 0 < y := lt_trans hρ0 hy.1
      have hr := (hiff y hy0.ne' (by rw [abs_le]; constructor <;> linarith [hy.2])).mp h0
      have hyS : y ∈ S := (hmemS y).mpr ⟨hy0, hylt, hr⟩
      have := Finset.le_max' S y hyS
      linarith [hy.1]
  have hsign : (rfun ε P T 1 + c0) * drf ε P T 1 < 0 := by
    rw [rfun_one ε T hroots]
    have hC1 : (critPoly P T).eval 1 = R.eval 2 := by
      rw [hRC 1 one_ne_zero]; norm_num
    unfold drf
    rw [hC1, reverse_eval_one]
    have := right_sign ε c0 (R.eval 2) (P.eval 1) hε hc0 hR2 (eval_one_ne hroots)
    simpa using this
  obtain ⟨y0, h1, h2, h3⟩ := bonus_right (fun y => rfun ε P T y + c0) (drf ε P T) hρ1 hF hFρ
    hFne hsign
  refine ⟨ρ, y0, fun pt h0 h1' hv => ?_, h1, h2, h3⟩
  exact Finset.le_max' S pt ((hmemS pt).mpr ⟨h0, h1',
    (hiff pt h0.ne' (by rw [abs_le]; constructor <;> linarith)).mp (by rw [hv]; ring)⟩)

theorem bonus_neg (hP0 : P.coeff 0 ≠ 0) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1)
    {T : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {q : ℝ} (hq : |q| < 1) {R : ℝ[X]}
    (hRC : ∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹))
    (hRm : R.eval (-2) < 0) {x0 : ℝ} (hx0 : -1 < x0 ∧ x0 < 0) (hx0v : rfun ε P T x0 = q) :
    ∃ ρ y0 : ℝ, (∀ pt : ℝ, -1 < pt → pt < 0 → rfun ε P T pt = q → ρ ≤ pt) ∧ y0 < ρ ∧
      -1 < y0 ∧ drf ε P T y0 = 0 := by
  classical
  have hQne : ∀ y : ℝ, |y| ≤ 1 → P.reverse.eval y ≠ 0 :=
    fun y hy => reverse_eval_ne P hP0 hroots hy
  have hq' := abs_lt.mp hq
  have hs1 := neg_one_pow_eq_or ℝ T
  have hs2 := neg_one_pow_eq_or ℝ P.natDegree
  have hεs : ε * (-1) ^ T * (-1) ^ P.natDegree - q ≠ 0 := by
    rcases hε with rfl | rfl <;> rcases hs1 with h1 | h1 <;> rcases hs2 with h2 | h2 <;>
      rw [h1, h2] <;> intro h <;> linarith
  set N2 : ℝ[X] := C ε * P - C q * (X ^ T * P.reverse) with hN2
  have hN2eval : ∀ y : ℝ, N2.eval y = ε * P.eval y - q * (y ^ T * P.reverse.eval y) := by
    intro y; simp [hN2]
  have hiff : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → (rfun ε P T y - q = 0 ↔ N2.eval y = 0) := by
    intro y hy0 hy1
    have hd : y ^ T * P.reverse.eval y ≠ 0 := mul_ne_zero (pow_ne_zero _ hy0) (hQne y hy1)
    rw [rfun_sub_iff ε q P T hy0 (hQne y hy1), hN2eval, div_eq_zero_iff]
    simp [hd]
  have hN2ne : N2 ≠ 0 := by
    intro h
    have h1 : N2.eval (-1) = 0 := by rw [h]; simp
    rw [hN2eval, reverse_eval_neg_one] at h1
    have hP1 := eval_neg_one_ne hroots
    have e : ε * P.eval (-1) - q * ((-1) ^ T * ((-1) ^ P.natDegree * P.eval (-1))) =
        (ε - q * (-1) ^ T * (-1) ^ P.natDegree) * P.eval (-1) := by ring
    rw [e] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · apply hεs
      rcases hε with rfl | rfl <;> rcases hs1 with h1 | h1 <;> rcases hs2 with h2' | h2' <;>
        rw [h1, h2'] <;> rw [h1, h2'] at h2 <;> linarith
    · exact hP1 h2
  set S : Finset ℝ := N2.roots.toFinset.filter (fun y => -1 < y ∧ y < 0) with hS
  have hmemS : ∀ y, y ∈ S ↔ -1 < y ∧ y < 0 ∧ N2.eval y = 0 := by
    intro y
    simp only [hS, Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hN2ne,
      Polynomial.IsRoot.def]
    tauto
  have hx0S : x0 ∈ S := (hmemS x0).mpr ⟨hx0.1, hx0.2,
    (hiff x0 hx0.2.ne (by rw [abs_le]; constructor <;> linarith [hx0.1, hx0.2])).mp
      (by rw [hx0v]; ring)⟩
  have hne : S.Nonempty := ⟨x0, hx0S⟩
  set ρ := S.min' hne with hρ
  have hρS : ρ ∈ S := Finset.min'_mem S hne
  obtain ⟨hρ0, hρ1, hρN⟩ := (hmemS ρ).mp hρS
  have hF : ∀ y ∈ Icc (-1) ρ, HasDerivAt (fun y => rfun ε P T y - q) (drf ε P T y) y := by
    intro y hy
    have hy0 : y ≠ 0 := by have := hy.2; exact (lt_of_le_of_lt this hρ1).ne
    have hy1 : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    exact (rfun_hasDerivAt' ε P hT hy0 (hQne y hy1)).sub_const q
  have hFρ : rfun ε P T ρ - q = 0 :=
    (hiff ρ hρ1.ne (by rw [abs_le]; constructor <;> linarith)).mpr hρN
  have hFne : ∀ y ∈ Ico (-1) ρ, rfun ε P T y - q ≠ 0 := by
    intro y hy h0
    by_cases hy1 : y = -1
    · subst hy1
      rw [rfun_neg_one ε T hroots] at h0
      exact hεs h0
    · have hygt : -1 < y := lt_of_le_of_ne hy.1 (Ne.symm hy1)
      have hy0 : y < 0 := lt_trans hy.2 hρ1
      have hr := (hiff y hy0.ne (by rw [abs_le]; constructor <;> linarith [hy.2])).mp h0
      have hyS : y ∈ S := (hmemS y).mpr ⟨hygt, hy0, hr⟩
      have := Finset.min'_le S y hyS
      linarith [hy.2]
  have hsign : 0 < (rfun ε P T (-1) - q) * drf ε P T (-1) := by
    rw [rfun_neg_one ε T hroots]
    have hC1 : (critPoly P T).eval (-1) = (-1) ^ P.natDegree * R.eval (-2) := by
      rw [hRC (-1) (by norm_num)]; norm_num
    unfold drf
    rw [hC1, reverse_eval_neg_one, pow_succ]
    have hP1 := eval_neg_one_ne hroots
    have := left_sign ε q (R.eval (-2)) (P.eval (-1)) ((-1) ^ T) ((-1) ^ P.natDegree) hε hs1 hs2 hq
      hRm hP1
    have e : ((-1 : ℝ) ^ T * -1) = -((-1) ^ T) := by ring
    rw [e]
    exact this
  obtain ⟨y0, h1, h2, h3⟩ := bonus_left (fun y => rfun ε P T y - q) (drf ε P T) hρ0 hF hFρ hFne
    hsign
  refine ⟨ρ, y0, fun pt h0 h1' hv => ?_, h2, h1, h3⟩
  exact Finset.min'_le S pt ((hmemS pt).mpr ⟨h0, h1',
    (hiff pt h1'.ne (by rw [abs_le]; constructor <;> linarith)).mp (by rw [hv]; ring)⟩)

end Bonus

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R5i: the contact lemma

`r = ε P/(x^T P*)` with `r(p_i) = -c0` at `m` distinct points of `(0,1)`, `r(x_b) = q` at `k` distinct points
of `(-1,0)`, and `deg P + 1 ≤ m + k`.  Then `critPoly(z) = z^v R(z + 1/z)` with `R ≥ 0` on `[-2,2]`; on the
unit circle this is `z r'/r ≥ 0`.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Filter Topology Set

noncomputable section

theorem contact_nonneg (P : ℝ[X]) (hP0 : P.coeff 0 ≠ 0)
    (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1)
    {T : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c0 q : ℝ} (hc0 : |c0| < 1)
    (hq : |q| < 1) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hv : P.natDegree + 1 ≤ m + k)
    (p : Fin m → ℝ) (hpinj : Function.Injective p) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hpv : ∀ i, rfun ε P T (p i) = -c0)
    (x : Fin k → ℝ) (hxinj : Function.Injective x) (hx : ∀ b, -1 < x b ∧ x b < 0)
    (hxv : ∀ b, rfun ε P T (x b) = q) :
    ∃ R : ℝ[X], R.natDegree ≤ P.natDegree ∧
      (∀ z : ℝ, z ≠ 0 → (critPoly P T).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) ∧
      ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y := by
  classical
  obtain ⟨R, hRdeg, hRC⟩ := exists_R P T
  have hCne := critPoly_ne_zero P hP0 hT
  have hR0 := R_ne_zero_of hCne hRC
  refine ⟨R, hRdeg, hRC, ?_⟩
  have hQne : ∀ y : ℝ, |y| ≤ 1 → P.reverse.eval y ≠ 0 :=
    fun y hy => reverse_eval_ne P hP0 hroots hy
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hdr0 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → drf ε P T y = 0 → R.eval (y + y⁻¹) = 0 := by
    intro y hy0 hy1 h
    have hden : y ^ (T + 1) * (P.reverse.eval y) ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hy0) (pow_ne_zero _ (hQne y hy1))
    unfold drf at h
    rw [div_eq_zero_iff, or_iff_left hden] at h
    have h2 : (critPoly P T).eval y = 0 := (mul_eq_zero.mp h).resolve_left hε0
    rw [hRC y hy0] at h2
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hy0)
  -- positive side
  obtain ⟨Yp, hYp, hcp, bp⟩ : ∃ Yp : Finset ℝ, (∀ y ∈ Yp, 2 < y ∧ R.eval y = 0) ∧
      m - 1 ≤ Yp.card ∧ (R.eval 2 < 0 → ∃ y, 2 < y ∧ R.eval y = 0 ∧ y ∉ Yp) := by
    set Zp : Finset ℝ := Finset.univ.image p with hZp
    have hZpcard : Zp.card = m := by
      rw [hZp, Finset.card_image_of_injective _ hpinj]; simp
    have hmemZp : ∀ z ∈ Zp, 0 < z ∧ z < 1 ∧ rfun ε P T z = -c0 := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(hp i).1, (hp i).2, hpv i⟩
    have hZne : Zp.Nonempty := by
      rw [← Finset.card_pos, hZpcard]; omega
    set a := Zp.min' hZne with ha_def
    set b := Zp.max' hZne with hb_def
    have ha : a ∈ Zp := Finset.min'_mem _ _
    have hb : b ∈ Zp := Finset.max'_mem _ _
    have hFd : ∀ y ∈ Icc a b, HasDerivAt (fun y => rfun ε P T y + c0) (drf ε P T y) y := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (hmemZp a ha).1 hy.1
      have hy1 : y < 1 := lt_of_le_of_lt hy.2 (hmemZp b hb).2.1
      exact (rfun_hasDerivAt' ε P hT hy0.ne'
        (hQne y (by rw [abs_le]; constructor <;> linarith))).add_const c0
    have hZ : ∀ z ∈ Zp, z ∈ Icc a b ∧ rfun ε P T z + c0 = 0 := by
      intro z hz
      exact ⟨⟨Finset.min'_le _ _ hz, Finset.le_max' _ _ hz⟩, by rw [(hmemZp z hz).2.2]; ring⟩
    obtain ⟨Dp, hDp, hcard⟩ := rolle_finite (fun y => rfun ε P T y + c0) (drf ε P T) Zp hFd hZ
    have hDp01 : ∀ d ∈ Dp, 0 < d ∧ d < 1 := by
      intro d hd
      obtain ⟨⟨z, hz, hzd⟩, ⟨z', hz', hdz'⟩, _⟩ := hDp d hd
      exact ⟨lt_trans (hmemZp z hz).1 hzd, lt_trans hdz' (hmemZp z' hz').2.1⟩
    refine ⟨Dp.image (fun d => d + d⁻¹), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      have h01 := hDp01 d hd
      exact ⟨two_lt_add_inv h01.1 h01.2, hdr0 d h01.1.ne'
        (by rw [abs_le]; constructor <;> linarith [h01.1, h01.2]) (hDp d hd).2.2⟩
    · rw [Finset.card_image_of_injOn]
      · omega
      · intro d hd d' hd' h
        have h1 := hDp01 d hd
        have h2 := hDp01 d' hd'
        exact inv_add_inj h1.1.ne' h2.1.ne' (by rw [abs_of_pos h1.1]; exact h1.2)
          (by rw [abs_of_pos h2.1]; exact h2.2) h
    · intro hR2
      obtain ⟨ρ, y0, hρ, hρy, hy1, hdy⟩ := bonus_pos hP0 hroots hT hε hc0 hRC hR2
        (p0 := a) ⟨(hmemZp a ha).1, (hmemZp a ha).2.1⟩ (hmemZp a ha).2.2
      have hy0pos : 0 < y0 := by
        have := hρ a (hmemZp a ha).1 (hmemZp a ha).2.1 (hmemZp a ha).2.2
        linarith [(hmemZp a ha).1]
      refine ⟨y0 + y0⁻¹, two_lt_add_inv hy0pos hy1,
        hdr0 y0 hy0pos.ne' (by rw [abs_le]; constructor <;> linarith) hdy, ?_⟩
      intro hmem
      obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hmem
      have h01 := hDp01 d hd
      have hdd := inv_add_inj h01.1.ne' hy0pos.ne' (by rw [abs_of_pos h01.1]; exact h01.2)
        (by rw [abs_of_pos hy0pos]; exact hy1) hdeq
      obtain ⟨_, ⟨z', hz', hdz'⟩, _⟩ := hDp d hd
      have := hρ z' (hmemZp z' hz').1 (hmemZp z' hz').2.1 (hmemZp z' hz').2.2
      linarith
  -- negative side
  obtain ⟨Ym, hYm, hcm, bm⟩ : ∃ Ym : Finset ℝ, (∀ y ∈ Ym, y < -2 ∧ R.eval y = 0) ∧
      k - 1 ≤ Ym.card ∧ (R.eval (-2) < 0 → ∃ y, y < -2 ∧ R.eval y = 0 ∧ y ∉ Ym) := by
    set Zx : Finset ℝ := Finset.univ.image x with hZx
    have hZxcard : Zx.card = k := by
      rw [hZx, Finset.card_image_of_injective _ hxinj]; simp
    have hmemZx : ∀ z ∈ Zx, -1 < z ∧ z < 0 ∧ rfun ε P T z = q := by
      intro z hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨(hx i).1, (hx i).2, hxv i⟩
    have hZne : Zx.Nonempty := by
      rw [← Finset.card_pos, hZxcard]; omega
    set a := Zx.min' hZne with ha_def
    set b := Zx.max' hZne with hb_def
    have ha : a ∈ Zx := Finset.min'_mem _ _
    have hb : b ∈ Zx := Finset.max'_mem _ _
    have hFd : ∀ y ∈ Icc a b, HasDerivAt (fun y => rfun ε P T y - q) (drf ε P T y) y := by
      intro y hy
      have hy0 : y < 0 := lt_of_le_of_lt hy.2 (hmemZx b hb).2.1
      have hy1 : -1 < y := lt_of_lt_of_le (hmemZx a ha).1 hy.1
      exact (rfun_hasDerivAt' ε P hT hy0.ne
        (hQne y (by rw [abs_le]; constructor <;> linarith))).sub_const q
    have hZ : ∀ z ∈ Zx, z ∈ Icc a b ∧ rfun ε P T z - q = 0 := by
      intro z hz
      exact ⟨⟨Finset.min'_le _ _ hz, Finset.le_max' _ _ hz⟩, by rw [(hmemZx z hz).2.2]; ring⟩
    obtain ⟨Dm, hDm, hcard⟩ := rolle_finite (fun y => rfun ε P T y - q) (drf ε P T) Zx hFd hZ
    have hDm01 : ∀ d ∈ Dm, -1 < d ∧ d < 0 := by
      intro d hd
      obtain ⟨⟨z, hz, hzd⟩, ⟨z', hz', hdz'⟩, _⟩ := hDm d hd
      exact ⟨lt_trans (hmemZx z hz).1 hzd, lt_trans hdz' (hmemZx z' hz').2.1⟩
    refine ⟨Dm.image (fun d => d + d⁻¹), ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      have h01 := hDm01 d hd
      exact ⟨add_inv_lt_neg_two h01.2 h01.1, hdr0 d h01.2.ne
        (by rw [abs_le]; constructor <;> linarith [h01.1, h01.2]) (hDm d hd).2.2⟩
    · rw [Finset.card_image_of_injOn]
      · omega
      · intro d hd d' hd' h
        have h1 := hDm01 d hd
        have h2 := hDm01 d' hd'
        exact inv_add_inj h1.2.ne h2.2.ne (by rw [abs_of_neg h1.2]; linarith [h1.1])
          (by rw [abs_of_neg h2.2]; linarith [h2.1]) h
    · intro hRm
      obtain ⟨ρ, y0, hρ, hρy, hy1, hdy⟩ := bonus_neg hP0 hroots hT hε hq hRC hRm
        (x0 := a) ⟨(hmemZx a ha).1, (hmemZx a ha).2.1⟩ (hmemZx a ha).2.2
      have hy0neg : y0 < 0 := by
        have := hρ a (hmemZx a ha).1 (hmemZx a ha).2.1 (hmemZx a ha).2.2
        linarith [(hmemZx a ha).2.1]
      refine ⟨y0 + y0⁻¹, add_inv_lt_neg_two hy0neg hy1,
        hdr0 y0 hy0neg.ne (by rw [abs_le]; constructor <;> linarith) hdy, ?_⟩
      intro hmem
      obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.mp hmem
      have h01 := hDm01 d hd
      have hdd := inv_add_inj h01.2.ne hy0neg.ne (by rw [abs_of_neg h01.2]; linarith [h01.1])
        (by rw [abs_of_neg hy0neg]; linarith) hdeq
      obtain ⟨⟨z, hz, hzd⟩, _, _⟩ := hDm d hd
      have := hρ z (hmemZx z hz).1 (hmemZx z hz).2.1 (hmemZx z hz).2.2
      linarith
  intro y hy1 hy2
  exact R_nonneg_of_counts R P.natDegree m k hR0 hRdeg hm hk hv Yp Ym hYp hYm hcp hcm bp bm y
    hy1 hy2

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R6a: from a minimal singular kernel vector to the Blaschke quotient

`interpolant_data`: for a minimal singular set `S` with kernel vector `v` there are `s`, `P`, `ε = ±1`
with `P(0) ≠ 0`, roots of `P` in the open disc, `s + deg P + 1 ≤ |S|` and
`f_a Q(z_a) = ε z_a^s P(z_a)` for every node `a ∈ S` (`Q = P*`): the Blaschke quotient interpolates.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset
open CatalanMeasure.Signed CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

noncomputable section

section Interp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The numerator polynomial of `φ`. -/
def nPhi (z v : ι → ℝ) (S : Finset ι) : ℝ[X] :=
  ∑ a ∈ S, Polynomial.C (v a) * ∏ b ∈ S.erase a, (1 - Polynomial.C (z b) * X)

/-- The numerator polynomial of `ψ`. -/
def nPsi (z f v : ι → ℝ) (S : Finset ι) : ℝ[X] :=
  ∑ a ∈ S, Polynomial.C (v a * f a) * ∏ b ∈ S.erase a, (1 - Polynomial.C (z b) * X)

/-- The common denominator. -/
def eDen (z : ι → ℝ) (S : Finset ι) : ℝ[X] := ∏ b ∈ S, (1 - Polynomial.C (z b) * X)

theorem aeval_eDen (z : ι → ℝ) (S : Finset ι) (ζ : ℂ) :
    aeval ζ (eDen z S) = ∏ b ∈ S, (1 - (z b : ℂ) * ζ) := by
  simp [eDen, map_prod]

theorem aeval_nPhi (z v : ι → ℝ) (S : Finset ι) (ζ : ℂ) (hζ : ∀ b, 1 - (z b : ℂ) * ζ ≠ 0)
    (hv : ∀ a, a ∉ S → v a = 0) :
    aeval ζ (nPhi z v S) = phiK z v ζ * aeval ζ (eDen z S) := by
  have h1 : phiK z v ζ = ∑ a ∈ S, (v a : ℂ) * kapp z a ζ := by
    unfold phiK
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha; simp [hv a ha]
  rw [h1, Finset.sum_mul, aeval_eDen]
  simp only [nPhi, map_sum, map_mul, aeval_C, map_prod, map_sub, map_one, aeval_X]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_prod_erase S (fun b => (1 - (z b : ℂ) * ζ)) ha]
  unfold kapp
  have hne := hζ a
  simp only [Complex.coe_algebraMap]
  rw [mul_assoc, ← mul_assoc (1 / (1 - (z a : ℂ) * ζ)), one_div_mul_cancel hne, one_mul]

theorem aeval_nPsi (z f v : ι → ℝ) (S : Finset ι) (ζ : ℂ) (hζ : ∀ b, 1 - (z b : ℂ) * ζ ≠ 0)
    (hv : ∀ a, a ∉ S → v a = 0) :
    aeval ζ (nPsi z f v S) = psiK z f v ζ * aeval ζ (eDen z S) := by
  have h1 : psiK z f v ζ = ∑ a ∈ S, ((v a * f a : ℝ) : ℂ) * kapp z a ζ := by
    unfold psiK
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha; simp [hv a ha]
  rw [h1, Finset.sum_mul, aeval_eDen]
  simp only [nPsi, map_sum, map_mul, aeval_C, map_prod, map_sub, map_one, aeval_X]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_prod_erase S (fun b => (1 - (z b : ℂ) * ζ)) ha]
  unfold kapp
  have hne := hζ a
  simp only [Complex.coe_algebraMap]
  push_cast
  linear_combination (-((v a : ℂ) * (f a : ℂ) * ∏ x ∈ S.erase a, (1 - (z x : ℂ) * ζ))) *
    (one_div_mul_cancel hne)

theorem natDegree_nPhi_le (z v : ι → ℝ) (S : Finset ι) : (nPhi z v S).natDegree ≤ S.card - 1 := by
  unfold nPhi
  refine natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  have : ∀ b ∈ S.erase a, (1 - Polynomial.C (z b) * X : ℝ[X]).natDegree ≤ 1 := by
    intro b _
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  refine (Finset.sum_le_sum this).trans ?_
  simp [Finset.card_erase_of_mem ha]

theorem exists_coprime_split (f g : ℝ[X]) (hg : g ≠ 0) :
    ∃ G A B : ℝ[X], G ≠ 0 ∧ f = G * A ∧ g = G * B ∧ IsCoprime A B := by
  classical
  have hG : GCDMonoid.gcd f g ≠ 0 := gcd_ne_zero_of_right hg
  refine ⟨GCDMonoid.gcd f g, f / GCDMonoid.gcd f g, g / GCDMonoid.gcd f g, hG, ?_, ?_,
    isCoprime_div_gcd_div_gcd hg⟩
  · exact (EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_left f g)).symm
  · exact (EuclideanDomain.mul_div_cancel' hG (GCDMonoid.gcd_dvd_right f g)).symm

theorem eval_nPhi_inv {z v : ι → ℝ} {S : Finset ι} (hz0 : ∀ a, z a ≠ 0)
    (hinj : Function.Injective z) {a0 : ι} (ha0 : a0 ∈ S) (hv : v a0 ≠ 0) :
    (nPhi z v S).eval (z a0)⁻¹ ≠ 0 := by
  unfold nPhi
  rw [eval_finsetSum, Finset.sum_eq_single a0]
  · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X]
    refine mul_ne_zero hv (Finset.prod_ne_zero_iff.mpr fun b hb => ?_)
    have hb' : b ≠ a0 := (Finset.mem_erase.mp hb).1
    intro h
    have h2 : z b = z a0 := by
      have := hz0 a0
      field_simp at h
      linarith
    exact hb' (hinj h2)
  · intro a ha hne
    simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_one, eval_X]
    have : a0 ∈ S.erase a := Finset.mem_erase.mpr ⟨hne.symm, ha0⟩
    rw [Finset.prod_eq_zero this (by rw [mul_inv_cancel₀ (hz0 a0)]; ring)]
    simp
  · intro h; exact absurd ha0 h

theorem interpolant_data {z f v : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ a, z a ≠ 0)
    (hz1 : ∀ a, |z a| < 1) (hf : ∀ a, |f a| < 1)
    (hpsd : ∀ u : ι → ℝ, 0 ≤ ∑ a, ∑ b, u a * pickW z f a b * u b)
    {S : Finset ι} (hS : MinKer (pickW z f) S) (hv0 : v ≠ 0) (hvs : ∀ a, a ∉ S → v a = 0)
    (hvk : ∀ c ∈ S, ∑ b, pickW z f c b * v b = 0) :
    ∃ (s : ℕ) (P : ℝ[X]) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ P.coeff 0 ≠ 0 ∧
      (∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) ∧ s + P.natDegree + 1 ≤ S.card ∧
      ∀ a ∈ S, ε * (z a) ^ s * P.eval (z a) = f a * P.reverse.eval (z a) := by
  classical
  have hvall : ∀ c, v c * ∑ b, pickW z f c b * v b = 0 := by
    intro c
    by_cases hc : c ∈ S
    · rw [hvk c hc, mul_zero]
    · rw [hvs c hc, zero_mul]
  have hvne := minKer_entries_ne_zero hS hv0 hvs hvk
  obtain ⟨a0, ha0⟩ : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hv0
    funext b
    exact hvs b (by rw [hne]; simp)
  have hden : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → ∀ b, 1 - (z b : ℂ) * ζ ≠ 0 :=
    fun ζ hζ b => one_sub_ne_zero_of_norm hz1 hζ b
  have hEne : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → aeval ζ (eDen z S) ≠ 0 := by
    intro ζ hζ
    rw [aeval_eDen]
    exact Finset.prod_ne_zero_iff.mpr fun b _ => hden ζ hζ b
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 →
      ‖aeval ζ (nPhi z v S)‖ = ‖aeval ζ (nPsi z f v S)‖ := by
    intro ζ hζ
    rw [aeval_nPhi z v S ζ (hden ζ hζ.le) hvs, aeval_nPsi z f v S ζ (hden ζ hζ.le) hvs,
      norm_mul, norm_mul]
    congr 1
    have := normSq_phi_eq_psi hz1 f v hvall hζ
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  have hNφ_ne : nPhi z v S ≠ 0 := by
    intro h
    exact eval_nPhi_inv hz0 hinj ha0 (hvne a0 ha0) (by rw [h]; simp)
  have hNψ_ne : nPsi z f v S ≠ 0 := by
    intro h
    apply hNφ_ne
    have hz : (nPhi z v S).map (algebraMap ℝ ℂ) = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine circle_infinite.mono fun ζ hζ => ?_
      have hζ' : ‖ζ‖ = 1 := hζ
      have := hcirc ζ hζ'
      rw [h, map_zero, norm_zero] at this
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_map]
      rw [← Polynomial.aeval_def]
      exact norm_eq_zero.mp this
    exact (Polynomial.map_eq_zero_iff (RingHom.injective _)).mp hz
  obtain ⟨G, A, B, hG, hNφ, hNψ, hcop⟩ := exists_coprime_split (nPhi z v S) (nPsi z f v S) hNψ_ne
  have hA0 : A ≠ 0 := fun h => hNφ_ne (by rw [hNφ, h, mul_zero])
  have hB0 : B ≠ 0 := fun h => hNψ_ne (by rw [hNψ, h, mul_zero])
  -- the polynomial identity for `A`, `B`
  have hid : A * A.reverse * X ^ B.natDegree = B * B.reverse * X ^ A.natDegree := by
    have h := poly_identity_of_circle (nPhi z v S) (nPsi z f v S) hcirc
    rw [hNφ, hNψ, Polynomial.reverse_mul_of_domain, Polynomial.reverse_mul_of_domain,
      Polynomial.natDegree_mul hG hB0, Polynomial.natDegree_mul hG hA0] at h
    have hGr : G.reverse ≠ 0 := fun hh => hG (Polynomial.reverse_eq_zero.mp hh)
    have hne : G * G.reverse * X ^ G.natDegree ≠ 0 :=
      mul_ne_zero (mul_ne_zero hG hGr) (pow_ne_zero _ X_ne_zero)
    refine mul_left_cancel₀ hne ?_
    rw [pow_add] at h
    linear_combination h
  -- `B` has no zero in the open disc
  have hBd : ∀ ζ : ℂ, ‖ζ‖ < 1 → aeval ζ B ≠ 0 := by
    intro ζ hζ hB
    have hψ : psiK z f v ζ = 0 := by
      have h1 := aeval_nPsi z f v S ζ (hden ζ hζ.le) hvs
      rw [hNψ, map_mul, hB, mul_zero] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (hEne ζ hζ.le)
    have hφ : phiK z v ζ = 0 := by
      have hle := normSq_phi_le_psi hz1 f v hpsd hvall hζ
      rw [hψ, map_zero] at hle
      have := Complex.normSq_eq_zero.mp (le_antisymm hle (Complex.normSq_nonneg _))
      exact this
    exact no_common_zero_disc hinj hz1 f v hf hpsd hS hv0 hvs hvk hζ ⟨hφ, hψ⟩
  obtain ⟨s, P, ε, hε, hP0, hAP, hBε, hroots⟩ := blaschke_form A B hA0 hB0 hcop hid hBd
  refine ⟨s, P, ε, hε, hP0, hroots, ?_, ?_⟩
  · -- degree
    have hPne : P ≠ 0 := fun h => hP0 (by simp [h])
    have h1 : A.natDegree = s + P.natDegree := by
      rw [hAP, Polynomial.natDegree_mul (pow_ne_zero _ X_ne_zero) hPne, Polynomial.natDegree_X_pow]
    have h2 : A.natDegree ≤ (nPhi z v S).natDegree := by
      rw [hNφ, Polynomial.natDegree_mul hG hA0]; omega
    have h3 := natDegree_nPhi_le z v S
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨a0, ha0⟩
    omega
  · intro a haS
    have hza : ‖(z a : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact (hz1 a).le
    have hza' : ‖(z a : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hz1 a
    have hnode := phi_node hz1 f v a
    rw [hvk a haS] at hnode
    simp only [Complex.ofReal_zero] at hnode
    have hE := hEne (z a : ℂ) hza
    have hφa := aeval_nPhi z v S (z a : ℂ) (hden _ hza) hvs
    have hψa := aeval_nPsi z f v S (z a : ℂ) (hden _ hza) hvs
    -- `Nφ(z_a) = f_a Nψ(z_a)`
    have hrel : aeval (z a : ℂ) (nPhi z v S) = (f a : ℂ) * aeval (z a : ℂ) (nPsi z f v S) := by
      rw [hφa, hψa]
      have : phiK z v (z a) = (f a : ℂ) * psiK z f v (z a) := by linear_combination hnode
      rw [this]; ring
    have hGa : aeval (z a : ℂ) G ≠ 0 := by
      intro hGz
      apply no_common_zero_disc hinj hz1 f v hf hpsd hS hv0 hvs hvk hza'
      have h1 : aeval (z a : ℂ) (nPhi z v S) = 0 := by rw [hNφ, map_mul, hGz, zero_mul]
      have h2 : aeval (z a : ℂ) (nPsi z f v S) = 0 := by rw [hNψ, map_mul, hGz, zero_mul]
      rw [hφa] at h1; rw [hψa] at h2
      exact ⟨(mul_eq_zero.mp h1).resolve_right hE, (mul_eq_zero.mp h2).resolve_right hE⟩
    rw [hNφ, hNψ, map_mul, map_mul] at hrel
    have hAB : aeval (z a : ℂ) A = (f a : ℂ) * aeval (z a : ℂ) B := by
      apply mul_left_cancel₀ hGa
      linear_combination hrel
    rw [hAP, hBε] at hAB
    simp only [map_mul, map_pow, aeval_X, aeval_C] at hAB
    have hreal : (z a) ^ s * P.eval (z a) = f a * (ε * P.reverse.eval (z a)) := by
      have h1 : ((z a ^ s * P.eval (z a) : ℝ) : ℂ) = ((f a * (ε * P.reverse.eval (z a)) : ℝ) : ℂ) := by
        push_cast
        have e1 : aeval (z a : ℂ) P = ((P.eval (z a) : ℝ) : ℂ) := by
          rw [show (z a : ℂ) = algebraMap ℝ ℂ (z a) from rfl,
            aeval_algebraMap_apply_eq_algebraMap_eval]; rfl
        have e2 : aeval (z a : ℂ) P.reverse = ((P.reverse.eval (z a) : ℝ) : ℂ) := by
          rw [show (z a : ℂ) = algebraMap ℝ ℂ (z a) from rfl,
            aeval_algebraMap_apply_eq_algebraMap_eval]; rfl
        rw [e1, e2] at hAB
        simpa [Complex.coe_algebraMap] using hAB
      exact_mod_cast h1
    have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    calc ε * z a ^ s * P.eval (z a) = ε * (z a ^ s * P.eval (z a)) := by ring
      _ = ε * (f a * (ε * P.reverse.eval (z a))) := by rw [hreal]
      _ = f a * (ε * ε) * P.reverse.eval (z a) := by ring
      _ = f a * P.reverse.eval (z a) := by rw [hε2]; ring

end Interp

end

end CatalanMeasure.GenD.Signed.PhysicalPick

/-!
# R6b: the contact lemma on finsets, the phase hypothesis, the final assembly

`PhaseHole` is the ONLY unproved ingredient: from the Blaschke quotient `h = ε X^s P/P*` with
`h(y) = -c y^t` at the positive nodes, `deg ≤ m + k - 1` and `Ω ≥ 0` (given here in the form of the
nonnegative polynomial `R`, or `t ≤ s`), the phase inequality of PROOF-C section 36.
-/

namespace CatalanMeasure.GenD.Signed.PhysicalPick

open Polynomial Finset Filter Topology Set
open CatalanMeasure.Signed CatalanMeasure.GenD.Signed CatalanMeasure.Parametric

noncomputable section

/-- **The open phase lemma (R6).**  See the notes: not proved. -/
def PhaseHole : Prop :=
  ∀ (Zp Zx : Finset ℝ) (t s : ℕ) (P : ℝ[X]) (ε q : ℝ),
    1 ≤ Zp.card → 1 ≤ Zx.card → 1 ≤ t → (ε = 1 ∨ ε = -1) → P.coeff 0 ≠ 0 →
    (∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) → s + P.natDegree + 1 ≤ Zp.card + Zx.card →
    |q| < 1 →
    (∀ y ∈ Zp, 0 < y ∧ y < 1 ∧ ε * y ^ s * P.eval y = -(1 / 100) * y ^ t * P.reverse.eval y) →
    (∀ y ∈ Zx, -1 < y ∧ y < 0 ∧ ε * y ^ s * P.eval y = q * y ^ t * P.reverse.eval y) →
    s < t →
    (∃ R : ℝ[X], R.natDegree ≤ P.natDegree ∧
        (∀ z : ℝ, z ≠ 0 → (critPoly P (t - s)).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) ∧
        ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y) →
    (t : ℝ) * Real.arctan 4 - ∑ y ∈ Zp, Real.arctan (4 * ((1 - y) / (1 + y))) ≤
      (Zx.card : ℝ) * Real.pi / 2 + Real.pi / 2 +
        (17 / 4) * (Zp.card : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2)

/-- If `t ≤ s` the positive nodes are roots of `ε X^{s-t} P + c0 P*`, so `m + t ≤ s + deg P`. -/
theorem card_add_le_of_t_le_s (P : ℝ[X]) (hP0 : P.coeff 0 ≠ 0)
    (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1) {s t : ℕ} (hts : t ≤ s) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) {c0 : ℝ} (hc0 : |c0| < 1) (Zp : Finset ℝ)
    (hZp : ∀ y ∈ Zp, 0 < y ∧ y < 1 ∧ ε * y ^ s * P.eval y = -c0 * y ^ t * P.reverse.eval y) :
    Zp.card + t ≤ s + P.natDegree := by
  classical
  set N : ℝ[X] := C ε * (X ^ (s - t) * P) + C c0 * P.reverse with hN
  have hNeval : ∀ y : ℝ, N.eval y = ε * (y ^ (s - t) * P.eval y) + c0 * P.reverse.eval y := by
    intro y; simp [hN]
  have hN1 : N.eval 1 ≠ 0 := by
    rw [hNeval, reverse_eval_one]
    have e : ε * (1 ^ (s - t) * P.eval 1) + c0 * P.eval 1 = (ε + c0) * P.eval 1 := by ring
    rw [e]
    refine mul_ne_zero ?_ (eval_one_ne hroots)
    have := abs_lt.mp hc0
    rcases hε with rfl | rfl <;> intro h <;> linarith
  have hNne : N ≠ 0 := fun h => hN1 (by rw [h]; simp)
  have hdeg : N.natDegree ≤ s - t + P.natDegree := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X_pow]
    · exact (natDegree_C_mul_le _ _).trans ((reverse_natDegree_le P).trans (by omega))
  have hsub : Zp ⊆ N.roots.toFinset := by
    intro y hy
    obtain ⟨h0, h1, h2⟩ := hZp y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hNne, Polynomial.IsRoot.def, hNeval]
    have hys : y ^ s = y ^ (s - t) * y ^ t := by rw [← pow_add]; congr 1; omega
    have hyt : y ^ t ≠ 0 := pow_ne_zero _ h0.ne'
    apply mul_left_cancel₀ hyt
    rw [hys] at h2
    linear_combination h2
  have hc := Finset.card_le_card hsub
  have h2 : N.roots.toFinset.card ≤ N.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' N)
  omega

/-- The contact lemma for finite node sets. -/
theorem contact_fs (P : ℝ[X]) (hP0 : P.coeff 0 ≠ 0) (hroots : ∀ ζ : ℂ, aeval ζ P = 0 → ‖ζ‖ < 1)
    {s t : ℕ} (hst : s < t) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c0 q : ℝ} (hc0 : |c0| < 1)
    (hq : |q| < 1) (Zp Zx : Finset ℝ) (hm : 1 ≤ Zp.card) (hk : 1 ≤ Zx.card)
    (hv : P.natDegree + 1 ≤ Zp.card + Zx.card)
    (hZp : ∀ y ∈ Zp, 0 < y ∧ y < 1 ∧ ε * y ^ s * P.eval y = -c0 * y ^ t * P.reverse.eval y)
    (hZx : ∀ y ∈ Zx, -1 < y ∧ y < 0 ∧ ε * y ^ s * P.eval y = q * y ^ t * P.reverse.eval y) :
    ∃ R : ℝ[X], R.natDegree ≤ P.natDegree ∧
      (∀ z : ℝ, z ≠ 0 → (critPoly P (t - s)).eval z = z ^ P.natDegree * R.eval (z + z⁻¹)) ∧
      ∀ y : ℝ, -2 ≤ y → y ≤ 2 → 0 ≤ R.eval y := by
  have hT : 1 ≤ t - s := by omega
  have hr : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ∀ g : ℝ,
      ε * y ^ s * P.eval y = g * y ^ t * P.reverse.eval y → rfun ε P (t - s) y = g := by
    intro y hy0 hy1 g h
    have hQ := reverse_eval_ne P hP0 hroots hy1
    unfold rfun
    have ht : y ^ t = y ^ s * y ^ (t - s) := by rw [← pow_add]; congr 1; omega
    rw [div_eq_iff (mul_ne_zero (pow_ne_zero _ hy0) hQ)]
    have hys : y ^ s ≠ 0 := pow_ne_zero _ hy0
    apply mul_left_cancel₀ hys
    rw [ht] at h
    linear_combination h
  exact contact_nonneg P hP0 hroots hT hε hc0 hq hm hk hv
    (fun i => ((Zp.equivFin.symm i : {x // x ∈ Zp}) : ℝ))
    (fun i j h => Zp.equivFin.symm.injective (Subtype.ext h))
    (fun i => ⟨(hZp _ (Zp.equivFin.symm i).2).1, (hZp _ (Zp.equivFin.symm i).2).2.1⟩)
    (fun i => by
      have h := hZp _ (Zp.equivFin.symm i).2
      have h0 : (0 : ℝ) < ((Zp.equivFin.symm i : {x // x ∈ Zp}) : ℝ) := h.1
      have h1 : ((Zp.equivFin.symm i : {x // x ∈ Zp}) : ℝ) < 1 := h.2.1
      rw [hr _ h0.ne' (by rw [abs_le]; constructor <;> linarith) (-c0) h.2.2])
    (fun i => ((Zx.equivFin.symm i : {x // x ∈ Zx}) : ℝ))
    (fun i j h => Zx.equivFin.symm.injective (Subtype.ext h))
    (fun i => ⟨(hZx _ (Zx.equivFin.symm i).2).1, (hZx _ (Zx.equivFin.symm i).2).2.1⟩)
    (fun i => by
      have h := hZx _ (Zx.equivFin.symm i).2
      have h0 : ((Zx.equivFin.symm i : {x // x ∈ Zx}) : ℝ) < 0 := h.2.1
      have h1 : -1 < ((Zx.equivFin.symm i : {x // x ∈ Zx}) : ℝ) := h.1
      rw [hr _ h0.ne (by rw [abs_le]; constructor <;> linarith) q h.2.2])

section Final

theorem winPickForm_eq_Qf {n : ℕ} (c : ℝ) (e : ℕ) (z : Fin n → ℝ) (u : Fin n → ℝ) :
    winPickForm c e z u = Qf (wFam c e z) 1 u := by
  unfold winPickForm Qf wFam gData winData
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem Qf_decomp {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} {e : ℕ} {z : ι → ℝ}
    (hz1 : ∀ a, |z a| < 1) (γ κ : ℝ) (v : ι → ℝ)
    (hκ : ∀ a, v a ≠ 0 → gData c e z γ a = κ * z a ^ e) :
    Qf (wFam c e z) γ v = (1 - κ ^ 2) * (∑ a, ∑ b, v a * (1 / (1 - z a * z b)) * v b) +
      κ ^ 2 * ∑ a, ∑ b, v a * ((1 - z a ^ e * z b ^ e) / (1 - z a * z b)) * v b := by
  unfold Qf wFam
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases ha : v a = 0
  · simp [ha]
  by_cases hb : v b = 0
  · simp [hb]
  rw [hκ a ha, hκ b hb]
  have hne : 1 - z a * z b ≠ 0 := by
    have h1 := hz1 a
    have h2 := hz1 b
    rw [abs_lt] at h1 h2
    intro h
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  field_simp
  ring

theorem Qf_pos_of_pos_support {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c < 1) {e : ℕ} {z : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ a, z a ≠ 0)
    (hz1 : ∀ a, |z a| < 1) (γ : ℝ) {v : ι → ℝ} (hv0 : v ≠ 0) (hvs : ∀ a, v a ≠ 0 → 0 < z a) :
    0 < Qf (wFam c e z) γ v := by
  rw [Qf_decomp hz1 γ (-c) v (fun a ha => by
    have : ¬ z a < 0 := not_lt.mpr (hvs a ha).le
    simp [gData, this])]
  have hK := kForm_pos hinj hz0 hz1 hv0
  have hG := geomForm_nonneg hz1 e v
  have h1 : 0 < 1 - (-c) ^ 2 := by nlinarith
  nlinarith [mul_pos h1 hK, mul_nonneg (sq_nonneg (-c)) hG]

theorem Qf_pos_of_neg_support {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} {e : ℕ}
    {z : ι → ℝ} (hinj : Function.Injective z) (hz0 : ∀ a, z a ≠ 0) (hz1 : ∀ a, |z a| < 1)
    {γ : ℝ} (hγ : |γ| < 1) {v : ι → ℝ} (hv0 : v ≠ 0) (hvs : ∀ a, v a ≠ 0 → z a < 0) :
    0 < Qf (wFam c e z) γ v := by
  rw [Qf_decomp hz1 γ γ v (fun a ha => by simp [gData, hvs a ha])]
  have hK := kForm_pos hinj hz0 hz1 hv0
  have hG := geomForm_nonneg hz1 e v
  have hγ' := abs_lt.mp hγ
  have h1 : 0 < 1 - γ ^ 2 := by nlinarith
  nlinarith [mul_pos h1 hK, mul_nonneg (sq_nonneg γ) hG]

theorem abs_gData_lt {ι : Type*} {c : ℝ} (hc : |c| < 1) {e : ℕ} {z : ι → ℝ}
    (hz1 : ∀ a, |z a| < 1) {γ : ℝ} (hγ : |γ| < 1) (a : ι) : |gData c e z γ a| < 1 := by
  unfold gData
  rw [abs_mul, abs_pow]
  have hz : |z a| ^ e ≤ 1 := pow_le_one₀ (abs_nonneg _) (hz1 a).le
  have hg : |(if z a < 0 then γ else -c)| < 1 := by
    split_ifs
    · exact hγ
    · rwa [abs_neg]
  calc |(if z a < 0 then γ else -c)| * |z a| ^ e ≤ |(if z a < 0 then γ else -c)| * 1 :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ < 1 := by rw [mul_one]; exact hg

theorem pickWindow_of_phaseHole (hole : PhaseHole) {n : ℕ} {z : Fin n → ℝ}
    (hinj : Function.Injective z) (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, |z i| < 1) (e : ℕ)
    (hstat : ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) * Real.pi / 2 + Real.pi / 2 +
        (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) <
      (e : ℝ) * Real.arctan 4 -
        ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), Real.arctan (4 * ((1 - z i) / (1 + z i)))) :
    PickWindow (1 / 100) e z := by
  classical
  have hc0 : (0 : ℝ) ≤ 1 / 100 := by norm_num
  have hc1 : (1 / 100 : ℝ) < 1 := by norm_num
  refine pickWindow_of_pickForm hinj hz0 hz1 (1 / 100) e (fun u => ?_)
  rw [winPickForm_eq_Qf]
  rcases pick_or_singular hinj hz0 hz1 hc0 hc1 e with h | ⟨γ, hγ0, hγ1, hpsd, v, hv0, hvk⟩
  · exact h u
  · exfalso
    have hγabs : |γ| < 1 := by rw [abs_lt]; constructor <;> linarith
    have hcabs : |(1 / 100 : ℝ)| < 1 := by rw [abs_lt]; constructor <;> norm_num
    set f : Fin n → ℝ := gData (1 / 100 : ℝ) e z γ with hf_def
    have hfabs : ∀ a, |f a| < 1 := fun a => abs_gData_lt hcabs hz1 hγabs a
    have hpsd' : ∀ u : Fin n → ℝ, 0 ≤ ∑ a, ∑ b, u a * pickW z f a b * u b := hpsd
    have hker : HasKer (pickW z f) Finset.univ :=
      ⟨v, hv0, fun a ha => absurd (Finset.mem_univ a) ha, fun c _ => hvk c⟩
    obtain ⟨S, hS⟩ := exists_minKer (pickW z f) hker
    obtain ⟨v', hv0', hvs', hvk'⟩ := hS.1
    obtain ⟨s, P, ε, hε, hP0, hroots, hdeg, hnode⟩ :=
      interpolant_data hinj hz0 hz1 hfabs hpsd' hS hv0' hvs' hvk'
    have hvall' : ∀ c, v' c * ∑ b, pickW z f c b * v' b = 0 := by
      intro c
      by_cases hc : c ∈ S
      · rw [hvk' c hc, mul_zero]
      · rw [hvs' c hc, zero_mul]
    have hQ0 : Qf (wFam (1 / 100 : ℝ) e z) γ v' = 0 := by
      unfold Qf
      refine Finset.sum_eq_zero fun a _ => ?_
      have := hvall' a
      calc ∑ b, v' a * wFam (1 / 100 : ℝ) e z γ a b * v' b
          = v' a * ∑ b, pickW z f a b * v' b := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by simp only [wFam, pickW, hf_def]; ring
        _ = 0 := this
    -- the support of `v'` contains positive and negative nodes
    set Sp : Finset (Fin n) := S.filter (fun a => 0 < z a) with hSp
    set Sn : Finset (Fin n) := S.filter (fun a => z a < 0) with hSn
    have hSsplit : ∀ a ∈ S, 0 < z a ∨ z a < 0 := fun a _ => lt_or_gt_of_ne (hz0 a) |>.symm
    have hSp_ne : 1 ≤ Sp.card := by
      by_contra h0
      have h0' : Sp = ∅ := Finset.card_eq_zero.mp (by omega)
      have hneg : ∀ a, v' a ≠ 0 → z a < 0 := by
        intro a ha
        have haS : a ∈ S := by
          by_contra hn; exact ha (hvs' a hn)
        rcases hSsplit a haS with h | h
        · exfalso
          have : a ∈ Sp := Finset.mem_filter.mpr ⟨haS, h⟩
          rw [h0'] at this; simp at this
        · exact h
      have := Qf_pos_of_neg_support (c := 1 / 100) (e := e) hinj hz0 hz1 hγabs hv0' hneg
      linarith
    have hSn_ne : 1 ≤ Sn.card := by
      by_contra h0
      have h0' : Sn = ∅ := Finset.card_eq_zero.mp (by omega)
      have hpos : ∀ a, v' a ≠ 0 → 0 < z a := by
        intro a ha
        have haS : a ∈ S := by
          by_contra hn; exact ha (hvs' a hn)
        rcases hSsplit a haS with h | h
        · exact h
        · exfalso
          have : a ∈ Sn := Finset.mem_filter.mpr ⟨haS, h⟩
          rw [h0'] at this; simp at this
      have := Qf_pos_of_pos_support (e := e) hc0 hc1 hinj hz0 hz1 γ hv0' hpos
      linarith
    have hcard : Sp.card + Sn.card = S.card := by
      have h1 := Finset.card_filter_add_card_filter_not (s := S) (fun a => 0 < z a)
      have h2 : S.filter (fun a => ¬ 0 < z a) = Sn := by
        ext a
        simp only [hSn, Finset.mem_filter]
        constructor
        · rintro ⟨h, h'⟩; exact ⟨h, lt_of_le_of_ne (not_lt.mp h') (hz0 a)⟩
        · rintro ⟨h, h'⟩; exact ⟨h, not_lt.mpr h'.le⟩
      rw [h2] at h1; exact h1
    -- the node sets
    set Zp : Finset ℝ := Sp.image z with hZp
    set Zx : Finset ℝ := Sn.image z with hZx
    have hZpc : Zp.card = Sp.card := Finset.card_image_of_injective _ hinj
    have hZxc : Zx.card = Sn.card := Finset.card_image_of_injective _ hinj
    have hPfull : Sp ⊆ Finset.univ.filter (fun i => 0 < z i) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩
    have hNfull : Sn ⊆ Finset.univ.filter (fun i => z i < 0) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩
    -- the arctan sums
    have hatn : ∀ a ∈ Finset.univ.filter (fun i => 0 < z i),
        0 ≤ Real.arctan (4 * ((1 - z a) / (1 + z a))) := by
      intro a ha
      have h0 := (Finset.mem_filter.mp ha).2
      have h1 := hz1 a
      rw [abs_lt] at h1
      have : 0 ≤ 4 * ((1 - z a) / (1 + z a)) := by
        have h2 : 0 < 1 + z a := by linarith
        have h3 : 0 ≤ 1 - z a := by linarith
        exact mul_nonneg (by norm_num) (div_nonneg h3 h2.le)
      have := Real.arctan_strictMono.monotone this
      simpa using this
    have hsum : ∑ y ∈ Zp, Real.arctan (4 * ((1 - y) / (1 + y))) ≤
        ∑ i ∈ Finset.univ.filter (fun i => 0 < z i), Real.arctan (4 * ((1 - z i) / (1 + z i))) := by
      rw [hZp, Finset.sum_image (fun a _ b _ h => hinj h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg hPfull (fun a ha _ => hatn a ha)
    have hmle : (Zp.card : ℝ) ≤ ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) := by
      rw [hZpc]; exact_mod_cast Finset.card_le_card hPfull
    have hkle : (Zx.card : ℝ) ≤ ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) := by
      rw [hZxc]; exact_mod_cast Finset.card_le_card hNfull
    -- `e ≥ 1`
    have he : 1 ≤ e := by
      by_contra h0
      have he0 : e = 0 := by omega
      have hs0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < z i),
          Real.arctan (4 * ((1 - z i) / (1 + z i))) := Finset.sum_nonneg hatn
      have hk0 : 0 ≤ ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) * Real.pi / 2 := by
        positivity
      have hm0 : 0 ≤ (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) *
          (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) := div_nonneg (by positivity) (by norm_num)
      rw [he0] at hstat
      simp only [Nat.cast_zero, zero_mul, zero_sub] at hstat
      linarith [Real.pi_pos]
    -- node equations
    have hZp_eq : ∀ y ∈ Zp, 0 < y ∧ y < 1 ∧
        ε * y ^ s * P.eval y = -(1 / 100) * y ^ e * P.reverse.eval y := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      have haS := (Finset.mem_filter.mp ha).1
      have hpa := (Finset.mem_filter.mp ha).2
      have hz1a := hz1 a
      rw [abs_lt] at hz1a
      refine ⟨hpa, hz1a.2, ?_⟩
      have h := hnode a haS
      have hfa : f a = -(1 / 100) * z a ^ e := by
        simp [hf_def, gData, not_lt.mpr hpa.le]
      rw [hfa] at h
      linarith
    have hZx_eq : ∀ y ∈ Zx, -1 < y ∧ y < 0 ∧
        ε * y ^ s * P.eval y = γ * y ^ e * P.reverse.eval y := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      have haS := (Finset.mem_filter.mp ha).1
      have hna := (Finset.mem_filter.mp ha).2
      have hz1a := hz1 a
      rw [abs_lt] at hz1a
      refine ⟨hz1a.1, hna, ?_⟩
      have h := hnode a haS
      have hfa : f a = γ * z a ^ e := by
        simp [hf_def, gData, hna]
      rw [hfa] at h
      linarith
    have hdeg' : s + P.natDegree + 1 ≤ Zp.card + Zx.card := by
      rw [hZpc, hZxc, hcard]; exact hdeg
    have hconst : 0 ≤ (17 / 4 : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) := by norm_num
    have h1 : (Zx.card : ℝ) * Real.pi / 2 ≤
        ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) * Real.pi / 2 := by
      have := Real.pi_pos
      nlinarith
    have h2 : (17 / 4) * (Zp.card : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) ≤
        (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) := by
      have e1 : (17 / 4) * (Zp.card : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) =
          (Zp.card : ℝ) * ((17 / 4 : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2)) := by ring
      have e2 : (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) * (1 / 100) ^ 2 /
          (1 - (1 / 100) ^ 2) =
          ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) *
            ((17 / 4 : ℝ) * (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2)) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hmle hconst
    by_cases hst : s < e
    · have hR := contact_fs P hP0 hroots hst hε (c0 := 1 / 100) (q := γ) hcabs hγabs Zp Zx
        (by rw [hZpc]; exact hSp_ne) (by rw [hZxc]; exact hSn_ne) (by omega) hZp_eq hZx_eq
      have hh := hole Zp Zx e s P ε γ (by rw [hZpc]; exact hSp_ne) (by rw [hZxc]; exact hSn_ne)
        he hε hP0 hroots hdeg' hγabs hZp_eq hZx_eq hst hR
      linarith
    · have hts : e ≤ s := by omega
      have hcnt := card_add_le_of_t_le_s P hP0 hroots hts hε hcabs Zp hZp_eq
      have hek : e + 1 ≤ Zx.card := by omega
      have hek' : (e : ℝ) + 1 ≤ ((Finset.univ.filter (fun i => z i < 0)).card : ℝ) := by
        have : e + 1 ≤ (Finset.univ.filter (fun i => z i < 0)).card :=
          hek.trans (by rw [hZxc]; exact Finset.card_le_card hNfull)
        exact_mod_cast this
      have hat : Real.arctan 4 < Real.pi / 2 := Real.arctan_lt_pi_div_two 4
      have hs0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < z i),
          Real.arctan (4 * ((1 - z i) / (1 + z i))) := Finset.sum_nonneg hatn
      have h3 : (e : ℝ) * Real.arctan 4 ≤ (e : ℝ) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hat.le (Nat.cast_nonneg _)
      have h5 : (e : ℝ) * (Real.pi / 2) ≤
          (((Finset.univ.filter (fun i => z i < 0)).card : ℝ) - 1) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have hm0 : 0 ≤ (17 / 4) * ((Finset.univ.filter (fun i => 0 < z i)).card : ℝ) *
          (1 / 100) ^ 2 / (1 - (1 / 100) ^ 2) := div_nonneg (by positivity) (by norm_num)
      linarith [Real.pi_pos]

end Final

end

end CatalanMeasure.GenD.Signed.PhysicalPick

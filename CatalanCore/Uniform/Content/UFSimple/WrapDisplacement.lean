module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

/-! # Schur displacement with independent core row and column coordinates

The two diagonal coordinate matrices may differ. This is the form needed
after eliminating the actual balanced pairs in a wrapped or prefix chain.
-/

open Matrix

namespace CatalanCore.Uniform.Content.UFSimple.WrapDisplacement

variable {R ι κ ρ : Type*} [CommRing R]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ρ]

/-- Inverse displacement with independent left and right coordinate matrices. -/
theorem inverse_displacement (Q Di Dj : Matrix ι ι R)
    (G : Matrix ι ρ R) (H : Matrix ρ ι R)
    (hQ : IsUnit Q.det) (h : Di * Q - Q * Dj = G * H) :
    Dj * Q⁻¹ - Q⁻¹ * Di = -(Q⁻¹ * G * H * Q⁻¹) := by
  have hleft : Q⁻¹ * (Di * Q) * Q⁻¹ = Q⁻¹ * Di := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ,
      Matrix.mul_one]
  have hright : Q⁻¹ * (Q * Dj) * Q⁻¹ = Dj * Q⁻¹ := by
    rw [← Matrix.mul_assoc Q⁻¹ Q Dj, Matrix.nonsing_inv_mul Q hQ,
      Matrix.one_mul]
  have hh := congrArg (fun M => Q⁻¹ * M * Q⁻¹) h
  rw [mul_sub, sub_mul, hleft, hright] at hh
  calc
    Dj * Q⁻¹ - Q⁻¹ * Di = -(Q⁻¹ * Di - Dj * Q⁻¹) := by abel
    _ = -(Q⁻¹ * G * H * Q⁻¹) := by simp only [hh, Matrix.mul_assoc]

/-- Schur elimination preserves a factored displacement, without identifying
core row coordinates with core column coordinates. -/
theorem schur_displacement (Q Di Dj : Matrix ι ι R)
    (B : Matrix ι κ R) (C : Matrix κ ι R) (D Dz Dy : Matrix κ κ R)
    (G : Matrix ι ρ R) (H : Matrix ρ ι R)
    (Gz : Matrix κ ρ R) (Hy : Matrix ρ κ R)
    (hQ : IsUnit Q.det)
    (hA : Di * Q - Q * Dj = G * H)
    (hB : Di * B - B * Dy = G * Hy)
    (hC : Dz * C - C * Dj = Gz * H)
    (hD : Dz * D - D * Dy = Gz * Hy) :
    Dz * (D - C * Q⁻¹ * B) - (D - C * Q⁻¹ * B) * Dy =
      (Gz - C * Q⁻¹ * G) * (Hy - H * Q⁻¹ * B) := by
  have hI := inverse_displacement Q Di Dj G H hQ hA
  have hcross : Dz * (C * Q⁻¹ * B) - (C * Q⁻¹ * B) * Dy =
      (Dz * C - C * Dj) * Q⁻¹ * B +
      C * (Dj * Q⁻¹ - Q⁻¹ * Di) * B +
      C * Q⁻¹ * (Di * B - B * Dy) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  calc
    Dz * (D - C * Q⁻¹ * B) - (D - C * Q⁻¹ * B) * Dy =
        (Dz * D - D * Dy) -
          (Dz * (C * Q⁻¹ * B) - (C * Q⁻¹ * B) * Dy) := by
      simp only [mul_sub, sub_mul]
      abel
    _ = Gz * Hy - ((Gz * H) * Q⁻¹ * B +
        C * (-(Q⁻¹ * G * H * Q⁻¹)) * B + C * Q⁻¹ * (G * Hy)) := by
      rw [hcross, hD, hC, hI, hB]
    _ = (Gz - C * Q⁻¹ * G) * (Hy - H * Q⁻¹ * B) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      abel

section Cleared

open Finset

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem mixed_cleared_inverse_commutator (A N : Matrix ι ι R) (g n : R)
    (hAN : A * N = g • 1) (hNA : N * A = g • 1) (ar ac PR PC : ι → R)
    (hA : ∀ i j, n * (ac j - ar i) * A i j = PC j - PR i) (i j : ι) :
    g * (n * (ar j - ac i)) * N i j =
      (∑ k, N i k * PR k) * (∑ k, N k j) - (∑ k, N i k) * (∑ k, PC k * N k j) := by
  have e1 : ∀ k l, N i k * (n * (ac l - ar k) * A k l) * N l j =
      N i k * (PC l - PR k) * N l j := fun k l => by rw [hA k l]
  have hs : ∑ k, ∑ l, N i k * (n * (ac l - ar k) * A k l) * N l j =
      ∑ k, ∑ l, N i k * (PC l - PR k) * N l j :=
    Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => e1 k l))
  -- left: ∑_k ∑_l N i k (n (ac l - ar k) A k l) N l j = n g (ac i - ar j) N i j... in terms of sums
  have hNA' : ∀ k l, ∑ m, N k m * A m l = if k = l then g else 0 := fun k l => by
    have := congrFun (congrFun hNA k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, mul_ite] using this
  have hAN' : ∀ k l, ∑ m, A k m * N m l = if k = l then g else 0 := fun k l => by
    have := congrFun (congrFun hAN k) l
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, mul_ite] using this
  have L : ∑ k, ∑ l, N i k * (n * (ac l - ar k) * A k l) * N l j =
      n * (g * ac i * N i j) - n * (g * ar j * N i j) := by
    have h1 : ∑ k, ∑ l, N i k * (n * ac l * A k l) * N l j = n * (g * ac i * N i j) := by
      calc ∑ k, ∑ l, N i k * (n * ac l * A k l) * N l j
          = ∑ l, n * ac l * N l j * (∑ k, N i k * A k l) := by
            rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro l _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
        _ = ∑ l, n * ac l * N l j * (if i = l then g else 0) := by
            apply Finset.sum_congr rfl; intro l _; rw [hNA']
        _ = n * (g * ac i * N i j) := by
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]; ring
    have h2 : ∑ k, ∑ l, N i k * (n * ar k * A k l) * N l j = n * (g * ar j * N i j) := by
      calc ∑ k, ∑ l, N i k * (n * ar k * A k l) * N l j
          = ∑ k, n * ar k * N i k * (∑ l, A k l * N l j) := by
            apply Finset.sum_congr rfl; intro k _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
        _ = ∑ k, n * ar k * N i k * (if k = j then g else 0) := by
            apply Finset.sum_congr rfl; intro k _; rw [hAN']
        _ = n * (g * ar j * N i j) := by
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring
    rw [← h1, ← h2, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have Rr : ∑ k, ∑ l, N i k * (PC l - PR k) * N l j =
      (∑ k, N i k) * (∑ k, PC k * N k j) - (∑ k, N i k * PR k) * (∑ k, N k j) := by
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; ring
  rw [hs] at L
  rw [Rr] at L
  linear_combination L

theorem mixed_cleared_schur_displacement (A N : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (g n : R)
    (hAN : A * N = g • 1) (hNA : N * A = g • 1)
    (ar ac PR PC : ι → R) (xr Pr xc Pc : κ → R)
    (hA : ∀ i j, n * (ac j - ar i) * A i j = PC j - PR i)
    (hB : ∀ i y, n * (xc y - ar i) * B i y = Pc y - PR i)
    (hC : ∀ z i, n * (ac i - xr z) * C z i = PC i - Pr z)
    (hD : ∀ z y, n * (xc y - xr z) * D z y = Pc y - Pr z) (z y : κ) :
    g * (n * (xc y - xr z)) * (g * D z y - (C * N * B) z y) =
      (g - ∑ i, C z i * ∑ k, N i k) * (g * Pc y - ∑ j, (∑ k, PC k * N k j) * B j y) -
      (g * Pr z - ∑ i, C z i * ∑ k, N i k * PR k) * (g - ∑ j, (∑ k, N k j) * B j y) := by
  set U1 := ∑ i, C z i * ∑ k, N i k with hU1
  set UP := ∑ i, C z i * ∑ k, N i k * PR k with hUP
  set W1 := ∑ j, (∑ k, N k j) * B j y with hW1
  set PW := ∑ j, (∑ k, PC k * N k j) * B j y with hPW
  have hS : (C * N * B) z y = ∑ i, ∑ j, C z i * N i j * B j y := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have key : ∀ i j, g * (n * (xc y - xr z)) * (C z i * N i j * B j y) =
      (C z i * (∑ k, N i k * PR k)) * ((∑ k, N k j) * B j y) -
        (C z i * (∑ k, N i k)) * ((∑ k, PC k * N k j) * B j y) +
      (g * (Pc y * (C z i * N i j) - C z i * (N i j * PR j)) +
      g * ((PC i * N i j * B j y) - Pr z * (N i j * B j y))) := by
    intro i j
    have hB' : n * xc y * B j y = n * ar j * B j y + Pc y - PR j := by
      have := hB j y; linear_combination this
    have hC' : n * xr z * C z i = n * ac i * C z i - PC i + Pr z := by
      have := hC z i; linear_combination -this
    have hK := mixed_cleared_inverse_commutator A N g n hAN hNA ar ac PR PC hA i j
    linear_combination (g * C z i * N i j) * hB' - (g * N i j * B j y) * hC' +
      (C z i * B j y) * hK
  have f1 : ∑ i, ∑ j, (C z i * (∑ k, N i k * PR k)) * ((∑ k, N k j) * B j y) = UP * W1 := by
    rw [hUP, hW1, Finset.sum_mul_sum]
  have f2 : ∑ i, ∑ j, (C z i * (∑ k, N i k)) * ((∑ k, PC k * N k j) * B j y) = U1 * PW := by
    rw [hU1, hPW, Finset.sum_mul_sum]
  have f3 : ∑ i, ∑ j, g * (Pc y * (C z i * N i j) - C z i * (N i j * PR j)) =
      g * (Pc y * U1 - UP) := by
    simp only [hU1, hUP, Finset.mul_sum, mul_sub, ← Finset.sum_sub_distrib]
  have f4 : ∑ i, ∑ j, g * ((PC i * N i j * B j y) - Pr z * (N i j * B j y)) =
      g * (PW - Pr z * W1) := by
    rw [Finset.sum_comm]
    simp only [hPW, hW1, Finset.mul_sum, Finset.sum_mul, mul_sub, ← Finset.sum_sub_distrib]
  have hsum : g * (n * (xc y - xr z)) * (C * N * B) z y =
      UP * W1 - U1 * PW + (g * (Pc y * U1 - UP) + g * (PW - Pr z * W1)) := by
    rw [hS, Finset.mul_sum]
    simp_rw [Finset.mul_sum, key]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [f1, f2, f3, f4]
  have hD' : g * (n * (xc y - xr z)) * (g * D z y) = g * g * (Pc y - Pr z) := by
    have := hD z y; linear_combination (g * g) * this
  rw [mul_sub, hD', hsum]
  ring

end Cleared

end CatalanCore.Uniform.Content.UFSimple.WrapDisplacement

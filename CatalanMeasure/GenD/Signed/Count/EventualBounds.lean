module

public import CatalanMeasure.GenD.Signed.Count.ScalarJetHost
public import CatalanMeasure.GenD.Signed.Count.DualRestriction
public import CatalanMeasure.GenD.Signed.Count.Relations

@[expose] public section
set_option Elab.async false

/-!
# Count layer: from a host to a nullity bound, uniform integer/leading error

* `nullity_ge_euler`: a `CountHost` gives `euler (m, widths, row spaces) S ≤ ν(N,p)` for EVERY
  subspace `S ≤ Dual V` (`S = ann U`).
* `euler_affine`, `euler_error_bound`: for integer weights `N·lead + β` the Euler value differs from
  `N·euler(lead)` by at most `d (|β_c| + Σ_j |β_j|)` uniformly in `S` (`d = dim V`).
* `nullity_ge_scaled`: combines them with any relation bound (P1/P5/P7) stated for the leading
  weights.
* `absorb_haircut`: an additive constant `B` is absorbed into a `10⁻⁶`-type haircut once `N ≥ B/η`.
-/

namespace CatalanMeasure.GenD.Signed.Count.EventualBounds
open Module Finset Decay2ScalarJetHost CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Signed.Count.DualRestriction
  CatalanMeasure.GenD.Signed.Count.Relations CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

section Bridge
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
variable {C : Type*} [Fintype C]
variable {S : SlotSystem P N p} {m : ℕ} {e width : C → ℕ}
  {B : ∀ c, V →ₗ[ZMod p] (Fin (e c) → ZMod p)}
  {lam : ∀ c, Fin (width c) → Fin m → ZMod p} {a r : ℕ}

/-- **Euler form of the host count.** -/
theorem nullity_ge_euler (I : CountHost S m e width B lam a r)
    (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hq : P.q N = a * p + r) (Sd : Submodule (ZMod p) (Dual (ZMod p) V)) :
    euler (m : ℝ) (fun c => (width c : ℝ)) (fun c => rowSpace (B c)) Sd ≤ (nullity P N p : ℝ) := by
  have h := I.count_int hP hN hp2 hH hq Sd.dualCoannihilator
  have hU := finrank_coannihilator Sd
  have hrk : ∀ c, (finrank (ZMod p) (LinearMap.range ((B c).comp Sd.dualCoannihilator.subtype)) : ℤ)
      = finrank (ZMod p) (LinearMap.range (B c)) -
        finrank (ZMod p) (rowSpace (B c) ⊓ Sd : Submodule (ZMod p) _) := by
    intro c
    have := rank_restrict_coannihilator (B c) Sd
    omega
  have hR : ∀ c, finrank (ZMod p) (rowSpace (B c)) = finrank (ZMod p) (LinearMap.range (B c)) :=
    fun c => finrank_rowSpace (B c)
  simp only [hrk] at h
  have h' : ((m : ℤ) * ((finrank (ZMod p) V : ℤ) - finrank (ZMod p) Sd) -
      ∑ c, (width c : ℤ) * ((finrank (ZMod p) (rowSpace (B c)) : ℤ) -
        finrank (ZMod p) (rowSpace (B c) ⊓ Sd : Submodule (ZMod p) _))) ≤ (nullity P N p : ℤ) := by
    have e1 : (finrank (ZMod p) Sd.dualCoannihilator : ℤ) =
        finrank (ZMod p) V - finrank (ZMod p) Sd := by omega
    rw [e1] at h
    simpa only [hR] using h
  have h'' : ((((m : ℤ) * ((finrank (ZMod p) V : ℤ) - finrank (ZMod p) Sd) -
      ∑ c, (width c : ℤ) * ((finrank (ZMod p) (rowSpace (B c)) : ℤ) -
        finrank (ZMod p) (rowSpace (B c) ⊓ Sd : Submodule (ZMod p) _)) : ℤ)) : ℝ) ≤
        ((nullity P N p : ℤ) : ℝ) := by exact_mod_cast h'
  unfold euler
  push_cast at h''
  simpa using h''

end Bridge

section Error
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {J : Type*} [Fintype J]

theorem euler_affine (N c0 bc : ℝ) (w0 bw : J → ℝ) (R : J → Submodule K (Dual K V))
    (S : Submodule K (Dual K V)) :
    euler (N * c0 + bc) (fun j => N * w0 j + bw j) R S =
      N * euler c0 w0 R S + euler bc bw R S := by
  unfold euler
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  ring

theorem abs_euler_le (c : ℝ) (w : J → ℝ) (R : J → Submodule K (Dual K V))
    (S : Submodule K (Dual K V)) :
    |euler c w R S| ≤ finrank K V * (|c| + ∑ j, |w j|) := by
  have hd : (0 : ℝ) ≤ finrank K V := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ (finrank K V : ℝ) - finrank K S := by
    have : finrank K S ≤ finrank K V := finrank_dual_le_of_sub S
    have : (finrank K S : ℝ) ≤ finrank K V := by exact_mod_cast this
    linarith
  have h1' : (finrank K V : ℝ) - finrank K S ≤ finrank K V := by
    have := (Nat.cast_nonneg (finrank K S) : (0:ℝ) ≤ finrank K S); linarith
  have h2 : ∀ j, 0 ≤ (finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _) ∧
      (finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _) ≤ finrank K V := by
    intro j
    have h3 : finrank K (R j ⊓ S : Submodule K _) ≤ finrank K (R j) :=
      Submodule.finrank_mono inf_le_left
    have h4 := rank_le (R j) S
    have h5 : finrank K S ≤ finrank K V := finrank_dual_le_of_sub S
    constructor
    · have : (finrank K (R j ⊓ S : Submodule K _) : ℝ) ≤ finrank K (R j) := by exact_mod_cast h3
      linarith
    · have : ((finrank K (R j) - finrank K (R j ⊓ S : Submodule K _) : ℕ) : ℝ) ≤ finrank K V := by
        exact_mod_cast (h4.trans (Nat.sub_le _ _))
      rwa [Nat.cast_sub h3] at this
  unfold euler
  have hc : |c * ((finrank K V : ℝ) - finrank K S)| ≤ |c| * finrank K V := by
    rw [abs_mul, abs_of_nonneg h1]
    exact mul_le_mul_of_nonneg_left h1' (abs_nonneg _)
  have hw : |∑ j, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _))| ≤
      ∑ j, |w j| * finrank K V := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (h2 j).1]
    exact mul_le_mul_of_nonneg_left (h2 j).2 (abs_nonneg _)
  calc |c * ((finrank K V : ℝ) - finrank K S) -
      ∑ j, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _))|
      ≤ |c * ((finrank K V : ℝ) - finrank K S)| +
        |∑ j, w j * ((finrank K (R j) : ℝ) - finrank K (R j ⊓ S : Submodule K _))| :=
        abs_sub _ _
    _ ≤ |c| * finrank K V + ∑ j, |w j| * finrank K V := add_le_add hc hw
    _ = finrank K V * (|c| + ∑ j, |w j|) := by rw [← Finset.sum_mul]; ring

/-- Uniform bounded error between the integer-weight Euler value and `N` times the leading one. -/
theorem euler_scaled_ge (N c0 bc B0 : ℝ) (w0 bw : J → ℝ) (R : J → Submodule K (Dual K V))
    (S : Submodule K (Dual K V)) (hbc : |bc| ≤ B0) (hbw : ∀ j, |bw j| ≤ B0) :
    N * euler c0 w0 R S - finrank K V * (1 + Fintype.card J) * B0 ≤
      euler (N * c0 + bc) (fun j => N * w0 j + bw j) R S := by
  rw [euler_affine]
  have := abs_euler_le bc bw R S
  have h1 : ∑ j, |bw j| ≤ ∑ _j : J, B0 := Finset.sum_le_sum fun j _ => hbw j
  have hd : (0 : ℝ) ≤ finrank K V := Nat.cast_nonneg _
  have h2 : |bc| + ∑ j, |bw j| ≤ (1 + Fintype.card J) * B0 := by
    simp at h1
    nlinarith
  have h3 : finrank K V * (|bc| + ∑ j, |bw j|) ≤ finrank K V * ((1 + Fintype.card J) * B0) :=
    mul_le_mul_of_nonneg_left h2 hd
  have h4 := neg_abs_le (euler bc bw R S)
  nlinarith

end Error

/-- **Eventual absorption.** A constant error `B` against a haircut `η > 0` disappears for
`N ≥ B / η`. -/
theorem haircut_ge {N B η x ν : ℝ} (hη : 0 < η) (hN : B / η ≤ N)
    (h : N * x - B ≤ ν) : N * (x - η) ≤ ν := by
  have : B ≤ N * η := by
    have := (div_le_iff₀ hη).mp hN
    linarith
  nlinarith

end
end CatalanMeasure.GenD.Signed.Count.EventualBounds
#print axioms CatalanMeasure.GenD.Signed.Count.EventualBounds.nullity_ge_euler
#print axioms CatalanMeasure.GenD.Signed.Count.EventualBounds.euler_scaled_ge
#print axioms CatalanMeasure.GenD.Signed.Count.EventualBounds.haircut_ge

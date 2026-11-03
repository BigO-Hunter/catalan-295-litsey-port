module
public import CatalanMeasure.GenD.RankFam
@[expose] public section

/-!
# Theorem S for a general design (GenD)

For `P : Parameters`, `N > 0`, an odd prime `p` with `H < p^2`, (H1) `q + h ≤ (p+1)/2` and
(H2) `n ≤ 4p + 2g + 1`, put `e = (p+1)/2 - q - h`, `a = b + q + 2g`, `Lam = g + q + h`,
`m0 = max(b + q, L + Lam - 4p)`, `m1 = min(p, L - 3p, a + 1)`.  Then the left nullity of the
filtered scaled residue matrix is at least `m1 - m0 - e` (truncated at zero).
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

/-- `e = (p+1)/2 - q - h`. -/
def sE (P : Parameters) (N p : ℕ) : ℕ := (p + 1) / 2 - P.q N - P.h N

/-- Lower residue bound `max(b+q, L+Lam-4p)`. -/
def sM0 (P : Parameters) (N p : ℕ) : ℕ :=
  max (P.b N + P.q N) (P.L N + (P.g N + P.q N + P.h N) - 4 * p)

/-- Upper residue bound `min(p, L-3p, a+1)`. -/
def sM1 (P : Parameters) (N p : ℕ) : ℕ :=
  min p (min (P.L N - 3 * p) (P.b N + P.q N + 2 * P.g N + 1))

/-- The `3w + e` functionals of Theorem S. -/
def sFam (P : Parameters) (N p m0 w e : ℕ) [Fact p.Prime] :
    Fin (3 * w + e) → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := fun a =>
  if a.val < w then coeffD P N p (p + m0 + a.val)
  else if a.val < 2 * w then coeffD P N p (2 * p + m0 + (a.val - w))
  else if a.val < 3 * w then coeffD P N p (3 * p + m0 + (a.val - 2 * w))
  else coeffQ P N p (4 * p + m0 + (a.val - 3 * w))

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- **Theorem S, block form.** -/
theorem s_block_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    {m0 m1 : ℕ} (hm0b : P.b N + P.q N ≤ m0)
    (hm0t : P.L N + (P.g N + P.q N + P.h N) ≤ 4 * p + m0)
    (hm1p : m1 ≤ p) (hm1a : m1 ≤ P.b N + P.q N + 2 * P.g N + 1) (hm1L : 3 * p + m1 ≤ P.L N)
    (he : m0 + sE P N p ≤ m1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (m1 - m0 - sE P N p) ≤ P.n N := by
  have hgn := two_g_lt_n hP hN
  have hodd := odd_of_ne_two hp2
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  have hHd : P.H N = P.C N + P.h N := rfl
  set w := m1 - m0 with hw
  set e := sE P N p with he'
  have hsE : e = (p + 1) / 2 - P.q N - P.h N := rfl
  have hr := rank_of_digit_block (J0 := 0) (nJ := 4) (m0 := m0) (m1 := m1) hP hN hp2 hH
    (by omega) hm1p
    (fun J mu _ _ h0 h1 => by omega)
    (fun J mu _ hJ h0 h1 => by
      have := Nat.mul_le_mul_right p (show J ≤ 3 by omega)
      omega)
    (m := 3 * w + e) (sFam P N p m0 w e) (by
      intro c hc mu h0 h1 u
      have hseq := digitSeq_design (P := P) hp2 hgn hH1 hH2 c
      have hfam : ∀ a : Fin (3 * w + e), sFam P N p m0 w e a c = 0 := hc
      refine digits_vanish_S hseq (two_ne_zero_zmod hp2) (m0 := m0) (m1 := m1) hm1p
        (by omega) (by omega) (by omega) (by omega) (by omega) he ?_ ?_ ?_ ?_ mu h0 h1 u
      · intro mu' h0' h1'
        have := hfam ⟨mu' - m0, by omega⟩
        simp only [sFam, if_pos (show mu' - m0 < w by omega), coeffD_apply] at this
        rwa [show p + m0 + (mu' - m0) = p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨w + (mu' - m0), by omega⟩
        simp only [sFam, if_neg (show ¬ (w + (mu' - m0) < w) by omega),
          if_pos (show w + (mu' - m0) < 2 * w by omega), coeffD_apply] at this
        rwa [show 2 * p + m0 + (w + (mu' - m0) - w) = 2 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨2 * w + (mu' - m0), by omega⟩
        simp only [sFam, if_neg (show ¬ (2 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (2 * w + (mu' - m0) < 2 * w) by omega),
          if_pos (show 2 * w + (mu' - m0) < 3 * w by omega), coeffD_apply] at this
        rwa [show 3 * p + m0 + (2 * w + (mu' - m0) - 2 * w) = 3 * p + mu' by omega] at this
      · intro mu' h0' h1'
        have := hfam ⟨3 * w + (mu' - m0), by omega⟩
        simp only [sFam, if_neg (show ¬ (3 * w + (mu' - m0) < w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 2 * w) by omega),
          if_neg (show ¬ (3 * w + (mu' - m0) < 3 * w) by omega), coeffQ_apply] at this
        rwa [show 4 * p + m0 + (3 * w + (mu' - m0) - 3 * w) = 4 * p + mu' by omega] at this)
  omega

/-- **Theorem S (general design).**  The left nullity of the filtered matrix is at least
`m1 - m0 - e`. -/
theorem s_rank (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (sM1 P N p - sM0 P N p - sE P N p) ≤ P.n N := by
  by_cases hnt : sM0 P N p + sE P N p < sM1 P N p
  · have hLd : P.L N = P.n N + P.b N + P.q N := rfl
    have h0 : sM0 P N p = max (P.b N + P.q N) (P.L N + (P.g N + P.q N + P.h N) - 4 * p) := rfl
    have h1 : sM1 P N p = min p (min (P.L N - 3 * p) (P.b N + P.q N + 2 * P.g N + 1)) := rfl
    exact s_block_rank hP hN hp2 hH hH1 hH2 (m0 := sM0 P N p) (m1 := sM1 P N p)
      (by omega) (by omega) (by omega) (by omega) (by omega) hnt.le
  · have := Matrix.rank_le_width (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val))
    omega

end
end
end CatalanMeasure.GenD

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

/-- Lower endpoint for the selected digit of Theorem S. -/
def sM0_k (P : Parameters) (N p k : ℕ) : ℕ :=
  max (P.b N + P.q N) (P.L N + (P.g N + P.q N + P.h N) - k * p)

/-- Upper endpoint; the support hypothesis of `digitSeq_design` is unchanged. -/
def sM1_k (P : Parameters) (N p k : ℕ) : ℕ :=
  min p (min (P.L N - (k - 1) * p) (P.b N + P.q N + 2 * P.g N + 1))

/-- The `(k-1)w+e` coefficient constraints, decoded only at positive width. -/
def sFam_k (P : Parameters) (N p k m0 w e : ℕ) [Fact p.Prime] :
    Fin ((k - 1) * w + e) → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p := fun i =>
  if i.val < (k - 1) * w then
    coeffD P N p ((i.val / w + 1) * p + m0 + i.val % w)
  else coeffQ P N p (k * p + m0 + (i.val - (k - 1) * w))

theorem s_block_rank_k {P : Parameters} {N p k : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1)
    {m0 m1 : ℕ} (hm0b : P.b N + P.q N ≤ m0)
    (hm0t : P.L N + (P.g N + P.q N + P.h N) ≤ k * p + m0)
    (hm1p : m1 ≤ p) (hm1a : m1 ≤ P.b N + P.q N + 2 * P.g N + 1)
    (hm1L : (k - 1) * p + m1 ≤ P.L N) (he : m0 + sE P N p ≤ m1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r j : Fin (P.n N) => filteredEntryRat P 0 N r.val j.val)).rank +
        (m1 - m0 - sE P N p) ≤ P.n N := by
  by_cases hw0 : m1 ≤ m0
  · simpa [Nat.sub_eq_zero_of_le hw0] using
      Matrix.rank_le_width (scaledResidueMatrix (p := p)
        (Matrix.of fun r j : Fin (P.n N) => filteredEntryRat P 0 N r.val j.val))
  have hgn := two_g_lt_n hP hN
  have hp0 := (Fact.out : p.Prime).pos
  have hLd : P.L N = P.n N + P.b N + P.q N := rfl
  have hCd : P.C N = P.L N + P.g N := rfl
  let w := m1 - m0
  let e := sE P N p
  have hwpos : 0 < w := by dsimp [w]; omega
  have hew : e ≤ w := by dsimp [w, e]; omega
  have hkp : (k + 1) * p = k * p + p := by rw [Nat.add_mul, Nat.one_mul]
  have hkw : k * w = (k - 1) * w + w := by
    have hh := congrArg (fun t : ℕ => t * w) (Nat.sub_add_cancel (show 1 ≤ k by omega))
    simpa only [Nat.add_mul, Nat.one_mul] using hh.symm
  have hr := rank_of_digit_block (J0 := 0) (nJ := k) (m0 := m0) (m1 := m1)
    hP hN hp2 hH (by omega) hm1p
    (fun J mu _ _ h0 _ => by omega)
    (fun J mu _ hJ h0 h1 => by
      have hJp := Nat.mul_le_mul_right p (show J ≤ k - 1 by omega)
      omega)
    (m := (k - 1) * w + e) (sFam_k P N p k m0 w e) (by
      intro c hc mu h0 h1 u
      have hseq := digitSeq_design (P := P) hp2 hgn hH1 hH2 c
      refine digits_vanish_Sk hseq hk (two_ne_zero_zmod hp2) hm1p hm1a hm1L
        (by omega) (by
          have hodd := odd_of_ne_two hp2
          have hpp := (Fact.out : p.Prime).two_le
          have heq : (k + 1) * p = k * p + p := by rw [Nat.add_mul, Nat.one_mul]
          omega) (by omega) he ?_ ?_ mu h0 h1 u
      · intro j hj0 hj mu' h0' h1'
        let i := (j - 1) * w + (mu' - m0)
        have hrem : mu' - m0 < w := by dsimp [w]; omega
        have hjw := Nat.mul_le_mul_right w (show j ≤ k - 1 by omega)
        have hjweq : j * w = (j - 1) * w + w := by
          have hh := congrArg (fun t : ℕ => t * w) (Nat.sub_add_cancel hj0)
          simpa only [Nat.add_mul, Nat.one_mul] using hh.symm
        have hib : i < (k - 1) * w := by dsimp [i]; omega
        have hdiv : i / w = j - 1 := by
          dsimp [i]
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hwpos,
            Nat.div_eq_of_lt hrem, zero_add]
        have hmod : i % w = mu' - m0 := by
          dsimp [i]
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
        have hh := hc ⟨i, by omega⟩
        simp only [sFam_k, if_pos hib, hdiv, hmod, coeffD_apply] at hh
        rwa [show (j - 1 + 1) * p + m0 + (mu' - m0) = j * p + mu' by
          rw [Nat.sub_add_cancel hj0]; omega] at hh
      · intro mu' h0' h1'
        change mu' < m0 + e at h1'
        have hseedBound : mu' - m0 < e := by omega
        have hh := hc ⟨(k - 1) * w + (mu' - m0), by omega⟩
        simp only [sFam_k,
          if_neg (show ¬ ((k - 1) * w + (mu' - m0) < (k - 1) * w) by omega),
          coeffQ_apply] at hh
        rwa [show k * p + m0 + ((k - 1) * w + (mu' - m0) - (k - 1) * w) =
          k * p + mu' by omega] at hh)
  dsimp only [w, e] at hr hkw hew
  omega

theorem s_rank_k {P : Parameters} {N p k : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (hH1 : P.q N + P.h N ≤ (p + 1) / 2) (hH2 : P.n N ≤ 4 * p + 2 * P.g N + 1) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r j : Fin (P.n N) => filteredEntryRat P 0 N r.val j.val)).rank +
        (sM1_k P N p k - sM0_k P N p k - sE P N p) ≤ P.n N := by
  by_cases hnt : sM0_k P N p k + sE P N p < sM1_k P N p k
  · have h0 : sM0_k P N p k = max (P.b N + P.q N)
        (P.L N + (P.g N + P.q N + P.h N) - k * p) := rfl
    have h1 : sM1_k P N p k = min p
        (min (P.L N - (k - 1) * p) (P.b N + P.q N + 2 * P.g N + 1)) := rfl
    exact s_block_rank_k hk hP hN hp2 hH hH1 hH2
      (m0 := sM0_k P N p k) (m1 := sM1_k P N p k)
      (by omega) (by omega) (by omega) (by omega) (by omega) hnt.le
  · have := Matrix.rank_le_width (scaledResidueMatrix (p := p)
      (Matrix.of fun r j : Fin (P.n N) => filteredEntryRat P 0 N r.val j.val))
    omega

end
end CatalanMeasure.GenD

#print axioms CatalanMeasure.GenD.s_block_rank_k
#print axioms CatalanMeasure.GenD.s_rank_k

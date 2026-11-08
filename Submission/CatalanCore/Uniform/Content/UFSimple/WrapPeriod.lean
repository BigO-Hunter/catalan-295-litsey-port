module

public import Submission.CatalanCore.Uniform.Content.UFSimple.Sep
public import Submission.CatalanCore.Uniform.Content.UFFamily.Entries

@[expose] public section

/-! # Noncancellation on a complete period

An Ioc interval of length p still contains at most one pole from each family.
This supplies the actual balanced-pair unit used by the wrapped core.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.UFFamily
  CatalanCore.Uniform.Content.UFSimple

namespace CatalanCore.Uniform.Content.UFSimple.WrapPeriod

variable {p : ℕ} [Fact p.Prime]

theorem eq_of_dvd_period {a b k k' : ℕ} (hk : a < k ∧ k ≤ b) (hk' : a < k' ∧ k' ≤ b)
    (hlen : b ≤ a + p) (h : (p : ℤ) ∣ (k : ℤ) - k') : k = k' := by
  obtain ⟨t, ht⟩ := h
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : (k : ℤ) - k' < p := by omega
  have h2 : -(p : ℤ) < (k : ℤ) - k' := by omega
  have ht0 : t = 0 := by
    rcases lt_trichotomy t 0 with h | h | h
    · have : (p : ℤ) * t ≤ -p := by nlinarith
      linarith
    · exact h
    · have : (p : ℤ) ≤ p * t := by nlinarith
      linarith
  subst ht0
  simp at ht
  omega

/-- At most one multiple of `p` in a short window. -/
theorem sum_inv_mult_period (a b : ℕ) (hlen : b ≤ a + p) :
    (∑ k ∈ Ioc a b, invResidue p k) =
      if h : ∃ k ∈ Ioc a b, p ∣ k then invResidue p h.choose else 0 := by
  classical
  split_ifs with h
  · have hk := h.choose_spec
    refine Finset.sum_eq_single_of_mem _ hk.1 fun k hk1 hne => ?_
    unfold invResidue
    rw [if_neg]
    intro hd
    apply hne
    have m1 := Finset.mem_Ioc.1 hk1
    have m2 := Finset.mem_Ioc.1 hk.1
    refine eq_of_dvd_period m1 m2 hlen ?_
    have := Int.natCast_dvd_natCast.2 hd
    have := Int.natCast_dvd_natCast.2 hk.2
    exact dvd_sub (by assumption) (by assumption)
  · refine Finset.sum_eq_zero fun k hk => ?_
    unfold invResidue
    rw [if_neg]
    exact fun hd => h ⟨k, hk, hd⟩

/-- At most one pole `p ∣ q k - o` in a short window. -/
theorem sum_inv_pole_period (q o a b : ℕ) (hqp : q < p) (hq : 0 < q) (hoq : o < q)
    (hlen : b ≤ a + p) :
    (∑ k ∈ Ioc a b, invResidue p (q * k - o)) =
      if h : ∃ k ∈ Ioc a b, p ∣ q * k - o then invResidue p (q * h.choose - o) else 0 := by
  classical
  split_ifs with h
  · have hk := h.choose_spec
    refine Finset.sum_eq_single_of_mem _ hk.1 fun k hk1 hne => ?_
    unfold invResidue
    rw [if_neg]
    intro hd
    apply hne
    have m1 := Finset.mem_Ioc.1 hk1
    have m2 := Finset.mem_Ioc.1 hk.1
    refine eq_of_dvd_period m1 m2 hlen ?_
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : p.Prime)
    have e1 : (((q * k - o : ℕ)) : ℤ) = q * k - o := by
      have h' : q ≤ q * k := Nat.le_mul_of_pos_right q (by omega)
      have : o ≤ q * k := by omega
      push_cast [this]; ring
    have e2 : (((q * h.choose - o : ℕ)) : ℤ) = q * h.choose - o := by
      have h' : q ≤ q * h.choose := Nat.le_mul_of_pos_right q (by omega)
      have : o ≤ q * h.choose := by omega
      push_cast [this]; ring
    have d1 := Int.natCast_dvd_natCast.2 hd
    have d2 := Int.natCast_dvd_natCast.2 hk.2
    rw [e1] at d1
    rw [e2] at d2
    have d3 : (p : ℤ) ∣ (q : ℤ) * ((k : ℤ) - h.choose) := by
      have := dvd_sub d1 d2
      have e : (q : ℤ) * k - o - (q * h.choose - o) = (q : ℤ) * ((k : ℤ) - h.choose) := by ring
      rwa [e] at this
    rcases hpp.dvd_or_dvd d3 with hq' | hq'
    · exfalso
      have := Int.le_of_dvd (by exact_mod_cast hq) hq'
      have : (q : ℤ) < p := by exact_mod_cast hqp
      omega
    · exact hq'
  · refine Finset.sum_eq_zero fun k hk => ?_
    unfold invResidue
    rw [if_neg]
    exact fun hd => h ⟨k, hk, hd⟩

set_option maxHeartbeats 1000000 in
/-- The pure arithmetic core of the separation lemma. -/
theorem sum_tm_ne_period (q o a b : ℕ) (hqp : q < p) (ho : 0 < o) (hoq : o < q) (hab : a < b)
    (hlen : b ≤ a + p) (hbp : b < p * p)
    (hsq : ∀ k, a < k → k ≤ b → ¬ p ^ 2 ∣ q * k - o)
    (hs : ∃ k, a < k ∧ k ≤ b ∧ (p ∣ k ∨ p ∣ q * k - o)) :
    (∑ k ∈ Ioc a b, tm p q o 1 k) ≠ 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  have hq : 0 < q := by omega
  unfold tm
  simp only [pow_one]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_inv_mult_period a b hlen,
    sum_inv_pole_period q o a b hqp hq hoq hlen]
  have hqz : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd hq hd; omega
  -- the multiple: `k₁ = p m`, `1 ≤ m < p`
  have hmult : ∀ k, a < k → k ≤ b → p ∣ k →
      invResidue p k = ((k / p : ℕ) : ZMod p)⁻¹ ∧ ((k / p : ℕ) : ZMod p) ≠ 0 := by
    intro k hk1 hk2 hd
    refine ⟨by unfold invResidue; rw [if_pos hd], ?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h2
    obtain ⟨m, hm⟩ := hd
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    rw [hm, Nat.mul_div_cancel_left _ hp.pos] at h2
    have := Nat.le_of_dvd hm0 h2
    have h3 : p * p ≤ p * m := Nat.mul_le_mul_left p this
    have h4 : p * m ≤ b := hm ▸ hk2
    have h5 : b < p * p := hbp
    linarith
  -- the pole: `q k₂ - o = p n`, `p ∤ n`
  have hpole : ∀ k, a < k → k ≤ b → p ∣ q * k - o →
      invResidue p (q * k - o) = (((q * k - o) / p : ℕ) : ZMod p)⁻¹ ∧
        (((q * k - o) / p : ℕ) : ZMod p) ≠ 0 := by
    intro k hk1 hk2 hd
    refine ⟨by unfold invResidue; rw [if_pos hd], ?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h2
    apply hsq k hk1 hk2
    obtain ⟨n, hn⟩ := hd
    rw [hn, Nat.mul_div_cancel_left _ hp.pos] at h2
    obtain ⟨n', hn'⟩ := h2
    exact ⟨n', by rw [hn, hn', pow_two, mul_assoc]⟩
  -- the multiple and the pole are different nodes
  split_ifs with h1 h2 h2
  · obtain ⟨hk1, hd1⟩ := h1.choose_spec
    obtain ⟨hk2, hd2⟩ := h2.choose_spec
    have m1 := Finset.mem_Ioc.1 hk1
    have m2 := Finset.mem_Ioc.1 hk2
    obtain ⟨e1, n1⟩ := hmult _ m1.1 m1.2 hd1
    obtain ⟨e2, n2⟩ := hpole _ m2.1 m2.2 hd2
    rw [e1, e2]
    intro hsum
    have h' : (((h1.choose / p : ℕ)) : ZMod p)⁻¹ =
        (q : ZMod p) * ((((q * h2.choose - o) / p : ℕ)) : ZMod p)⁻¹ := sub_eq_zero.1 hsum
    have heq : (((q * h2.choose - o) / p : ℕ) : ZMod p) = (q : ZMod p) * ((h1.choose / p : ℕ) : ZMod p) := by
      rw [inv_eq_iff_eq_inv, mul_inv, inv_inv] at h'
      rw [h', ← mul_assoc, mul_inv_cancel₀ hqz, one_mul]
    have hdv : (p : ℤ) ∣ (q : ℤ) * ((h1.choose / p : ℕ) : ℤ) - (((q * h2.choose - o) / p : ℕ) : ℤ) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).1
        (by simp only [Int.cast_mul, Int.cast_natCast]; exact heq)
    have hk1e : (h1.choose : ℤ) = p * ((h1.choose / p : ℕ) : ℤ) := by
      have := Nat.mul_div_cancel' hd1
      rw [← Nat.cast_mul]; exact congrArg _ this.symm
    have hk2e : (q : ℤ) * h2.choose - o = p * (((q * h2.choose - o) / p : ℕ) : ℤ) := by
      have hle' : q ≤ q * h2.choose := Nat.le_mul_of_pos_right q (by omega)
      have hle : o ≤ q * h2.choose := by omega
      have := Nat.mul_div_cancel' hd2
      have h'' : ((q * h2.choose - o : ℕ) : ℤ) = p * (((q * h2.choose - o) / p : ℕ) : ℤ) := by
        rw [← Nat.cast_mul]; exact congrArg _ this.symm
      rw [Nat.cast_sub hle, Nat.cast_mul] at h''
      linarith
    exact mult_pole_int (by exact_mod_cast hp.pos) (by exact_mod_cast hq) (by exact_mod_cast hqp)
      (by exact_mod_cast ho) (by exact_mod_cast hoq) hk1e hk2e (by omega) (by omega) hdv
  · obtain ⟨hk1, hd1⟩ := h1.choose_spec
    have m1 := Finset.mem_Ioc.1 hk1
    obtain ⟨e1, n1⟩ := hmult _ m1.1 m1.2 hd1
    rw [e1, mul_zero, sub_zero]
    exact inv_ne_zero n1
  · obtain ⟨hk2, hd2⟩ := h2.choose_spec
    have m2 := Finset.mem_Ioc.1 hk2
    obtain ⟨e2, n2⟩ := hpole _ m2.1 m2.2 hd2
    rw [e2, zero_sub, neg_ne_zero]
    exact mul_ne_zero hqz (inv_ne_zero n2)
  · exfalso
    obtain ⟨k, hk1, hk2, hk⟩ := hs
    rcases hk with hk | hk
    · exact h1 ⟨k, Finset.mem_Ioc.2 ⟨hk1, hk2⟩, hk⟩
    · exact h2 ⟨k, Finset.mem_Ioc.2 ⟨hk1, hk2⟩, hk⟩

variable {Fr : Frame} {q o N : ℕ}

/-- **Lemma S (two-term separation).** A singular index in `(a, b]`, `b - a < p`, separates the
prefix residues. -/
theorem V_ne_of_sing_period (T : TwoTermData Fr q o) (hqp : q < p) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {a b : ℕ} (hab : a < b) (hbN : b < N) (hlen : b ≤ a + p)
    (hs : ∃ k, a < k ∧ k ≤ b ∧ (p ∣ k ∨ p ∣ q * k - o)) :
    (twoTermPoleData T hN hsq hnorm hnorm0).V a ≠ (twoTermPoleData T hN hsq hnorm hnorm0).V b := by
  intro h
  have hsub := (twoTermPoleData T hN hsq hnorm hnorm0).V_sub hab.le
  rw [h, sub_self] at hsub
  have e : (∑ k ∈ Ioc a b, (twoTermPoleData T hN hsq hnorm hnorm0).dv k) =
      ∑ k ∈ Ioc a b, tm p q o 1 k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have := Finset.mem_Ioc.1 hk
    exact dv_eq T hN hsq hnorm hnorm0 (by omega) (by omega)
  rw [e] at hsub
  exact sum_tm_ne_period q o a b hqp T.o_pos T.o_lt hab hlen (lt_of_lt_of_le hbN hN)
    (fun k hk1 hk2 => hsq k (by omega) (by omega)) hs hsub.symm


/-- A complete period always contains a noncanceling ordinary pole. -/
theorem V_period_ne (T : TwoTermData Fr q o) (hqp : q<p) (hN : N≤p*p)
    (hsq : ∀ t, 1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) {a : ℕ} (ha : a+p<N) :
    (twoTermPoleData T hN hsq hnorm hnorm0).V a ≠
      (twoTermPoleData T hN hsq hnorm hnorm0).V (a+p) := by
  have hp := (Fact.out : p.Prime).pos
  have hm := Nat.mod_lt a hp
  have he := Nat.div_add_mod a p
  let k := p*(a/p)+p
  have hk1 : a<k := by dsimp [k]; omega
  have hk2 : k≤a+p := by dsimp [k]; omega
  have hdk : p∣k := by
    dsimp [k]
    exact dvd_add (dvd_mul_right p (a/p)) (dvd_refl p)
  exact V_ne_of_sing_period T hqp hN hsq hnorm hnorm0 (by omega) ha (by omega)
    ⟨k,hk1,hk2,Or.inl hdk⟩

/-- The actual p²-scaled entry of every balanced pair has nonzero reduction. -/
theorem balanced_entry_ne (T : TwoTermData Fr q o) (hqp : q<p) (hN : N<p*p)
    (hsq : ∀ t, 1≤t → t<N → ¬p^2∣q*t-o) (hnorm : Fr.norm∈S p)
    (hnorm0 : red p Fr.norm≠0) {a : ℕ} (ha : a+p<N) :
    red p ((p:ℚ)^2*Fr.Mn a (a+p)) ≠ 0 := by
  have hp := (Fact.out : p.Prime).pos
  let D := twoTermPoleData T hN.le hsq hnorm hnorm0
  have hv := V_period_ne T hqp hN.le hsq hnorm hnorm0 ha
  have gg := D.good_square hN (by omega : a<a+p) ha
  have hi : invResidue p p = (1 : ZMod p) := by
    simp [invResidue, Nat.div_self hp]
  have hdiff : a+p-a=p := by omega
  rw [gg.eq, hdiff, hi, mul_one]
  exact mul_ne_zero (inv_ne_zero hnorm0) (sub_ne_zero.mpr (Ne.symm hv))

end CatalanCore.Uniform.Content.UFSimple.WrapPeriod

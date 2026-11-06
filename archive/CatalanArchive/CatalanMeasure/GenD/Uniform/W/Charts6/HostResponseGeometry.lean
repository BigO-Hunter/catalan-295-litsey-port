module
public import CatalanMeasure.GenD.Uniform.W.Charts6.HostSourceRows
@[expose] public section
set_option Elab.async false

/-! Exact geometry of a seen physical p-step response, before row selection. -/
namespace CatalanMeasure.GenD.Uniform.W.Charts6

/-- The four interval boundaries derived from the remainder and the full
p-step column range. All arithmetic is in integers, so the endpoints are exact. -/
def responseLo (H L p a J : Nat) (S : Int) : Int :=
  max 0 (max ((H : Int) - (S + 1) * p)
    ((H : Int) - L + ((J : Int) + a - S) * p))

def responseHi (H b p cm J : Nat) (S : Int) : Int :=
  min cm (min p (min ((H : Int) - S * p)
    ((H : Int) - b + ((J : Int) - S) * p)))

theorem response_in_exact_interval {H b L p a cm j e : Nat}
    (hp : 0 < p) (hj : b ≤ j) (hl : j + a * p < L)
    (hep : e < p) (hec : e < cm)
    (hdiv : (p : Int) ∣ (H : Int) - 1 - ((j % p : Nat) : Int) - e) :
    let S := ((H : Int) - 1 - ((j % p : Nat) : Int) - e) / p
    responseLo H L p a (j / p) S ≤ (e : Int) ∧
      (e : Int) < responseHi H b p cm (j / p) S := by
  obtain ⟨s, hs⟩ := hdiv
  have hpz : (p : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have heq : ((H : Int) - 1 - ((j % p : Nat) : Int) - e) / p = s := by
    rw [hs]; exact Int.mul_ediv_cancel_left _ hpz
  dsimp only
  rw [heq]
  have hb : (b : Int) ≤ j := by exact_mod_cast hj
  have hL : (j : Int) + (a : Int) * p < L := by exact_mod_cast hl
  have hL1 : (j : Int) + (a : Int) * p + 1 ≤ L := by omega
  have hE : (e : Int) < p := by exact_mod_cast hep
  have hC : (e : Int) < cm := by exact_mod_cast hec
  have hE0 : (0 : Int) ≤ e := by positivity
  have hm : (((j % p : Nat) : Int)) < p := by exact_mod_cast Nat.mod_lt j hp
  have hm1 : ((j % p : Nat) : Int) + 1 ≤ p := by omega
  have hm0 : (0 : Int) ≤ ((j % p : Nat) : Int) := by positivity
  have hJ : (p : Int) * ((j / p : Nat) : Int) + ((j % p : Nat) : Int) = j := by
    exact_mod_cast Nat.div_add_mod j p
  simp only [responseLo, responseHi, max_le_iff, lt_min_iff]
  refine ⟨⟨hE0, ?_, ?_⟩, ⟨hC, hE, ?_, ?_⟩⟩ <;>
    nlinarith only [hs, hb, hL1, hJ, hm1, hm0]

/-- For a fixed H quotient there are exactly two candidate response labels.
The subtraction is signed, including the lower boundary when the quotient is zero. -/
theorem response_label_cases {H p j e : Nat} {S0 : Int}
    (hp : 0 < p) (he : e < p)
    (hlo : S0 * p ≤ (H : Int) - 1)
    (hhi : (H : Int) - 1 < (S0 + 1) * p)
    (hdiv : (p : Int) ∣ (H : Int) - 1 - ((j % p : Nat) : Int) - e) :
    let S := ((H : Int) - 1 - ((j % p : Nat) : Int) - e) / p
    S = S0 ∨ S = S0 - 1 := by
  obtain ⟨s, hs⟩ := hdiv
  have hpz : (0 : Int) < p := by exact_mod_cast hp
  have heq : ((H : Int) - 1 - ((j % p : Nat) : Int) - e) / p = s := by
    rw [hs]; exact Int.mul_ediv_cancel_left _ hpz.ne'
  dsimp only
  rw [heq]
  have hE : (e : Int) < p := by exact_mod_cast he
  have hE0 : (0 : Int) ≤ e := by positivity
  have hm : ((j % p : Nat) : Int) < p := by exact_mod_cast Nat.mod_lt j hp
  have hm0 : (0 : Int) ≤ ((j % p : Nat) : Int) := by positivity
  have hm1 : ((j % p : Nat) : Int) + 1 ≤ p := by omega
  have hE1 : (e : Int) + 1 ≤ p := by omega
  have h1 : s ≤ S0 := by
    by_contra hn
    have hh : (S0 + 1) * (p : Int) ≤ s * p :=
      mul_le_mul_of_nonneg_right (by omega) hpz.le
    nlinarith only [hh, hhi, hs, hE0, hm0]
  have h2 : S0 - 1 ≤ s := by
    by_contra hn
    have hh : s * (p : Int) ≤ (S0 - 2) * p :=
      mul_le_mul_of_nonneg_right (by omega) hpz.le
    nlinarith only [hh, hlo, hs, hE1, hm1]
  omega

end CatalanMeasure.GenD.Uniform.W.Charts6

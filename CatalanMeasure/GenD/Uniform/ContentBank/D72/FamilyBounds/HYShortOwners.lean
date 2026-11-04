module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.FamilyBounds.HYShort
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 8000000
namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.ContentBank.D72.HYShort
noncomputable section
private theorem hy_miss_card {D K r : Nat} (k0 : Fin K) (good : Fin D → Fin K → Prop)
    [DecidablePred (fun u : Fin D × Fin K => ¬ good u.1 u.2)]
    (hg : ∀ t k, k ≠ k0 ∨ t.val < r → good t k) :
    (Finset.univ.filter (fun u : Fin D × Fin K => ¬ good u.1 u.2)).card ≤ D-r := by
  have hh : ∀ u ∈ Finset.univ.filter (fun u : Fin D × Fin K => ¬ good u.1 u.2),
      u.2 = k0 ∧ r ≤ u.1.val := by
    intro u hu
    have hf := (Finset.mem_filter.mp hu).2
    by_contra h
    apply hf
    apply hg
    by_contra he
    push_neg at he
    exact h he
  refine (Finset.card_le_card_of_injOn (t := Finset.range (D-r))
    (fun u : Fin D × Fin K => u.1.val-r) ?_ ?_).trans_eq (Finset.card_range _)
  · intro u hu
    have h := hh u hu
    have hu' := u.1.isLt
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · intro u hu v hv huv
    have h1 := hh u hu
    have h2 := hh v hv
    have huv' : u.1.val - r = v.1.val - r := huv
    exact Prod.ext (Fin.ext (by omega)) (h1.1.trans h2.1.symm)



/-- Lower-tail variant: all failures sit in slot `k0` at offsets `t < r`. At the top slot the
lower member `hlo` leaves the row range for small `t` once `(K-2) p + (p-1)/2 ≥ n - g`. -/
private theorem hy_miss_card_low {D K r : Nat} (k0 : Fin K) (good : Fin D → Fin K → Prop)
    [DecidablePred (fun u : Fin D × Fin K => ¬ good u.1 u.2)]
    (hg : ∀ t k, k ≠ k0 ∨ r ≤ t.val → good t k) :
    (Finset.univ.filter (fun u : Fin D × Fin K => ¬ good u.1 u.2)).card ≤ r := by
  have hh : ∀ u ∈ Finset.univ.filter (fun u : Fin D × Fin K => ¬ good u.1 u.2),
      u.2 = k0 ∧ u.1.val < r := by
    intro u hu
    have hf := (Finset.mem_filter.mp hu).2
    by_contra h
    apply hf
    apply hg
    by_contra he
    push_neg at he
    exact h ⟨he.1, he.2⟩
  refine (Finset.card_le_card_of_injOn (t := Finset.range r)
    (fun u : Fin D × Fin K => u.1.val) ?_ ?_).trans_eq (Finset.card_range _)
  · intro u hu
    have h := hh u hu
    simp only [Finset.coe_range, Set.mem_Iio]
    exact h.2
  · intro u hu v hv huv
    have h1 := hh u hu
    have h2 := hh v hv
    exact Prod.ext (Fin.ext huv) (h1.1.trans h2.1.symm)


def shortHY10App (N p : Nat) : Prop :=
  1000 ≤ N ∧ 97*N < 11*p ∧ 500000*p ≤ 4409091*N ∧ ¬ p ∣ ZHY10
def shortHY10Val (N p : Nat) : Nat := ((354*N-40*p)/2)-1

theorem shortHY10Bound {N p : Nat} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P72.H N < p^2) (happ : shortHY10App N p) :
    shortHY10Val N p ≤ nullity P72 N p := by
  obtain ⟨hN0, hl, hh0, hZ⟩ := happ
  have hP : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  let D := 6*N-(p-1)/2
  let rl : Nat := 7 * p + (p-1)/2 + 1 - 66 * N
  let rt := 66 * N - 1 - 7 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 9 D (-1) ≤ rl+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card_low (k0 := (8 : Fin 9)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 9 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hlo, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rl, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
    · apply hy_miss_card (k0 := (8 : Fin 9)) (D := D) (r := rt) (good := fun t k => InRange P72 N (W.Slots.hhi p 9 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hhi, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rt, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega

  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨e,J⟩ hm
    simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
    have hJrange : P72.L N / p + 2 ≤ 14 := by
      have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12*p)
      omega
    have hJ : J < 14 := hm.1.2.trans_le hJrange
    interval_cases J <;> simp only [HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm <;> (try simp only [and_true] at hm) <;> omega
  have hNoBad (j : Nat) (hj : P72.b N ≤ j) (hL : j < P72.L N) :
      ¬ HyBad (hyEmax P72 N p D) (hyA0 P72 N p) (hyNQ P72 N p D) 10 p
        (hyEta P72 N p 10) (j%p) (j/p) := by
    intro h
    have hmem : (j%p,j/p) ∈ edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D := by
      have hd := Nat.div_add_mod' j p
      have hb := Nat.div_le_div_right hL.le (c := p)
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨Nat.mod_lt _ hP.pos, by omega⟩, by omega, by omega, h⟩
    have h0 := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hH0 : 10+4 ≤ P72.H N := by rw [p72_H]; omega
  have h := hy_short_val_le_nullity p72_admissible hN hp2 hH
    (s := 10) (K := 9) (Dn := D) (k0 := -1)
    (by simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]; repeat' apply And.intro; all_goals omega)
    hNoBad (hyCell_10 hp2 hZ hH0)
  apply le_trans ?_ h
  rw [he]
  generalize hyMiss P72 N p 9 D (-1) = M at hmiss ⊢
  simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, shortHY10Val]
  simp only [D, rl, rt] at hmiss
  omega

def shortHY10LB72 : NullityLB P72 :=
  NullityLB.ofWindow P72 shortHY10App shortHY10Val fun N p hN hp hp2 hH happ => by
    letI : Fact p.Prime := ⟨hp⟩
    exact shortHY10Bound hN hp2 hH happ

#time theorem w115_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (97 / 11 : ℝ) * N < p → (p : ℝ) ≤ (4409091 / 500000 : ℝ) * N →
    (N : ℝ) * ((177 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (shortHY10LB72.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 1000 ZHY10)] with N hN
  intro p hp hlo hhi
  have hl : 97*N < 11*p := by
    exact_mod_cast (show (97 : ℝ)*N < 11*p by linarith)
  have hh : 500000*p ≤ 4409091*N := by
    exact_mod_cast (show 500000*(p : ℝ) ≤ 4409091*N by linarith)
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hZ : ZHY10 ≤ N := (le_max_right _ _).trans hN
  have happ : shortHY10App N p := ⟨hN0,hl,hh,fun hd => by
    have := Nat.le_of_dvd ZHY10_pos hd
    omega⟩
  have hk : shortHY10LB72.kap N p = shortHY10Val N p := by simp [shortHY10LB72, NullityLB.ofWindow, happ]
  have hbound : 354*N ≤ 2*shortHY10LB72.kap N p+4+40*p := by
    rw [hk]; unfold shortHY10Val; omega
  have hR : 354*(N : ℝ) ≤ 2*(shortHY10LB72.kap N p : ℝ)+4+40*p := by exact_mod_cast hbound
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((177 / 1 : ℝ) + (-20 / 1 : ℝ) * ((p : ℝ) / N)) =
      (177 / 1 : ℝ) * N + (-20 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

def shortHY9App (N p : Nat) : Prop :=
  1000 ≤ N ∧ 97*N < 10*p ∧ 850000000*p ≤ 8300000001*N ∧ ¬ p ∣ ZHY9
def shortHY9Val (N p : Nat) : Nat := ((206*N-21*p)/2)-1

theorem shortHY9Bound {N p : Nat} [Fact p.Prime] (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P72.H N < p^2) (happ : shortHY9App N p) :
    shortHY9Val N p ≤ nullity P72 N p := by
  obtain ⟨hN0, hl, hh0, hZ⟩ := happ
  have hP : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  let D := 6*N-(p-1)/2
  let rl : Nat := 6 * N - (p-1)/2
  let rt := 66 * N - 1 - 6 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 8 D (-1) ≤ (D-rl)+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card (k0 := (0 : Fin 8)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 8 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hlo, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rl, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
    · apply hy_miss_card (k0 := (7 : Fin 8)) (D := D) (r := rt) (good := fun t k => InRange P72 N (W.Slots.hhi p 8 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hhi, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rt, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega

  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    rintro ⟨e,J⟩ hm
    simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
    have hJrange : P72.L N / p + 2 ≤ 14 := by
      have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12*p)
      omega
    have hJ : J < 14 := hm.1.2.trans_le hJrange
    interval_cases J <;> simp only [HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm <;> (try simp only [and_true] at hm) <;> omega
  have hNoBad (j : Nat) (hj : P72.b N ≤ j) (hL : j < P72.L N) :
      ¬ HyBad (hyEmax P72 N p D) (hyA0 P72 N p) (hyNQ P72 N p D) 9 p
        (hyEta P72 N p 9) (j%p) (j/p) := by
    intro h
    have hmem : (j%p,j/p) ∈ edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D := by
      have hd := Nat.div_add_mod' j p
      have hb := Nat.div_le_div_right hL.le (c := p)
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨Nat.mod_lt _ hP.pos, by omega⟩, by omega, by omega, h⟩
    have h0 := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hH0 : 9+4 ≤ P72.H N := by rw [p72_H]; omega
  have h := hy_short_val_le_nullity p72_admissible hN hp2 hH
    (s := 9) (K := 8) (Dn := D) (k0 := -1)
    (by simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]; repeat' apply And.intro; all_goals omega)
    hNoBad (hyCell_9 hp2 hZ hH0)
  apply le_trans ?_ h
  rw [he]
  generalize hyMiss P72 N p 8 D (-1) = M at hmiss ⊢
  simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, shortHY9Val]
  simp only [D, rl, rt] at hmiss
  omega

def shortHY9LB72 : NullityLB P72 :=
  NullityLB.ofWindow P72 shortHY9App shortHY9Val fun N p hN hp hp2 hH happ => by
    letI : Fact p.Prime := ⟨hp⟩
    exact shortHY9Bound hN hp2 hH happ

#time theorem w121_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (97 / 10 : ℝ) * N < p → (p : ℝ) ≤ (8300000001 / 850000000 : ℝ) * N →
    (N : ℝ) * ((103 / 1 : ℝ) + (-21 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (shortHY9LB72.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 1000 ZHY9)] with N hN
  intro p hp hlo hhi
  have hl : 97*N < 10*p := by
    exact_mod_cast (show (97 : ℝ)*N < 10*p by linarith)
  have hh : 850000000*p ≤ 8300000001*N := by
    exact_mod_cast (show 850000000*(p : ℝ) ≤ 8300000001*N by linarith)
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hZ : ZHY9 ≤ N := (le_max_right _ _).trans hN
  have happ : shortHY9App N p := ⟨hN0,hl,hh,fun hd => by
    have := Nat.le_of_dvd ZHY9_pos hd
    omega⟩
  have hk : shortHY9LB72.kap N p = shortHY9Val N p := by simp [shortHY9LB72, NullityLB.ofWindow, happ]
  have hbound : 206*N ≤ 2*shortHY9LB72.kap N p+4+21*p := by
    rw [hk]; unfold shortHY9Val; omega
  have hR : 206*(N : ℝ) ≤ 2*(shortHY9LB72.kap N p : ℝ)+4+21*p := by exact_mod_cast hbound
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((103 / 1 : ℝ) + (-21 / 2 : ℝ) * ((p : ℝ) / N)) =
      (103 / 1 : ℝ) * N + (-21 / 2 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

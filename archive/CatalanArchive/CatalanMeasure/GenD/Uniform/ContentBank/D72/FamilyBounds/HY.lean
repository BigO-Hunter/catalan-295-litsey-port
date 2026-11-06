module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.HYPlus.HyLB
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 8000000

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.HYPlus CatalanMeasure.GenD.Uniform.W.Slots
open CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

def hyLB72 : NullityLB P72 := mLB' P72 p72_admissible

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

#time theorem w107_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (70 / 9 : ℝ) * N < p → (p : ℝ) ≤ (86 / 11 : ℝ) * N →
    (N : ℝ) * ((-105 / 1 : ℝ) + (27 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY11)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY11 ≤ N := (le_max_right _ _).trans hN
  have hl : 70 * N < 9 * p := by
    exact_mod_cast (show (70 : ℝ) * N < 9 * p by linarith)
  have hh0 : 11 * p ≤ 86 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 86 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 12 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨12, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 11 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY11 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY11_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 11 10 ZHY11 D = hyVal P72 N p 11 10 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 11 10 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 11 10 ZHY11 D ≤ hyKapS P72 N p 11 10 ZHY11 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 11 10 ZHY11 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_right _ _).trans (le_max_right _ _))
  let rl := 8 * p + (p-1)/2 + 1 - 66 * N
  let rt := 66 * N - 1 - 8 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 10 D (-1) ≤ rl+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card_low (k0 := (9 : Fin 10)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hlo, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rl, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
    · apply hy_miss_card (k0 := (9 : Fin 10)) (D := D) (r := rt) (good := fun t k => InRange P72 N (W.Slots.hhi p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hhi, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rt, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D).card ≤ ((97 * N - 12 * p) - (11 * N - p)) := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D ⊆ (Finset.Ico (11 * N - p) (97 * N - 12 * p) ×ˢ ({1} : Finset Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 27 * p ≤ 2 * hyLB72.kap N p + 4 + 210 * N := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 27 * p ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 210 * N := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((-105 / 1 : ℝ) + (27 / 2 : ℝ) * ((p : ℝ) / N)) =
      (-105 / 1 : ℝ) * N + (27 / 2 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w108_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (86 / 11 : ℝ) * N < p → (p : ℝ) ≤ (87 / 11 : ℝ) * N →
    (N : ℝ) * ((-19 / 1 : ℝ) + (5 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY11)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY11 ≤ N := (le_max_right _ _).trans hN
  have hl : 86 * N < 11 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 11 * p by linarith)
  have hh0 : 11 * p ≤ 87 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 87 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 12 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨12, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 11 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY11 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY11_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 11 10 ZHY11 D = hyVal P72 N p 11 10 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 11 10 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 11 10 ZHY11 D ≤ hyKapS P72 N p 11 10 ZHY11 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 11 10 ZHY11 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_right _ _).trans (le_max_right _ _))
  let rl := 8 * p + (p-1)/2 + 1 - 66 * N
  let rt := 66 * N - 1 - 8 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 10 D (-1) ≤ rl+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card_low (k0 := (9 : Fin 10)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hlo, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rl, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
    · apply hy_miss_card (k0 := (9 : Fin 10)) (D := D) (r := rt) (good := fun t k => InRange P72 N (W.Slots.hhi p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hhi, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rt, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D).card ≤ 0 := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D ⊆ (∅ : Finset (Nat × Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 5 * p ≤ 2 * hyLB72.kap N p + 4 + 38 * N := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 5 * p ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 38 * N := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((-19 / 1 : ℝ) + (5 / 2 : ℝ) * ((p : ℝ) / N)) =
      (-19 / 1 : ℝ) * N + (5 / 2 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w109_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (87 / 11 : ℝ) * N < p → (p : ℝ) ≤ (8 / 1 : ℝ) * N →
    (N : ℝ) * ((68 / 1 : ℝ) + (-17 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY11)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY11 ≤ N := (le_max_right _ _).trans hN
  have hl : 87 * N < 11 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 11 * p by linarith)
  have hh0 : 1 * p ≤ 8 * N := by
    exact_mod_cast (show (1 : ℝ) * p ≤ 8 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 12 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨12, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 11 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY11 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY11_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 11 10 ZHY11 D = hyVal P72 N p 11 10 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 11 10 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 11 10 ZHY11 D ≤ hyKapS P72 N p 11 10 ZHY11 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 11 10 ZHY11 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_right _ _).trans (le_max_right _ _))
  let rl := 8 * p + (p-1)/2 + 1 - 66 * N
  let rt := 66 * N - 1 - 8 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 10 D (-1) ≤ rl+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card_low (k0 := (9 : Fin 10)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hlo, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rl, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
    · apply hy_miss_card (k0 := (9 : Fin 10)) (D := D) (r := rt) (good := fun t k => InRange P72 N (W.Slots.hhi p 10 (-1) k t))
      intro t k hk
      have ht := t.isLt
      obtain ⟨kv, hkb⟩ := k
      simp only [InRange, W.Slots.hhi, cen, W.Slots.hh, P72, Signed.dc72_toParameters, Parameters.n, Parameters.g, rt, D] at ht hk ⊢
      interval_cases kv <;> (try omega) <;> rcases hk with hk | hk <;>
        first | exact absurd (Fin.ext rfl) hk | omega
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D).card ≤ 0 := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 11 (hyEta P72 N p 11) D ⊆ (∅ : Finset (Nat × Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 136 * N ≤ 2 * hyLB72.kap N p + 4 + 17 * p := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 136 * N ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 17 * p := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((68 / 1 : ℝ) + (-17 / 2 : ℝ) * ((p : ℝ) / N)) =
      (68 / 1 : ℝ) * N + (-17 / 2 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w111_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (17 / 2 : ℝ) * N < p → (p : ℝ) ≤ (43 / 5 : ℝ) * N →
    (N : ℝ) * ((-93 / 1 : ℝ) + (11 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY10)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY10 ≤ N := (le_max_right _ _).trans hN
  have hl : 17 * N < 2 * p := by
    exact_mod_cast (show (17 : ℝ) * N < 2 * p by linarith)
  have hh0 : 5 * p ≤ 43 * N := by
    exact_mod_cast (show (5 : ℝ) * p ≤ 43 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 11 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨11, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 93 * N - 10 * p - (p-1)/2
  have hnum : HYNum P72 N p 10 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY10 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY10_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 10 9 ZHY10 D = hyVal P72 N p 10 9 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 10 9 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 10 9 ZHY10 D ≤ hyKapS P72 N p 10 9 ZHY10 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 10 9 ZHY10 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_left _ _).trans (le_max_right _ _))
  let rl := 6 * N - (p-1)/2
  let rt := 66 * N - 1 - 7 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 9 D (-1) ≤ (D-rl)+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card (k0 := (0 : Fin 9)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 9 (-1) k t))
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D).card ≤ ((97 * N - 11 * p) - (11 * N - p)) + ((87 * N - 10 * p) - 0) := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D ⊆ (Finset.Ico (11 * N - p) (97 * N - 11 * p) ×ˢ ({1} : Finset Nat)) ∪ (Finset.Ico 0 (87 * N - 10 * p) ×ˢ ({10} : Finset Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    apply (Finset.card_union_le _ _).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 22 * p ≤ 2 * hyLB72.kap N p + 4 + 186 * N := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 22 * p ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 186 * N := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((-93 / 1 : ℝ) + (11 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-93 / 1 : ℝ) * N + (11 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w112_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (43 / 5 : ℝ) * N < p → (p : ℝ) ≤ (87 / 10 : ℝ) * N →
    (N : ℝ) * ((-7 / 1 : ℝ) + (1 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY10)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY10 ≤ N := (le_max_right _ _).trans hN
  have hl : 43 * N < 5 * p := by
    exact_mod_cast (show (43 : ℝ) * N < 5 * p by linarith)
  have hh0 : 10 * p ≤ 87 * N := by
    exact_mod_cast (show (10 : ℝ) * p ≤ 87 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 11 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨11, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 10 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY10 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY10_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 10 9 ZHY10 D = hyVal P72 N p 10 9 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 10 9 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 10 9 ZHY10 D ≤ hyKapS P72 N p 10 9 ZHY10 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 10 9 ZHY10 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_left _ _).trans (le_max_right _ _))
  let rl := 6 * N - (p-1)/2
  let rt := 66 * N - 1 - 7 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 9 D (-1) ≤ (D-rl)+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card (k0 := (0 : Fin 9)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 9 (-1) k t))
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D).card ≤ 0 := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D ⊆ (∅ : Finset (Nat × Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 2 * p ≤ 2 * hyLB72.kap N p + 4 + 14 * N := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 2 * p ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 14 * N := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((-7 / 1 : ℝ) + (1 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-7 / 1 : ℝ) * N + (1 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w113_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (87 / 10 : ℝ) * N < p → (p : ℝ) ≤ (35 / 4 : ℝ) * N →
    (N : ℝ) * ((80 / 1 : ℝ) + (-9 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY10)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY10 ≤ N := (le_max_right _ _).trans hN
  have hl : 87 * N < 10 * p := by
    exact_mod_cast (show (87 : ℝ) * N < 10 * p by linarith)
  have hh0 : 4 * p ≤ 35 * N := by
    exact_mod_cast (show (4 : ℝ) * p ≤ 35 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 11 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨11, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 10 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY10 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY10_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 10 9 ZHY10 D = hyVal P72 N p 10 9 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 10 9 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 10 9 ZHY10 D ≤ hyKapS P72 N p 10 9 ZHY10 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 10 9 ZHY10 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_left _ _).trans (le_max_right _ _))
  let rl := 6 * N - (p-1)/2
  let rt := 66 * N - 1 - 7 * p - (p-1)/2
  have hmiss : hyMiss P72 N p 9 D (-1) ≤ (D-rl)+(D-rt) := by
    unfold hyMiss
    apply Nat.add_le_add
    · apply hy_miss_card (k0 := (0 : Fin 9)) (D := D) (r := rl) (good := fun t k => InRange P72 N (W.Slots.hlo p 9 (-1) k t))
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D).card ≤ 0 := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D ⊆ (∅ : Finset (Nat × Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 160 * N ≤ 2 * hyLB72.kap N p + 4 + 18 * p := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 160 * N ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 18 * p := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((80 / 1 : ℝ) + (-9 / 1 : ℝ) * ((p : ℝ) / N)) =
      (80 / 1 : ℝ) * N + (-9 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w114_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (35 / 4 : ℝ) * N < p → (p : ℝ) ≤ (97 / 11 : ℝ) * N →
    (N : ℝ) * ((80 / 1 : ℝ) + (-9 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY10)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY10 ≤ N := (le_max_right _ _).trans hN
  have hl : 35 * N < 4 * p := by
    exact_mod_cast (show (35 : ℝ) * N < 4 * p by linarith)
  have hh0 : 11 * p ≤ 97 * N := by
    exact_mod_cast (show (11 : ℝ) * p ≤ 97 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 11 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨11, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := 6 * N - (p-1)/2
  have hnum : HYNum P72 N p 10 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY10 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY10_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 10 9 ZHY10 D = hyVal P72 N p 10 9 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 10 9 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 10 9 ZHY10 D ≤ hyKapS P72 N p 10 9 ZHY10 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 10 9 ZHY10 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans ((le_max_left _ _).trans (le_max_right _ _))
  let rl := 7 * p + (p-1)/2 + 1 - 66 * N
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D).card ≤ 0 := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 10 (hyEta P72 N p 10) D ⊆ (∅ : Finset (Nat × Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 160 * N ≤ 2 * hyLB72.kap N p + 4 + 18 * p := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 160 * N ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 18 * p := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((80 / 1 : ℝ) + (-9 / 1 : ℝ) * ((p : ℝ) / N)) =
      (80 / 1 : ℝ) * N + (-9 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w117_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (66 / 7 : ℝ) * N < p → (p : ℝ) ≤ (86 / 9 : ℝ) * N →
    (N : ℝ) * ((-66 / 1 : ℝ) + (7 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY9)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY9 ≤ N := (le_max_right _ _).trans hN
  have hl : 66 * N < 7 * p := by
    exact_mod_cast (show (66 : ℝ) * N < 7 * p by linarith)
  have hh0 : 9 * p ≤ 86 * N := by
    exact_mod_cast (show (9 : ℝ) * p ≤ 86 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 10 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨10, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := (186 * N + 1 - 19 * p) / 2
  have hnum : HYNum P72 N p 9 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY9 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY9_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 9 8 ZHY9 D = hyVal P72 N p 9 8 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 9 8 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 9 8 ZHY9 D ≤ hyKapS P72 N p 9 8 ZHY9 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 9 8 ZHY9 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans (le_max_left _ _)
  let rl := 6 * N - (p-1)/2
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D).card ≤ ((97 * N - 10 * p) - (11 * N - p)) + ((87 * N - 9 * p) - (0)) := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D ⊆ (Finset.Ico (11 * N - p) (97 * N - 10 * p) ×ˢ ({1} : Finset Nat)) ∪ (Finset.Ico (0) (87 * N - 9 * p) ×ˢ ({9} : Finset Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    apply (Finset.card_union_le _ _).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 14 * p ≤ 2 * hyLB72.kap N p + 4 + 132 * N := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 14 * p ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 132 * N := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((-66 / 1 : ℝ) + (7 / 1 : ℝ) * ((p : ℝ) / N)) =
      (-66 / 1 : ℝ) * N + (7 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

#time theorem w118_hcert72 : ∀ᶠ N : Nat in Filter.atTop, ∀ p : Nat, p.Prime →
    (86 / 9 : ℝ) * N < p → (p : ℝ) ≤ (202 / 21 : ℝ) * N →
    (N : ℝ) * ((20 / 1 : ℝ) + (-2 / 1 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (hyLB72.kap N p : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1000 ZHY9)] with N hN
  intro p hP hlo hhi
  letI : Fact p.Prime := ⟨hP⟩
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hNZb : ZHY9 ≤ N := (le_max_right _ _).trans hN
  have hl : 86 * N < 9 * p := by
    exact_mod_cast (show (86 : ℝ) * N < 9 * p by linarith)
  have hh0 : 21 * p ≤ 202 * N := by
    exact_mod_cast (show (21 : ℝ) * p ≤ 202 * N by linarith)
  have hnp : N < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := hP.eq_two_or_odd.resolve_left hp2
  have hp97 : 97 < p := by omega
  have hne : 97 * N ≠ 10 * p := by
    intro heq
    have hm : p ∣ 97 * N := ⟨10, heq.trans (Nat.mul_comm _ _)⟩
    rcases hP.dvd_mul.mp hm with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  let D := (186 * N + 1 - 19 * p) / 2
  have hnum : HYNum P72 N p 9 D := by
    simp only [HYNum, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h]
    repeat' apply And.intro
    all_goals omega
  have hz : ¬ p ∣ ZHY9 := by
    intro hd
    have hpZ := Nat.le_of_dvd ZHY9_pos hd
    omega
  have hD : D < p := by dsimp [D]; omega
  have hterm : hyTermG P72 N p 9 8 ZHY9 D = hyVal P72 N p 9 8 D (-1) := by
    unfold hyTermG
    rw [dif_pos hP, if_pos ⟨hp2,hnum,by rw [p72_H]; omega,hz⟩]
  have hv : hyVal P72 N p 9 8 D (-1) ≤ hyLB72.kap N p := by
    rw [← hterm]
    have key : hyTermG P72 N p 9 8 ZHY9 D ≤ hyKapS P72 N p 9 8 ZHY9 :=
      Finset.le_sup (f := fun k => hyTermG P72 N p 9 8 ZHY9 k) (Finset.mem_range.mpr hD)
    have hk : hyLB72.kap N p = hyKap P72 N p := by simp [hyLB72, mLB', NullityLB.ofWindow]
    rw [hk]; unfold hyKap
    exact key.trans (le_max_left _ _)
  let rl := 6 * N - (p-1)/2
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
  have he : (edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D).card ≤ ((87 * N - 9 * p) - (0)) := by
    have hsub : edgeSet P72 N p (hyA0 P72 N p) (hyNQ P72 N p D) 9 (hyEta P72 N p 9) D ⊆ (Finset.Ico (0) (87 * N - 9 * p) ×ˢ ({9} : Finset Nat)) := by
      rintro ⟨l,J⟩ hm
      simp only [edgeSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hm
      have hJrange : P72.L N / p + 2 ≤ 14 := by
        have h := (Nat.div_lt_iff_lt_mul hP.pos).mpr (by rw [p72_L]; omega : P72.L N < 12 * p)
        omega
      have hJ : J < 14 := hm.1.2.trans_le hJrange
      interval_cases J <;>
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton,
          Finset.notMem_empty, Prod.mk.injEq, HyBad, hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hm ⊢ <;> (try simp only [and_true]) <;> omega
    apply (Finset.card_le_card hsub).trans
    simp [Finset.card_product, Nat.card_Ico]
  have hbound : 40 * N ≤ 2 * hyLB72.kap N p + 4 + 4 * p := by
    unfold hyVal hyConds at hv
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at hv
    simp only [D, rl, rt, P72, Signed.dc72_toParameters] at hmiss
    simp only [hyEta, hyEmax, hyA0, hyNQ, hyF, D, P72, Signed.dc72_toParameters, Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h] at he
    omega
  have hboundR : 40 * N ≤ 2 * (hyLB72.kap N p : ℝ) + 4 + 4 * p := by
    exact_mod_cast hbound
  have hNZ : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq : (N : ℝ) * ((20 / 1 : ℝ) + (-2 / 1 : ℝ) * ((p : ℝ) / N)) =
      (20 / 1 : ℝ) * N + (-2 / 1 : ℝ) * p := by field_simp <;> ring
  rw [heq]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

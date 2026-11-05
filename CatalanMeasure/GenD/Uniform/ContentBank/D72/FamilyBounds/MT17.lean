module
public import CatalanMeasure.GenD.Uniform.ContentBank.D72.OddProfile
public import CatalanMeasure.GenD.Uniform.W.MTGlue.LB
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72
open Filter CatalanMeasure.GenD CatalanMeasure.Parametric
open CatalanMeasure.GenD.Uniform.W.MTGlue CatalanMeasure.GenD.Uniform.W.SlotsT
open CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

private theorem glue_foldl_nonzero (xs : List Nat) (a : Nat) (ha : a ≠ 0)
    (hx : ∀ x ∈ xs, x ≠ 0) : xs.foldl Nat.lcm a ≠ 0 := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (Nat.lcm_ne_zero ha (hx x (List.mem_cons_self)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

private theorem glue17_mod_ne72 : cell17.modulus ≠ 0 := by
  have hZ : ZmG ≠ 0 := by
    unfold ZmG
    refine glue_foldl_nonzero _ _ two_ne_zero ?_
    intro x hx
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨u, -, J, -, rfl | rfl⟩ := hx <;> exact Rat.den_nz _
  have h := cell17_ky
  unfold GlueCell.modulus
  exact Nat.mul_ne_zero (Nat.mul_ne_zero hZ (by simpa [cell17] using h.1))
    (by simpa [cell17] using h.2)

def mt17LB72 : NullityLB P72 := glueCellLB P72 p72_admissible cell17

theorem w087_hcert72 : ∀ᶠ N : Nat in atTop, ∀ p : Nat, p.Prime →
    (43 / 8 : ℝ) * N < p → (p : ℝ) ≤ (97 / 18 : ℝ) * N →
    (N : ℝ) * (-77 + (29 / 2 : ℝ) * ((p : ℝ) / N)) - 2 ≤ (mt17LB72.kap N p : ℝ) := by
  filter_upwards [eventually_ge_atTop (max 1000 cell17.modulus)] with N hN
  intro p hp hlo hhi
  have hN0 : 1000 ≤ N := (le_max_left _ _).trans hN
  have hM : cell17.modulus ≤ N := (le_max_right _ _).trans hN
  have hl : 43*N < 8*p := by
    exact_mod_cast (show (43 : ℝ)*N < 8*p by linarith)
  have hu : 18*p ≤ 97*N := by
    exact_mod_cast (show 18*(p : ℝ) ≤ 97*N by linarith)
  have hne : 18*p ≠ 97*N := by
    intro he
    have hd : p ∣ 97*N := ⟨18, he.symm.trans (Nat.mul_comm _ _)⟩
    rcases hp.dvd_mul.mp hd with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 97) h
      omega
    · have := Nat.le_of_dvd (by omega : 0 < N) h
      omega
  have ho : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hc : Nat.Coprime p cell17.modulus :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h =>
      by have := Nat.le_of_dvd (Nat.pos_of_ne_zero glue17_mod_ne72) h; omega)
  let D := 6*N-p
  have hw : GlueWin P72 N p cell17 D 0 := by
    unfold GlueWin
    change D ≤ (p-1)/2 ∧ p ≤ 4*N+(p-1)/2 ∧ 4*N+(p-1)/2-p < p ∧
      17*p+1 ≤ P72.H N ∧ p ≤ P72.H N-1-17*p ∧ P72.H N-1-17*p < 2*p ∧
      4*N+D ≤ (P72.H N-1-17*p)+1 ∧ 0 ≤ P72.H N-1-17*p-p+1 ∧
      (∀ j, P72.b N ≤ j → j < P72.L N →
        P72.H N-1-17*p-(4*N+D-1) ≤ j%p → j/p ∈ Finset.Icc 2 15) ∧
      (∀ j, P72.b N ≤ j → j < P72.L N →
        j%p+0+p ≤ P72.H N-1-17*p → j/p ∈ Finset.Icc 3 16)
    rw [p72_H, p72_L]
    refine ⟨by dsimp [D]; omega, by omega, by omega, by omega, by omega, by omega,
      by dsimp [D]; omega, by omega, ?_, ?_⟩
    · intro j hj hj' ht
      change 11*N ≤ j at hj
      rw [Finset.mem_Icc]
      have hr := Nat.mod_lt j hp.pos
      have hdiv := Nat.div_add_mod j p
      dsimp [D] at ht
      constructor
      · by_contra hn
        have hm := Nat.mul_le_mul_left p (show j/p ≤ 1 by omega)
        omega
      · by_contra hn
        have hm := Nat.mul_le_mul_left p (show 16 ≤ j/p by omega)
        omega
    · intro j hj hj' ht
      change 11*N ≤ j at hj
      rw [Finset.mem_Icc]
      have hdiv := Nat.div_add_mod j p
      constructor
      · by_contra hn
        have hm := Nat.mul_le_mul_left p (show j/p ≤ 2 by omega)
        omega
      · by_contra hn
        have hm := Nat.mul_le_mul_left p (show 17 ≤ j/p by omega)
        omega
  have hrow (k : Fin 14) (t : Int) (h0 : -(D : Int) ≤ t) (h1 : t ≤ D) :
      InRange P72 N (cen p 14 (-1) k+t) := by
    have hk := k.isLt
    have hpI : (0 : Int) ≤ p := by positivity
    have hkl : (-1 : Int)*p ≤ (-1+(k.val : Int))*p :=
      mul_le_mul_of_nonneg_right (by omega) hpI
    have hkh : (-1+(k.val : Int))*p ≤ 12*(p : Int) :=
      mul_le_mul_of_nonneg_right (by omega) hpI
    change -((6*N : Nat) : Int) ≤ (-1+(k.val : Int))*p+t ∧
      (-1+(k.val : Int))*p+t < ((72*N : Nat) : Int)-(6*N : Nat)
    dsimp [D] at h0 h1
    omega
  have hm : mixMiss P72 N p 14 D (-1) = 0 := by
    have hp' (t : Fin D) (k : Fin 14) :
        InRange P72 N (cen p 14 (-1) k+(t.val : Int)+1) := by
      have ht := t.isLt
      simpa only [add_assoc] using hrow k (t.val+1) (by omega) (by omega)
    have hn (t : Fin D) (k : Fin 14) :
        InRange P72 N (cen p 14 (-1) k-((t.val : Int)+1)) := by
      have ht := t.isLt
      simpa only [sub_eq_add_neg] using hrow k (-(t.val+1)) (by omega) (by omega)
    have h0 (k : Fin 14) : InRange P72 N (cen p 14 (-1) k) := by
      simpa using hrow k 0 (by omega) (by omega)
    have e1 : mmP P72 N p 14 D (-1) = ∅ := by
      unfold mmP; rw [Finset.filter_eq_empty_iff]
      intro dk _; exact not_not.mpr (by simpa only [add_assoc] using hp' dk.1 dk.2)
    have e2 : mmM P72 N p 14 D (-1) = ∅ := by
      unfold mmM; rw [Finset.filter_eq_empty_iff]
      intro dk _; exact not_not.mpr (hn dk.1 dk.2)
    have e3 : mm0 P72 N p 14 (-1) = ∅ := by
      unfold mm0; rw [Finset.filter_eq_empty_iff]
      intro k _; exact not_not.mpr (h0 k)
    unfold mixMiss; rw [e1, e2, e3]; simp
  have hk := mtGlueVal1_le_glueCellLB P72 p72_admissible cell17 hp hc hw
  change mtGlueVal1 P72 N p 17 14 D 0 (-1) ≤ mt17LB72.kap N p at hk
  have hb : 29*p ≤ 2*mt17LB72.kap N p+4+154*N := by
    unfold mtGlueVal1 at hk
    rw [hm, p72_H] at hk
    change _ - (p-4*N-(4*N+(p-1)/2-p)) ≤ _ at hk
    dsimp [D] at hk
    omega
  have hbR : 29*(p : ℝ) ≤ 2*(mt17LB72.kap N p : ℝ)+4+154*N := by exact_mod_cast hb
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * (-77 + 29/2*((p : ℝ)/N)) = -77*N+29/2*p := by
    field_simp <;> ring
  rw [he]
  linarith

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72

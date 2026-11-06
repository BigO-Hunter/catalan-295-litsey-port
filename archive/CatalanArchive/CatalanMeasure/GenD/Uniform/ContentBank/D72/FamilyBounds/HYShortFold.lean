module
public import CatalanMeasure.GenD.Uniform.W.Slots.HPrime
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.ContentBank.D72.HYShort
open Polynomial CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {p : Nat} [Fact p.Prime]

def shortFold (p η l : Nat) (f : Nat → ZMod p) : ZMod p :=
  (if l ≤ η then f (η-l) else 0) + f (η+p-l)

theorem shortFold_poly {v η : Nat} (hv : v < p) (hη : η < p) (f : (ZMod p)[X])
    (hdvd : ((X - 1) ^ v : (ZMod p)[X]) ∣ f) (hdeg : f.natDegree < η + p) :
    ∃ G : (ZMod p)[X], G.degree < ((p-v : Nat) : WithBot Nat) ∧
      ∀ l : ZMod p, shortFold p η l.val f.coeff = G.eval l := by
  classical
  let T := ∑ e ∈ Finset.range p, monomial e (f.coeff (e+p))
  have ht (m : Nat) : T.coeff m = if m < p then f.coeff (m+p) else 0 := by
    simp only [T, finset_sum_coeff, coeff_monomial]
    by_cases hm : m < p
    · rw [if_pos hm, Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [hb]
      · exact fun hn => (hn (Finset.mem_range.mpr hm)).elim
    · rw [if_neg hm]
      apply Finset.sum_eq_zero
      intro b hb
      have hb' := Finset.mem_range.mp hb
      simp [show b ≠ m by omega]
  let W := f - (X^p - 1) * T
  have hw (m : Nat) : W.coeff m =
      f.coeff m - ((if p ≤ m then T.coeff (m-p) else 0) - T.coeff m) := by
    simp only [W, coeff_sub, sub_mul, one_mul, coeff_X_pow_mul']
  have hf (m : Nat) (hm : η+p ≤ m) : f.coeff m = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hWp (m : Nat) (hm : p ≤ m) : W.coeff m = 0 := by
    rw [hw, ht, ht, if_pos hm, if_neg (by omega : ¬ m < p), sub_zero]
    by_cases hmp : m-p < p
    · rw [if_pos hmp, Nat.sub_add_cancel hm, sub_self]
    · rw [if_neg hmp, hf m (by omega), sub_zero]
  have hWlt : W.natDegree ≤ p-1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    exact hWp m (by omega)
  have hWdvd : ((X - 1) ^ v : (ZMod p)[X]) ∣ W := by
    refine dvd_sub hdvd (dvd_mul_of_dvd_left ?_ _)
    rw [← sub_one_pow_prime]
    exact pow_dvd_pow _ hv.le
  obtain ⟨G,hG,hGe⟩ := jflat_poly hv W hWdvd (p-1) hWlt
    (fun i hi => by omega)
  have hl (m : Nat) (hm : m < p) : W.coeff m = f.coeff m + f.coeff (m+p) := by
    rw [hw, if_neg (by omega : ¬ p ≤ m), ht, if_pos hm]
    ring
  let k := p-1-η
  refine ⟨taylor (k : ZMod p) G, by simpa [degree_taylor] using hG, ?_⟩
  intro l
  have hlt := ZMod.val_lt l
  have hk : k < p := by dsimp [k]; omega
  have hkv : (k : ZMod p).val = k := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]
  rw [taylor_eval, ← hGe]
  have hr := ZMod.val_lt (l + (k : ZMod p))
  rw [if_pos (by omega : (l + (k : ZMod p)).val ≤ p-1)]
  by_cases hle : l.val ≤ η
  · have hv : (l + (k : ZMod p)).val = l.val + k := by
      rw [ZMod.val_add, hkv, Nat.mod_eq_of_lt]
      dsimp [k]; omega
    rw [hv, hl _ (by omega), shortFold, if_pos hle]
    dsimp [k]
    rw [show p-1-(l.val + (p-1-η)) = η-l.val by omega,
      show η-l.val+p = η+p-l.val by omega]
  · have hv : (l + (k : ZMod p)).val = l.val + k - p := by
      rw [ZMod.val_add_of_le, hkv]
      rw [hkv]; dsimp [k]; omega
    rw [hv, hl _ (by omega), shortFold, if_neg hle, zero_add]
    dsimp [k]
    rw [show p-1-(l.val + (p-1-η)-p) = η+p-l.val by omega,
      hf (η+p-l.val+p) (by omega), add_zero]

end
end CatalanMeasure.GenD.Uniform.ContentBank.D72.HYShort

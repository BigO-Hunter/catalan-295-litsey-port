module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.TruncatedRoot
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell

/-- Absolute coefficient mass at 2, computed by a linear Horner fold. -/
def mass : List ℚ → ℚ
  | [] => 0
  | a :: p => |a| + 2 * mass p

theorem mass_eval (p : List ℚ) :
    ((mass p : ℚ) : ℝ) = polyTow (p.map (fun a => |a|)) 0 2 := by
  induction p with
  | nil => simp [mass, polyTow]
  | cons a p ih => simp only [mass, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
      ih, List.map_cons, polyTow]

theorem tail_bound (p : List ℚ) (c : ℚ) (M : ℕ) (hM : M ≤ p.length)
    (hc : |c| ≤ 1) (y r : ℝ) (hy : |y| ≤ r) (hr : r ≤ 1) :
    polyTow p 0 (y + c) ≤ polyTow (shiftL c M p) 0 y +
      ((mass p : ℚ) : ℝ) * r^(M+1) := by
  let f : ℕ → ℝ := fun k => ((shiftL c p.length p).getD k 0 : ℝ) * y^k
  let C : ℕ → ℝ := fun k => ((shiftL 1 p.length (p.map (fun a => |a|))).getD k 0 : ℝ)
  have hC (k : ℕ) : |(((shiftL c p.length p).getD k 0 : ℚ) : ℝ)| ≤ C k := by
    dsimp [C]
    exact_mod_cast shiftL_dom c hc p.length p k
  have hC0 (k : ℕ) : 0 ≤ C k := (abs_nonneg _).trans (hC k)
  have hp : ∑ k ∈ Finset.range (p.length+1), f k = polyTow p 0 (y+c) := by
    have h := polyTow_shiftL p c y
    rw [polyTow_sum,shiftL_length] at h
    exact h
  have hpre : ∑ k ∈ Finset.range (M+1), f k = polyTow (shiftL c M p) 0 y := by
    rw [polyTow_sum,shiftL_length]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    dsimp [f]
    rw [shiftL_spec c p.length p k (hk'.trans hM), shiftL_spec c M p k hk']
  have hmass : ∑ k ∈ Finset.range (p.length+1), C k = ((mass p : ℚ) : ℝ) := by
    have h := polyTow_shiftL (p.map (fun a => |a|)) 1 1
    rw [polyTow_sum] at h
    simp only [shiftL_length, List.length_map, one_pow, mul_one] at h
    rw [mass_eval]
    convert h using 2 <;> norm_num [C]
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hy
  have htail : ∑ k ∈ Finset.Ico (M+1) (p.length+1), f k ≤
      ((mass p : ℚ) : ℝ)*r^(M+1) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico (M+1) (p.length+1), C k * r^(M+1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := (Finset.mem_Ico.mp hk).1
        have hy' : |y|^k ≤ r^(M+1) :=
          (pow_le_pow_left₀ (abs_nonneg y) hy _).trans
            (pow_le_pow_of_le_one hr0 hr hk')
        calc
          f k ≤ |f k| := le_abs_self _
          _ ≤ _ := by
            dsimp [f]
            rw [abs_mul,abs_pow]
            exact mul_le_mul (hC k) hy' (by positivity) (hC0 k)
      _ = (∑ k ∈ Finset.Ico (M+1) (p.length+1), C k) * r^(M+1) := by
        rw [Finset.sum_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [← hmass]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        · intro k _ _
          exact hC0 k
  rw [← hp, ← Finset.sum_range_add_sum_Ico f (Nat.succ_le_succ hM), hpre]
  linarith only [htail]

theorem raw_bound (p : List ℚ) (lo hi : ℚ) (M : ℕ) (hM : M ≤ p.length)
    (hc : |(lo+hi)/2| ≤ (1 : ℚ)) (hr : (hi-lo)/2 ≤ (1 : ℚ)) :
    Bnd lo hi (fun x => polyTow p 0 x) (shiftLK ((lo+hi)/2) M p)
      (mass p * ((hi-lo)/2)^(M+1)) := by
  intro x hx
  have h := tail_bound p ((lo+hi)/2) M hM hc
    (x-(((lo+hi)/2 : ℚ) : ℝ)) ((((hi-lo)/2 : ℚ)) : ℝ)
    (hx_abs lo hi x hx) (by exact_mod_cast hr)
  have he : x - (((lo+hi)/2 : ℚ) : ℝ) + (((lo+hi)/2 : ℚ) : ℝ) = x := by ring
  rw [he] at h
  simpa only [shiftLK_eq', Rat.cast_mul, Rat.cast_pow] using h

theorem merge_sound (fq : FieldQ) (ts : List LTerm) {nL nA Mp Ml P : ℕ}
    {lo hi : ℚ} (hlo : lo < hi) {pd : List (ℚ × (List ℚ × List ℚ))}
    {qd : List (ℚ × ℚ)} {S Ap Aq Al γ : List ℚ} {Es Ep Eq El T : ℚ}
    (hs : BndU lo hi (fun x => polyTow fq.poly 0 x) S Es)
    (hp : plogsRoundM nL nA Ml P lo hi (mergeSites fq.plogs) pd = some (Ap,Ep))
    (hq : polesRoundM nL nA Mp P lo hi fq.poles qd = some (Aq,Eq))
    (hl : BndU lo hi (fun x => lfieldTower ts 0 x) Al El)
    (hsmall : chebPolyUB (vecAdd S (vecAdd Ap (vecAdd Aq Al))) γ+Es+Ep+Eq+El ≤ T) :
    ∀ x ∈ Icc (lo : ℝ) (hi : ℝ),
      fieldTower fq (poleF fq.poles) 0 x + lfieldTower ts 0 x ≤ (T : ℝ) := by
  intro x hx
  have hp := plogsRoundM_bnd hlo (mergeSites fq.plogs) pd Ap Ep hp x hx
  beta_reduce at hp
  rw [mergeSites_eq] at hp
  have hq := polesRoundM_bnd hlo fq.poles qd Aq Eq hq x hx
  have hL := hl x hx
  have hs0 := hs x hx
  have hc := chebPoly_le (vecAdd S (vecAdd Ap (vecAdd Aq Al))) γ
    ((x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)) (hx_unit hlo x hx)
  rw [polyTow_vecAdd,polyTow_vecAdd,polyTow_vecAdd] at hc
  rw [fieldTower_zero]
  have hT := (Rat.cast_le (K := ℝ)).mpr hsmall
  simp only [Rat.cast_add] at hT
  beta_reduce at hs0 hq hL
  linarith

#print axioms mass_eval
#print axioms tail_bound
#print axioms raw_bound
#print axioms merge_sound

end CatalanMeasure.GenD.Signed.Data.Cells.D72.TruncatedRoot

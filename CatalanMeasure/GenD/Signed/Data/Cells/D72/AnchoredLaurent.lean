module

public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.AdaptiveAnchor

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells.D72.AdaptiveAnchor
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell
open CatalanMeasure.GenD.Signed.LogEval

/-- The Laurent approximation argument depends on the anchor enclosure, not its implementation. -/
theorem laurent_error {M P : ℕ} {c r : ℚ} {t : LTerm} {d : LaurentPieceData}
    (hg : laurentGeom c r M t d = true)
    (hlog : ∀ ab, t.2 = some ab →
        |(d.L : ℝ)-Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (d.eps : ℝ))
    (y : ℝ) (hy : |y| ≤ (r : ℝ)) :
    |mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
      polyTow (laurentPoly t c d.L M P) 0 y| ≤
      ((laurentCoeffErr t c d.L d.eps r M P +
        laurentTail c d.q0 (laurentQL t d) (qabs' d.L+d.eps) M d.K t : ℚ) : ℝ) := by
  simp only [laurentGeom, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hr,hc,hq0,hq0',hry,hqL,hqL',hMK,hε⟩,haff⟩ := hg
  have hguard : ∀ ab, t.2 = some ab → ab.1*c-ab.2 ≠ 0 ∧
      qabs' ab.1*r ≤ laurentQL t d*qabs' (ab.1*c-ab.2) := by
    intro ab hab
    rw [hab] at haff
    exact of_decide_eq_true haff
  have hneQ : ∀ ab, t.2 = some ab → ab.1*c-ab.2 ≠ 0 := fun ab hab => (hguard ab hab).1
  have hne : ∀ ab, t.2 = some ab → (ab.1 : ℝ)*(c : ℝ)-ab.2 ≠ 0 := by
    intro ab hab
    have hn := hneQ ab hab
    exact_mod_cast hn
  have hL : ∀ ab, t.2 = some ab →
      |(d.L : ℝ)-Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ (d.eps : ℝ) := hlog
  have hLB : ∀ ab, t.2 = some ab →
      |Real.log (|(ab.1 : ℝ)*(c : ℝ)-ab.2|)| ≤ ((qabs' d.L+d.eps : ℚ) : ℝ) := by
    intro ab hab
    have he := abs_le.mp (hL ab hab)
    rw [Rat.cast_add, qabs'_cast, abs_le]
    constructor <;> linarith [he.1, he.2, le_abs_self (d.L : ℝ), neg_abs_le (d.L : ℝ)]
  have hy0 : |y| ≤ (d.q0 : ℝ)*|(c : ℝ)| := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hry
    simp only [Rat.cast_mul, qabs'_cast] at hh
    exact hy.trans hh
  have hR : ∀ ab, t.2 = some ab →
      |(ab.1 : ℝ)*y/((ab.1 : ℝ)*(c : ℝ)-ab.2)| ≤ (laurentQL t d : ℝ) := by
    intro ab hab
    have hh := (Rat.cast_le (K := ℝ)).mpr (hguard ab hab).2
    simp only [Rat.cast_mul, qabs'_cast] at hh
    push_cast at hh
    rw [abs_div, abs_mul]
    apply (div_le_iff₀ (abs_pos.mpr (hne ab hab))).mpr
    exact (mul_le_mul_of_nonneg_left hy (abs_nonneg (ab.1 : ℝ))).trans hh
  have ht := laurentMajorant_tail t c d.q0 (laurentQL t d) (qabs' d.L+d.eps) M d.K y
    hc hq0 hq0' hqL hqL' hMK hy0 hne hLB hR
  have hp := laurentCoeffErr_spec t c d.L d.eps r M P hc y hy hneQ hL
  have he : mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
      polyTow (laurentPoly t c d.L M P) 0 y =
    (mulTower (zTow t.1) (lfTower t.2) 0 ((c : ℝ)+y) -
      ∑ k ∈ Finset.range (M+1), mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k) +
    ((∑ k ∈ Finset.range (M+1), mulTower (zTow t.1) (lfTower t.2) k (c : ℝ)/(k.factorial : ℝ)*y^k) -
      polyTow (laurentPoly t c d.L M P) 0 y) := by ring
  rw [he, Rat.cast_add]
  have hb := (abs_add_le _ _).trans (add_le_add ht hp)
  linarith


def raw (M P : ℕ) (c r : ℚ) (t : LTerm) (d : LaurentPieceData) : Option (List ℚ × ℚ) :=
  if laurentGeom c r M t d then
    some (laurentPoly t c d.L M P,
      laurentCoeffErr t c d.L d.eps r M P +
        laurentTail c d.q0 (laurentQL t d) (qabs' d.L+d.eps) M d.K t)
  else none

def cached (M P : Nat) (c r : ℚ) (t : LTerm) (d : LaurentPieceData)
    (Z C F : Nat → ℚ) (coarse : ℚ) : Option (List ℚ × ℚ) :=
  if laurentGeom c r M t d then
    some ((List.range (M+1)).map (fun k => dyRound P (C k)),
      (∑ k ∈ Finset.range (M+1),
        (lEps t.2 d.eps*qabs' (Z k) + qabs' (C k-dyRound P (C k)))*r^k) +
      ((∑ k ∈ Finset.Ico (M+1) (d.K+1), F k) + coarse))
  else none

theorem cached_eq {M P : Nat} {c r : ℚ} {t : LTerm} {d : LaurentPieceData}
    {Z C F : Nat → ℚ} {coarse : ℚ}
    (hz : ∀ k, k ≤ M → Z k = zHat t.1 c k)
    (hc : ∀ k, k ≤ M → C k = lTermCoef t c d.L k)
    (hf : ∀ k, k ∈ Finset.Ico (M+1) (d.K+1) →
      F k = laurentFineCoef c d.q0 (laurentQL t d) (qabs' d.L+d.eps) t k)
    (ht : coarse = laurentCoarseTail c (max d.q0 (laurentQL t d)) (qabs' d.L+d.eps) d.K t) :
    cached M P c r t d Z C F coarse = raw M P c r t d := by
  have hp : (List.range (M+1)).map (fun k => dyRound P (C k)) = laurentPoly t c d.L M P := by
    apply List.map_congr_left
    intro k hk
    rw [hc k (by simpa only [List.mem_range, Nat.lt_succ_iff] using hk)]
  have he : (∑ k ∈ Finset.range (M+1),
      (lEps t.2 d.eps*qabs' (Z k) + qabs' (C k-dyRound P (C k)))*r^k) =
      laurentCoeffErr t c d.L d.eps r M P := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [hz k hk', hc k hk']
  have hf' : (∑ k ∈ Finset.Ico (M+1) (d.K+1), F k) =
      ∑ k ∈ Finset.Ico (M+1) (d.K+1),
        laurentFineCoef c d.q0 (laurentQL t d) (qabs' d.L+d.eps) t k := by
    exact Finset.sum_congr rfl hf
  simp only [cached, raw, hp, he, hf', ht, laurentTail]


theorem term_sound {lo hi : ℚ} {M P : ℕ} {t : LTerm} {d : LaurentPieceData}
    {A : List ℚ} {E : ℚ} (hlo : lo < hi)
    (hlog : ∀ ab, t.2 = some ab →
      |(d.L : ℝ)-Real.log (|(ab.1 : ℝ)*(((lo+hi)/2 : ℚ) : ℝ)-ab.2|)| ≤ (d.eps : ℝ))
    (h : cellRoundApx P lo hi (raw M P ((lo+hi)/2) ((hi-lo)/2) t d) = some (A,E)) :
    BndU lo hi (fun x => mulTower (zTow t.1) (lfTower t.2) 0 x) A E := by
  apply cellRoundApx_bnd hlo ?_ h
  intro B F hb x hx
  unfold raw at hb
  split_ifs at hb with hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl,rfl⟩ := hb
  have hA := laurent_error (P := P) hg hlog (x-(((lo+hi)/2 : ℚ) : ℝ)) (hx_abs lo hi x hx)
  have he : (((lo+hi)/2 : ℚ) : ℝ)+(x-(((lo+hi)/2 : ℚ) : ℝ)) = x := by ring
  rw [he] at hA
  have hu := (abs_le.mp hA).2
  linarith

theorem anchorFits {n : ℕ} {q L e v ε : ℚ} (ha : anchor n q = some (v,ε))
    (he : qabs' (v-L) + ε ≤ e) :
    |(L : ℝ) - Real.log (|(q : ℝ)|)| ≤ (e : ℝ) := by
  have ha := anchor_sound ha
  have hr := (Rat.cast_le (K := ℝ)).mpr he
  simp only [Rat.cast_add, Rat.cast_sub, qabs'_cast] at hr
  rw [abs_sub_comm (v : ℝ) (L : ℝ)] at hr
  calc
    _ = |((L : ℝ)-v) + ((v : ℝ)-Real.log |(q : ℝ)|)| := by congr 1 <;> ring
    _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_sub_comm (v : ℝ)]; linarith)

def anchorCheck (n : ℕ) (q L e : ℚ) : Bool :=
  match anchor n q with
  | none => false
  | some (v, ε) => decide (qabs' (v-L) + ε ≤ e)

theorem anchorCheck_sound {n : ℕ} {q L e : ℚ} (h : anchorCheck n q L e = true) :
    |(L : ℝ) - Real.log (|(q : ℝ)|)| ≤ (e : ℝ) := by
  unfold anchorCheck at h
  split at h
  · simp at h
  · rename_i v ε ha
    exact anchorFits ha (of_decide_eq_true h)

theorem merge_sound (fq : FieldQ) (ts : List LTerm) {nL nA Mp Ml P : ℕ}
    {lo hi : ℚ} (hlo : lo < hi) {pd : List (ℚ × (List ℚ × List ℚ))}
    {qd : List (ℚ × ℚ)} {S Ap Aq Al γ : List ℚ} {Es Ep Eq El T : ℚ}
    (hs : polyRoundApx P lo hi fq.poly = (S,Es))
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
  have hs0 := polyRoundApx_bnd hlo P fq.poly x hx
  rw [hs] at hs0
  have hc := chebPoly_le (vecAdd S (vecAdd Ap (vecAdd Aq Al))) γ
    ((x-(((lo+hi)/2 : ℚ) : ℝ))/(((hi-lo)/2 : ℚ) : ℝ)) (hx_unit hlo x hx)
  rw [polyTow_vecAdd,polyTow_vecAdd,polyTow_vecAdd] at hc
  rw [fieldTower_zero]
  have hT := (Rat.cast_le (K := ℝ)).mpr hsmall
  simp only [Rat.cast_add] at hT
  beta_reduce at hs0 hq hL
  linarith

#print axioms laurent_error
#print axioms cached_eq
#print axioms term_sound
#print axioms anchorFits
#print axioms anchorCheck_sound
#print axioms merge_sound

end CatalanMeasure.GenD.Signed.Data.Cells.D72.AdaptiveAnchor

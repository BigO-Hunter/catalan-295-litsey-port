module

public import Submission.CatalanMeasure.GenD.Signed.RouteI.MomentInputs
public import Submission.CatalanMeasure.GenD.Signed.RouteI.AngularCap

@[expose] public section
set_option Elab.async false

/-!
# Route I `GasCert`: the C8 producer feeds the C6 consumer

Joins `MomentInputs` (C8: `BinRec`, `RecOK`, `coefR`, `coef_err`) with `AngularCap` (C6:
`AngRadiusCert.hb`, `AngRadiusCert.hG`, `gasA`).  Everything is generic in the source `S`.

Bridge facts (conventions of the two modules):
* `Partitioned gas (recs.map cells)` (C8, `CellCut`) gives `Binning gas (recs.map cells)` (C6,
  `SplitInto`/`Refines`): `CellCut` and `SplitInto` are the same cut tree, bins regroup by a permutation.
* C8 `binD a c l` is C6 `binD l a c`; C8 `binAlpha a b c l = 2 b A/(m D)` is C6
  `binAlpha l a c b`; so `kernelCoef bins p s t k = - trueCoef p t s recs (k+1)` and
  `kernelC bins p s = constTrue p s recs` (the factor `m_b/2` agrees term by term).
* Negative species: C8 works on the reflected cells (`reflectL`) with `u = -cos theta`; C6 works on the
  original negative cells with `u = cos theta`.  Reflection fixes mass and `B`, negates `A`, hence
  `alpha_C6 (reflectL b) = - alpha_C8 b` and `kernelCoef (reflect bins) p s t k =
  (-1)^(k+1) * (- trueCoef p t s recs (k+1))`.  The C6 bins are `(recs.map cells).map reflectL`.
* Both kernels of the negative species are summed in `gasA`; the coefficient list `glNeg` adds the two
  C8 record lists coefficientwise (with the parity sign `(-1)^(k+1)`) over the denominator `2^P`.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.GasCert

open CatalanMeasure.GenD.Signed.RouteI.CapFields
open CatalanMeasure.GenD.Signed.RouteI.MomentInputs
open CatalanMeasure.GenD.Signed.RouteI.MomentSource (Partitioned CellCut reflectL)
open CatalanMeasure.GenD.Signed.RouteI.AngularSource (kernelC kernelCoef Binning Refines SplitInto cellLeft cellRight)
open CatalanMeasure.GenD.Signed.RouteI.AngularCap (gasA gasConst gasCoefK)

noncomputable section

/-! ### Reflection -/

lemma reflect_reflect (c : YCell) : c.reflect.reflect = c := by
  cases c; simp [YCell.reflect]

lemma reflectL_reflectL (l : List YCell) : reflectL (reflectL l) = l := by
  simp [reflectL, List.map_map, Function.comp_def, reflect_reflect]

lemma massL_reflectL (l : List YCell) : massL (reflectL l) = massL l := by
  simp [massL, reflectL, List.map_map, Function.comp_def, YCell.reflect]

lemma physL_reflectL {b : List YCell} (hb : ∀ c ∈ b, 2 ≤ c.lo) (f : ℝ → ℝ) :
    physL (reflectL b) f = physL b (fun x => f (-x)) := by
  have h := MomentSource.physL_reflect (l := reflectL b) (fun c hc => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    have := hb d hd
    simp [YCell.reflect]; linarith) f
  rw [reflectL_reflectL] at h
  exact h

/-! ### `Partitioned` gives `Binning` -/

lemma splitInto_of_cellCut {c : YCell} {L : List YCell} (h : CellCut c L) : SplitInto c L := by
  induction h with
  | refl c => exact SplitInto.refl c
  | split c m h1 h2 _ _ ih1 ih2 => exact SplitInto.split c m h1 h2 _ _ ih1 ih2

lemma cellLeft_reflect (c : YCell) {m : ℝ} (h2 : m < c.hi) (h' : c.reflect.lo < -m) :
    cellLeft c.reflect (-m) h' = (cellRight c m h2).reflect := by
  simp only [cellLeft, cellRight, YCell.reflect, YCell.mk.injEq, true_and]
  ring

lemma cellRight_reflect (c : YCell) {m : ℝ} (h1 : c.lo < m) (h' : -m < c.reflect.hi) :
    cellRight c.reflect (-m) h' = (cellLeft c m h1).reflect := by
  simp only [cellLeft, cellRight, YCell.reflect, YCell.mk.injEq, true_and]
  ring

lemma splitInto_reflect {c : YCell} {L : List YCell} (h : SplitInto c L) :
    ∃ L', SplitInto c.reflect L' ∧ L'.Perm (L.map YCell.reflect) := by
  induction h with
  | refl c => exact ⟨[c.reflect], SplitInto.refl _, by simp⟩
  | split c m h1 h2 a b _ _ iha ihb =>
    obtain ⟨a', ha', pa⟩ := iha
    obtain ⟨b', hb', pb⟩ := ihb
    have h1' : c.reflect.lo < -m := by simp [YCell.reflect]; linarith
    have h2' : -m < c.reflect.hi := by simp [YCell.reflect]; linarith
    rw [← cellLeft_reflect c h2 h1'] at hb'
    rw [← cellRight_reflect c h1 h2'] at ha'
    refine ⟨b' ++ a', SplitInto.split c.reflect (-m) h1' h2' b' a' hb' ha', ?_⟩
    rw [List.map_append]
    exact (pb.append pa).trans List.perm_append_comm

lemma binning_of_partitioned {gas : List YCell} {bins : List (List YCell)}
    (hp : Partitioned gas bins) : Binning gas bins := by
  obtain ⟨pieces, hF, hperm⟩ := hp
  have key : ∀ (gs : List YCell) (ps : List (List YCell)), List.Forall₂ CellCut gs ps →
      Refines gs ps.flatten := by
    intro gs ps hF
    induction hF with
    | nil => exact Refines.nil
    | cons hc _ ih => exact Refines.cons _ _ _ _ (splitInto_of_cellCut hc) ih
  exact ⟨pieces.flatten, key _ _ hF, hperm.symm⟩

lemma binning_of_partitioned_reflect {gas : List YCell} {bins : List (List YCell)}
    (hp : Partitioned (reflectL gas) bins) : Binning gas (bins.map reflectL) := by
  obtain ⟨pieces, hF, hperm⟩ := hp
  have hF' : List.Forall₂ (fun c L => CellCut c.reflect L) gas pieces := by
    simpa [reflectL, List.forall₂_map_left_iff] using hF
  have key : ∀ (gs : List YCell) (ps : List (List YCell)),
      List.Forall₂ (fun c L => CellCut c.reflect L) gs ps →
      ∃ sl, Refines gs sl ∧ sl.Perm (ps.flatten.map YCell.reflect) := by
    intro gs ps hF
    induction hF with
    | nil => exact ⟨[], Refines.nil, by simp⟩
    | @cons c L gs' ps' hc _ ih =>
      obtain ⟨sl, hr, hs⟩ := ih
      obtain ⟨L', hL', pL⟩ := splitInto_reflect (splitInto_of_cellCut hc)
      rw [reflect_reflect] at hL'
      refine ⟨L' ++ sl, Refines.cons c gs' L' sl hL' hr, ?_⟩
      simp only [List.flatten_cons, List.map_append]
      exact pL.append hs
  obtain ⟨sl, hr, hs⟩ := key _ _ hF'
  refine ⟨sl, hr, ?_⟩
  have e : (bins.map reflectL).flatten = bins.flatten.map YCell.reflect := by
    show (bins.map (List.map YCell.reflect)).flatten = _
    rw [List.map_flatten]
  rw [e]
  exact ((hperm.map _).symm).trans hs.symm

/-! ### Bridge lemmas: C8 true coefficients are C6 kernel coefficients -/

lemma alpha_eq (b : List YCell) (p s t : ℝ) :
    AngularSource.binAlpha b p s t = MomentSource.binAlpha p t s b := by
  unfold AngularSource.binAlpha MomentSource.binAlpha AngularSource.binD MomentSource.binD
    AngularSource.binM1 AngularSource.binM2
  have : (physL b fun x => x) = physL b id := rfl
  rw [this]
  have key : ∀ (m M1 D t : ℝ), 2 * t * (M1 / m) / D = 2 * t * M1 / (m * D) := fun _ _ _ _ => by ring
  exact key _ _ _ _

lemma kernelC_pos (recs : List BinRec) (p s : ℝ) :
    kernelC (recs.map BinRec.cells) p s = constTrue p s recs := by
  unfold kernelC constTrue
  rw [List.map_map]
  rfl

lemma kernelCoef_pos (recs : List BinRec) (p s t : ℝ) (k : ℕ) :
    kernelCoef (recs.map BinRec.cells) p s t k = - trueCoef p t s recs (k + 1) := by
  unfold kernelCoef trueCoef
  rw [List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply, alpha_eq]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

lemma binD_reflect {b : List YCell} (hb : ∀ c ∈ b, 2 ≤ c.lo) (p s : ℝ) :
    AngularSource.binD (reflectL b) p s = MomentSource.binD p s b := by
  unfold AngularSource.binD MomentSource.binD AngularSource.binM2
  rw [physL_reflectL hb, massL_reflectL]
  simp

lemma alpha_reflect {b : List YCell} (hb : ∀ c ∈ b, 2 ≤ c.lo) (p s t : ℝ) :
    AngularSource.binAlpha (reflectL b) p s t = - MomentSource.binAlpha p t s b := by
  unfold AngularSource.binAlpha
  rw [binD_reflect hb]
  unfold AngularSource.binM1 MomentSource.binAlpha
  rw [physL_reflectL hb, massL_reflectL]
  have h1 : physL b (fun x => (fun x : ℝ => x) (-x)) = - physL b id := by
    have := MomentSource.physL_const_mul b (-1) id
    simpa using this
  rw [h1]
  ring

lemma kernelC_neg {recs : List BinRec} (hpos : ∀ r ∈ recs, ∀ c ∈ r.cells, 2 ≤ c.lo) (p s : ℝ) :
    kernelC ((recs.map BinRec.cells).map reflectL) p s = constTrue p s recs := by
  unfold kernelC constTrue
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp_apply]
  rw [massL_reflectL, binD_reflect (hpos r hr)]

lemma kernelCoef_neg {recs : List BinRec} (hpos : ∀ r ∈ recs, ∀ c ∈ r.cells, 2 ≤ c.lo)
    (p s t : ℝ) (k : ℕ) :
    kernelCoef ((recs.map BinRec.cells).map reflectL) p s t k =
      (-1) ^ (k + 1) * (- trueCoef p t s recs (k + 1)) := by
  unfold kernelCoef trueCoef
  rw [List.map_map, List.map_map, mul_neg]
  congr 1
  rw [list_mul_sum]
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp_apply]
  rw [massL_reflectL, alpha_reflect (hpos r hr), neg_pow]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-! ### The integer coefficient lists -/

/-- Power-basis numerators of `gasA` over `2^P`, positive species. -/
def glPos (P : ℕ) (recs : List BinRec) (cnum : ℤ) (n : ℕ) : List ℤ :=
  cnum :: (List.range n).map fun k => -((coefNum (k + 1) (Sagg P recs (k + 1)) : ℕ) : ℤ)

/-- Power-basis numerators of `gasA` over `2^P`, negative species (two record lists, parity sign). -/
def glNeg (P : ℕ) (recs₁ recs₂ : List BinRec) (cnum : ℤ) (n : ℕ) : List ℤ :=
  cnum :: (List.range n).map fun k =>
    (-1) ^ (k + 1) * (-((coefNum (k + 1) (Sagg P recs₁ (k + 1)) +
      coefNum (k + 1) (Sagg P recs₂ (k + 1)) : ℕ) : ℤ))

lemma glPos_length (P recs cnum n) : (glPos P recs cnum n).length = n + 1 := by simp [glPos]
lemma glNeg_length (P r₁ r₂ cnum n) : (glNeg P r₁ r₂ cnum n).length = n + 1 := by simp [glNeg]
lemma glPos_ne_nil (P recs cnum n) : glPos P recs cnum n ≠ [] := by simp [glPos]
lemma glNeg_ne_nil (P r₁ r₂ cnum n) : glNeg P r₁ r₂ cnum n ≠ [] := by simp [glNeg]

lemma glPos_getD_zero (P recs cnum n) : (glPos P recs cnum n).getD 0 0 = cnum := by simp [glPos]
lemma glNeg_getD_zero (P r₁ r₂ cnum n) : (glNeg P r₁ r₂ cnum n).getD 0 0 = cnum := by simp [glNeg]

lemma glPos_getD_succ (P recs cnum n) {k : ℕ} (hk : k < n) :
    (glPos P recs cnum n).getD (k + 1) 0 = -((coefNum (k + 1) (Sagg P recs (k + 1)) : ℕ) : ℤ) := by
  simp [glPos, List.getD_eq_getElem?_getD, hk]

lemma glNeg_getD_succ (P r₁ r₂ cnum n) {k : ℕ} (hk : k < n) :
    (glNeg P r₁ r₂ cnum n).getD (k + 1) 0 = (-1) ^ (k + 1) *
      (-((coefNum (k + 1) (Sagg P r₁ (k + 1)) + coefNum (k + 1) (Sagg P r₂ (k + 1)) : ℕ) : ℤ)) := by
  simp [glNeg, List.getD_eq_getElem?_getD, hk]

lemma sum_abs_bound (g : ℕ → ℝ) (E0 B : ℝ) (n : ℕ) (h0 : |g 0| ≤ E0)
    (hk : ∀ k < n, |g (k + 1)| ≤ B) : ∑ j ∈ Finset.range (n + 1), |g j| ≤ E0 + n * B := by
  rw [Finset.sum_range_succ']
  have : ∑ k ∈ Finset.range n, |g (k + 1)| ≤ ∑ k ∈ Finset.range n, B :=
    Finset.sum_le_sum fun k hk' => hk k (Finset.mem_range.1 hk')
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  linarith

/-! ### Positive species -/

/-- **Positive species.**  From a partition of the gas into the bins `recs.map cells` and per-record
`RecOK`, the C6 binning hypothesis `hb` holds and the C6 coefficient bound `hG` holds for the integer
list `glPos` over `gd = 2^P`, with `eG = η0 + n * coefBudget`. -/
theorem gasCert_pos (S : CapSource) {recs : List BinRec} (i : ℕ)
    (hp : Partitioned (S.gas Sign.pos) (recs.map BinRec.cells)) {n P : ℕ} {δ : BinRec → ℝ}
    (h : ∀ r ∈ recs, RecOK P ((S.rad i) ^ 2) (S.rad i) 1 (δ r) r)
    (cnum : ℤ) {η0 : ℝ} (hc0 : |(cnum : ℝ) / 2 ^ P - constTrue ((S.rad i) ^ 2) 1 recs| ≤ η0) :
    Binning (S.gas Sign.pos) (recs.map BinRec.cells) ∧
    ∑ j ∈ Finset.range (n + 1),
      |gasA S Sign.pos i (recs.map BinRec.cells) j -
        (((glPos P recs cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      η0 + n * coefBudget P δ recs := by
  refine ⟨binning_of_partitioned hp, ?_⟩
  apply sum_abs_bound _ η0 _ n
  · simp only [gasA, gasConst, glPos_getD_zero, kernelC_pos]
    simp only [reduceCtorEq, ite_false, add_zero]
    rw [abs_sub_comm]
    push_cast
    exact hc0
  · intro k hk
    simp only [gasA, gasCoefK, glPos_getD_succ P recs cnum n hk, kernelCoef_pos]
    simp only [reduceCtorEq, ite_false, add_zero]
    have hb := coef_err h (j := k + 1) (by omega)
    unfold coefR at hb
    rw [← abs_neg]
    convert hb using 2
    push_cast
    ring

/-! ### Negative species -/

/-- **Negative species.**  Bins are the reflections of the C8 bins (so that `Binning (S.gas neg)` holds
for the original negative cells); both kernels are summed and the parity sign is absorbed in `glNeg`. -/
theorem gasCert_neg (S : CapSource) {recs₁ recs₂ : List BinRec} (i : ℕ)
    (hp : Partitioned (reflectL (S.gas Sign.neg)) (recs₁.map BinRec.cells))
    (hbins : recs₂.map BinRec.cells = recs₁.map BinRec.cells)
    (hg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2) (hw : ∀ c ∈ S.gas Sign.neg, 0 < c.w)
    {n P : ℕ} {δ₁ δ₂ : BinRec → ℝ}
    (h₁ : ∀ r ∈ recs₁, RecOK P ((S.rad i) ^ 2) (S.rad i) 1 (δ₁ r) r)
    (h₂ : ∀ r ∈ recs₂, RecOK P 1 (S.rad i) ((S.rad i) ^ 2) (δ₂ r) r)
    (cnum : ℤ) {c₁ c₂ η₁ η₂ : ℝ}
    (hc₁ : |c₁ - constTrue ((S.rad i) ^ 2) 1 recs₁| ≤ η₁)
    (hc₂ : |c₂ - constTrue 1 ((S.rad i) ^ 2) recs₂| ≤ η₂)
    (hcsum : c₁ + c₂ = (cnum : ℝ) / 2 ^ P) :
    Binning (S.gas Sign.neg) ((recs₁.map BinRec.cells).map reflectL) ∧
    ∑ j ∈ Finset.range (n + 1),
      |gasA S Sign.neg i ((recs₁.map BinRec.cells).map reflectL) j -
        (((glNeg P recs₁ recs₂ cnum n).getD j 0 : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ)| ≤
      (η₁ + η₂) + n * (coefBudget P δ₁ recs₁ + coefBudget P δ₂ recs₂) := by
  have hPos := MomentSource.posL_reflect hg
  have hW := MomentSource.reflectL_w hw
  have hcells := hp.cells hPos hW
  have hpos₁ : ∀ r ∈ recs₁, ∀ c ∈ r.cells, 2 ≤ c.lo := fun r hr c hc =>
    (hcells r.cells (List.mem_map_of_mem hr) c hc).1
  have hpos₂ : ∀ r ∈ recs₂, ∀ c ∈ r.cells, 2 ≤ c.lo := fun r hr c hc =>
    (hcells r.cells (hbins ▸ List.mem_map_of_mem hr) c hc).1
  have hb6 : (recs₁.map BinRec.cells).map reflectL = (recs₂.map BinRec.cells).map reflectL := by
    rw [hbins]
  refine ⟨binning_of_partitioned_reflect hp, ?_⟩
  apply sum_abs_bound _ (η₁ + η₂) _ n
  · have e1 := kernelC_neg hpos₁ ((S.rad i) ^ 2) 1
    have e2 : kernelC ((recs₁.map BinRec.cells).map reflectL) 1 ((S.rad i) ^ 2) =
        constTrue 1 ((S.rad i) ^ 2) recs₂ := by
      rw [hb6]; exact kernelC_neg hpos₂ 1 ((S.rad i) ^ 2)
    simp only [gasA, gasConst, glNeg_getD_zero, ite_true, e1, e2]
    have : (cnum : ℝ) / ((2 ^ P : ℕ) : ℝ) = c₁ + c₂ := by push_cast; exact hcsum.symm
    rw [this]
    have h3 := abs_add_le (constTrue ((S.rad i) ^ 2) 1 recs₁ - c₁) (constTrue 1 ((S.rad i) ^ 2) recs₂ - c₂)
    rw [abs_sub_comm] at hc₁ hc₂
    have : constTrue ((S.rad i) ^ 2) 1 recs₁ + constTrue 1 ((S.rad i) ^ 2) recs₂ - (c₁ + c₂) =
      (constTrue ((S.rad i) ^ 2) 1 recs₁ - c₁) + (constTrue 1 ((S.rad i) ^ 2) recs₂ - c₂) := by ring
    rw [this]
    linarith
  · intro k hk
    have e1 := kernelCoef_neg hpos₁ ((S.rad i) ^ 2) 1 (S.rad i) k
    have e2 : kernelCoef ((recs₁.map BinRec.cells).map reflectL) 1 ((S.rad i) ^ 2) (S.rad i) k =
        (-1) ^ (k + 1) * (- trueCoef 1 (S.rad i) ((S.rad i) ^ 2) recs₂ (k + 1)) := by
      rw [hb6]; exact kernelCoef_neg hpos₂ 1 ((S.rad i) ^ 2) (S.rad i) k
    simp only [gasA, gasCoefK, glNeg_getD_succ P recs₁ recs₂ cnum n hk, ite_true, e1, e2]
    have hb1 := coef_err h₁ (j := k + 1) (by omega)
    have hb2 := coef_err h₂ (j := k + 1) (by omega)
    unfold coefR at hb1 hb2
    have hsq : |((-1 : ℝ)) ^ (k + 1)| = 1 := by simp
    have eq : (-1 : ℝ) ^ (k + 1) * (-trueCoef ((S.rad i) ^ 2) (S.rad i) 1 recs₁ (k + 1)) +
        (-1) ^ (k + 1) * (-trueCoef 1 (S.rad i) ((S.rad i) ^ 2) recs₂ (k + 1)) -
        (((-1 : ℤ) ^ (k + 1) * (-((coefNum (k + 1) (Sagg P recs₁ (k + 1)) +
          coefNum (k + 1) (Sagg P recs₂ (k + 1)) : ℕ) : ℤ)) : ℤ) : ℝ) / ((2 ^ P : ℕ) : ℝ) =
        (-1) ^ (k + 1) * -((-((coefNum (k + 1) (Sagg P recs₁ (k + 1)) : ℕ) : ℝ) / 2 ^ P +
          trueCoef ((S.rad i) ^ 2) (S.rad i) 1 recs₁ (k + 1)) +
          (-((coefNum (k + 1) (Sagg P recs₂ (k + 1)) : ℕ) : ℝ) / 2 ^ P +
          trueCoef 1 (S.rad i) ((S.rad i) ^ 2) recs₂ (k + 1))) := by
      push_cast
      ring
    rw [eq, abs_mul, abs_neg, hsq, one_mul]
    exact (abs_add_le _ _).trans (add_le_add hb1 hb2)

end

#print axioms gasCert_pos
#print axioms gasCert_neg

end CatalanMeasure.GenD.Signed.RouteI.GasCert

module

public import CatalanMeasure.GenD.Signed.Interp
public import CatalanMeasure.GenD.Signed.SigmaCap
public import CatalanMeasure.GenD.Signed.SpikeEnds
public import CatalanMeasure.GenD.Signed.SheetNear

/-!
# Phase 2 contract: the complete `SignedNearBounds` from endpoint data

`Phase2Data I` bundles exactly the data a Phase 2 data module supplies for `I` α-intervals:
the two endpoint trial families `DA i`, `DB i` at `αA i < αB i`, the endpoint suprema of the row,
column and FIXED-ROW fields (`fNegM`, `fPosMS`, `fPosMR`, `fNearMS`), the endpoint constants and
curvature, the dual chord `zb`, the cap constants (`CapEnd`) and the two budget inequalities.
`Phase2Data.toBounds` assembles the contract of `EnergyNear` from

* `SignedNearBounds.ofEnds` (Theorem M) for `e_mem, v_summable, R_geom, t_geom, reference, rowNeg,
  rowPos, column, const_le, budgetFix`;
* `fixedSum_ends` (below), the endpoint form of `fixedSumAt_of_cap` (Theorem S with the top cap):
  the fixed-row fields are exactly affine in the interpolation weight (`fNegM_interp`, ...), so
  endpoint suprema suffice; `ZB := zbCap` of the chord cap data;
* `spikeFix_of_ends` (Theorem SE) for `spikeFix`.

`Phase2Data.signedSecondSheetNear` is the end-to-end corollary: `SignedSecondSheetCore` for the
sheet, given the identification of the data with the sheet's problem data.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Filter OAI.InternalCatalan

noncomputable section

/-! ### 1. Elementary mixing -/

theorem mix_le {l a b A B ε : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ A + ε) (hb : b ≤ B + ε) :
    (1 - l) * a + l * b ≤ ((1 - l) * A + l * B) + ε := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_le_const {l a b M : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ M) (hb : b ≤ M) :
    (1 - l) * a + l * b ≤ M := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_nonneg {l a b : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (1 - l) * a + l * b :=
  add_nonneg (mul_nonneg (sub_nonneg.2 h1) ha) (mul_nonneg h0 hb)

theorem abs_le_one_of_Ioo {x a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hx : x ∈ Ioo a b) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ### 2. The cap data at the two endpoints and its chord -/

/-- The σ-cap data of one α-interval at its two endpoint trials `A`, `B`: the node threshold `gs`,
the top-cell start `xc`, the cap density `C1`, the off-top bounds `lam*` and the top-cell constants
`g*` of the fixed-row fields of each endpoint, the log coefficients `rSA, rSB` of the near field
and `rP` of the positive field (the latter is not interpolated: it only has to dominate
`rc α`). -/
structure CapEnd where
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  lamNA : ℝ
  lamNB : ℝ
  lamPA : ℝ → ℝ
  lamPB : ℝ → ℝ
  gPA : ℝ → ℝ
  gPB : ℝ → ℝ
  rP : ℝ → ℝ
  lamSA : ℝ → ℝ → ℝ
  lamSB : ℝ → ℝ → ℝ
  gSA : ℝ → ℝ → ℝ
  gSB : ℝ → ℝ → ℝ
  rSA : ℝ → ℝ → ℝ
  rSB : ℝ → ℝ → ℝ

/-- The cap data of the interpolated family: chords of the endpoint bounds. -/
def CapEnd.toS (E : CapEnd) (αA αB : ℝ) : SigmaCapData where
  gs := E.gs
  xc := E.xc
  C1 := E.C1
  lamN := fun α => chord αA αB E.lamNA E.lamNB α
  lamP := fun α => chord αA αB (E.lamPA α) (E.lamPB α) α
  gP := fun α => chord αA αB (E.gPA α) (E.gPB α) α
  rP := E.rP
  lamS := fun α β => chord αA αB (E.lamSA α β) (E.lamSB α β) α
  gS := fun α β => chord αA αB (E.gSA α β) (E.gSB α β) α
  rS := fun α β => chord αA αB (E.rSA α β) (E.rSB α β) α

/-! ### 3. `fixedSum` of one interval from endpoint data -/

/-- **`fixedSum` of one α-interval from the endpoint bounds of the fixed-row fields.**  The fields
`fNegM, fPosMS, fPosMR, fNearMS` of the interpolated family are affine in the weight, so the
endpoint hypotheses (A and B, same form as the hypotheses of `fixedSumAt_of_cap`) give those of
the chord cap data `E.toS αA αB`; `ZB := zbCap (E.toS αA αB)`. -/
theorem fixedSum_ends {ncount : ℕ → ℕ} {Rm Rn : ℕ → ℝ → ℝ} {rc αA αB lo hi : ℝ}
    {DA DB : ℕ → SignedData} (h : IntervalEnds αA αB lo hi DA DB) (E : CapEnd)
    (constant : ℕ → ℝ → ℝ)
    {FixAdm : ∀ (N m1 m2 s : ℕ), (Fin m1 → ℝ) → (Fin m2 → ℝ) → (Fin s → ℝ) → Prop}
    (hxc0 : 0 ≤ E.xc) (hxc1 : E.xc < 1) (hC1 : 0 < E.C1) (hrc : 0 ≤ rc) (hlo : 0 ≤ lo)
    (hhi : hi ≤ 1) (hn : ∀ N, 0 < ncount N) (hν : ∀ N, (DA N).ν = (ncount N : ℝ))
    (hrP : ∀ α ∈ Icc lo hi, rc * α ≤ E.rP α)
    (hrSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, 0 ≤ E.rSA α β)
    (hrSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, 0 ≤ E.rSB α β)
    (umin : ℕ → ℝ) (hum0 : ∀ N, 0 < umin N) (hum1 : ∀ N, umin N ≤ 1) (Bd Rbd : ℝ)
    (hBdPA : ∀ α ∈ Icc lo hi, E.gPA α - E.lamPA α ≤ Bd)
    (hBdPB : ∀ α ∈ Icc lo hi, E.gPB α - E.lamPB α ≤ Bd)
    (hBdSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.gSA α β - E.lamSA α β ≤ Bd)
    (hBdSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.gSB α β - E.lamSB α β ≤ Bd)
    (hRP : ∀ α ∈ Icc lo hi, E.rP α ≤ Rbd)
    (hRSA : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.rSA α β ≤ Rbd)
    (hRSB : ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α, E.rSB α β ≤ Rbd)
    (hn_top : Tendsto (fun N => (ncount N : ℝ)) atTop atTop)
    (hlogu : Tendsto (fun N => -Real.log (umin N) / (ncount N : ℝ)) atTop (nhds 0))
    (hFix : ∀ N m1 m2 s (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      FixAdm N m1 m2 s yn yp zp →
        FixAdmCap E.gs E.xc E.C1 (ncount N : ℝ) (umin N) yn yp zp)
    (hnegA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -E.gs → (DA N).fNegM (Rm N) x ≤ E.lamNA + ε)
    (hnegB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -E.gs → (DB N).fNegM (Rm N) x ≤ E.lamNB + ε)
    (hposA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DA N).fPosMR (Rm N) rc α x ≤ E.lamPA α + ε)
    (hposB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DB N).fPosMR (Rm N) rc α x ≤ E.lamPB α + ε)
    (hposTopA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x → (DA N).fPosMS (Rm N) x ≤ E.gPA α + ε)
    (hposTopB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x → (DB N).fPosMS (Rm N) x ≤ E.gPB α + ε)
    (hnearA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DA N).fNearMS (Rn N) α β x ≤ E.lamSA α β + ε)
    (hnearB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.gs ≤ x → x < E.xc →
        (DB N).fNearMS (Rn N) α β x ≤ E.lamSB α β + ε)
    (hnearTopA : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x →
        (DA N).fNearMS (Rn N) α β x ≤
          E.gSA α β + ε + E.rSA α β * (-Real.log (1 - x ^ 2)))
    (hnearTopB : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc lo hi, ∀ β ∈ Icc 0 α,
      ∀ x ∈ Ioo (0 : ℝ) 1, E.xc ≤ x →
        (DB N).fNearMS (Rn N) α β x ≤
          E.gSB α β + ε + E.rSB α β * (-Real.log (1 - x ^ 2))) :
    FixedSumAt ncount (interpFamily αA αB DA DB constant) Rm Rn rc lo hi
      (zbCap (E.toS αA αB)) FixAdm := by
  have hmem : ∀ α ∈ Icc lo hi, 0 ≤ interpL αA αB α ∧ interpL αA αB α ≤ 1 :=
    fun α hα => h.mem hα
  refine fixedSumAt_of_cap (E.toS αA αB) (ZB := zbCap (E.toS αA αB)) hxc0 hxc1 hC1 hrc hlo hhi
    hn (fun N α => hν N) hrP ?_ umin hum0 hum1 Bd Rbd ?_ ?_ ?_ ?_ hn_top hlogu hFix
    (fun _ _ _ _ _ _ => le_rfl) ?_ ?_ ?_ ?_ ?_
  · intro α hα β hβ
    exact mix_nonneg (hmem α hα).1 (hmem α hα).2 (hrSA α hα β hβ) (hrSB α hα β hβ)
  · intro α hα
    have := mix_le_const (hmem α hα).1 (hmem α hα).2 (hBdPA α hα) (hBdPB α hα)
    simp only [CapEnd.toS, chord]; nlinarith [this]
  · intro α hα β hβ
    have := mix_le_const (hmem α hα).1 (hmem α hα).2 (hBdSA α hα β hβ) (hBdSB α hα β hβ)
    simp only [CapEnd.toS, chord]; nlinarith [this]
  · intro α hα
    exact hRP α hα
  · intro α hα β hβ
    exact mix_le_const (hmem α hα).1 (hmem α hα).2 (hRSA α hα β hβ) (hRSB α hα β hβ)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnegA ε hε, hnegB ε hε] with N rA rB a b α hα x hx hxg
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNegM (Rm N) x ≤
      chord αA αB E.lamNA E.lamNB α + ε
    rw [fNegM_interp hl0 hl1 (h.compat N) rA rB (Rm N) (abs_le_one_of_Ioo le_rfl (by norm_num) hx)]
    exact mix_le hl0 hl1 (a α hα x hx hxg) (b α hα x hx hxg)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hposA ε hε, hposB ε hε] with N rA rB a b α hα x hx hg hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fPosMR (Rm N) rc α x ≤
      chord αA αB (E.lamPA α) (E.lamPB α) α + ε
    rw [fPosMR_interp hl0 hl1 (h.compat N) rA rB (Rm N) rc α
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα x hx hg hc) (b α hα x hx hg hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hposTopA ε hε, hposTopB ε hε] with N rA rB a b α hα x hx hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fPosMS (Rm N) x ≤
      chord αA αB (E.gPA α) (E.gPB α) α + ε
    rw [fPosMS_interp hl0 hl1 (h.compat N) rA rB (Rm N)
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα x hx hc) (b α hα x hx hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnearA ε hε, hnearB ε hε]
      with N rA rB a b α hα β hβ x hx hg hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNearMS (Rn N) α β x ≤
      chord αA αB (E.lamSA α β) (E.lamSB α β) α + ε
    rw [fNearMS_interp hl0 hl1 (h.compat N) rA rB (Rn N) α β
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    exact mix_le hl0 hl1 (a α hα β hβ x hx hg hc) (b α hα β hβ x hx hg hc)
  · intro ε hε
    filter_upwards [h.regA, h.regB, hnearTopA ε hε, hnearTopB ε hε]
      with N rA rB a b α hα β hβ x hx hc
    obtain ⟨hl0, hl1⟩ := hmem α hα
    show (SignedData.interp (DA N) (DB N) (interpL αA αB α) (constant N α)).fNearMS (Rn N) α β x ≤
      chord αA αB (E.gSA α β) (E.gSB α β) α + ε +
        chord αA αB (E.rSA α β) (E.rSB α β) α * (-Real.log (1 - x ^ 2))
    rw [fNearMS_interp hl0 hl1 (h.compat N) rA rB (Rn N) α β
      (abs_le_one_of_Ioo (by norm_num) le_rfl hx)]
    have e1 := mul_le_mul_of_nonneg_left (a α hα β hβ x hx hc) (sub_nonneg.2 hl1)
    have e2 := mul_le_mul_of_nonneg_left (b α hα β hβ x hx hc) hl0
    simp only [chord]
    nlinarith [e1, e2]

/-! ### 4. The complete Phase 2 data and the contract -/

/-- **Everything a Phase 2 data module supplies** for `I` α-intervals (see `NOTES-PC.md`). -/
structure Phase2Data (I : ℕ) where
  -- scale, partition, problem data
  ncount : ℕ → ℕ
  ncount_pos : ∀ N, 0 < ncount N
  B : ℝ
  cost : ℝ
  α1 : ℝ
  α1_nonneg : 0 ≤ α1
  lo : Fin I → ℝ
  hi : Fin I → ℝ
  cover : ∀ α : ℝ, 0 ≤ α → α ≤ α1 → ∃ i, lo i ≤ α ∧ α ≤ hi i
  Rf : ℕ → ℝ → ℝ
  Cf : ℕ → ℝ → ℝ
  Rm : ℕ → ℝ → ℝ
  Rn : ℕ → ℝ → ℝ
  constant : ℕ → ℝ → ℝ
  -- endpoint trials
  αA : Fin I → ℝ
  αB : Fin I → ℝ
  DA : Fin I → ℕ → SignedData
  DB : Fin I → ℕ → SignedData
  hends : ∀ i, IntervalEnds (αA i) (αB i) (lo i) (hi i) (DA i) (DB i)
  hν : ∀ i N, (DA i N).ν = (ncount N : ℝ)
  hRf : ∀ i N, (DA i N).Rf = Rf N
  hCf : ∀ i N, (DA i N).Cf = Cf N
  mA : ∀ i, ∀ᶠ N : ℕ in atTop, 1 = ∑ τ, ((DA i N).μ τ).real univ ∧
    1 - αA i = ∑ τ, ((DA i N).μf τ).real univ
  mB : ∀ i, ∀ᶠ N : ℕ in atTop, 1 = ∑ τ, ((DB i N).μ τ).real univ ∧
    1 - αB i = ∑ τ, ((DB i N).μf τ).real univ
  -- endpoint suprema of the free-row, column fields
  SnA : Fin I → ℝ
  SnB : Fin I → ℝ
  SpA : Fin I → ℝ
  SpB : Fin I → ℝ
  SyA : Fin I → ℝ
  SyB : Fin I → ℝ
  hSnA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
    (DA i N).fNeg x ≤ SnA i + ε
  hSnB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (-1 : ℝ) 0,
    (DB i N).fNeg x ≤ SnB i + ε
  hSpA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
    (DA i N).fPosS x ≤ SpA i + ε
  hSpB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x ∈ Ioo (0 : ℝ) 1,
    (DB i N).fPosS x ≤ SpB i + ε
  hSyA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
    (DA i N).fCol s ≤ SyA i + ε
  hSyB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
    (DB i N).fCol s ≤ SyB i + ε
  -- endpoint constants and curvature
  cP : Fin I → ℝ → ℝ
  rA : Fin I → ℝ
  rB : Fin I → ℝ
  κc : Fin I → ℝ
  hP : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    constant N α ≤ cP i α + ε
  hrA : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DA i N).constTotal (ncount N) - (DA i N).constant ≤ rA i + ε
  hrB : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    (DB i N).constTotal (ncount N) - (DB i N).constant ≤ rB i + ε
  hκ : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    κc i - ε ≤ curvQ (DA i N) (DB i N) (ncount N)
  -- the rest of the contract
  κlo : Fin I → ℝ
  κhi : Fin I → ℝ
  epsSplit : Fin I → ℝ
  epsSplit_pos : ∀ i, 0 < epsSplit i
  epsSplit_le : ∀ i, epsSplit i ≤ 1
  Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop
  LRf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → ℝ
  cp : Fin I → ℕ → ℝ → ℝ
  cp_pos : ∀ i N α, 0 < cp i N α
  cp_le : ∀ i N α, cp i N α ≤ 1
  err_small : ∀ i {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    (DA i N).errJ3 (cp i N α) (ncount N) ≤ ε
  -- the spike data (Theorem SE): margin below theta, LRf is the log-ratio, and the class gives
  -- a witness pair at the two endpoint trials (same configuration, same margin cp i N alpha)
  cp_theta : ∀ i N α, cp i N α ≤ (DA i N).θ
  hLR : ∀ i N k q m1 m2 xn gp yn yp, LRf N k q m1 m2 xn gp yn yp =
    logRatioZ (DA i N).sp (Fin.append xn yn) (Fin.append gp yp)
  hCls : ∀ i N α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
    ∃ bcap, Nonempty (PairCls (DA i N) (DB i N) (cp i N α) bcap xn gp yn yp)
  -- the σ cap (Theorem S): endpoint data and side conditions
  capE : Fin I → CapEnd
  hxc0 : ∀ i, 0 ≤ (capE i).xc
  hxc1 : ∀ i, (capE i).xc < 1
  hC1 : ∀ i, 0 < (capE i).C1
  hlo0 : ∀ i, 0 ≤ lo i
  hhi1 : ∀ i, hi i ≤ 1
  hrP : ∀ i, ∀ α ∈ Icc (lo i) (hi i), remC (epsSplit i) * α ≤ (capE i).rP α
  hrSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSA α β
  hrSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, 0 ≤ (capE i).rSB α β
  umin : ℕ → ℝ
  hum0 : ∀ N, 0 < umin N
  hum1 : ∀ N, umin N ≤ 1
  Bd : Fin I → ℝ
  Rbd : Fin I → ℝ
  hBdPA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).gPA α - (capE i).lamPA α ≤ Bd i
  hBdPB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).gPB α - (capE i).lamPB α ≤ Bd i
  hBdSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSA α β - (capE i).lamSA α β ≤ Bd i
  hBdSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α,
    (capE i).gSB α β - (capE i).lamSB α β ≤ Bd i
  hRP : ∀ i, ∀ α ∈ Icc (lo i) (hi i), (capE i).rP α ≤ Rbd i
  hRSA : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, (capE i).rSA α β ≤ Rbd i
  hRSB : ∀ i, ∀ α ∈ Icc (lo i) (hi i), ∀ β ∈ Icc 0 α, (capE i).rSB α β ≤ Rbd i
  hn_top : Tendsto (fun N => (ncount N : ℝ)) atTop atTop
  hlogu : Tendsto (fun N => -Real.log (umin N) / (ncount N : ℝ)) atTop (nhds 0)
  -- the common (geometric) cap parameters of the admissibility predicate `FixAdmCap gs xc C1 n umin`
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  hgs : ∀ i, (capE i).gs ≤ gs
  hxc : ∀ i, xc ≤ (capE i).xc
  hC1le : ∀ i, C1 ≤ (capE i).C1
  -- endpoint bounds of the fixed-row fields
  hnegA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs → (DA i N).fNegM (Rm N) x ≤ (capE i).lamNA + ε
  hnegB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (-1 : ℝ) 0, x ≤ -(capE i).gs → (DB i N).fNegM (Rm N) x ≤ (capE i).lamNB + ε
  hposA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA i N).fPosMR (Rm N) (remC (epsSplit i)) α x ≤ (capE i).lamPA α + ε
  hposB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB i N).fPosMR (Rm N) (remC (epsSplit i)) α x ≤ (capE i).lamPB α + ε
  hposTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x → (DA i N).fPosMS (Rm N) x ≤ (capE i).gPA α + ε
  hposTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x → (DB i N).fPosMS (Rm N) x ≤ (capE i).gPB α + ε
  hnearA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DA i N).fNearMS (Rn N) α β x ≤ (capE i).lamSA α β + ε
  hnearB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).gs ≤ x → x < (capE i).xc →
      (DB i N).fNearMS (Rn N) α β x ≤ (capE i).lamSB α β + ε
  hnearTopA : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DA i N).fNearMS (Rn N) α β x ≤
        (capE i).gSA α β + ε + (capE i).rSA α β * (-Real.log (1 - x ^ 2))
  hnearTopB : ∀ i, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ α ∈ Icc (lo i) (hi i),
    ∀ β ∈ Icc 0 α, ∀ x ∈ Ioo (0 : ℝ) 1, (capE i).xc ≤ x →
      (DB i N).fNearMS (Rn N) α β x ≤
        (capE i).gSB α β + ε + (capE i).rSB α β * (-Real.log (1 - x ^ 2))
  -- the budget: the dual chord zb dominates zbCap, and the budget at κlo, κhi
  zb : Fin I → ℝ → ℝ
  hZB : ∀ (i : Fin I) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo i ≤ c + d + e →
    c + d + e ≤ hi i → zbCap ((capE i).toS (αA i) (αB i)) c d e ≤ zb i (c + d + e)
  hbudLo : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
    interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α + (2 * α - α ^ 2) * Real.log 2 +
      κlo i * chord (αA i) (αB i) (SnA i) (SnB i) α +
      (1 - κlo i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α
  hbudHi : ∀ i, ∀ α ∈ Icc (lo i) (hi i),
    interpCInf (αA i) (αB i) (cP i α) (rA i) (rB i) (κc i) α + (2 * α - α ^ 2) * Real.log 2 +
      κhi i * chord (αA i) (αB i) (SnA i) (SnB i) α +
      (1 - κhi i - α) * chord (αA i) (αB i) (SpA i) (SpB i) α +
      (1 - α) * chord (αA i) (αB i) (SyA i) (SyB i) α + zb i α ≤ B + cost * α

theorem remC_nonneg {ε : ℝ} (h : 0 < ε) : 0 ≤ remC ε := by
  unfold remC; positivity

/-- `FixAdmCap` is monotone in the geometry: a larger node threshold, a smaller top-cell start and
a smaller cap density give a stronger predicate. -/
theorem FixAdmCap_mono {gs gs' xc xc' C1 C1' n umin : ℝ} {m1 m2 s : ℕ} {yn : Fin m1 → ℝ}
    {yp : Fin m2 → ℝ} {zp : Fin s → ℝ} (hgs : gs' ≤ gs) (hxc : xc ≤ xc') (hC : C1 ≤ C1')
    (hn : 0 ≤ n) (hu : 0 ≤ umin) (h : FixAdmCap gs xc C1 n umin yn yp zp) :
    FixAdmCap gs' xc' C1' n umin yn yp zp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have key : ∀ y : ℝ, y ≤ 1 - umin → C1 * n * (1 - y) + 1 ≤ C1' * n * (1 - y) + 1 := by
    intro y hy
    have : 0 ≤ n * (1 - y) := mul_nonneg hn (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hC this]
  refine ⟨fun j => (h1 j).trans (by linarith), fun j => hgs.trans (h2 j),
    fun j => hgs.trans (h3 j), h4, h5, fun j hj => (h6 j (hxc.trans hj)).trans (key _ (h4 j)),
    fun j hj => (h7 j (hxc.trans hj)).trans (key _ (h5 j))⟩

/-- The single admissibility predicate of the Phase 2 contract (common geometry). -/
def Phase2Data.FixAdm {I : ℕ} (D : Phase2Data I) (N m1 m2 s : ℕ) (yn : Fin m1 → ℝ)
    (yp : Fin m2 → ℝ) (zp : Fin s → ℝ) : Prop :=
  FixAdmCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N) yn yp zp

/-- It implies the cap predicate of every interval. -/
theorem Phase2Data.hFix {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    ∀ N m1 m2 s (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ),
      D.FixAdm N m1 m2 s yn yp zp →
        FixAdmCap (D.capE i).gs (D.capE i).xc (D.capE i).C1 (D.ncount N : ℝ) (D.umin N)
          yn yp zp :=
  fun N _ _ _ _ _ _ h => FixAdmCap_mono (D.hgs i) (D.hxc i) (D.hC1le i) (Nat.cast_nonneg _)
    (D.hum0 N).le h

/-! ### Admissibility of the actual marked nodes -/

/-- **What `hlink` needs about the actual marked nodes `y`** (all marked rows, both signs): every
node has `|y| ≥ gs` (this is a property of each node: take it into `G`), every node is at
distance `≥ umin` from `1`, and the top count `#{i : y_j ≤ y_i} ≤ C1 n (1 - y_j) + 1` for
`y_j ≥ xc`. -/
def MarkedCap (gs xc C1 n umin : ℝ) {m : ℕ} (y : Fin m → ℝ) : Prop :=
  (∀ j, gs ≤ |y j|) ∧ (∀ j, y j ≤ 1 - umin) ∧
    ∀ j, xc ≤ y j → ((Finset.univ.filter (fun i => y j ≤ y i)).card : ℝ) ≤ C1 * n * (1 - y j) + 1

theorem count_sub_le {m a : ℕ} (y : Fin m → ℝ) (f : Fin a → Fin m) (hf : Function.Injective f)
    (j : Fin a) :
    (Finset.univ.filter (fun i => y (f j) ≤ y (f i))).card ≤
      (Finset.univ.filter (fun i => y (f j) ≤ y i)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    simpa using hi
  · exact hf.injOn

/-- **`FixAdm` for every splitting** (the clause of `SignedNearClassLink`): from `MarkedCap` of the
marked rows `y`, the sign split `σy` and any splitting `τ` of the positives into first-kind and
near rows, the three lists satisfy `FixAdmCap`.  The top count of a sub-family is at most the
count of all marked rows. -/
theorem fixAdmCap_of_marked {gs xc C1 n umin : ℝ} (hxc : 0 ≤ xc) {m m1 m2 r s' : ℕ}
    {y : Fin m → ℝ} (hM : MarkedCap gs xc C1 n umin y) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (τ : Fin r ⊕ Fin s' ≃ Fin m2) :
    FixAdmCap gs xc C1 n umin (fun b => y (σy (Sum.inl b)))
      (fun j => y (σy (Sum.inr (τ (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => h2 _, fun j => h2 _, fun j hj => ?_,
    fun j hj => ?_⟩
  · have := h1 (σy (Sum.inl j)); rw [abs_of_neg (hyneg j)] at this; linarith
  · have := h1 (σy (Sum.inr (τ (Sum.inl j)))); rwa [abs_of_pos (hypos _)] at this
  · have := h1 (σy (Sum.inr (τ (Sum.inr j)))); rwa [abs_of_pos (hypos _)] at this
  · have hinj : Function.Injective
        (fun i : Fin r => σy (Sum.inr (τ (Sum.inl i)))) :=
      fun a b hab => Sum.inl_injective (τ.injective (Sum.inr_injective (σy.injective hab)))
    exact (Nat.cast_le.2 (count_sub_le y _ hinj j)).trans (h3 _ hj)
  · have hinj : Function.Injective
        (fun i : Fin s' => σy (Sum.inr (τ (Sum.inr i)))) :=
      fun a b hab => Sum.inr_injective (τ.injective (Sum.inr_injective (σy.injective hab)))
    exact (Nat.cast_le.2 (count_sub_le y _ hinj j)).trans (h3 _ hj)

/-- The complete contract `SignedNearBounds I` from the Phase 2 data. -/
def Phase2Data.toBounds {I : ℕ} (D : Phase2Data I) : SignedNearBounds I :=
  SignedNearBounds.ofEnds D.ncount D.ncount_pos D.B D.cost D.α1 D.α1_nonneg D.lo D.hi D.cover
    D.Rf D.Cf D.Rm D.Rn D.constant D.αA D.αB D.DA D.DB D.hends D.hν D.hRf D.hCf D.mA D.mB
    D.SnA D.SnB D.SpA D.SpB D.SyA D.SyB D.hSnA D.hSnB D.hSpA D.hSpB D.hSyA D.hSyB
    D.cP D.rA D.rB D.κc D.hP D.hrA D.hrB D.hκ D.κlo D.κhi D.epsSplit D.epsSplit_pos
    D.epsSplit_le (fun i => zbCap ((D.capE i).toS (D.αA i) (D.αB i))) D.zb D.Clsf D.LRf D.FixAdm
    D.cp D.cp_pos D.cp_le D.err_small
    (spikeFix_of_ends D.αA D.αB D.DA D.DB D.constant D.cp D.cp_pos D.cp_le D.cp_theta D.Clsf
      D.LRf D.hLR D.hCls)
    (fun i ε hε => fixedSum_ends (D.hends i) (D.capE i) D.constant (D.hxc0 i) (D.hxc1 i)
      (D.hC1 i) (remC_nonneg (D.epsSplit_pos i)) (D.hlo0 i) (D.hhi1 i) D.ncount_pos (D.hν i)
      (D.hrP i) (D.hrSA i) (D.hrSB i) D.umin D.hum0 D.hum1 (D.Bd i) (D.Rbd i)
      (D.hBdPA i) (D.hBdPB i) (D.hBdSA i) (D.hBdSB i) (D.hRP i) (D.hRSA i) (D.hRSB i)
      D.hn_top D.hlogu (D.hFix i) (D.hnegA i) (D.hnegB i) (D.hposA i) (D.hposB i)
      (D.hposTopA i) (D.hposTopB i) (D.hnearA i) (D.hnearB i) (D.hnearTopA i) (D.hnearTopB i)
      ε hε)
    D.hZB D.hbudLo D.hbudHi

/-- The budget's `ZB` and the `ZB` of the field `fixedSum` are the same function `zbCap`. -/
theorem Phase2Data.toBounds_ZB {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    D.toBounds.ZB i = zbCap ((D.capE i).toS (D.αA i) (D.αB i)) := rfl

/-- Conformance of the produced `fixedSum` with `FixedSumAt`. -/
theorem Phase2Data.toBounds_fixedSum {I : ℕ} (D : Phase2Data I) (i : Fin I) :
    FixedSumAt D.toBounds.ncount (D.toBounds.D i) D.toBounds.Rm D.toBounds.Rn
      (remC (D.toBounds.epsSplit i)) (D.toBounds.lo i) (D.toBounds.hi i) (D.toBounds.ZB i)
      D.toBounds.FixAdm :=
  fixedSumAt_conform D.toBounds i

/-! ### 5. The end-to-end corollary -/

section Sheet

open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic

/-- **End-to-end.**  The signed second-case sheet bound (`SignedSecondSheetCore`) from the Phase 2
endpoint data `D`, the identification of the data with the sheet's problem data, the cost
`D.cost * n0 ≤ c2`, the non-class branch `hnon` (old energy route) and the class link `hlink`
(which delivers `Clsf` and `FixAdm` for every splitting).  Nothing else is needed. -/
theorem Phase2Data.signedSecondSheetNear {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop)
    (hn : ∀ N, D.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      D.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, D.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, D.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, D.Rn N = groupedNearField P N)
    (hCf : ∀ N, D.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', D.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : D.B = -target0 + Real.log 2 / 2)
    (hcost : D.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (hlink : SignedNearClassLink P D.toBounds Cls G) :
    SignedSecondSheetCore P G target0 c2 D.α1 :=
  _root_.CatalanMeasure.Signed.signedSecondSheetNear hP G target0 c2 Cls D.toBounds hn hconst hRf hRm hRn hCf hLRf hB hcost
    hnon hlink

end Sheet

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNear

#print axioms CatalanMeasure.Signed.fixedSum_ends
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds_ZB
#print axioms CatalanMeasure.Signed.FixAdmCap_mono
#print axioms CatalanMeasure.Signed.Phase2Data.hFix
#print axioms CatalanMeasure.Signed.fixAdmCap_of_marked

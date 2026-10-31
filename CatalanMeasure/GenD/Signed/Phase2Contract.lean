module

public import CatalanMeasure.GenD.Signed.Interp
public import CatalanMeasure.GenD.Signed.SigmaCap
public import CatalanMeasure.GenD.Signed.SpikeEnds
public import CatalanMeasure.GenD.Signed.SheetNear
public import CatalanMeasure.GenD.Signed.MarkedCap

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
    Nonempty (PairCls (DA i N) (DB i N) (cp i N α) xn gp yn yp)
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

/-! `MarkedCap` (the cap of the actual marked rows) is defined in `MarkedCap.lean`. -/

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

/-- **The near-optimal class (the dichotomy of PROOF-A 17.9(a), Lemma 4).**  A free configuration
`z` is in the class when SOME marked selection `(x, y)` and column configuration `s` violate the
old-route (grouped-product) bound at `target`, with no `ε`.  Off the class the old route holds by
definition, so the non-class branch `hnon` is automatic (`hnon_nearOpt`); all the content is in the
class branch (`hlink`: Lemma K containment, spike witnesses).  See `SPIKE-CLASS.md` §1. -/
def nearOptCls (P : Parameters) (target cost : ℝ) (G : ℝ → Prop) :
    ∀ (N r : ℕ), (Fin r → ℝ) → Prop :=
  fun N r z => ∃ (a b : ℕ) (_ : r + a + b = P.n N) (x : Fin a → ℝ) (y : Fin b → ℝ)
    (s : Fin r → ℝ),
    (∀ i, z i ∈ Ioo (-1 : ℝ) 1) ∧ (∀ i, z i ≠ 0) ∧ (∀ i, x i ∈ Ioo (-1 : ℝ) 1) ∧
    (∀ i, G (x i)) ∧ (∀ i, y i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, s i ∈ Ioo (0 : ℝ) 1) ∧
    Function.Injective z ∧ Function.Injective (Fin.append z x) ∧ Function.Injective y ∧
    Function.Injective s ∧
    Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2) + cost * N * (a + b)) <
      groupedProduct P N z x y s

/-- The non-class branch for the near-optimal class: no hypothesis. -/
theorem hnon_nearOpt (P : Parameters) (target cost : ℝ) (G : ℝ → Prop) :
    GroupedMarkedProductCostOnRestr P target cost G
      (fun N r _ _ z _ _ _ => ¬ nearOptCls P target cost G N r z) := by
  intro ε hε
  refine Filter.Eventually.of_forall fun N r a b hrab z x y s hz hz0 hx hxG hy hs hzi hzxi hyi hsi
    hQ => ?_
  by_contra h0
  have h := lt_of_not_ge h0
  apply hQ
  refine ⟨a, b, hrab, x, y, s, hz, hz0, hx, hxG, hy, hs, hzi, hzxi, hyi, hsi,
    lt_of_le_of_lt ?_ h⟩
  apply Real.exp_le_exp.mpr
  have h0 : 0 ≤ ((P.n0 : ℝ) * N) ^ 2 * ε := by positivity
  have e : ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2 + ε) =
      ((P.n0 : ℝ) * N) ^ 2 * (-target + Real.log 2 / 2) + ((P.n0 : ℝ) * N) ^ 2 * ε := by ring
  rw [e]
  linarith

/-- **End-to-end with the near-optimal class:** `hnon` discharged; what remains is the data `D`,
the identification and the class link for `nearOptCls`. -/
theorem Phase2Data.signedSecondSheetNear_nearOpt {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
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
    (hlink : SignedNearClassLink P D.toBounds (nearOptCls P target0 c2 G) G) :
    SignedSecondSheetCore P G target0 c2 D.α1 :=
  D.signedSecondSheetNear hP G target0 c2 _ hn hconst hRf hRm hRn hCf hLRf hB hcost
    (hnon_nearOpt P target0 c2 G) hlink

/-- **Node-set form** (`Nd`, SheetNear `signedSecondSheetNearNd`) with the near-optimal class. -/
theorem Phase2Data.signedSecondSheetNearNd_nearOpt {I : ℕ} (D : Phase2Data I) {P : Parameters}
    (hP : Admissible P) (G : ℝ → Prop) (target0 c2 : ℝ)
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
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P D.toBounds (nearOptCls P target0 c2 G) G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 D.α1 :=
  _root_.CatalanMeasure.Signed.signedSecondSheetNearNd hP G target0 c2 _ D.toBounds hn hconst
    hRf hRm hRn hCf hLRf hB hcost (hnon_nearOpt P target0 c2 G) Nd hlink

/-- **The `FixAdm` clause of `hlink` from the node set** (NOTES-MC wiring): for marked rows that
are node images (`NodeSub τ`) of a node set with `NodeCap` at the common cap data of `D`, every
sign split and every splitting satisfy `D.FixAdm`.  For the real nodes take
`τ := gapNodesD P (2g/(1+g²))` and `hZ := nodeCap_gap ..` (with `D.C1` the node constant
`J/(n · 2 xc √(1-a²))`, `D.umin N = √(1-a²)/(2(J+1))`). -/
theorem Phase2Data.fixAdm_of_nodeSub {I : ℕ} (D : Phase2Data I) {J : ℕ → ℕ}
    {τ : (N : ℕ) → Fin (J N) → ℝ} {N m m1 m2 r s' : ℕ} {y : Fin m → ℝ}
    (hxc : 0 ≤ D.xc)
    (hZ : NodeCap D.gs D.xc D.C1 (D.ncount N : ℝ) (D.umin N)
      (fun a => OAI.InternalCatalan.realCoordinate (τ N a)))
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hNd : NodeSub τ N m y) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m)
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (τ' : Fin r ⊕ Fin s' ≃ Fin m2) :
    D.FixAdm N m1 r s' (fun b => y (σy (Sum.inl b)))
      (fun j => y (σy (Sum.inr (τ' (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ' (Sum.inr j))))) :=
  fixAdmCap_of_marked hxc (markedCap_of_nodeSub hZ hy hNd) σy hyneg hypos τ'

end Sheet


/-! ### Spike witnesses from per-trial certificates (`spikeWitness_of_cert`)

`SpikeTrialCert D m ρ Kn Tn` is the per-trial, per-`m` data: finitely many real (in practice
rational) constants and inequalities that do not depend on the configuration.  `Kn` bounds the
number of negative rows, `Tn` the total number of rows plus one. -/

structure SpikeTrialCert (D : SignedData) (m : ℕ) (ρ Kn Tn : ℝ) where
  c1 : ℝ
  κ : ℝ
  L : ℝ
  De2 : ℝ
  Sg : ℝ
  A : ℝ
  K0 : ℝ
  A1 : ℝ
  B1 : ℝ
  BR : ℝ
  hθ : D.θ ∈ Ioc (0 : ℝ) (1 / 2)
  hc1 : 0 < c1
  hκ0 : 0 ≤ κ
  hκ1 : κ < 1
  hsp : 0 < D.sp
  hmκ : (m : ℝ) ≤ κ * D.sp
  hb : ∀ u ∈ Icc (-1 : ℝ) 1, c1 ≤ chebPs D.b u
  hpoly : ∀ u ∈ Icc (-1 : ℝ) 1,
    κ * (1 - ρ ^ 2) ≤ (chebPs D.b u - (1 - κ) * c1) * (1 + 2 * ρ * u + ρ ^ 2)
  hL0 : 0 ≤ L
  hL : Real.log (2 / (1 + realEnergyTau D.e ^ 2 * (1 - D.θ))) ≤ L
  hDe : ∀ y, 1 - D.θ ≤ y → y < 1 → barrierTrialS D.b (-y) - barrierTrialS D.b (-ρ) ≤ De2
  hSg : Real.log (1 - realEnergyTau D.e ^ 2 * (1 - D.θ) ^ 2) - Real.log (1 - ρ ^ 2) ≤ Sg
  hA : ∑' j : ℕ, |D.a j| ≤ A
  hK : costRem D.b (D.sp - m) m ρ ≤ K0
  hfin : 2 * (m : ℝ) * (Kn * L + 2 * (D.sp : ℝ) * De2 + m * Sg + 2 * D.ν * D.e * A) +
    (m : ℝ) * K0 ≤ D.ν * (((2 * m : ℕ) : ℝ) * D.cs)
  hkph : 0 ≤ D.kph
  hA1 : |barrierTrialS D.a (-D.τ * (1 - D.θ))| ≤ A1
  hB1 : |barrierTrialS D.b (-(1 - D.θ))| ≤ B1
  hBR : |∑' n : ℕ, D.R n * (D.τ * (1 - D.θ)) ^ (n + 1) / ((n : ℝ) + 1)| ≤ BR
  hph : 2 * D.ν * A1 + D.ν * BR + Tn * Real.log (1 / D.θ) + 2 * (D.sp : ℝ) * B1 + D.ν * D.cs ≤
    D.ν * D.kph

theorem SpikeTrialCert.m_lt {D : SignedData} {m : ℕ} {ρ Kn Tn : ℝ}
    (C : SpikeTrialCert D m ρ Kn Tn) : m < D.sp := by
  have h1 := C.hmκ
  have h2 : (0 : ℝ) < D.sp := by exact_mod_cast C.hsp
  have : (m : ℝ) < D.sp := by nlinarith [C.hκ1, C.hκ0]
  exact_mod_cast this

theorem SpikeTrialCert.cheb {D : SignedData} {m : ℕ} {ρ Kn Tn : ℝ} (hρ : |ρ| < 1)
    (C : SpikeTrialCert D m ρ Kn Tn) : SpikeChebOK D m ρ C.c1 :=
  spikeChebOK_of_cert hρ C.hκ0 C.hmκ C.m_lt.le C.hb C.hpoly

theorem SpikeTrialCert.costOK {D : SignedData} (E : SpikeEnv D) (rD : SignedRegular D) {m : ℕ}
    {ρ Kn Tn : ℝ} (C : SpikeTrialCert D m ρ Kn Tn) {K q' M : ℕ} (hM : M = 2 * m ∨ M + 1 = 2 * m)
    (xn : Fin K → ℝ) (y : Fin q' → ℝ) (z : Fin M → ℝ)
    (hx : ∀ b, |xn b| ≤ 1) (hy : ∀ j, |y j| ≤ 1) (hz : ∀ i, 1 - D.θ ≤ z i ∧ z i < 1)
    (hK : (K : ℝ) ≤ Kn) (hT : ((K + q' + M + 1 : ℕ) : ℝ) ≤ Tn) :
    SpikeCostOK D m xn y z (1 - D.θ) ρ := by
  have hm : m ≤ D.sp := C.m_lt.le
  have hcast : ((D.sp - m : ℕ) : ℝ) + m = D.sp := by
    rw [Nat.cast_sub hm]; ring
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hν := E.hν
  have hkL : (K : ℝ) * C.L ≤ Kn * C.L := mul_le_mul_of_nonneg_right hK C.hL0
  have hbound : ∀ w : Fin (2 * m) → ℝ, (∀ p, 1 - D.θ ≤ w p ∧ w p < 1) →
      spikeCost D.ν D.e D.a D.b (D.sp - m) m ρ (1 - D.θ) K w ≤
        D.ν * (((2 * m : ℕ) : ℝ) * D.cs) := by
    intro w hw
    have h := spikeCost_le_of_bounds hν.le E.he.1.le D.a D.b (D.sp - m) m K w C.hL
      (fun p => C.hDe _ (hw p).1 (hw p).2) C.hSg C.hA C.hK
    rw [hcast] at h
    have : 2 * (m : ℝ) * ((K : ℝ) * C.L) ≤ 2 * m * (Kn * C.L) :=
      mul_le_mul_of_nonneg_left hkL (by positivity)
    nlinarith [C.hfin, h, this]
  rcases hM with hM | hM
  · subst hM
    apply SpikeCostOK.of_even
    have := hbound z hz
    nlinarith [mul_nonneg hν.le C.hkph]
  · have hz' : ∀ i, |z i| ≤ 1 := fun i =>
      abs_le.mpr ⟨by linarith [(hz i).1, C.hθ.2], (hz i).2.le⟩
    refine SpikeCostOK.of_odd_cert D hν rD hM xn y z hx hy hz' C.hθ ρ C.hA1 C.hB1 C.hBR
      (hbound _ (extFam_mem z (1 - D.θ) (1 - D.θ) hz ⟨le_refl _, by linarith [C.hθ.1]⟩)) ?_
    have hlog : 0 ≤ Real.log (1 / D.θ) := Real.log_nonneg (by
      rw [le_div_iff₀ C.hθ.1]; linarith [C.hθ.2])
    have := mul_le_mul_of_nonneg_right hT hlog
    linarith [C.hph]

/-- **The witness pair from the certificates** (the `hCls` of the contract).  For a configuration
whose free and marked rows are in range, whose counts are bounded (`Kn`, `Tn`) and whose spike count is at most `Mmax` (Lemma K,
`free_spike_count`), the per-trial certificates of both endpoints for every `m` with
`2m ≤ Mmax + 1` (one pole `ρ` per `m`, i.e. per q-interval) give a `PairCls`. -/
theorem pairCls_of_cert {DA DB : SignedData} (hc : InterpCompat DA DB) (rA : SignedRegular DA)
    (rB : SignedRegular DB) (EA : SpikeEnv DA) (EB : SpikeEnv DB) {c' Kn Tn : ℝ}
    {k q m1 m2 : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ)
    (yp : Fin m2 → ℝ) (hX : ∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0)
    (hG : ∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1)
    (hK : (((k + m1 : ℕ)) : ℝ) ≤ Kn) (hT : ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn) {Mmax : ℕ}
    (hMc : (Finset.univ.filter (fun p => 1 - DA.θ < Fin.append gp yp p)).card ≤ Mmax)
    (hcert : ∀ m : ℕ, 2 * m ≤ Mmax + 1 → ∃ ρ : ℝ, |ρ| < 1 ∧ ρ ≤ DA.τ ^ 2 * (1 - DA.θ) ∧
      Nonempty (SpikeTrialCert DA m ρ Kn Tn) ∧ Nonempty (SpikeTrialCert DB m ρ Kn Tn)) :
    Nonempty (PairCls DA DB c' xn gp yn yp) := by
  classical
  set G := Fin.append gp yp with hGdef
  set X := Fin.append xn yn with hXdef
  set S := Finset.univ.filter (fun p => 1 - DA.θ < G p) with hS
  obtain ⟨q', M, τ', hnot, hin⟩ := exists_split_finset S
  set y : Fin q' → ℝ := fun j => G (τ' (Sum.inl j)) with hy
  set z : Fin M → ℝ := fun j => G (τ' (Sum.inr j)) with hz
  have hMS : M ≤ S.card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin M))) (t := S)
      (fun j => τ' (Sum.inr j)) (fun j _ => hin j)
      (fun a _ b _ hab => Sum.inr_injective (τ'.injective hab))
    simpa using this
  obtain ⟨m, hM⟩ : ∃ m : ℕ, M = 2 * m ∨ M + 1 = 2 * m :=
    ⟨(M + 1) / 2, by omega⟩
  have h2m : 2 * m ≤ Mmax + 1 := by omega
  obtain ⟨ρ, hρ, hρd, ⟨CA⟩, ⟨CB⟩⟩ := hcert m h2m
  have hθB : DB.θ = DA.θ := hc.θ
  have hX1 : ∀ b, |X b| ≤ 1 := fun b => abs_le.mpr ⟨(hX b).1.le, by linarith [(hX b).2]⟩
  have hG1 : ∀ p, |G p| ≤ 1 := fun p => abs_le.mpr ⟨by linarith [(hG p).1], (hG p).2.le⟩
  have hy1 : ∀ j, |y j| ≤ 1 := fun j => hG1 _
  have hzA : ∀ i, 1 - DA.θ ≤ z i ∧ z i < 1 := fun i =>
    ⟨(Finset.mem_filter.mp (hin i)).2.le, (hG _).2⟩
  have hzB : ∀ i, 1 - DB.θ ≤ z i ∧ z i < 1 := by rw [hθB]; exact hzA
  have hσ : ∀ i, G ((finSumFinEquiv.symm.trans τ') i) = Fin.append y z i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hy]
    · simp [hz]
  have hcnt : ((k + m1 + q' + M + 1 : ℕ) : ℝ) ≤ Tn := by
    have hqM : q' + M = q + m2 := by simpa using Fintype.card_congr τ'
    have : k + m1 + q' + M + 1 = k + m1 + (q + m2) + 1 := by omega
    rw [this]; exact hT
  have hcostA := CA.costOK EA rA hM X y z hX1 hy1 hzA hK hcnt
  have hcostB := CB.costOK EB rB hM X y z hX1 hy1 hzB hK hcnt
  rw [hθB] at hcostB
  have hyns : ∀ j, y j ≤ 1 - DA.θ := fun j => by
    by_contra h
    exact hnot j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩)
  have SP : SpikePair DA DB c' X G :=
    { q' := q'
      M := M
      m := m
      y := y
      z := z
      zph := 1 - DA.θ
      σ := finSumFinEquiv.symm.trans τ'
      hσ := hσ
      hM := hM
      hm := CA.m_lt
      hy_not_spike := hyns
      hz_spike := fun i => (Finset.mem_filter.mp (hin i)).2
      hzph := ⟨le_refl _, by linarith [CA.hθ.1]⟩
      ρ := ρ
      c1A := CA.c1
      c1B := CB.c1
      hρ := hρ
      hρd := hρd
      hc1A := CA.hc1
      hc1B := CB.hc1
      hPA := CA.cheb hρ
      hPB := CB.cheb hρ
      hcostA := hcostA
      hcostB := hcostB }
  exact ⟨⟨hc, rA, rB, EA, EB, SP⟩⟩


/-- **`hCls` of `Phase2Data` from the certificates.**  If the class `Clsf` carries the ranges, the
row counts (`Kn N`, `Tn N`) and the spike count `≤ Mmax N` (free spikes: `free_spike_count`;
marked spikes: the node top count of `MarkedCap`), and every endpoint trial has its certificate
for every `m` with `2m ≤ Mmax N + 1`, then the `hCls` field holds. -/
theorem hCls_of_cert {I : ℕ} {DA DB : Fin I → ℕ → SignedData} (cp : Fin I → ℕ → ℝ → ℝ)
    (hc : ∀ i N, InterpCompat (DA i N) (DB i N)) (rA : ∀ i N, SignedRegular (DA i N))
    (rB : ∀ i N, SignedRegular (DB i N)) (EA : ∀ i N, SpikeEnv (DA i N))
    (EB : ∀ i N, SpikeEnv (DB i N))
    (Clsf : ∀ (_ k q m1 m2 : ℕ), (Fin k → ℝ) → (Fin q → ℝ) → (Fin m1 → ℝ) → (Fin m2 → ℝ) → Prop)
    (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ)
    (hClsf : ∀ N k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      (∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0) ∧ (∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1) ∧
      (((k + m1 : ℕ)) : ℝ) ≤ Kn N ∧ ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn N ∧
      ∀ i, (Finset.univ.filter (fun p => 1 - (DA i N).θ < Fin.append gp yp p)).card ≤ Mmax N)
    (hcert : ∀ i N (m : ℕ), 2 * m ≤ Mmax N + 1 → ∃ ρ : ℝ, |ρ| < 1 ∧
      ρ ≤ (DA i N).τ ^ 2 * (1 - (DA i N).θ) ∧
      Nonempty (SpikeTrialCert (DA i N) m ρ (Kn N) (Tn N)) ∧
      Nonempty (SpikeTrialCert (DB i N) m ρ (Kn N) (Tn N))) :
    ∀ i N α k q m1 m2 xn gp yn yp, Clsf N k q m1 m2 xn gp yn yp →
      Nonempty (PairCls (DA i N) (DB i N) (cp i N α) xn gp yn yp) := by
  intro i N α k q m1 m2 xn gp yn yp h
  obtain ⟨hX, hG, hK, hT, hM⟩ := hClsf N k q m1 m2 xn gp yn yp h
  exact pairCls_of_cert (hc i N) (rA i N) (rB i N) (EA i N) (EB i N) xn gp yn yp hX hG hK hT
    (hM i) (hcert i N)

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNear

#print axioms CatalanMeasure.Signed.fixedSum_ends
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds
#print axioms CatalanMeasure.Signed.Phase2Data.toBounds_ZB
#print axioms CatalanMeasure.Signed.FixAdmCap_mono
#print axioms CatalanMeasure.Signed.Phase2Data.hFix
#print axioms CatalanMeasure.Signed.fixAdmCap_of_marked
#print axioms CatalanMeasure.Signed.hnon_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNear_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.signedSecondSheetNearNd_nearOpt
#print axioms CatalanMeasure.Signed.Phase2Data.fixAdm_of_nodeSub
#print axioms CatalanMeasure.Signed.pairCls_of_cert
#print axioms CatalanMeasure.Signed.hCls_of_cert

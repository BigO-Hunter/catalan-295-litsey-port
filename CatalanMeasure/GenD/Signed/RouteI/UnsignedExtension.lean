module

public import Mathlib.Analysis.Calculus.MeanValue
public import CatalanMeasure.GenD.Analytic.Glue
public import CatalanMeasure.GenD.Cert.ResW
public import CatalanMeasure.CellCert.FieldsSLink
public import CatalanMeasure.CellCert.ScaledSeries

@[expose] public section

/-!
# C15: the unsigned extension of the D58 residual cap to `[98749/1000000, 401/2500]`

Theorem side only: no numeric data, no certificate instances.

Imports, and what each is for.
* `Mathlib.Analysis.Calculus.MeanValue`: `antitoneOn_of_deriv_nonpos` (the piece lemma).
* `Analytic.Glue`: `resFieldGen`, `gRes` (via `Analytic.Const`), the consumer `secondTrial_of_fields`.
* `Cert.ResW`: `resFieldW` (the same function as `resFieldGen`), continuity on `[-1,1]`.
* `CellCert.FieldsSLink`: `finUR`, `poleOfTail`, `sum_qt_poleOfTail`, `hasDerivAt_log_one_add_sq`.
* `CellCert.ScaledSeries`: `trialSeqS_U_hasSum`.
None of them is a certificate-data module.

## Trace of the producer output types to the consumer type

Consumer (`Analytic.secondTrial_of_fields`, `Signed.Data.Trial72.EndpointAdapters.secondEnd_of_fields`,
which fill `SecondTrialBoundsEnd.marked`; `SecondTrialBoundsEnd` itself has no field named `residual`,
`residual` is its real parameter):
`residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual`,
where `u : ℕ → ℝ` is the `p` of the trial.  The retained provider
(`DesignInstance.PositiveCert.RCover.residual_sup_S`) states
`∀ x ∈ Icc (-1 : ℝ) 1, 401/2500 ≤ |x| → resFieldW ((53/58 : ℚ) : ℝ) (trialSeqS Pc P) x ≤ MR`,
`MR = -315531/5000000`.  `resFieldW ρ u` and `resFieldGen ρ u` are the same term
`-ρ * log (1 + x^2) - 2 * barrierTrialT u x`, so they are defeq, and `u = trialSeqS Pc P`.
`G58 x := x ≤ -19501/100000 ∨ 98749/1000000 ≤ x` (`RouteI.Literals`): `G58 x → x ≤ -19501/100000 ∨ 98749/1000000 ≤ x`
is `id`.  Both `x ≤ -19501/100000` and `401/2500 ≤ x` lie in `401/2500 ≤ |x|` (retained support);
the rest of `G58`, `98749/1000000 ≤ x < 401/2500`, is the extension proved here.  Hence the terminal
theorem `residual_sup_unsigned` has, with `residual` the consumer's parameter and `u = trialSeqS Pc Pt`,
exactly the type of `residual_sup`.  `G` is a variable with a coverage hypothesis, so the `G58`
instance (`hG := fun x h => h`) needs no import of `RouteI.Literals`.  Endpoint `x = 1` stays in
the retained provider (`1 ∈ [401/2500, 1]`); the near selected-determinant slot is not touched.

## What a later instance must supply (hypotheses of `residual_sup_unsigned`)
* `hρ : gRes P = 53/58`, `hdisk : tailsInDisk Pt = true`, `hz : ∀ t ∈ Pt, t.zr ≠ 0 ∨ t.zi ≠ 0`
  (so `0 < |z| < 1` on all 75 tails; `Pc`, `Pt` the pinned `Pc`/`P` lists).
* `hret`: the retained residual cap `residual` on `401/2500 ≤ |x|` (`residual_sup_S`).
* `hres : -315531/5000000 ≤ residual`.
* `hend : resFieldGen (gRes P) (trialSeqS Pc Pt) (98749/1000000) ≤ -8830153/100000000`
  (the source-bound endpoint evaluation).
* four per-piece derivative caps for the explicit derivative `resDeriv` (see below) on
  `(98749/1000000, 456647/4000000)`, `(456647/4000000, 259149/2000000)`,
  `(259149/2000000, 579949/4000000)`, `(579949/4000000, 401/2500)`, with caps
  `-134409/100000`, `-184553/100000`, `-174970/100000`, `-164062/100000`.  These are the M10
  rational-pole remainder inequalities (order 12, lower pole distances above the halfwidth, exact shifted
  degree-159 polynomial and its full tail); they are produced by the Taylor-cell machinery
  (`Signed.TaylorCell`) applied to the pole list `resPolesW`, with the reciprocal tower shifted
  by one derivative order relative to the log field.
-/

open Set OAI.InternalCatalan

namespace CatalanMeasure.GenD.Signed.RouteI.UnsignedExtension
open CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
  CatalanMeasure.Parametric
noncomputable section

/-! ### 1. The generic cover theorem -/

/-- Antitone on `[a,b]` and on `[b,c]` gives antitone on `[a,c]`. -/
theorem antitoneOn_glue {R : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : AntitoneOn R (Icc a b)) (h2 : AntitoneOn R (Icc b c)) : AntitoneOn R (Icc a c) := by
  intro x hx y hy hxy
  rcases le_total y b with hyb | hby
  · exact h1 ⟨hx.1, hxy.trans hyb⟩ ⟨hy.1, hyb⟩ hxy
  · rcases le_total x b with hxb | hbx
    · have e1 : R b ≤ R x := h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb
      have e2 : R y ≤ R b := h2 ⟨le_rfl, hbc⟩ ⟨hby, hy.2⟩ hby
      linarith only [e1, e2]
    · exact h2 ⟨hbx, hx.2⟩ ⟨hbx.trans hxy, hy.2⟩ hxy

/-- One piece: continuous on `[a,b]`, differentiable inside with derivative `≤ 0`. -/
theorem antitoneOn_piece {R R' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn R (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt R (R' x) x)
    (hneg : ∀ x ∈ Ioo a b, R' x ≤ 0) : AntitoneOn R (Icc a b) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hc ?_ ?_
  · rw [interior_Icc]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx; rw [(hd x hx).deriv]; exact hneg x hx

/-- **Generic cover theorem.**  `c 0 ≤ c 1 ≤ … ≤ c n` is a finite exact adjacent cover of
`[c 0, c n]`; `R` is continuous on `[c 0, c n]`, has derivative `R' x` at every interior point, and
`R' ≤ 0` on the interior of each piece.  Then `R` is antitone on `[c 0, c n]`. -/
theorem antitoneOn_of_cover {R R' : ℝ → ℝ} (n : ℕ) (c : ℕ → ℝ)
    (hmono : ∀ i < n, c i ≤ c (i + 1))
    (hcont : ContinuousOn R (Icc (c 0) (c n)))
    (hderiv : ∀ x ∈ Ioo (c 0) (c n), HasDerivAt R (R' x) x)
    (hneg : ∀ i < n, ∀ x ∈ Ioo (c i) (c (i + 1)), R' x ≤ 0) :
    AntitoneOn R (Icc (c 0) (c n)) := by
  have hle : ∀ i j, i ≤ j → j ≤ n → c i ≤ c j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j _ ih => intro hj; exact (ih (by omega)).trans (hmono j (by omega))
  have key : ∀ k, k ≤ n → AntitoneOn R (Icc (c 0) (c k)) := by
    intro k
    induction k with
    | zero =>
      intro _ x hx y hy _
      have hx0 : x = c 0 := le_antisymm hx.2 hx.1
      have hy0 : y = c 0 := le_antisymm hy.2 hy.1
      rw [hx0, hy0]
    | succ k ih =>
      intro hk
      have hpiece : AntitoneOn R (Icc (c k) (c (k + 1))) := by
        refine antitoneOn_piece ?_ ?_ (hneg k (by omega))
        · refine hcont.mono (Icc_subset_Icc (hle 0 k (by omega) (by omega)) (hle (k + 1) n hk le_rfl))
        · intro x hx
          exact hderiv x ⟨(hle 0 k (by omega) (by omega)).trans_lt hx.1,
            hx.2.trans_le (hle (k + 1) n hk le_rfl)⟩
      exact antitoneOn_glue (hle 0 k (by omega) (by omega)) (hmono k (by omega)) (ih (by omega))
        hpiece
  exact key n le_rfl

/-- Corollary: the endpoint bound propagates to the whole cover. -/
theorem le_of_cover {R R' : ℝ → ℝ} (n : ℕ) (c : ℕ → ℝ)
    (hmono : ∀ i < n, c i ≤ c (i + 1))
    (hcont : ContinuousOn R (Icc (c 0) (c n)))
    (hderiv : ∀ x ∈ Ioo (c 0) (c n), HasDerivAt R (R' x) x)
    (hneg : ∀ i < n, ∀ x ∈ Ioo (c i) (c (i + 1)), R' x ≤ 0)
    {e cap : ℝ} (hend : R (c 0) ≤ e) (hcap : e ≤ cap) :
    ∀ x ∈ Icc (c 0) (c n), R x ≤ cap := by
  intro x hx
  have h := antitoneOn_of_cover n c hmono hcont hderiv hneg ⟨le_rfl, (hx.1.trans hx.2)⟩ hx hx.1
  linarith only [h, hend, hcap]

/-! ### 2. The source identity for `resFieldGen (gRes P)` -/

/-- The Joukowski map `J(z) = (z + 1/z) / 2`. -/
def joukowski (z : ℂ) : ℂ := (z + z⁻¹) / 2

/-- The derivative of `R(x) = -2 Σ p_j T_j(x)/j - d log (1+x²) + Σ_tails Re (w Log (1 - 2xz + z²))`
at `x ∈ (-1,1)`, with `p_j = Pc_j / 2^40`, `d = ρ`, and tails `(z, w)`:
`R'(x) = P'_R(x) + Σ Re (w / (x - J z)) - 2 d Re (1 / (x - i))`, where `P'_R = -2 finUR Pc`. -/
def resDeriv (Pc : List ℤ) (Pt : List TailQ) (ρ : ℝ) (x : ℝ) : ℝ :=
  -2 * finUR Pc x
    + (Pt.map (fun t => (((TailQ.toC t).2) * ((x : ℂ) - joukowski (TailQ.toC t).1)⁻¹).re)).sum
    - 2 * ρ * ((1 : ℂ) / ((x : ℂ) - Complex.I)).re

theorem poleOfTail_pc (t : TailQ) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0) :
    (poleOfTail t).pc = joukowski (TailQ.toC t).1 := by
  have hn : (t.zr : ℝ) ^ 2 + (t.zi : ℝ) ^ 2 ≠ 0 := by
    rcases hz with h | h
    · have : (t.zr : ℝ) ≠ 0 := by exact_mod_cast h
      positivity
    · have : (t.zi : ℝ) ≠ 0 := by exact_mod_cast h
      positivity
  apply Complex.ext
  · simp [PoleR.pc, poleOfTail, joukowski, TailQ.toC, barrierComplex, Complex.inv_re,
      Complex.normSq_apply]
    field_simp
    ring
  · simp [PoleR.pc, poleOfTail, joukowski, TailQ.toC, barrierComplex, Complex.inv_im,
      Complex.normSq_apply]
    field_simp
    ring

theorem qt_poleOfTail_eq (t : TailQ) (hz : t.zr ≠ 0 ∨ t.zi ≠ 0) (x : ℝ) :
    qt (poleOfTail t) 0 x =
      (((TailQ.toC t).2) * ((x : ℂ) - joukowski (TailQ.toC t).1)⁻¹).re := by
  unfold qt qe
  rw [poleOfTail_pc t hz]
  have : (poleOfTail t).rho = (TailQ.toC t).2 := by
    simp [PoleR.rho, poleOfTail, TailQ.toC, barrierComplex]
  rw [this]
  simp

theorem re_inv_sub_I (x : ℝ) : ((1 : ℂ) / ((x : ℂ) - Complex.I)).re = x / (x ^ 2 + 1) := by
  have h : (x : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  simp [Complex.inv_re, Complex.normSq_apply]
  field_simp

/-- **Source identity.**  On `(-1,1)` the field `resFieldGen ρ (trialSeqS Pc Pt)` is differentiable
with derivative `resDeriv Pc Pt ρ x`. -/
theorem resFieldGen_hasDerivAt (ρ : ℝ) {Pc : List ℤ} {Pt : List TailQ}
    (hP : tailsInDisk Pt = true) (hz : ∀ t ∈ Pt, t.zr ≠ 0 ∨ t.zi ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (resFieldGen ρ (trialSeqS Pc Pt)) (resDeriv Pc Pt ρ x) x := by
  have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  obtain ⟨sP1, sP2⟩ := trialSeqS_summable (cs := Pc) hP
  have hT := barrierTrialT_hasDerivAt_series (trialSeqS Pc Pt) sP1 sP2 hx
  rw [(trialSeqS_U_hasSum Pc hP hxa).tsum_eq] at hT
  have hg := (hasDerivAt_log_one_add_sq x).const_mul (-ρ)
  have hall := hg.sub (hT.const_mul 2)
  unfold resFieldGen
  refine hall.congr_deriv ?_
  have hs := sum_qt_poleOfTail Pt hP hz hxa
  have hs' : (Pt.map (fun t => (((TailQ.toC t).2) *
      ((x : ℂ) - joukowski (TailQ.toC t).1)⁻¹).re)).sum =
      -2 * ((((Pt.map TailQ.toC).map (fun zr : ℂ × ℂ =>
        zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum).re) := by
    rw [← hs, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_apply]
    exact (qt_poleOfTail_eq t (hz t ht) x).symm
  unfold resDeriv
  rw [hs', re_inv_sub_I, add_comm (x ^ 2) 1]
  unfold finUR
  ring

/-- Continuity of the field on `[-1,1]` for the pinned tails. -/
theorem resFieldGen_continuousOn (ρ : ℝ) {Pc : List ℤ} {Pt : List TailQ}
    (hP : tailsInDisk Pt = true) :
    ContinuousOn (resFieldGen ρ (trialSeqS Pc Pt)) (Icc (-1 : ℝ) 1) :=
  resFieldW_continuousOn ρ (trialSeqS_summable (cs := Pc) hP).1

/-- The same identity for the design field: `ρ = gRes P = 53/58`. -/
theorem resFieldGen_gRes_hasDerivAt {P : Parameters} (hρ : gRes P = 53 / 58)
    {Pc : List ℤ} {Pt : List TailQ}
    (hP : tailsInDisk Pt = true) (hz : ∀ t ∈ Pt, t.zr ≠ 0 ∨ t.zi ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (resFieldGen (gRes P) (trialSeqS Pc Pt)) (resDeriv Pc Pt (53 / 58) x) x := by
  rw [hρ]; exact resFieldGen_hasDerivAt _ hP hz hx

/-! ### 3. The terminal consumer -/

/-- The four-piece extension: the endpoint bound and the four derivative caps give the cap on the
whole extension interval. -/
theorem extension_cap {R R' : ℝ → ℝ}
    (hcont : ContinuousOn R (Icc (98749 / 1000000) (401 / 2500)))
    (hderiv : ∀ x ∈ Ioo (98749 / 1000000 : ℝ) (401 / 2500), HasDerivAt R (R' x) x)
    (h1 : ∀ x ∈ Ioo (98749 / 1000000 : ℝ) (456647 / 4000000), R' x ≤ -134409 / 100000)
    (h2 : ∀ x ∈ Ioo (456647 / 4000000 : ℝ) (259149 / 2000000), R' x ≤ -184553 / 100000)
    (h3 : ∀ x ∈ Ioo (259149 / 2000000 : ℝ) (579949 / 4000000), R' x ≤ -174970 / 100000)
    (h4 : ∀ x ∈ Ioo (579949 / 4000000 : ℝ) (401 / 2500), R' x ≤ -164062 / 100000)
    (hend : R (98749 / 1000000) ≤ -8830153 / 100000000) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500), R x ≤ -315531 / 5000000 := by
  have hanti : AntitoneOn R (Icc (98749 / 1000000 : ℝ) (401 / 2500)) := by
    have hsub : ∀ a b : ℝ, 98749 / 1000000 ≤ a → b ≤ 401 / 2500 →
        (∀ x ∈ Ioo a b, R' x ≤ 0) → AntitoneOn R (Icc a b) := by
      intro a b ha hb hneg
      refine antitoneOn_piece (hcont.mono (Icc_subset_Icc ha hb)) (fun x hx => hderiv x ?_) hneg
      exact ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
    have p1 := hsub (98749 / 1000000) (456647 / 4000000) le_rfl (by norm_num)
      (fun x hx => (h1 x hx).trans (by norm_num))
    have p2 := hsub (456647 / 4000000) (259149 / 2000000) (by norm_num) (by norm_num)
      (fun x hx => (h2 x hx).trans (by norm_num))
    have p3 := hsub (259149 / 2000000) (579949 / 4000000) (by norm_num) (by norm_num)
      (fun x hx => (h3 x hx).trans (by norm_num))
    have p4 := hsub (579949 / 4000000) (401 / 2500) (by norm_num) le_rfl
      (fun x hx => (h4 x hx).trans (by norm_num))
    exact antitoneOn_glue (by norm_num) (by norm_num)
      (antitoneOn_glue (by norm_num) (by norm_num)
        (antitoneOn_glue (by norm_num) (by norm_num) p1 p2) p3) p4
  intro x hx
  have h := hanti ⟨le_rfl, by norm_num⟩ hx hx.1
  linarith only [h, hend]

/-- **Terminal consumer.**  This has exactly the type of `residual_sup` in
`Analytic.secondTrial_of_fields` / `secondEnd_of_fields` for `u = trialSeqS Pc Pt`, with
`G ⊆ {x ≤ -19501/100000} ∪ {98749/1000000 ≤ x}` (e.g. `G58`). -/
theorem residual_sup_unsigned {P : Parameters} {Pc : List ℤ} {Pt : List TailQ} {G : ℝ → Prop}
    {residual : ℝ} (hρ : gRes P = 53 / 58)
    (hdisk : tailsInDisk Pt = true) (hz : ∀ t ∈ Pt, t.zr ≠ 0 ∨ t.zi ≠ 0)
    (hG : ∀ x, G x → x ≤ -19501 / 100000 ∨ (98749 / 1000000 : ℝ) ≤ x)
    (hret : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
      resFieldGen (gRes P) (trialSeqS Pc Pt) x ≤ residual)
    (hres : (-315531 / 5000000 : ℝ) ≤ residual)
    (hend : resFieldGen (gRes P) (trialSeqS Pc Pt) (98749 / 1000000) ≤ -8830153 / 100000000)
    (h1 : ∀ x ∈ Ioo (98749 / 1000000 : ℝ) (456647 / 4000000),
      resDeriv Pc Pt (53 / 58) x ≤ -134409 / 100000)
    (h2 : ∀ x ∈ Ioo (456647 / 4000000 : ℝ) (259149 / 2000000),
      resDeriv Pc Pt (53 / 58) x ≤ -184553 / 100000)
    (h3 : ∀ x ∈ Ioo (259149 / 2000000 : ℝ) (579949 / 4000000),
      resDeriv Pc Pt (53 / 58) x ≤ -174970 / 100000)
    (h4 : ∀ x ∈ Ioo (579949 / 4000000 : ℝ) (401 / 2500),
      resDeriv Pc Pt (53 / 58) x ≤ -164062 / 100000) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) (trialSeqS Pc Pt) x ≤ residual := by
  have hext := extension_cap (R := resFieldGen (gRes P) (trialSeqS Pc Pt))
    (R' := resDeriv Pc Pt (53 / 58))
    ((resFieldGen_continuousOn _ hdisk).mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (fun x hx => resFieldGen_gRes_hasDerivAt hρ hdisk hz
      ⟨by linarith only [hx.1], by linarith only [hx.2]⟩)
    h1 h2 h3 h4 hend
  intro x hx hGx
  rcases le_or_gt (401 / 2500 : ℝ) |x| with hab | hab
  · exact hret x hx hab
  · rcases hG x hGx with hneg | hpos
    · exfalso
      have : -x ≤ |x| := neg_le_abs x
      linarith only [hneg, hab, this]
    · exact (hext x ⟨hpos, by
        have : x ≤ |x| := le_abs_self x
        linarith only [hab, this]⟩).trans hres

end
end CatalanMeasure.GenD.Signed.RouteI.UnsignedExtension

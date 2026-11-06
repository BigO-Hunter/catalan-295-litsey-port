module

public import CatalanMeasure.GenD.Signed.Count.NullityConstructor

public import CatalanMeasure.GenD.Uniform.BaselineBank.GlueMZH.Win
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Signed.DecayOfData

@[expose] public section
set_option Elab.async false

/-!
# Count layer: from the count `NullityLB` to `data295.D_growth` and `data295.eta_le`

Trace (terminal consumer `RouteI.catalan_irrationalityMeasure_295`):

* `hcontent` : `log (canonicalNormalizer … lb 79 _).D N ≤ (price + ε) N²` with
  `price = gDg gain = 24733/4 + (2673/8) log 2 - gain` is exactly the conclusion of
  `Ledger3.growth_of_families` for the family list `lbC :: fams13` and the selected disjoint
  window list `ws` (`growth_count`).
* each count window `cw a b c0 c1` is certified against the constructed `countLB` by
  `wincert_count` (both `WinCert` clauses: the ceiling bound, and `116 N ≤ safeOddLoss` for
  `b ≤ 59/2` from `wincert_cw`); retained W13 windows keep their own certificates.
* `hgain` : `eta295 < 58² (T296 - log 2 / 2) - gDg gain` once `gain ≥ 220607/10000`
  (`eta295_lt_of_gain`).
-/

namespace CatalanMeasure.GenD.Signed.Count.WinCertGlue
open CatalanMeasure.Parametric OAI.InternalCatalan Filter CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.LedgerW
  CatalanMeasure.GenD.Uniform.Bank540.Ledger CatalanMeasure.GenD.Uniform.Bank540.Ledger3
  CatalanMeasure.GenD.Uniform.Bank540.Ledger4
  CatalanMeasure.GenD.Signed.Count.NullityConstructor D58
noncomputable section

/-- Both `WinCert` clauses for an affine count window, from the constructed `countLB`. -/
theorem wincert_count (ws : List CountPiece) (N0 : ℕ) hpiece (a b c0 c1 : ℝ)
    (hmem : (⟨a, b, c0, c1⟩ : CountPiece) ∈ ws)
    {na da nb db : ℕ} {A B : ℤ} {d : ℕ}
    (hd : 0 < d) (hda : 0 < da) (hdb : 0 < db) (ha : a * da = na) (hb : b * db = nb)
    (hc0 : c0 * d = A) (hc1 : c1 * d = B) (hb59 : 2 * nb ≤ 59 * db) :
    WinCert (countLB design ws N0 hpiece) (cw a b c0 c1) := by
  refine wincert_cw (countLB design ws N0 hpiece) hd hda hdb ha hb hc0 hc1 hb59
    (N0 := N0) ?_
  intro N p hN hp h1 h2
  have hda' : (0 : ℝ) < da := by exact_mod_cast hda
  have hdb' : (0 : ℝ) < db := by exact_mod_cast hdb
  have h1r : (na : ℝ) * N < da * p := by exact_mod_cast h1
  have h2r : (db : ℝ) * p ≤ nb * N := by exact_mod_cast h2
  rw [← ha] at h1r
  rw [← hb] at h2r
  have h1' : a * N < p := by
    have : (da : ℝ) * (a * N) < da * p := by nlinarith [h1r]
    exact lt_of_mul_lt_mul_left this hda'.le
  have h2' : (p : ℝ) ≤ b * N := by
    have : (db : ℝ) * p ≤ db * (b * N) := by nlinarith [h2r]
    exact le_of_mul_le_mul_left this hdb'
  have hk := countLB_kap_ge design ws N0 hpiece hmem hN h1' h2'
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hAr : (A : ℝ) = c0 * d := hc0.symm
  have hBr : (B : ℝ) = c1 * d := hc1.symm
  have : ((A * (N : ℤ) + B * (p : ℤ) : ℤ) : ℝ) ≤
      (((d : ℤ) * (((countLB design ws N0 hpiece).kap N p : ℕ) + 2 : ℤ) : ℤ) : ℝ) := by
    push_cast
    rw [hAr, hBr]
    nlinarith [hk, hdr]
  exact_mod_cast this

/-- **Denominator growth** (`data295.D_growth` with `price = gDg gain`). -/
theorem growth_count (lbC : NullityLB design) (ws : List KapWindow) (gain : ℝ)
    (hsum : (ws.map (KapWindow.area 58)).sum = gain)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78)
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (fams0 : List (NullityLB design))
    (hcert : ∀ w ∈ ws, WinCert lbC w ∨ ∃ lb ∈ fams0, WinCert lb w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (((canonicalNormalizer design D58.Odd.design_admissible
        (famLB (lbC :: fams0)) 79
        (by rw [D58.Odd.design_H]; norm_num)).D N : ℕ) : ℝ) ≤
        (gDg gain + ε) * (N : ℝ) ^ 2 := by
  have h := growth_of_families (lbC :: fams0) ws gain hsum hpos hord hrec
    (fun w hw => by
      rcases hcert w hw with h | ⟨lb, hlb, h⟩
      · exact ⟨lbC, List.mem_cons_self, h⟩
      · exact ⟨lb, List.mem_cons_of_mem _ hlb, h⟩) hε
  unfold gDg
  exact h


/-- The exact `hcontent` of `RouteI.catalan_irrationalityMeasure_295` for
`lb := famLB (lbC :: fams0)` (the design `⟨58,9,3,5,3⟩` is `dc58.toParameters` by `rfl`). -/
theorem hcontent_terminal (lbC : NullityLB design) (ws : List KapWindow) (gain : ℝ)
    (hsum : (ws.map (KapWindow.area 58)).sum = gain)
    (hpos : ∀ w ∈ ws, 0 < w.a ∧ w.a < w.b ∧ w.b ≤ 78)
    (hord : ws.Pairwise (fun s t => s.b ≤ t.a))
    (hrec : ∀ w ∈ ws, w.b ≤ 1 ∨ 2 ≤ w.a)
    (fams0 : List (NullityLB design))
    (hcert : ∀ w ∈ ws, WinCert lbC w ∨ ∃ lb ∈ fams0, WinCert lb w) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      Real.log ((canonicalNormalizer Signed.dc58.toParameters Signed.dc58.admissible
        (famLB (lbC :: fams0)) 79 Signed.RouteI.dc58_normalizer_cut).D N : ℝ) ≤
        (gDg gain + ε) * (N : ℝ) ^ 2 :=
  fun _ hε => growth_count lbC ws gain hsum hpos hord hrec fams0 hcert hε

/-- **`eta_le`** from the gain: `eta295 < tΔ - gD`. -/
theorem eta295_lt_of_gain {gain : ℝ} (h : (220607 / 10000 : ℝ) ≤ gain) :
    RouteI.eta295 < 58 ^ 2 * (RouteI.T296 - Real.log 2 / 2) - gDg gain := by
  obtain ⟨hl, hh⟩ := D58.log2_bounds
  unfold gDg RouteI.eta295 RouteI.T296 RouteI.content295 RouteI.shift296
  norm_num [K590.target, D58.lo, D58.hi] at hl hh h ⊢
  linarith

end
end CatalanMeasure.GenD.Signed.Count.WinCertGlue
#print axioms CatalanMeasure.GenD.Signed.Count.WinCertGlue.wincert_count
#print axioms CatalanMeasure.GenD.Signed.Count.WinCertGlue.growth_count
#print axioms CatalanMeasure.GenD.Signed.Count.WinCertGlue.eta295_lt_of_gain
#print axioms CatalanMeasure.GenD.Signed.Count.WinCertGlue.hcontent_terminal

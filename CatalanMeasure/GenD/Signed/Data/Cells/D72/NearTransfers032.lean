module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers032
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers032
open D72.LogTransfer
def d2Transfer256Lo : ℚ := (d2LitsNearTransfers032.q2 (1327746417) 1 (-31))
def d2Transfer256Hi : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer256Cap : ℚ := (d2LitsNearTransfers032.q2 (576140099418486577219) 1 (-75))
def d2Transfer256C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (-5))
def d2Transfer256S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer256Arithmetic : weightedUpper d2Transfer256C0 d2Log133Lo d2Log133Hi ≤ d2Transfer256Cap := by decide +kernel
theorem d2Transfer256Bound : ∀ x ∈ Set.Icc ((d2Transfer256Lo:ℚ):ℝ) ((d2Transfer256Hi:ℚ):ℝ), ((d2Transfer256C0:ℚ):ℝ)*Real.log |x-((d2Transfer256S0:ℚ):ℝ)| ≤ ((d2Transfer256Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer256S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer256S0,d2Transfer256Lo,d2Transfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer256C0 then |x-((d2Transfer256S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2Transfer256S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer256S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer256S0,d2Transfer256Lo,d2Transfer256Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer256C0,d2Log133Q,d2Transfer256S0,d2Transfer256Lo,d2Transfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer256C0 d2Transfer256S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have har : (((weightedUpper d2Transfer256C0 d2Log133Lo d2Log133Hi:ℚ):ℝ)) ≤ ((d2Transfer256Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer256Arithmetic
  linarith
#print axioms d2Transfer256Arithmetic
#print axioms d2Transfer256Bound
def d2Transfer257Lo : ℚ := (d2LitsNearTransfers032.q2 (1327746417) 1 (-31))
def d2Transfer257Hi : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer257Cap : ℚ := (d2LitsNearTransfers032.q2 (1087541265740096182339) 1 (-75))
def d2Transfer257C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 11 (-5))
def d2Transfer257S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
def d2Transfer257C1 : ℚ := (d2LitsNearTransfers032.q2 (-5) 11 (-4))
def d2Transfer257S1 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer257Arithmetic : weightedUpper d2Transfer257C0 d2Log133Lo d2Log133Hi + weightedUpper d2Transfer257C1 d2Log41Lo d2Log41Hi ≤ d2Transfer257Cap := by decide +kernel
theorem d2Transfer257Bound : ∀ x ∈ Set.Icc ((d2Transfer257Lo:ℚ):ℝ) ((d2Transfer257Hi:ℚ):ℝ), ((d2Transfer257C0:ℚ):ℝ)*Real.log |x-((d2Transfer257S0:ℚ):ℝ)| + ((d2Transfer257C1:ℚ):ℝ)*Real.log |x-((d2Transfer257S1:ℚ):ℝ)| ≤ ((d2Transfer257Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer257S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257S0,d2Transfer257Lo,d2Transfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer257C0 then |x-((d2Transfer257S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2Transfer257S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer257S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257S0,d2Transfer257Lo,d2Transfer257Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257C0,d2Log133Q,d2Transfer257S0,d2Transfer257Lo,d2Transfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer257C0 d2Transfer257S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have hn1 : x-((d2Transfer257S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257S1,d2Transfer257Lo,d2Transfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer257C1 then |x-((d2Transfer257S1:ℚ):ℝ)| ≤ ((d2Log41Q:ℚ):ℝ) else ((d2Log41Q:ℚ):ℝ) ≤ |x-((d2Transfer257S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer257S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257S1,d2Transfer257Lo,d2Transfer257Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer257C1,d2Log41Q,d2Transfer257S1,d2Transfer257Lo,d2Transfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer257C1 d2Transfer257S1 d2Log41Q d2Log41Lo d2Log41Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log41Bounds
  have har : (((weightedUpper d2Transfer257C0 d2Log133Lo d2Log133Hi:ℚ):ℝ) + ((weightedUpper d2Transfer257C1 d2Log41Lo d2Log41Hi:ℚ):ℝ)) ≤ ((d2Transfer257Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer257Arithmetic
  linarith
#print axioms d2Transfer257Arithmetic
#print axioms d2Transfer257Bound
def d2Transfer258Lo : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer258Hi : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer258Cap : ℚ := (d2LitsNearTransfers032.q2 (7950334446886927103) 1 (-72))
def d2Transfer258C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 25 (-4))
def d2Transfer258S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer258Arithmetic : weightedUpper d2Transfer258C0 d2Log134Lo d2Log134Hi ≤ d2Transfer258Cap := by decide +kernel
theorem d2Transfer258Bound : ∀ x ∈ Set.Icc ((d2Transfer258Lo:ℚ):ℝ) ((d2Transfer258Hi:ℚ):ℝ), ((d2Transfer258C0:ℚ):ℝ)*Real.log |x-((d2Transfer258S0:ℚ):ℝ)| ≤ ((d2Transfer258Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer258S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer258S0,d2Transfer258Lo,d2Transfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer258C0 then |x-((d2Transfer258S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2Transfer258S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer258S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer258S0,d2Transfer258Lo,d2Transfer258Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer258C0,d2Log134Q,d2Transfer258S0,d2Transfer258Lo,d2Transfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer258C0 d2Transfer258S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have har : (((weightedUpper d2Transfer258C0 d2Log134Lo d2Log134Hi:ℚ):ℝ)) ≤ ((d2Transfer258Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer258Arithmetic
  linarith
#print axioms d2Transfer258Arithmetic
#print axioms d2Transfer258Bound
def d2Transfer259Lo : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer259Hi : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer259Cap : ℚ := (d2LitsNearTransfers032.q2 (12834319480620268287) 1 (-72))
def d2Transfer259C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 275 (-4))
def d2Transfer259S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
def d2Transfer259C1 : ℚ := (d2LitsNearTransfers032.q2 (-1) 55 (-3))
def d2Transfer259S1 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer259Arithmetic : weightedUpper d2Transfer259C0 d2Log134Lo d2Log134Hi + weightedUpper d2Transfer259C1 d2Log40Lo d2Log40Hi ≤ d2Transfer259Cap := by decide +kernel
theorem d2Transfer259Bound : ∀ x ∈ Set.Icc ((d2Transfer259Lo:ℚ):ℝ) ((d2Transfer259Hi:ℚ):ℝ), ((d2Transfer259C0:ℚ):ℝ)*Real.log |x-((d2Transfer259S0:ℚ):ℝ)| + ((d2Transfer259C1:ℚ):ℝ)*Real.log |x-((d2Transfer259S1:ℚ):ℝ)| ≤ ((d2Transfer259Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer259S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259S0,d2Transfer259Lo,d2Transfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer259C0 then |x-((d2Transfer259S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2Transfer259S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer259S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259S0,d2Transfer259Lo,d2Transfer259Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259C0,d2Log134Q,d2Transfer259S0,d2Transfer259Lo,d2Transfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer259C0 d2Transfer259S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have hn1 : x-((d2Transfer259S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259S1,d2Transfer259Lo,d2Transfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer259C1 then |x-((d2Transfer259S1:ℚ):ℝ)| ≤ ((d2Log40Q:ℚ):ℝ) else ((d2Log40Q:ℚ):ℝ) ≤ |x-((d2Transfer259S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer259S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259S1,d2Transfer259Lo,d2Transfer259Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer259C1,d2Log40Q,d2Transfer259S1,d2Transfer259Lo,d2Transfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer259C1 d2Transfer259S1 d2Log40Q d2Log40Lo d2Log40Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log40Bounds
  have har : (((weightedUpper d2Transfer259C0 d2Log134Lo d2Log134Hi:ℚ):ℝ) + ((weightedUpper d2Transfer259C1 d2Log40Lo d2Log40Hi:ℚ):ℝ)) ≤ ((d2Transfer259Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer259Arithmetic
  linarith
#print axioms d2Transfer259Arithmetic
#print axioms d2Transfer259Bound
def d2Transfer260Lo : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer260Hi : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer260Cap : ℚ := (d2LitsNearTransfers032.q2 (72299405771334957823) 1 (-72))
def d2Transfer260C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (-5))
def d2Transfer260S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer260Arithmetic : weightedUpper d2Transfer260C0 d2Log134Lo d2Log134Hi ≤ d2Transfer260Cap := by decide +kernel
theorem d2Transfer260Bound : ∀ x ∈ Set.Icc ((d2Transfer260Lo:ℚ):ℝ) ((d2Transfer260Hi:ℚ):ℝ), ((d2Transfer260C0:ℚ):ℝ)*Real.log |x-((d2Transfer260S0:ℚ):ℝ)| ≤ ((d2Transfer260Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer260S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer260S0,d2Transfer260Lo,d2Transfer260Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer260C0 then |x-((d2Transfer260S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2Transfer260S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer260S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer260S0,d2Transfer260Lo,d2Transfer260Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer260C0,d2Log134Q,d2Transfer260S0,d2Transfer260Lo,d2Transfer260Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer260C0 d2Transfer260S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have har : (((weightedUpper d2Transfer260C0 d2Log134Lo d2Log134Hi:ℚ):ℝ)) ≤ ((d2Transfer260Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer260Arithmetic
  linarith
#print axioms d2Transfer260Arithmetic
#print axioms d2Transfer260Bound
def d2Transfer261Lo : ℚ := (d2LitsNearTransfers032.q2 (664712069) 1 (-30))
def d2Transfer261Hi : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer261Cap : ℚ := (d2LitsNearTransfers032.q2 (136224551561536158463) 1 (-72))
def d2Transfer261C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 11 (-5))
def d2Transfer261S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
def d2Transfer261C1 : ℚ := (d2LitsNearTransfers032.q2 (-5) 11 (-4))
def d2Transfer261S1 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer261Arithmetic : weightedUpper d2Transfer261C0 d2Log134Lo d2Log134Hi + weightedUpper d2Transfer261C1 d2Log40Lo d2Log40Hi ≤ d2Transfer261Cap := by decide +kernel
theorem d2Transfer261Bound : ∀ x ∈ Set.Icc ((d2Transfer261Lo:ℚ):ℝ) ((d2Transfer261Hi:ℚ):ℝ), ((d2Transfer261C0:ℚ):ℝ)*Real.log |x-((d2Transfer261S0:ℚ):ℝ)| + ((d2Transfer261C1:ℚ):ℝ)*Real.log |x-((d2Transfer261S1:ℚ):ℝ)| ≤ ((d2Transfer261Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer261S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261S0,d2Transfer261Lo,d2Transfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer261C0 then |x-((d2Transfer261S0:ℚ):ℝ)| ≤ ((d2Log134Q:ℚ):ℝ) else ((d2Log134Q:ℚ):ℝ) ≤ |x-((d2Transfer261S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer261S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261S0,d2Transfer261Lo,d2Transfer261Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261C0,d2Log134Q,d2Transfer261S0,d2Transfer261Lo,d2Transfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer261C0 d2Transfer261S0 d2Log134Q d2Log134Lo d2Log134Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log134Bounds
  have hn1 : x-((d2Transfer261S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261S1,d2Transfer261Lo,d2Transfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer261C1 then |x-((d2Transfer261S1:ℚ):ℝ)| ≤ ((d2Log40Q:ℚ):ℝ) else ((d2Log40Q:ℚ):ℝ) ≤ |x-((d2Transfer261S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer261S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261S1,d2Transfer261Lo,d2Transfer261Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer261C1,d2Log40Q,d2Transfer261S1,d2Transfer261Lo,d2Transfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer261C1 d2Transfer261S1 d2Log40Q d2Log40Lo d2Log40Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log40Bounds
  have har : (((weightedUpper d2Transfer261C0 d2Log134Lo d2Log134Hi:ℚ):ℝ) + ((weightedUpper d2Transfer261C1 d2Log40Lo d2Log40Hi:ℚ):ℝ)) ≤ ((d2Transfer261Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer261Arithmetic
  linarith
#print axioms d2Transfer261Arithmetic
#print axioms d2Transfer261Bound
def d2Transfer262Lo : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer262Hi : ℚ := (d2LitsNearTransfers032.q2 (333194895) 1 (-29))
def d2Transfer262Cap : ℚ := (d2LitsNearTransfers032.q2 (2107594563250375816115) 1 (-80))
def d2Transfer262C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 25 (-4))
def d2Transfer262S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer262Arithmetic : weightedUpper d2Transfer262C0 d2Log135Lo d2Log135Hi ≤ d2Transfer262Cap := by decide +kernel
theorem d2Transfer262Bound : ∀ x ∈ Set.Icc ((d2Transfer262Lo:ℚ):ℝ) ((d2Transfer262Hi:ℚ):ℝ), ((d2Transfer262C0:ℚ):ℝ)*Real.log |x-((d2Transfer262S0:ℚ):ℝ)| ≤ ((d2Transfer262Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer262S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer262S0,d2Transfer262Lo,d2Transfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer262C0 then |x-((d2Transfer262S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer262S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer262S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer262S0,d2Transfer262Lo,d2Transfer262Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer262C0,d2Log135Q,d2Transfer262S0,d2Transfer262Lo,d2Transfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer262C0 d2Transfer262S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2Transfer262C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2Transfer262Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer262Arithmetic
  linarith
#print axioms d2Transfer262Arithmetic
#print axioms d2Transfer262Bound
def d2Transfer263Lo : ℚ := (d2LitsNearTransfers032.q2 (1331101859) 1 (-31))
def d2Transfer263Hi : ℚ := (d2LitsNearTransfers032.q2 (333194895) 1 (-29))
def d2Transfer263Cap : ℚ := (d2LitsNearTransfers032.q2 (3357894731886111159219) 1 (-80))
def d2Transfer263C0 : ℚ := (d2LitsNearTransfers032.q2 (1) 275 (-4))
def d2Transfer263S0 : ℚ := (d2LitsNearTransfers032.q2 (-1) 1 (0))
def d2Transfer263C1 : ℚ := (d2LitsNearTransfers032.q2 (-1) 55 (-3))
def d2Transfer263S1 : ℚ := (d2LitsNearTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer263Arithmetic : weightedUpper d2Transfer263C0 d2Log135Lo d2Log135Hi + weightedUpper d2Transfer263C1 d2Log39Lo d2Log39Hi ≤ d2Transfer263Cap := by decide +kernel
theorem d2Transfer263Bound : ∀ x ∈ Set.Icc ((d2Transfer263Lo:ℚ):ℝ) ((d2Transfer263Hi:ℚ):ℝ), ((d2Transfer263C0:ℚ):ℝ)*Real.log |x-((d2Transfer263S0:ℚ):ℝ)| + ((d2Transfer263C1:ℚ):ℝ)*Real.log |x-((d2Transfer263S1:ℚ):ℝ)| ≤ ((d2Transfer263Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer263S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263S0,d2Transfer263Lo,d2Transfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer263C0 then |x-((d2Transfer263S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer263S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer263S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263S0,d2Transfer263Lo,d2Transfer263Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263C0,d2Log135Q,d2Transfer263S0,d2Transfer263Lo,d2Transfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer263C0 d2Transfer263S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2Transfer263S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263S1,d2Transfer263Lo,d2Transfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer263C1 then |x-((d2Transfer263S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2Transfer263S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer263S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263S1,d2Transfer263Lo,d2Transfer263Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers032.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer263C1,d2Log39Q,d2Transfer263S1,d2Transfer263Lo,d2Transfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer263C1 d2Transfer263S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2Transfer263C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2Transfer263C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2Transfer263Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer263Arithmetic
  linarith
#print axioms d2Transfer263Arithmetic
#print axioms d2Transfer263Bound
end CatalanMeasure.GenD.Signed.Data.Cells

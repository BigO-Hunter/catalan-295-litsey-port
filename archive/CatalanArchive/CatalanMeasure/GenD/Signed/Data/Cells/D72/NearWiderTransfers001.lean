module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers001
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers001
open D72.LogTransfer
def d2WiderTransfer8Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (3334455) 1 (-24))
def d2WiderTransfer8Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (313261) 1 (-20))
def d2WiderTransfer8Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (648894057) 1 (-39))
def d2WiderTransfer8C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 25 (-4))
def d2WiderTransfer8S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer8Arithmetic : weightedUpper d2WiderTransfer8C0 d2Log113Lo d2Log113Hi ≤ d2WiderTransfer8Cap := by decide +kernel
theorem d2WiderTransfer8Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer8Lo:ℚ):ℝ) ((d2WiderTransfer8Hi:ℚ):ℝ), ((d2WiderTransfer8C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer8S0:ℚ):ℝ)| ≤ ((d2WiderTransfer8Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer8S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer8S0,d2WiderTransfer8Lo,d2WiderTransfer8Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer8C0 then |x-((d2WiderTransfer8S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer8S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer8S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer8S0,d2WiderTransfer8Lo,d2WiderTransfer8Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer8C0,d2Log113Q,d2WiderTransfer8S0,d2WiderTransfer8Lo,d2WiderTransfer8Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer8C0 d2WiderTransfer8S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2WiderTransfer8C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer8Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer8Arithmetic
  linarith
#print axioms d2WiderTransfer8Arithmetic
#print axioms d2WiderTransfer8Bound
def d2WiderTransfer9Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (3334455) 1 (-24))
def d2WiderTransfer9Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (313261) 1 (-20))
def d2WiderTransfer9Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (2432512853) 1 (-40))
def d2WiderTransfer9C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 275 (-4))
def d2WiderTransfer9S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
def d2WiderTransfer9C1 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 55 (-3))
def d2WiderTransfer9S1 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer9Arithmetic : weightedUpper d2WiderTransfer9C0 d2Log113Lo d2Log113Hi + weightedUpper d2WiderTransfer9C1 d2Log61Lo d2Log61Hi ≤ d2WiderTransfer9Cap := by decide +kernel
theorem d2WiderTransfer9Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer9Lo:ℚ):ℝ) ((d2WiderTransfer9Hi:ℚ):ℝ), ((d2WiderTransfer9C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer9S0:ℚ):ℝ)| + ((d2WiderTransfer9C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer9S1:ℚ):ℝ)| ≤ ((d2WiderTransfer9Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer9S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9S0,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer9C0 then |x-((d2WiderTransfer9S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer9S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer9S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9S0,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9C0,d2Log113Q,d2WiderTransfer9S0,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer9C0 d2WiderTransfer9S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2WiderTransfer9S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9S1,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer9C1 then |x-((d2WiderTransfer9S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer9S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer9S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9S1,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer9C1,d2Log61Q,d2WiderTransfer9S1,d2WiderTransfer9Lo,d2WiderTransfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer9C1 d2WiderTransfer9S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2WiderTransfer9C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer9C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer9Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer9Arithmetic
  linarith
#print axioms d2WiderTransfer9Arithmetic
#print axioms d2WiderTransfer9Bound
def d2WiderTransfer10Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (313261) 1 (-20))
def d2WiderTransfer10Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (6689897) 1 (-24))
def d2WiderTransfer10Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (648894057) 1 (-39))
def d2WiderTransfer10C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 25 (-4))
def d2WiderTransfer10S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer10Arithmetic : weightedUpper d2WiderTransfer10C0 d2Log117Lo d2Log117Hi ≤ d2WiderTransfer10Cap := by decide +kernel
theorem d2WiderTransfer10Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer10Lo:ℚ):ℝ) ((d2WiderTransfer10Hi:ℚ):ℝ), ((d2WiderTransfer10C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer10S0:ℚ):ℝ)| ≤ ((d2WiderTransfer10Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer10S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer10S0,d2WiderTransfer10Lo,d2WiderTransfer10Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer10C0 then |x-((d2WiderTransfer10S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer10S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer10S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer10S0,d2WiderTransfer10Lo,d2WiderTransfer10Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer10C0,d2Log117Q,d2WiderTransfer10S0,d2WiderTransfer10Lo,d2WiderTransfer10Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer10C0 d2WiderTransfer10S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2WiderTransfer10C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer10Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer10Arithmetic
  linarith
#print axioms d2WiderTransfer10Arithmetic
#print axioms d2WiderTransfer10Bound
def d2WiderTransfer11Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (313261) 1 (-20))
def d2WiderTransfer11Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (6689897) 1 (-24))
def d2WiderTransfer11Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (2432512853) 1 (-40))
def d2WiderTransfer11C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 275 (-4))
def d2WiderTransfer11S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
def d2WiderTransfer11C1 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 55 (-3))
def d2WiderTransfer11S1 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer11Arithmetic : weightedUpper d2WiderTransfer11C0 d2Log117Lo d2Log117Hi + weightedUpper d2WiderTransfer11C1 d2Log57Lo d2Log57Hi ≤ d2WiderTransfer11Cap := by decide +kernel
theorem d2WiderTransfer11Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer11Lo:ℚ):ℝ) ((d2WiderTransfer11Hi:ℚ):ℝ), ((d2WiderTransfer11C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer11S0:ℚ):ℝ)| + ((d2WiderTransfer11C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer11S1:ℚ):ℝ)| ≤ ((d2WiderTransfer11Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer11S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11S0,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer11C0 then |x-((d2WiderTransfer11S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer11S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer11S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11S0,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11C0,d2Log117Q,d2WiderTransfer11S0,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer11C0 d2WiderTransfer11S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2WiderTransfer11S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11S1,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer11C1 then |x-((d2WiderTransfer11S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer11S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer11S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11S1,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer11C1,d2Log57Q,d2WiderTransfer11S1,d2WiderTransfer11Lo,d2WiderTransfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer11C1 d2WiderTransfer11S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2WiderTransfer11C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer11C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer11Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer11Arithmetic
  linarith
#print axioms d2WiderTransfer11Arithmetic
#print axioms d2WiderTransfer11Bound
def d2WiderTransfer12Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (6689897) 1 (-24))
def d2WiderTransfer12Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (4183809) 1 (-23))
def d2WiderTransfer12Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (648894057) 1 (-39))
def d2WiderTransfer12C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 25 (-4))
def d2WiderTransfer12S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer12Arithmetic : weightedUpper d2WiderTransfer12C0 d2Log120Lo d2Log120Hi ≤ d2WiderTransfer12Cap := by decide +kernel
theorem d2WiderTransfer12Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer12Lo:ℚ):ℝ) ((d2WiderTransfer12Hi:ℚ):ℝ), ((d2WiderTransfer12C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer12S0:ℚ):ℝ)| ≤ ((d2WiderTransfer12Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer12S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer12S0,d2WiderTransfer12Lo,d2WiderTransfer12Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer12C0 then |x-((d2WiderTransfer12S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer12S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer12S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer12S0,d2WiderTransfer12Lo,d2WiderTransfer12Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer12C0,d2Log120Q,d2WiderTransfer12S0,d2WiderTransfer12Lo,d2WiderTransfer12Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer12C0 d2WiderTransfer12S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2WiderTransfer12C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer12Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer12Arithmetic
  linarith
#print axioms d2WiderTransfer12Arithmetic
#print axioms d2WiderTransfer12Bound
def d2WiderTransfer13Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (6689897) 1 (-24))
def d2WiderTransfer13Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (4183809) 1 (-23))
def d2WiderTransfer13Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (2432512853) 1 (-40))
def d2WiderTransfer13C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 275 (-4))
def d2WiderTransfer13S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
def d2WiderTransfer13C1 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 55 (-3))
def d2WiderTransfer13S1 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer13Arithmetic : weightedUpper d2WiderTransfer13C0 d2Log120Lo d2Log120Hi + weightedUpper d2WiderTransfer13C1 d2Log54Lo d2Log54Hi ≤ d2WiderTransfer13Cap := by decide +kernel
theorem d2WiderTransfer13Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer13Lo:ℚ):ℝ) ((d2WiderTransfer13Hi:ℚ):ℝ), ((d2WiderTransfer13C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer13S0:ℚ):ℝ)| + ((d2WiderTransfer13C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer13S1:ℚ):ℝ)| ≤ ((d2WiderTransfer13Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer13S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13S0,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer13C0 then |x-((d2WiderTransfer13S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer13S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer13S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13S0,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13C0,d2Log120Q,d2WiderTransfer13S0,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer13C0 d2WiderTransfer13S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2WiderTransfer13S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13S1,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer13C1 then |x-((d2WiderTransfer13S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer13S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer13S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13S1,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer13C1,d2Log54Q,d2WiderTransfer13S1,d2WiderTransfer13Lo,d2WiderTransfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer13C1 d2WiderTransfer13S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2WiderTransfer13C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer13C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer13Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer13Arithmetic
  linarith
#print axioms d2WiderTransfer13Arithmetic
#print axioms d2WiderTransfer13Bound
def d2WiderTransfer14Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (4183809) 1 (-23))
def d2WiderTransfer14Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (18412957) 1 (-25))
def d2WiderTransfer14Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (648894057) 1 (-39))
def d2WiderTransfer14C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 25 (-4))
def d2WiderTransfer14S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer14Arithmetic : weightedUpper d2WiderTransfer14C0 d2Log121Lo d2Log121Hi ≤ d2WiderTransfer14Cap := by decide +kernel
theorem d2WiderTransfer14Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer14Lo:ℚ):ℝ) ((d2WiderTransfer14Hi:ℚ):ℝ), ((d2WiderTransfer14C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer14S0:ℚ):ℝ)| ≤ ((d2WiderTransfer14Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer14S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer14S0,d2WiderTransfer14Lo,d2WiderTransfer14Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer14C0 then |x-((d2WiderTransfer14S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer14S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer14S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer14S0,d2WiderTransfer14Lo,d2WiderTransfer14Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer14C0,d2Log121Q,d2WiderTransfer14S0,d2WiderTransfer14Lo,d2WiderTransfer14Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer14C0 d2WiderTransfer14S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2WiderTransfer14C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer14Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer14Arithmetic
  linarith
#print axioms d2WiderTransfer14Arithmetic
#print axioms d2WiderTransfer14Bound
def d2WiderTransfer15Lo : ℚ := (d2LitsNearWiderTransfers001.q2 (4183809) 1 (-23))
def d2WiderTransfer15Hi : ℚ := (d2LitsNearWiderTransfers001.q2 (18412957) 1 (-25))
def d2WiderTransfer15Cap : ℚ := (d2LitsNearWiderTransfers001.q2 (2432512853) 1 (-40))
def d2WiderTransfer15C0 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 275 (-4))
def d2WiderTransfer15S0 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 1 (0))
def d2WiderTransfer15C1 : ℚ := (d2LitsNearWiderTransfers001.q2 (-1) 55 (-3))
def d2WiderTransfer15S1 : ℚ := (d2LitsNearWiderTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer15Arithmetic : weightedUpper d2WiderTransfer15C0 d2Log121Lo d2Log121Hi + weightedUpper d2WiderTransfer15C1 d2Log53Lo d2Log53Hi ≤ d2WiderTransfer15Cap := by decide +kernel
theorem d2WiderTransfer15Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer15Lo:ℚ):ℝ) ((d2WiderTransfer15Hi:ℚ):ℝ), ((d2WiderTransfer15C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer15S0:ℚ):ℝ)| + ((d2WiderTransfer15C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer15S1:ℚ):ℝ)| ≤ ((d2WiderTransfer15Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer15S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15S0,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer15C0 then |x-((d2WiderTransfer15S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer15S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer15S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15S0,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15C0,d2Log121Q,d2WiderTransfer15S0,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer15C0 d2WiderTransfer15S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2WiderTransfer15S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15S1,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer15C1 then |x-((d2WiderTransfer15S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer15S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer15S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15S1,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers001.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer15C1,d2Log53Q,d2WiderTransfer15S1,d2WiderTransfer15Lo,d2WiderTransfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer15C1 d2WiderTransfer15S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2WiderTransfer15C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer15C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer15Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer15Arithmetic
  linarith
#print axioms d2WiderTransfer15Arithmetic
#print axioms d2WiderTransfer15Bound
end CatalanMeasure.GenD.Signed.Data.Cells

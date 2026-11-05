module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers001
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers001
open D72.LogTransfer
def d2Transfer8Lo : ℚ := (d2LitsNearTransfers001.q2 (14931593) 1 (-27))
def d2Transfer8Hi : ℚ := (d2LitsNearTransfers001.q2 (31540907) 1 (-28))
def d2Transfer8Cap : ℚ := (d2LitsNearTransfers001.q2 (648894057) 1 (-39))
def d2Transfer8C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 25 (-4))
def d2Transfer8S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer8Arithmetic : weightedUpper d2Transfer8C0 d2Log94Lo d2Log94Hi ≤ d2Transfer8Cap := by decide +kernel
theorem d2Transfer8Bound : ∀ x ∈ Set.Icc ((d2Transfer8Lo:ℚ):ℝ) ((d2Transfer8Hi:ℚ):ℝ), ((d2Transfer8C0:ℚ):ℝ)*Real.log |x-((d2Transfer8S0:ℚ):ℝ)| ≤ ((d2Transfer8Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer8S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer8S0,d2Transfer8Lo,d2Transfer8Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer8C0 then |x-((d2Transfer8S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer8S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer8S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer8S0,d2Transfer8Lo,d2Transfer8Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer8C0,d2Log94Q,d2Transfer8S0,d2Transfer8Lo,d2Transfer8Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer8C0 d2Transfer8S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have har : (((weightedUpper d2Transfer8C0 d2Log94Lo d2Log94Hi:ℚ):ℝ)) ≤ ((d2Transfer8Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer8Arithmetic
  linarith
#print axioms d2Transfer8Arithmetic
#print axioms d2Transfer8Bound
def d2Transfer9Lo : ℚ := (d2LitsNearTransfers001.q2 (14931593) 1 (-27))
def d2Transfer9Hi : ℚ := (d2LitsNearTransfers001.q2 (31540907) 1 (-28))
def d2Transfer9Cap : ℚ := (d2LitsNearTransfers001.q2 (2432512853) 1 (-40))
def d2Transfer9C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 275 (-4))
def d2Transfer9S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
def d2Transfer9C1 : ℚ := (d2LitsNearTransfers001.q2 (-1) 55 (-3))
def d2Transfer9S1 : ℚ := (d2LitsNearTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer9Arithmetic : weightedUpper d2Transfer9C0 d2Log94Lo d2Log94Hi + weightedUpper d2Transfer9C1 d2Log80Lo d2Log80Hi ≤ d2Transfer9Cap := by decide +kernel
theorem d2Transfer9Bound : ∀ x ∈ Set.Icc ((d2Transfer9Lo:ℚ):ℝ) ((d2Transfer9Hi:ℚ):ℝ), ((d2Transfer9C0:ℚ):ℝ)*Real.log |x-((d2Transfer9S0:ℚ):ℝ)| + ((d2Transfer9C1:ℚ):ℝ)*Real.log |x-((d2Transfer9S1:ℚ):ℝ)| ≤ ((d2Transfer9Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer9S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9S0,d2Transfer9Lo,d2Transfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer9C0 then |x-((d2Transfer9S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer9S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer9S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9S0,d2Transfer9Lo,d2Transfer9Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9C0,d2Log94Q,d2Transfer9S0,d2Transfer9Lo,d2Transfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer9C0 d2Transfer9S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have hn1 : x-((d2Transfer9S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9S1,d2Transfer9Lo,d2Transfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer9C1 then |x-((d2Transfer9S1:ℚ):ℝ)| ≤ ((d2Log80Q:ℚ):ℝ) else ((d2Log80Q:ℚ):ℝ) ≤ |x-((d2Transfer9S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer9S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9S1,d2Transfer9Lo,d2Transfer9Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer9C1,d2Log80Q,d2Transfer9S1,d2Transfer9Lo,d2Transfer9Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer9C1 d2Transfer9S1 d2Log80Q d2Log80Lo d2Log80Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log80Bounds
  have har : (((weightedUpper d2Transfer9C0 d2Log94Lo d2Log94Hi:ℚ):ℝ) + ((weightedUpper d2Transfer9C1 d2Log80Lo d2Log80Hi:ℚ):ℝ)) ≤ ((d2Transfer9Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer9Arithmetic
  linarith
#print axioms d2Transfer9Arithmetic
#print axioms d2Transfer9Bound
def d2Transfer10Lo : ℚ := (d2LitsNearTransfers001.q2 (31540907) 1 (-28))
def d2Transfer10Hi : ℚ := (d2LitsNearTransfers001.q2 (8304657) 1 (-26))
def d2Transfer10Cap : ℚ := (d2LitsNearTransfers001.q2 (648894057) 1 (-39))
def d2Transfer10C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 25 (-4))
def d2Transfer10S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer10Arithmetic : weightedUpper d2Transfer10C0 d2Log95Lo d2Log95Hi ≤ d2Transfer10Cap := by decide +kernel
theorem d2Transfer10Bound : ∀ x ∈ Set.Icc ((d2Transfer10Lo:ℚ):ℝ) ((d2Transfer10Hi:ℚ):ℝ), ((d2Transfer10C0:ℚ):ℝ)*Real.log |x-((d2Transfer10S0:ℚ):ℝ)| ≤ ((d2Transfer10Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer10S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer10S0,d2Transfer10Lo,d2Transfer10Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer10C0 then |x-((d2Transfer10S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer10S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer10S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer10S0,d2Transfer10Lo,d2Transfer10Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer10C0,d2Log95Q,d2Transfer10S0,d2Transfer10Lo,d2Transfer10Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer10C0 d2Transfer10S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2Transfer10C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2Transfer10Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer10Arithmetic
  linarith
#print axioms d2Transfer10Arithmetic
#print axioms d2Transfer10Bound
def d2Transfer11Lo : ℚ := (d2LitsNearTransfers001.q2 (31540907) 1 (-28))
def d2Transfer11Hi : ℚ := (d2LitsNearTransfers001.q2 (8304657) 1 (-26))
def d2Transfer11Cap : ℚ := (d2LitsNearTransfers001.q2 (2432512853) 1 (-40))
def d2Transfer11C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 275 (-4))
def d2Transfer11S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
def d2Transfer11C1 : ℚ := (d2LitsNearTransfers001.q2 (-1) 55 (-3))
def d2Transfer11S1 : ℚ := (d2LitsNearTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer11Arithmetic : weightedUpper d2Transfer11C0 d2Log95Lo d2Log95Hi + weightedUpper d2Transfer11C1 d2Log79Lo d2Log79Hi ≤ d2Transfer11Cap := by decide +kernel
theorem d2Transfer11Bound : ∀ x ∈ Set.Icc ((d2Transfer11Lo:ℚ):ℝ) ((d2Transfer11Hi:ℚ):ℝ), ((d2Transfer11C0:ℚ):ℝ)*Real.log |x-((d2Transfer11S0:ℚ):ℝ)| + ((d2Transfer11C1:ℚ):ℝ)*Real.log |x-((d2Transfer11S1:ℚ):ℝ)| ≤ ((d2Transfer11Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer11S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11S0,d2Transfer11Lo,d2Transfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer11C0 then |x-((d2Transfer11S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer11S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer11S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11S0,d2Transfer11Lo,d2Transfer11Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11C0,d2Log95Q,d2Transfer11S0,d2Transfer11Lo,d2Transfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer11C0 d2Transfer11S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2Transfer11S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11S1,d2Transfer11Lo,d2Transfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer11C1 then |x-((d2Transfer11S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2Transfer11S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer11S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11S1,d2Transfer11Lo,d2Transfer11Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer11C1,d2Log79Q,d2Transfer11S1,d2Transfer11Lo,d2Transfer11Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer11C1 d2Transfer11S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2Transfer11C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2Transfer11C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2Transfer11Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer11Arithmetic
  linarith
#print axioms d2Transfer11Arithmetic
#print axioms d2Transfer11Bound
def d2Transfer12Lo : ℚ := (d2LitsNearTransfers001.q2 (8304657) 1 (-26))
def d2Transfer12Hi : ℚ := (d2LitsNearTransfers001.q2 (34896349) 1 (-28))
def d2Transfer12Cap : ℚ := (d2LitsNearTransfers001.q2 (648894057) 1 (-39))
def d2Transfer12C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 25 (-4))
def d2Transfer12S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer12Arithmetic : weightedUpper d2Transfer12C0 d2Log96Lo d2Log96Hi ≤ d2Transfer12Cap := by decide +kernel
theorem d2Transfer12Bound : ∀ x ∈ Set.Icc ((d2Transfer12Lo:ℚ):ℝ) ((d2Transfer12Hi:ℚ):ℝ), ((d2Transfer12C0:ℚ):ℝ)*Real.log |x-((d2Transfer12S0:ℚ):ℝ)| ≤ ((d2Transfer12Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer12S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer12S0,d2Transfer12Lo,d2Transfer12Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer12C0 then |x-((d2Transfer12S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer12S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer12S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer12S0,d2Transfer12Lo,d2Transfer12Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer12C0,d2Log96Q,d2Transfer12S0,d2Transfer12Lo,d2Transfer12Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer12C0 d2Transfer12S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have har : (((weightedUpper d2Transfer12C0 d2Log96Lo d2Log96Hi:ℚ):ℝ)) ≤ ((d2Transfer12Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer12Arithmetic
  linarith
#print axioms d2Transfer12Arithmetic
#print axioms d2Transfer12Bound
def d2Transfer13Lo : ℚ := (d2LitsNearTransfers001.q2 (8304657) 1 (-26))
def d2Transfer13Hi : ℚ := (d2LitsNearTransfers001.q2 (34896349) 1 (-28))
def d2Transfer13Cap : ℚ := (d2LitsNearTransfers001.q2 (2432512853) 1 (-40))
def d2Transfer13C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 275 (-4))
def d2Transfer13S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
def d2Transfer13C1 : ℚ := (d2LitsNearTransfers001.q2 (-1) 55 (-3))
def d2Transfer13S1 : ℚ := (d2LitsNearTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer13Arithmetic : weightedUpper d2Transfer13C0 d2Log96Lo d2Log96Hi + weightedUpper d2Transfer13C1 d2Log78Lo d2Log78Hi ≤ d2Transfer13Cap := by decide +kernel
theorem d2Transfer13Bound : ∀ x ∈ Set.Icc ((d2Transfer13Lo:ℚ):ℝ) ((d2Transfer13Hi:ℚ):ℝ), ((d2Transfer13C0:ℚ):ℝ)*Real.log |x-((d2Transfer13S0:ℚ):ℝ)| + ((d2Transfer13C1:ℚ):ℝ)*Real.log |x-((d2Transfer13S1:ℚ):ℝ)| ≤ ((d2Transfer13Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer13S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13S0,d2Transfer13Lo,d2Transfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer13C0 then |x-((d2Transfer13S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer13S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer13S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13S0,d2Transfer13Lo,d2Transfer13Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13C0,d2Log96Q,d2Transfer13S0,d2Transfer13Lo,d2Transfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer13C0 d2Transfer13S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have hn1 : x-((d2Transfer13S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13S1,d2Transfer13Lo,d2Transfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer13C1 then |x-((d2Transfer13S1:ℚ):ℝ)| ≤ ((d2Log78Q:ℚ):ℝ) else ((d2Log78Q:ℚ):ℝ) ≤ |x-((d2Transfer13S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer13S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13S1,d2Transfer13Lo,d2Transfer13Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer13C1,d2Log78Q,d2Transfer13S1,d2Transfer13Lo,d2Transfer13Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer13C1 d2Transfer13S1 d2Log78Q d2Log78Lo d2Log78Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log78Bounds
  have har : (((weightedUpper d2Transfer13C0 d2Log96Lo d2Log96Hi:ℚ):ℝ) + ((weightedUpper d2Transfer13C1 d2Log78Lo d2Log78Hi:ℚ):ℝ)) ≤ ((d2Transfer13Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer13Arithmetic
  linarith
#print axioms d2Transfer13Arithmetic
#print axioms d2Transfer13Bound
def d2Transfer14Lo : ℚ := (d2LitsNearTransfers001.q2 (34896349) 1 (-28))
def d2Transfer14Hi : ℚ := (d2LitsNearTransfers001.q2 (18287035) 1 (-27))
def d2Transfer14Cap : ℚ := (d2LitsNearTransfers001.q2 (648894057) 1 (-39))
def d2Transfer14C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 25 (-4))
def d2Transfer14S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer14Arithmetic : weightedUpper d2Transfer14C0 d2Log97Lo d2Log97Hi ≤ d2Transfer14Cap := by decide +kernel
theorem d2Transfer14Bound : ∀ x ∈ Set.Icc ((d2Transfer14Lo:ℚ):ℝ) ((d2Transfer14Hi:ℚ):ℝ), ((d2Transfer14C0:ℚ):ℝ)*Real.log |x-((d2Transfer14S0:ℚ):ℝ)| ≤ ((d2Transfer14Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer14S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer14S0,d2Transfer14Lo,d2Transfer14Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer14C0 then |x-((d2Transfer14S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer14S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer14S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer14S0,d2Transfer14Lo,d2Transfer14Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer14C0,d2Log97Q,d2Transfer14S0,d2Transfer14Lo,d2Transfer14Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer14C0 d2Transfer14S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have har : (((weightedUpper d2Transfer14C0 d2Log97Lo d2Log97Hi:ℚ):ℝ)) ≤ ((d2Transfer14Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer14Arithmetic
  linarith
#print axioms d2Transfer14Arithmetic
#print axioms d2Transfer14Bound
def d2Transfer15Lo : ℚ := (d2LitsNearTransfers001.q2 (34896349) 1 (-28))
def d2Transfer15Hi : ℚ := (d2LitsNearTransfers001.q2 (18287035) 1 (-27))
def d2Transfer15Cap : ℚ := (d2LitsNearTransfers001.q2 (2432512853) 1 (-40))
def d2Transfer15C0 : ℚ := (d2LitsNearTransfers001.q2 (1) 275 (-4))
def d2Transfer15S0 : ℚ := (d2LitsNearTransfers001.q2 (-1) 1 (0))
def d2Transfer15C1 : ℚ := (d2LitsNearTransfers001.q2 (-1) 55 (-3))
def d2Transfer15S1 : ℚ := (d2LitsNearTransfers001.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer15Arithmetic : weightedUpper d2Transfer15C0 d2Log97Lo d2Log97Hi + weightedUpper d2Transfer15C1 d2Log77Lo d2Log77Hi ≤ d2Transfer15Cap := by decide +kernel
theorem d2Transfer15Bound : ∀ x ∈ Set.Icc ((d2Transfer15Lo:ℚ):ℝ) ((d2Transfer15Hi:ℚ):ℝ), ((d2Transfer15C0:ℚ):ℝ)*Real.log |x-((d2Transfer15S0:ℚ):ℝ)| + ((d2Transfer15C1:ℚ):ℝ)*Real.log |x-((d2Transfer15S1:ℚ):ℝ)| ≤ ((d2Transfer15Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer15S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15S0,d2Transfer15Lo,d2Transfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer15C0 then |x-((d2Transfer15S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer15S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer15S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15S0,d2Transfer15Lo,d2Transfer15Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15C0,d2Log97Q,d2Transfer15S0,d2Transfer15Lo,d2Transfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer15C0 d2Transfer15S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have hn1 : x-((d2Transfer15S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15S1,d2Transfer15Lo,d2Transfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer15C1 then |x-((d2Transfer15S1:ℚ):ℝ)| ≤ ((d2Log77Q:ℚ):ℝ) else ((d2Log77Q:ℚ):ℝ) ≤ |x-((d2Transfer15S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer15S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15S1,d2Transfer15Lo,d2Transfer15Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers001.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer15C1,d2Log77Q,d2Transfer15S1,d2Transfer15Lo,d2Transfer15Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer15C1 d2Transfer15S1 d2Log77Q d2Log77Lo d2Log77Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log77Bounds
  have har : (((weightedUpper d2Transfer15C0 d2Log97Lo d2Log97Hi:ℚ):ℝ) + ((weightedUpper d2Transfer15C1 d2Log77Lo d2Log77Hi:ℚ):ℝ)) ≤ ((d2Transfer15Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer15Arithmetic
  linarith
#print axioms d2Transfer15Arithmetic
#print axioms d2Transfer15Bound
end CatalanMeasure.GenD.Signed.Data.Cells

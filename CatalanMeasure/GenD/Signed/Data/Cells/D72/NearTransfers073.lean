module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers073
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers073
open D72.LogTransfer
def d2Transfer584Lo : ℚ := (d2LitsNearTransfers073.q2 (88751317) 1 (-27))
def d2Transfer584Hi : ℚ := (d2LitsNearTransfers073.q2 (45214519) 1 (-26))
def d2Transfer584Cap : ℚ := (d2LitsNearTransfers073.q2 (5457531006538657118737) 1 (-78))
def d2Transfer584C0 : ℚ := (d2LitsNearTransfers073.q2 (23) 25 (-5))
def d2Transfer584S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer584Arithmetic : weightedUpper d2Transfer584C0 d2Log165Lo d2Log165Hi ≤ d2Transfer584Cap := by decide +kernel
theorem d2Transfer584Bound : ∀ x ∈ Set.Icc ((d2Transfer584Lo:ℚ):ℝ) ((d2Transfer584Hi:ℚ):ℝ), ((d2Transfer584C0:ℚ):ℝ)*Real.log |x-((d2Transfer584S0:ℚ):ℝ)| ≤ ((d2Transfer584Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer584S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer584S0,d2Transfer584Lo,d2Transfer584Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer584C0 then |x-((d2Transfer584S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer584S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer584S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer584S0,d2Transfer584Lo,d2Transfer584Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer584C0,d2Log165Q,d2Transfer584S0,d2Transfer584Lo,d2Transfer584Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer584C0 d2Transfer584S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2Transfer584C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2Transfer584Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer584Arithmetic
  linarith
#print axioms d2Transfer584Arithmetic
#print axioms d2Transfer584Bound
def d2Transfer585Lo : ℚ := (d2LitsNearTransfers073.q2 (88751317) 1 (-27))
def d2Transfer585Hi : ℚ := (d2LitsNearTransfers073.q2 (45214519) 1 (-26))
def d2Transfer585Cap : ℚ := (d2LitsNearTransfers073.q2 (9670277854355474692625) 1 (-78))
def d2Transfer585C0 : ℚ := (d2LitsNearTransfers073.q2 (3) 275 (-5))
def d2Transfer585S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
def d2Transfer585C1 : ℚ := (d2LitsNearTransfers073.q2 (-5) 11 (-4))
def d2Transfer585S1 : ℚ := (d2LitsNearTransfers073.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer585Arithmetic : weightedUpper d2Transfer585C0 d2Log165Lo d2Log165Hi + weightedUpper d2Transfer585C1 d2Log9Lo d2Log9Hi ≤ d2Transfer585Cap := by decide +kernel
theorem d2Transfer585Bound : ∀ x ∈ Set.Icc ((d2Transfer585Lo:ℚ):ℝ) ((d2Transfer585Hi:ℚ):ℝ), ((d2Transfer585C0:ℚ):ℝ)*Real.log |x-((d2Transfer585S0:ℚ):ℝ)| + ((d2Transfer585C1:ℚ):ℝ)*Real.log |x-((d2Transfer585S1:ℚ):ℝ)| ≤ ((d2Transfer585Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer585S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585S0,d2Transfer585Lo,d2Transfer585Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer585C0 then |x-((d2Transfer585S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer585S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer585S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585S0,d2Transfer585Lo,d2Transfer585Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585C0,d2Log165Q,d2Transfer585S0,d2Transfer585Lo,d2Transfer585Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer585C0 d2Transfer585S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2Transfer585S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585S1,d2Transfer585Lo,d2Transfer585Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer585C1 then |x-((d2Transfer585S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2Transfer585S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer585S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585S1,d2Transfer585Lo,d2Transfer585Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer585C1,d2Log9Q,d2Transfer585S1,d2Transfer585Lo,d2Transfer585Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer585C1 d2Transfer585S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2Transfer585C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2Transfer585C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2Transfer585Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer585Arithmetic
  linarith
#print axioms d2Transfer585Arithmetic
#print axioms d2Transfer585Bound
def d2Transfer586Lo : ℚ := (d2LitsNearTransfers073.q2 (45214519) 1 (-26))
def d2Transfer586Hi : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer586Cap : ℚ := (d2LitsNearTransfers073.q2 (4621244410980826169991) 1 (-79))
def d2Transfer586C0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 55 (-3))
def d2Transfer586S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
def d2Transfer586C1 : ℚ := (d2LitsNearTransfers073.q2 (-1) 55 (-3))
def d2Transfer586S1 : ℚ := (d2LitsNearTransfers073.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer586Arithmetic : weightedUpper d2Transfer586C0 d2Log165Lo d2Log165Hi + weightedUpper d2Transfer586C1 d2Log8Lo d2Log8Hi ≤ d2Transfer586Cap := by decide +kernel
theorem d2Transfer586Bound : ∀ x ∈ Set.Icc ((d2Transfer586Lo:ℚ):ℝ) ((d2Transfer586Hi:ℚ):ℝ), ((d2Transfer586C0:ℚ):ℝ)*Real.log |x-((d2Transfer586S0:ℚ):ℝ)| + ((d2Transfer586C1:ℚ):ℝ)*Real.log |x-((d2Transfer586S1:ℚ):ℝ)| ≤ ((d2Transfer586Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer586S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586S0,d2Transfer586Lo,d2Transfer586Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer586C0 then |x-((d2Transfer586S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2Transfer586S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer586S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586S0,d2Transfer586Lo,d2Transfer586Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586C0,d2Log165Q,d2Transfer586S0,d2Transfer586Lo,d2Transfer586Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer586C0 d2Transfer586S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2Transfer586S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586S1,d2Transfer586Lo,d2Transfer586Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer586C1 then |x-((d2Transfer586S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2Transfer586S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer586S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586S1,d2Transfer586Lo,d2Transfer586Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer586C1,d2Log8Q,d2Transfer586S1,d2Transfer586Lo,d2Transfer586Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer586C1 d2Transfer586S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2Transfer586C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2Transfer586C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2Transfer586Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer586Arithmetic
  linarith
#print axioms d2Transfer586Arithmetic
#print axioms d2Transfer586Bound
def d2Transfer587Lo : ℚ := (d2LitsNearTransfers073.q2 (45214519) 1 (-26))
def d2Transfer587Hi : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer587Cap : ℚ := (d2LitsNearTransfers073.q2 (12287142347943969636999) 1 (-79))
def d2Transfer587C0 : ℚ := (d2LitsNearTransfers073.q2 (23) 25 (-5))
def d2Transfer587S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer587Arithmetic : weightedUpper d2Transfer587C0 d2Log166Lo d2Log166Hi ≤ d2Transfer587Cap := by decide +kernel
theorem d2Transfer587Bound : ∀ x ∈ Set.Icc ((d2Transfer587Lo:ℚ):ℝ) ((d2Transfer587Hi:ℚ):ℝ), ((d2Transfer587C0:ℚ):ℝ)*Real.log |x-((d2Transfer587S0:ℚ):ℝ)| ≤ ((d2Transfer587Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer587S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer587S0,d2Transfer587Lo,d2Transfer587Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer587C0 then |x-((d2Transfer587S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer587S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer587S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer587S0,d2Transfer587Lo,d2Transfer587Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer587C0,d2Log166Q,d2Transfer587S0,d2Transfer587Lo,d2Transfer587Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer587C0 d2Transfer587S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2Transfer587C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2Transfer587Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer587Arithmetic
  linarith
#print axioms d2Transfer587Arithmetic
#print axioms d2Transfer587Bound
def d2Transfer588Lo : ℚ := (d2LitsNearTransfers073.q2 (45214519) 1 (-26))
def d2Transfer588Hi : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer588Cap : ℚ := (d2LitsNearTransfers073.q2 (20712636043577604784775) 1 (-79))
def d2Transfer588C0 : ℚ := (d2LitsNearTransfers073.q2 (3) 275 (-5))
def d2Transfer588S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
def d2Transfer588C1 : ℚ := (d2LitsNearTransfers073.q2 (-5) 11 (-4))
def d2Transfer588S1 : ℚ := (d2LitsNearTransfers073.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer588Arithmetic : weightedUpper d2Transfer588C0 d2Log166Lo d2Log166Hi + weightedUpper d2Transfer588C1 d2Log8Lo d2Log8Hi ≤ d2Transfer588Cap := by decide +kernel
theorem d2Transfer588Bound : ∀ x ∈ Set.Icc ((d2Transfer588Lo:ℚ):ℝ) ((d2Transfer588Hi:ℚ):ℝ), ((d2Transfer588C0:ℚ):ℝ)*Real.log |x-((d2Transfer588S0:ℚ):ℝ)| + ((d2Transfer588C1:ℚ):ℝ)*Real.log |x-((d2Transfer588S1:ℚ):ℝ)| ≤ ((d2Transfer588Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer588S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588S0,d2Transfer588Lo,d2Transfer588Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer588C0 then |x-((d2Transfer588S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer588S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer588S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588S0,d2Transfer588Lo,d2Transfer588Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588C0,d2Log166Q,d2Transfer588S0,d2Transfer588Lo,d2Transfer588Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer588C0 d2Transfer588S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2Transfer588S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588S1,d2Transfer588Lo,d2Transfer588Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer588C1 then |x-((d2Transfer588S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2Transfer588S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer588S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588S1,d2Transfer588Lo,d2Transfer588Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer588C1,d2Log8Q,d2Transfer588S1,d2Transfer588Lo,d2Transfer588Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer588C1 d2Transfer588S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2Transfer588C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2Transfer588C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2Transfer588Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer588Arithmetic
  linarith
#print axioms d2Transfer588Arithmetic
#print axioms d2Transfer588Bound
def d2Transfer589Lo : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer589Hi : ℚ := (d2LitsNearTransfers073.q2 (25123841) 1 (-25))
def d2Transfer589Cap : ℚ := (d2LitsNearTransfers073.q2 (15487665051695413563023) 1 (-80))
def d2Transfer589C0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 55 (-3))
def d2Transfer589S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
def d2Transfer589C1 : ℚ := (d2LitsNearTransfers073.q2 (-1) 55 (-3))
def d2Transfer589S1 : ℚ := (d2LitsNearTransfers073.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer589Arithmetic : weightedUpper d2Transfer589C0 d2Log166Lo d2Log166Hi + weightedUpper d2Transfer589C1 d2Log7Lo d2Log7Hi ≤ d2Transfer589Cap := by decide +kernel
theorem d2Transfer589Bound : ∀ x ∈ Set.Icc ((d2Transfer589Lo:ℚ):ℝ) ((d2Transfer589Hi:ℚ):ℝ), ((d2Transfer589C0:ℚ):ℝ)*Real.log |x-((d2Transfer589S0:ℚ):ℝ)| + ((d2Transfer589C1:ℚ):ℝ)*Real.log |x-((d2Transfer589S1:ℚ):ℝ)| ≤ ((d2Transfer589Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer589S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589S0,d2Transfer589Lo,d2Transfer589Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer589C0 then |x-((d2Transfer589S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer589S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer589S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589S0,d2Transfer589Lo,d2Transfer589Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589C0,d2Log166Q,d2Transfer589S0,d2Transfer589Lo,d2Transfer589Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer589C0 d2Transfer589S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2Transfer589S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589S1,d2Transfer589Lo,d2Transfer589Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer589C1 then |x-((d2Transfer589S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2Transfer589S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer589S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589S1,d2Transfer589Lo,d2Transfer589Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer589C1,d2Log7Q,d2Transfer589S1,d2Transfer589Lo,d2Transfer589Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer589C1 d2Transfer589S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2Transfer589C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2Transfer589C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2Transfer589Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer589Arithmetic
  linarith
#print axioms d2Transfer589Arithmetic
#print axioms d2Transfer589Bound
def d2Transfer590Lo : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer590Hi : ℚ := (d2LitsNearTransfers073.q2 (25123841) 1 (-25))
def d2Transfer590Cap : ℚ := (d2LitsNearTransfers073.q2 (30819460925621700497039) 1 (-80))
def d2Transfer590C0 : ℚ := (d2LitsNearTransfers073.q2 (23) 25 (-5))
def d2Transfer590S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer590Arithmetic : weightedUpper d2Transfer590C0 d2Log167Lo d2Log167Hi ≤ d2Transfer590Cap := by decide +kernel
theorem d2Transfer590Bound : ∀ x ∈ Set.Icc ((d2Transfer590Lo:ℚ):ℝ) ((d2Transfer590Hi:ℚ):ℝ), ((d2Transfer590C0:ℚ):ℝ)*Real.log |x-((d2Transfer590S0:ℚ):ℝ)| ≤ ((d2Transfer590Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer590S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer590S0,d2Transfer590Lo,d2Transfer590Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer590C0 then |x-((d2Transfer590S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer590S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer590S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer590S0,d2Transfer590Lo,d2Transfer590Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer590C0,d2Log167Q,d2Transfer590S0,d2Transfer590Lo,d2Transfer590Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer590C0 d2Transfer590S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2Transfer590C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2Transfer590Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer590Arithmetic
  linarith
#print axioms d2Transfer590Arithmetic
#print axioms d2Transfer590Bound
def d2Transfer591Lo : ℚ := (d2LitsNearTransfers073.q2 (2930765) 1 (-22))
def d2Transfer591Hi : ℚ := (d2LitsNearTransfers073.q2 (25123841) 1 (-25))
def d2Transfer591Cap : ℚ := (d2LitsNearTransfers073.q2 (47670448316888970792591) 1 (-80))
def d2Transfer591C0 : ℚ := (d2LitsNearTransfers073.q2 (3) 275 (-5))
def d2Transfer591S0 : ℚ := (d2LitsNearTransfers073.q2 (-1) 1 (0))
def d2Transfer591C1 : ℚ := (d2LitsNearTransfers073.q2 (-5) 11 (-4))
def d2Transfer591S1 : ℚ := (d2LitsNearTransfers073.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer591Arithmetic : weightedUpper d2Transfer591C0 d2Log167Lo d2Log167Hi + weightedUpper d2Transfer591C1 d2Log7Lo d2Log7Hi ≤ d2Transfer591Cap := by decide +kernel
theorem d2Transfer591Bound : ∀ x ∈ Set.Icc ((d2Transfer591Lo:ℚ):ℝ) ((d2Transfer591Hi:ℚ):ℝ), ((d2Transfer591C0:ℚ):ℝ)*Real.log |x-((d2Transfer591S0:ℚ):ℝ)| + ((d2Transfer591C1:ℚ):ℝ)*Real.log |x-((d2Transfer591S1:ℚ):ℝ)| ≤ ((d2Transfer591Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer591S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591S0,d2Transfer591Lo,d2Transfer591Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer591C0 then |x-((d2Transfer591S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer591S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer591S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591S0,d2Transfer591Lo,d2Transfer591Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591C0,d2Log167Q,d2Transfer591S0,d2Transfer591Lo,d2Transfer591Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer591C0 d2Transfer591S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2Transfer591S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591S1,d2Transfer591Lo,d2Transfer591Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer591C1 then |x-((d2Transfer591S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2Transfer591S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer591S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591S1,d2Transfer591Lo,d2Transfer591Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers073.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer591C1,d2Log7Q,d2Transfer591S1,d2Transfer591Lo,d2Transfer591Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer591C1 d2Transfer591S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2Transfer591C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2Transfer591C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2Transfer591Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer591Arithmetic
  linarith
#print axioms d2Transfer591Arithmetic
#print axioms d2Transfer591Bound
end CatalanMeasure.GenD.Signed.Data.Cells

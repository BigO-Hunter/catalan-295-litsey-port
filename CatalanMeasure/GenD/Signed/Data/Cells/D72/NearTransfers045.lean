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
namespace d2LitsNearTransfers045
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers045
open D72.LogTransfer
def d2Transfer360Lo : ℚ := (d2LitsNearTransfers045.q2 (13400781) 1 (-24))
def d2Transfer360Hi : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer360Cap : ℚ := (d2LitsNearTransfers045.q2 (64491342773095502170709) 1 (-80))
def d2Transfer360C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (-5))
def d2Transfer360S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer360Arithmetic : weightedUpper d2Transfer360C0 d2Log169Lo d2Log169Hi ≤ d2Transfer360Cap := by decide +kernel
theorem d2Transfer360Bound : ∀ x ∈ Set.Icc ((d2Transfer360Lo:ℚ):ℝ) ((d2Transfer360Hi:ℚ):ℝ), ((d2Transfer360C0:ℚ):ℝ)*Real.log |x-((d2Transfer360S0:ℚ):ℝ)| ≤ ((d2Transfer360Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer360S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer360S0,d2Transfer360Lo,d2Transfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer360C0 then |x-((d2Transfer360S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer360S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer360S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer360S0,d2Transfer360Lo,d2Transfer360Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer360C0,d2Log169Q,d2Transfer360S0,d2Transfer360Lo,d2Transfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer360C0 d2Transfer360S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2Transfer360C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2Transfer360Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer360Arithmetic
  linarith
#print axioms d2Transfer360Arithmetic
#print axioms d2Transfer360Bound
def d2Transfer361Lo : ℚ := (d2LitsNearTransfers045.q2 (13400781) 1 (-24))
def d2Transfer361Hi : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer361Cap : ℚ := (d2LitsNearTransfers045.q2 (80856180095387009534549) 1 (-80))
def d2Transfer361C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 11 (-5))
def d2Transfer361S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
def d2Transfer361C1 : ℚ := (d2LitsNearTransfers045.q2 (-5) 11 (-4))
def d2Transfer361S1 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer361Arithmetic : weightedUpper d2Transfer361C0 d2Log169Lo d2Log169Hi + weightedUpper d2Transfer361C1 d2Log5Lo d2Log5Hi ≤ d2Transfer361Cap := by decide +kernel
theorem d2Transfer361Bound : ∀ x ∈ Set.Icc ((d2Transfer361Lo:ℚ):ℝ) ((d2Transfer361Hi:ℚ):ℝ), ((d2Transfer361C0:ℚ):ℝ)*Real.log |x-((d2Transfer361S0:ℚ):ℝ)| + ((d2Transfer361C1:ℚ):ℝ)*Real.log |x-((d2Transfer361S1:ℚ):ℝ)| ≤ ((d2Transfer361Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer361S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361S0,d2Transfer361Lo,d2Transfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer361C0 then |x-((d2Transfer361S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer361S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer361S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361S0,d2Transfer361Lo,d2Transfer361Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361C0,d2Log169Q,d2Transfer361S0,d2Transfer361Lo,d2Transfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer361C0 d2Transfer361S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2Transfer361S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361S1,d2Transfer361Lo,d2Transfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer361C1 then |x-((d2Transfer361S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2Transfer361S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer361S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361S1,d2Transfer361Lo,d2Transfer361Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer361C1,d2Log5Q,d2Transfer361S1,d2Transfer361Lo,d2Transfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer361C1 d2Transfer361S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2Transfer361C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2Transfer361C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2Transfer361Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer361Arithmetic
  linarith
#print axioms d2Transfer361Arithmetic
#print axioms d2Transfer361Bound
def d2Transfer362Lo : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer362Hi : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer362Cap : ℚ := (d2LitsNearTransfers045.q2 (35745599033710447825519) 1 (-79))
def d2Transfer362C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 25 (-4))
def d2Transfer362S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer362Arithmetic : weightedUpper d2Transfer362C0 d2Log170Lo d2Log170Hi ≤ d2Transfer362Cap := by decide +kernel
theorem d2Transfer362Bound : ∀ x ∈ Set.Icc ((d2Transfer362Lo:ℚ):ℝ) ((d2Transfer362Hi:ℚ):ℝ), ((d2Transfer362C0:ℚ):ℝ)*Real.log |x-((d2Transfer362S0:ℚ):ℝ)| ≤ ((d2Transfer362Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer362S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer362S0,d2Transfer362Lo,d2Transfer362Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer362C0 then |x-((d2Transfer362S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer362S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer362S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer362S0,d2Transfer362Lo,d2Transfer362Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer362C0,d2Log170Q,d2Transfer362S0,d2Transfer362Lo,d2Transfer362Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer362C0 d2Transfer362S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2Transfer362C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2Transfer362Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer362Arithmetic
  linarith
#print axioms d2Transfer362Arithmetic
#print axioms d2Transfer362Bound
def d2Transfer363Lo : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer363Hi : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer363Cap : ℚ := (d2LitsNearTransfers045.q2 (36370749118028315497071) 1 (-79))
def d2Transfer363C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 275 (-4))
def d2Transfer363S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
def d2Transfer363C1 : ℚ := (d2LitsNearTransfers045.q2 (-1) 55 (-3))
def d2Transfer363S1 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer363Arithmetic : weightedUpper d2Transfer363C0 d2Log170Lo d2Log170Hi + weightedUpper d2Transfer363C1 d2Log4Lo d2Log4Hi ≤ d2Transfer363Cap := by decide +kernel
theorem d2Transfer363Bound : ∀ x ∈ Set.Icc ((d2Transfer363Lo:ℚ):ℝ) ((d2Transfer363Hi:ℚ):ℝ), ((d2Transfer363C0:ℚ):ℝ)*Real.log |x-((d2Transfer363S0:ℚ):ℝ)| + ((d2Transfer363C1:ℚ):ℝ)*Real.log |x-((d2Transfer363S1:ℚ):ℝ)| ≤ ((d2Transfer363Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer363S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363S0,d2Transfer363Lo,d2Transfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer363C0 then |x-((d2Transfer363S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer363S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer363S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363S0,d2Transfer363Lo,d2Transfer363Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363C0,d2Log170Q,d2Transfer363S0,d2Transfer363Lo,d2Transfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer363C0 d2Transfer363S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2Transfer363S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363S1,d2Transfer363Lo,d2Transfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer363C1 then |x-((d2Transfer363S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2Transfer363S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer363S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363S1,d2Transfer363Lo,d2Transfer363Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer363C1,d2Log4Q,d2Transfer363S1,d2Transfer363Lo,d2Transfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer363C1 d2Transfer363S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2Transfer363C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2Transfer363C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2Transfer363Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer363Arithmetic
  linarith
#print axioms d2Transfer363Arithmetic
#print axioms d2Transfer363Bound
def d2Transfer364Lo : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer364Hi : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer364Cap : ℚ := (d2LitsNearTransfers045.q2 (43982280163239795757679) 1 (-79))
def d2Transfer364C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (-5))
def d2Transfer364S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer364Arithmetic : weightedUpper d2Transfer364C0 d2Log170Lo d2Log170Hi ≤ d2Transfer364Cap := by decide +kernel
theorem d2Transfer364Bound : ∀ x ∈ Set.Icc ((d2Transfer364Lo:ℚ):ℝ) ((d2Transfer364Hi:ℚ):ℝ), ((d2Transfer364C0:ℚ):ℝ)*Real.log |x-((d2Transfer364S0:ℚ):ℝ)| ≤ ((d2Transfer364Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer364S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer364S0,d2Transfer364Lo,d2Transfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer364C0 then |x-((d2Transfer364S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer364S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer364S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer364S0,d2Transfer364Lo,d2Transfer364Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer364C0,d2Log170Q,d2Transfer364S0,d2Transfer364Lo,d2Transfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer364C0 d2Transfer364S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2Transfer364C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2Transfer364Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer364Arithmetic
  linarith
#print axioms d2Transfer364Arithmetic
#print axioms d2Transfer364Bound
def d2Transfer365Lo : ℚ := (d2LitsNearTransfers045.q2 (7539251) 1 (-23))
def d2Transfer365Hi : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer365Cap : ℚ := (d2LitsNearTransfers045.q2 (52164698824385549439599) 1 (-79))
def d2Transfer365C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 11 (-5))
def d2Transfer365S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
def d2Transfer365C1 : ℚ := (d2LitsNearTransfers045.q2 (-5) 11 (-4))
def d2Transfer365S1 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer365Arithmetic : weightedUpper d2Transfer365C0 d2Log170Lo d2Log170Hi + weightedUpper d2Transfer365C1 d2Log4Lo d2Log4Hi ≤ d2Transfer365Cap := by decide +kernel
theorem d2Transfer365Bound : ∀ x ∈ Set.Icc ((d2Transfer365Lo:ℚ):ℝ) ((d2Transfer365Hi:ℚ):ℝ), ((d2Transfer365C0:ℚ):ℝ)*Real.log |x-((d2Transfer365S0:ℚ):ℝ)| + ((d2Transfer365C1:ℚ):ℝ)*Real.log |x-((d2Transfer365S1:ℚ):ℝ)| ≤ ((d2Transfer365Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer365S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365S0,d2Transfer365Lo,d2Transfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer365C0 then |x-((d2Transfer365S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer365S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer365S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365S0,d2Transfer365Lo,d2Transfer365Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365C0,d2Log170Q,d2Transfer365S0,d2Transfer365Lo,d2Transfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer365C0 d2Transfer365S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2Transfer365S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365S1,d2Transfer365Lo,d2Transfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer365C1 then |x-((d2Transfer365S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2Transfer365S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer365S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365S1,d2Transfer365Lo,d2Transfer365Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer365C1,d2Log4Q,d2Transfer365S1,d2Transfer365Lo,d2Transfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer365C1 d2Transfer365S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2Transfer365C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2Transfer365C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2Transfer365Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer365Arithmetic
  linarith
#print axioms d2Transfer365Arithmetic
#print axioms d2Transfer365Bound
def d2Transfer366Lo : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer366Hi : ℚ := (d2LitsNearTransfers045.q2 (65347171) 1 (-26))
def d2Transfer366Cap : ℚ := (d2LitsNearTransfers045.q2 (47256162031528428522913) 1 (-79))
def d2Transfer366C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 25 (-4))
def d2Transfer366S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer366Arithmetic : weightedUpper d2Transfer366C0 d2Log171Lo d2Log171Hi ≤ d2Transfer366Cap := by decide +kernel
theorem d2Transfer366Bound : ∀ x ∈ Set.Icc ((d2Transfer366Lo:ℚ):ℝ) ((d2Transfer366Hi:ℚ):ℝ), ((d2Transfer366C0:ℚ):ℝ)*Real.log |x-((d2Transfer366S0:ℚ):ℝ)| ≤ ((d2Transfer366Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer366S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer366S0,d2Transfer366Lo,d2Transfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer366C0 then |x-((d2Transfer366S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer366S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer366S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer366S0,d2Transfer366Lo,d2Transfer366Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer366C0,d2Log171Q,d2Transfer366S0,d2Transfer366Lo,d2Transfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer366C0 d2Transfer366S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2Transfer366C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2Transfer366Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer366Arithmetic
  linarith
#print axioms d2Transfer366Arithmetic
#print axioms d2Transfer366Bound
def d2Transfer367Lo : ℚ := (d2LitsNearTransfers045.q2 (31834725) 1 (-25))
def d2Transfer367Hi : ℚ := (d2LitsNearTransfers045.q2 (65347171) 1 (-26))
def d2Transfer367Cap : ℚ := (d2LitsNearTransfers045.q2 (47881312115846296194465) 1 (-79))
def d2Transfer367C0 : ℚ := (d2LitsNearTransfers045.q2 (1) 275 (-4))
def d2Transfer367S0 : ℚ := (d2LitsNearTransfers045.q2 (-1) 1 (0))
def d2Transfer367C1 : ℚ := (d2LitsNearTransfers045.q2 (-1) 55 (-3))
def d2Transfer367S1 : ℚ := (d2LitsNearTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer367Arithmetic : weightedUpper d2Transfer367C0 d2Log171Lo d2Log171Hi + weightedUpper d2Transfer367C1 d2Log3Lo d2Log3Hi ≤ d2Transfer367Cap := by decide +kernel
theorem d2Transfer367Bound : ∀ x ∈ Set.Icc ((d2Transfer367Lo:ℚ):ℝ) ((d2Transfer367Hi:ℚ):ℝ), ((d2Transfer367C0:ℚ):ℝ)*Real.log |x-((d2Transfer367S0:ℚ):ℝ)| + ((d2Transfer367C1:ℚ):ℝ)*Real.log |x-((d2Transfer367S1:ℚ):ℝ)| ≤ ((d2Transfer367Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer367S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367S0,d2Transfer367Lo,d2Transfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer367C0 then |x-((d2Transfer367S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer367S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer367S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367S0,d2Transfer367Lo,d2Transfer367Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367C0,d2Log171Q,d2Transfer367S0,d2Transfer367Lo,d2Transfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer367C0 d2Transfer367S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2Transfer367S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367S1,d2Transfer367Lo,d2Transfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer367C1 then |x-((d2Transfer367S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2Transfer367S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer367S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367S1,d2Transfer367Lo,d2Transfer367Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer367C1,d2Log3Q,d2Transfer367S1,d2Transfer367Lo,d2Transfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer367C1 d2Transfer367S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2Transfer367C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2Transfer367C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2Transfer367Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer367Arithmetic
  linarith
#print axioms d2Transfer367Arithmetic
#print axioms d2Transfer367Bound
end CatalanMeasure.GenD.Signed.Data.Cells

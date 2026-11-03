module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers026
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers026
open D72.LogTransfer
def d2WiderTransfer208Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (21768399) 1 (-25))
def d2WiderTransfer208Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer208Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (11277963293974301228885) 1 (-79))
def d2WiderTransfer208C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (-5))
def d2WiderTransfer208S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer208Arithmetic : weightedUpper d2WiderTransfer208C0 d2Log164Lo d2Log164Hi ≤ d2WiderTransfer208Cap := by decide +kernel
theorem d2WiderTransfer208Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer208Lo:ℚ):ℝ) ((d2WiderTransfer208Hi:ℚ):ℝ), ((d2WiderTransfer208C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer208S0:ℚ):ℝ)| ≤ ((d2WiderTransfer208Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer208S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer208S0,d2WiderTransfer208Lo,d2WiderTransfer208Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer208C0 then |x-((d2WiderTransfer208S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer208S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer208S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer208S0,d2WiderTransfer208Lo,d2WiderTransfer208Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer208C0,d2Log164Q,d2WiderTransfer208S0,d2WiderTransfer208Lo,d2WiderTransfer208Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer208C0 d2WiderTransfer208S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2WiderTransfer208C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer208Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer208Arithmetic
  linarith
#print axioms d2WiderTransfer208Arithmetic
#print axioms d2WiderTransfer208Bound
def d2WiderTransfer209Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (21768399) 1 (-25))
def d2WiderTransfer209Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer209Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (19460381955120054910805) 1 (-79))
def d2WiderTransfer209C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 11 (-5))
def d2WiderTransfer209S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
def d2WiderTransfer209C1 : ℚ := (d2LitsNearWiderTransfers026.q2 (-5) 11 (-4))
def d2WiderTransfer209S1 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer209Arithmetic : weightedUpper d2WiderTransfer209C0 d2Log164Lo d2Log164Hi + weightedUpper d2WiderTransfer209C1 d2Log10Lo d2Log10Hi ≤ d2WiderTransfer209Cap := by decide +kernel
theorem d2WiderTransfer209Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer209Lo:ℚ):ℝ) ((d2WiderTransfer209Hi:ℚ):ℝ), ((d2WiderTransfer209C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer209S0:ℚ):ℝ)| + ((d2WiderTransfer209C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer209S1:ℚ):ℝ)| ≤ ((d2WiderTransfer209Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer209S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209S0,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer209C0 then |x-((d2WiderTransfer209S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer209S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer209S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209S0,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209C0,d2Log164Q,d2WiderTransfer209S0,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer209C0 d2WiderTransfer209S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2WiderTransfer209S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209S1,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer209C1 then |x-((d2WiderTransfer209S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer209S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer209S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209S1,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer209C1,d2Log10Q,d2WiderTransfer209S1,d2WiderTransfer209Lo,d2WiderTransfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer209C1 d2WiderTransfer209S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2WiderTransfer209C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer209C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer209Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer209Arithmetic
  linarith
#print axioms d2WiderTransfer209Arithmetic
#print axioms d2WiderTransfer209Bound
def d2WiderTransfer210Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer210Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer210Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (1849900766862984443043) 1 (-78))
def d2WiderTransfer210C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 25 (-4))
def d2WiderTransfer210S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer210Arithmetic : weightedUpper d2WiderTransfer210C0 d2Log165Lo d2Log165Hi ≤ d2WiderTransfer210Cap := by decide +kernel
theorem d2WiderTransfer210Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer210Lo:ℚ):ℝ) ((d2WiderTransfer210Hi:ℚ):ℝ), ((d2WiderTransfer210C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer210S0:ℚ):ℝ)| ≤ ((d2WiderTransfer210Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer210S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer210S0,d2WiderTransfer210Lo,d2WiderTransfer210Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer210C0 then |x-((d2WiderTransfer210S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer210S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer210S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer210S0,d2WiderTransfer210Lo,d2WiderTransfer210Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer210C0,d2Log165Q,d2WiderTransfer210S0,d2WiderTransfer210Lo,d2WiderTransfer210Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer210C0 d2WiderTransfer210S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2WiderTransfer210C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer210Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer210Arithmetic
  linarith
#print axioms d2WiderTransfer210Arithmetic
#print axioms d2WiderTransfer210Bound
def d2WiderTransfer211Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer211Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer211Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (2162475809021918278819) 1 (-78))
def d2WiderTransfer211C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 275 (-4))
def d2WiderTransfer211S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
def d2WiderTransfer211C1 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 55 (-3))
def d2WiderTransfer211S1 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer211Arithmetic : weightedUpper d2WiderTransfer211C0 d2Log165Lo d2Log165Hi + weightedUpper d2WiderTransfer211C1 d2Log9Lo d2Log9Hi ≤ d2WiderTransfer211Cap := by decide +kernel
theorem d2WiderTransfer211Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer211Lo:ℚ):ℝ) ((d2WiderTransfer211Hi:ℚ):ℝ), ((d2WiderTransfer211C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer211S0:ℚ):ℝ)| + ((d2WiderTransfer211C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer211S1:ℚ):ℝ)| ≤ ((d2WiderTransfer211Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer211S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211S0,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer211C0 then |x-((d2WiderTransfer211S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer211S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer211S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211S0,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211C0,d2Log165Q,d2WiderTransfer211S0,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer211C0 d2WiderTransfer211S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2WiderTransfer211S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211S1,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer211C1 then |x-((d2WiderTransfer211S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer211S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer211S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211S1,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer211C1,d2Log9Q,d2WiderTransfer211S1,d2WiderTransfer211Lo,d2WiderTransfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer211C1 d2WiderTransfer211S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2WiderTransfer211C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer211C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer211Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer211Arithmetic
  linarith
#print axioms d2WiderTransfer211Arithmetic
#print axioms d2WiderTransfer211Bound
def d2WiderTransfer212Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer212Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer212Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (5968241331627658409123) 1 (-78))
def d2WiderTransfer212C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (-5))
def d2WiderTransfer212S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer212Arithmetic : weightedUpper d2WiderTransfer212C0 d2Log165Lo d2Log165Hi ≤ d2WiderTransfer212Cap := by decide +kernel
theorem d2WiderTransfer212Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer212Lo:ℚ):ℝ) ((d2WiderTransfer212Hi:ℚ):ℝ), ((d2WiderTransfer212C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer212S0:ℚ):ℝ)| ≤ ((d2WiderTransfer212Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer212S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer212S0,d2WiderTransfer212Lo,d2WiderTransfer212Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer212C0 then |x-((d2WiderTransfer212S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer212S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer212S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer212S0,d2WiderTransfer212Lo,d2WiderTransfer212Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer212C0,d2Log165Q,d2WiderTransfer212S0,d2WiderTransfer212Lo,d2WiderTransfer212Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer212C0 d2WiderTransfer212S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2WiderTransfer212C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer212Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer212Arithmetic
  linarith
#print axioms d2WiderTransfer212Arithmetic
#print axioms d2WiderTransfer212Bound
def d2WiderTransfer213Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (88751317) 1 (-27))
def d2WiderTransfer213Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer213Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (10059450662200535250083) 1 (-78))
def d2WiderTransfer213C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 11 (-5))
def d2WiderTransfer213S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
def d2WiderTransfer213C1 : ℚ := (d2LitsNearWiderTransfers026.q2 (-5) 11 (-4))
def d2WiderTransfer213S1 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer213Arithmetic : weightedUpper d2WiderTransfer213C0 d2Log165Lo d2Log165Hi + weightedUpper d2WiderTransfer213C1 d2Log9Lo d2Log9Hi ≤ d2WiderTransfer213Cap := by decide +kernel
theorem d2WiderTransfer213Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer213Lo:ℚ):ℝ) ((d2WiderTransfer213Hi:ℚ):ℝ), ((d2WiderTransfer213C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer213S0:ℚ):ℝ)| + ((d2WiderTransfer213C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer213S1:ℚ):ℝ)| ≤ ((d2WiderTransfer213Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer213S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213S0,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer213C0 then |x-((d2WiderTransfer213S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer213S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer213S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213S0,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213C0,d2Log165Q,d2WiderTransfer213S0,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer213C0 d2WiderTransfer213S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2WiderTransfer213S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213S1,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer213C1 then |x-((d2WiderTransfer213S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer213S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer213S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213S1,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer213C1,d2Log9Q,d2WiderTransfer213S1,d2WiderTransfer213Lo,d2WiderTransfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer213C1 d2WiderTransfer213S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2WiderTransfer213C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer213C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer213Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer213Arithmetic
  linarith
#print axioms d2WiderTransfer213Arithmetic
#print axioms d2WiderTransfer213Bound
def d2WiderTransfer214Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer214Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (2930765) 1 (-22))
def d2WiderTransfer214Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (10188572794624507164743) 1 (-80))
def d2WiderTransfer214C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 25 (-4))
def d2WiderTransfer214S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer214Arithmetic : weightedUpper d2WiderTransfer214C0 d2Log166Lo d2Log166Hi ≤ d2WiderTransfer214Cap := by decide +kernel
theorem d2WiderTransfer214Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer214Lo:ℚ):ℝ) ((d2WiderTransfer214Hi:ℚ):ℝ), ((d2WiderTransfer214C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer214S0:ℚ):ℝ)| ≤ ((d2WiderTransfer214Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer214S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer214S0,d2WiderTransfer214Lo,d2WiderTransfer214Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer214C0 then |x-((d2WiderTransfer214S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer214S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer214S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer214S0,d2WiderTransfer214Lo,d2WiderTransfer214Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer214C0,d2Log166Q,d2WiderTransfer214S0,d2WiderTransfer214Lo,d2WiderTransfer214Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer214C0 d2WiderTransfer214S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2WiderTransfer214C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer214Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer214Arithmetic
  linarith
#print axioms d2WiderTransfer214Arithmetic
#print axioms d2WiderTransfer214Bound
def d2WiderTransfer215Lo : ℚ := (d2LitsNearWiderTransfers026.q2 (45214519) 1 (-26))
def d2WiderTransfer215Hi : ℚ := (d2LitsNearWiderTransfers026.q2 (2930765) 1 (-22))
def d2WiderTransfer215Cap : ℚ := (d2LitsNearWiderTransfers026.q2 (11438872963260242507847) 1 (-80))
def d2WiderTransfer215C0 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 275 (-4))
def d2WiderTransfer215S0 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 1 (0))
def d2WiderTransfer215C1 : ℚ := (d2LitsNearWiderTransfers026.q2 (-1) 55 (-3))
def d2WiderTransfer215S1 : ℚ := (d2LitsNearWiderTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer215Arithmetic : weightedUpper d2WiderTransfer215C0 d2Log166Lo d2Log166Hi + weightedUpper d2WiderTransfer215C1 d2Log8Lo d2Log8Hi ≤ d2WiderTransfer215Cap := by decide +kernel
theorem d2WiderTransfer215Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer215Lo:ℚ):ℝ) ((d2WiderTransfer215Hi:ℚ):ℝ), ((d2WiderTransfer215C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer215S0:ℚ):ℝ)| + ((d2WiderTransfer215C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer215S1:ℚ):ℝ)| ≤ ((d2WiderTransfer215Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer215S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215S0,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer215C0 then |x-((d2WiderTransfer215S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer215S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer215S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215S0,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215C0,d2Log166Q,d2WiderTransfer215S0,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer215C0 d2WiderTransfer215S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2WiderTransfer215S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215S1,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer215C1 then |x-((d2WiderTransfer215S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer215S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer215S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215S1,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers026.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer215C1,d2Log8Q,d2WiderTransfer215S1,d2WiderTransfer215Lo,d2WiderTransfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer215C1 d2WiderTransfer215S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2WiderTransfer215C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer215C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer215Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer215Arithmetic
  linarith
#print axioms d2WiderTransfer215Arithmetic
#print axioms d2WiderTransfer215Bound
end CatalanMeasure.GenD.Signed.Data.Cells

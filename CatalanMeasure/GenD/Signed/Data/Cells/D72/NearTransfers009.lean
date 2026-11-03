module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers009
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers009
open D72.LogTransfer
def d2Transfer72Lo : ℚ := (d2LitsNearTransfers009.q2 (21768399) 1 (-25))
def d2Transfer72Hi : ℚ := (d2LitsNearTransfers009.q2 (2930765) 1 (-22))
def d2Transfer72Cap : ℚ := (d2LitsNearTransfers009.q2 (2194498745222390080969) 1 (-80))
def d2Transfer72C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 25 (-4))
def d2Transfer72S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer72Arithmetic : weightedUpper d2Transfer72C0 d2Log166Lo d2Log166Hi ≤ d2Transfer72Cap := by decide +kernel
theorem d2Transfer72Bound : ∀ x ∈ Set.Icc ((d2Transfer72Lo:ℚ):ℝ) ((d2Transfer72Hi:ℚ):ℝ), ((d2Transfer72C0:ℚ):ℝ)*Real.log |x-((d2Transfer72S0:ℚ):ℝ)| ≤ ((d2Transfer72Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer72S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer72S0,d2Transfer72Lo,d2Transfer72Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer72C0 then |x-((d2Transfer72S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer72S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer72S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer72S0,d2Transfer72Lo,d2Transfer72Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer72C0,d2Log166Q,d2Transfer72S0,d2Transfer72Lo,d2Transfer72Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer72C0 d2Transfer72S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2Transfer72C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2Transfer72Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer72Arithmetic
  linarith
#print axioms d2Transfer72Arithmetic
#print axioms d2Transfer72Bound
def d2Transfer73Lo : ℚ := (d2LitsNearTransfers009.q2 (21768399) 1 (-25))
def d2Transfer73Hi : ℚ := (d2LitsNearTransfers009.q2 (2930765) 1 (-22))
def d2Transfer73Cap : ℚ := (d2LitsNearTransfers009.q2 (3442141790077976831433) 1 (-80))
def d2Transfer73C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 275 (-4))
def d2Transfer73S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
def d2Transfer73C1 : ℚ := (d2LitsNearTransfers009.q2 (-1) 55 (-3))
def d2Transfer73S1 : ℚ := (d2LitsNearTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer73Arithmetic : weightedUpper d2Transfer73C0 d2Log166Lo d2Log166Hi + weightedUpper d2Transfer73C1 d2Log8Lo d2Log8Hi ≤ d2Transfer73Cap := by decide +kernel
theorem d2Transfer73Bound : ∀ x ∈ Set.Icc ((d2Transfer73Lo:ℚ):ℝ) ((d2Transfer73Hi:ℚ):ℝ), ((d2Transfer73C0:ℚ):ℝ)*Real.log |x-((d2Transfer73S0:ℚ):ℝ)| + ((d2Transfer73C1:ℚ):ℝ)*Real.log |x-((d2Transfer73S1:ℚ):ℝ)| ≤ ((d2Transfer73Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer73S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73S0,d2Transfer73Lo,d2Transfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer73C0 then |x-((d2Transfer73S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2Transfer73S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer73S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73S0,d2Transfer73Lo,d2Transfer73Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73C0,d2Log166Q,d2Transfer73S0,d2Transfer73Lo,d2Transfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer73C0 d2Transfer73S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2Transfer73S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73S1,d2Transfer73Lo,d2Transfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer73C1 then |x-((d2Transfer73S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2Transfer73S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer73S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73S1,d2Transfer73Lo,d2Transfer73Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer73C1,d2Log8Q,d2Transfer73S1,d2Transfer73Lo,d2Transfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer73C1 d2Transfer73S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2Transfer73C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2Transfer73C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2Transfer73Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer73Arithmetic
  linarith
#print axioms d2Transfer73Arithmetic
#print axioms d2Transfer73Bound
def d2Transfer74Lo : ℚ := (d2LitsNearTransfers009.q2 (2930765) 1 (-22))
def d2Transfer74Hi : ℚ := (d2LitsNearTransfers009.q2 (13400781) 1 (-24))
def d2Transfer74Cap : ℚ := (d2LitsNearTransfers009.q2 (3318553540790580091593) 1 (-80))
def d2Transfer74C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 25 (-4))
def d2Transfer74S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer74Arithmetic : weightedUpper d2Transfer74C0 d2Log168Lo d2Log168Hi ≤ d2Transfer74Cap := by decide +kernel
theorem d2Transfer74Bound : ∀ x ∈ Set.Icc ((d2Transfer74Lo:ℚ):ℝ) ((d2Transfer74Hi:ℚ):ℝ), ((d2Transfer74C0:ℚ):ℝ)*Real.log |x-((d2Transfer74S0:ℚ):ℝ)| ≤ ((d2Transfer74Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer74S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer74S0,d2Transfer74Lo,d2Transfer74Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer74C0 then |x-((d2Transfer74S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer74S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer74S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer74S0,d2Transfer74Lo,d2Transfer74Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer74C0,d2Log168Q,d2Transfer74S0,d2Transfer74Lo,d2Transfer74Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer74C0 d2Transfer74S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2Transfer74C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2Transfer74Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer74Arithmetic
  linarith
#print axioms d2Transfer74Arithmetic
#print axioms d2Transfer74Bound
def d2Transfer75Lo : ℚ := (d2LitsNearTransfers009.q2 (2930765) 1 (-22))
def d2Transfer75Hi : ℚ := (d2LitsNearTransfers009.q2 (13400781) 1 (-24))
def d2Transfer75Cap : ℚ := (d2LitsNearTransfers009.q2 (4566196585646166842057) 1 (-80))
def d2Transfer75C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 275 (-4))
def d2Transfer75S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
def d2Transfer75C1 : ℚ := (d2LitsNearTransfers009.q2 (-1) 55 (-3))
def d2Transfer75S1 : ℚ := (d2LitsNearTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer75Arithmetic : weightedUpper d2Transfer75C0 d2Log168Lo d2Log168Hi + weightedUpper d2Transfer75C1 d2Log6Lo d2Log6Hi ≤ d2Transfer75Cap := by decide +kernel
theorem d2Transfer75Bound : ∀ x ∈ Set.Icc ((d2Transfer75Lo:ℚ):ℝ) ((d2Transfer75Hi:ℚ):ℝ), ((d2Transfer75C0:ℚ):ℝ)*Real.log |x-((d2Transfer75S0:ℚ):ℝ)| + ((d2Transfer75C1:ℚ):ℝ)*Real.log |x-((d2Transfer75S1:ℚ):ℝ)| ≤ ((d2Transfer75Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer75S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75S0,d2Transfer75Lo,d2Transfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer75C0 then |x-((d2Transfer75S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer75S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer75S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75S0,d2Transfer75Lo,d2Transfer75Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75C0,d2Log168Q,d2Transfer75S0,d2Transfer75Lo,d2Transfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer75C0 d2Transfer75S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2Transfer75S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75S1,d2Transfer75Lo,d2Transfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer75C1 then |x-((d2Transfer75S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2Transfer75S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer75S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75S1,d2Transfer75Lo,d2Transfer75Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer75C1,d2Log6Q,d2Transfer75S1,d2Transfer75Lo,d2Transfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer75C1 d2Transfer75S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2Transfer75C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2Transfer75C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2Transfer75Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer75Arithmetic
  linarith
#print axioms d2Transfer75Arithmetic
#print axioms d2Transfer75Bound
def d2Transfer76Lo : ℚ := (d2LitsNearTransfers009.q2 (13400781) 1 (-24))
def d2Transfer76Hi : ℚ := (d2LitsNearTransfers009.q2 (7539251) 1 (-23))
def d2Transfer76Cap : ℚ := (d2LitsNearTransfers009.q2 (1305212840693843503075) 1 (-78))
def d2Transfer76C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 25 (-4))
def d2Transfer76S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer76Arithmetic : weightedUpper d2Transfer76C0 d2Log169Lo d2Log169Hi ≤ d2Transfer76Cap := by decide +kernel
theorem d2Transfer76Bound : ∀ x ∈ Set.Icc ((d2Transfer76Lo:ℚ):ℝ) ((d2Transfer76Hi:ℚ):ℝ), ((d2Transfer76C0:ℚ):ℝ)*Real.log |x-((d2Transfer76S0:ℚ):ℝ)| ≤ ((d2Transfer76Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer76S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer76S0,d2Transfer76Lo,d2Transfer76Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer76C0 then |x-((d2Transfer76S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer76S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer76S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer76S0,d2Transfer76Lo,d2Transfer76Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer76C0,d2Log169Q,d2Transfer76S0,d2Transfer76Lo,d2Transfer76Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer76C0 d2Transfer76S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2Transfer76C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2Transfer76Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer76Arithmetic
  linarith
#print axioms d2Transfer76Arithmetic
#print axioms d2Transfer76Bound
def d2Transfer77Lo : ℚ := (d2LitsNearTransfers009.q2 (13400781) 1 (-24))
def d2Transfer77Hi : ℚ := (d2LitsNearTransfers009.q2 (7539251) 1 (-23))
def d2Transfer77Cap : ℚ := (d2LitsNearTransfers009.q2 (1617123601907740190691) 1 (-78))
def d2Transfer77C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 275 (-4))
def d2Transfer77S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
def d2Transfer77C1 : ℚ := (d2LitsNearTransfers009.q2 (-1) 55 (-3))
def d2Transfer77S1 : ℚ := (d2LitsNearTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer77Arithmetic : weightedUpper d2Transfer77C0 d2Log169Lo d2Log169Hi + weightedUpper d2Transfer77C1 d2Log5Lo d2Log5Hi ≤ d2Transfer77Cap := by decide +kernel
theorem d2Transfer77Bound : ∀ x ∈ Set.Icc ((d2Transfer77Lo:ℚ):ℝ) ((d2Transfer77Hi:ℚ):ℝ), ((d2Transfer77C0:ℚ):ℝ)*Real.log |x-((d2Transfer77S0:ℚ):ℝ)| + ((d2Transfer77C1:ℚ):ℝ)*Real.log |x-((d2Transfer77S1:ℚ):ℝ)| ≤ ((d2Transfer77Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer77S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77S0,d2Transfer77Lo,d2Transfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer77C0 then |x-((d2Transfer77S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer77S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer77S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77S0,d2Transfer77Lo,d2Transfer77Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77C0,d2Log169Q,d2Transfer77S0,d2Transfer77Lo,d2Transfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer77C0 d2Transfer77S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2Transfer77S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77S1,d2Transfer77Lo,d2Transfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer77C1 then |x-((d2Transfer77S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2Transfer77S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer77S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77S1,d2Transfer77Lo,d2Transfer77Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer77C1,d2Log5Q,d2Transfer77S1,d2Transfer77Lo,d2Transfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer77C1 d2Transfer77S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2Transfer77C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2Transfer77C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2Transfer77Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer77Arithmetic
  linarith
#print axioms d2Transfer77Arithmetic
#print axioms d2Transfer77Bound
def d2Transfer78Lo : ℚ := (d2LitsNearTransfers009.q2 (7539251) 1 (-23))
def d2Transfer78Hi : ℚ := (d2LitsNearTransfers009.q2 (31834725) 1 (-25))
def d2Transfer78Cap : ℚ := (d2LitsNearTransfers009.q2 (110917324485095330623) 1 (-74))
def d2Transfer78C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 25 (-4))
def d2Transfer78S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer78Arithmetic : weightedUpper d2Transfer78C0 d2Log170Lo d2Log170Hi ≤ d2Transfer78Cap := by decide +kernel
theorem d2Transfer78Bound : ∀ x ∈ Set.Icc ((d2Transfer78Lo:ℚ):ℝ) ((d2Transfer78Hi:ℚ):ℝ), ((d2Transfer78C0:ℚ):ℝ)*Real.log |x-((d2Transfer78S0:ℚ):ℝ)| ≤ ((d2Transfer78Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer78S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer78S0,d2Transfer78Lo,d2Transfer78Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer78C0 then |x-((d2Transfer78S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer78S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer78S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer78S0,d2Transfer78Lo,d2Transfer78Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer78C0,d2Log170Q,d2Transfer78S0,d2Transfer78Lo,d2Transfer78Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer78C0 d2Transfer78S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2Transfer78C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2Transfer78Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer78Arithmetic
  linarith
#print axioms d2Transfer78Arithmetic
#print axioms d2Transfer78Bound
def d2Transfer79Lo : ℚ := (d2LitsNearTransfers009.q2 (7539251) 1 (-23))
def d2Transfer79Hi : ℚ := (d2LitsNearTransfers009.q2 (31834725) 1 (-25))
def d2Transfer79Cap : ℚ := (d2LitsNearTransfers009.q2 (130411747060963873599) 1 (-74))
def d2Transfer79C0 : ℚ := (d2LitsNearTransfers009.q2 (1) 275 (-4))
def d2Transfer79S0 : ℚ := (d2LitsNearTransfers009.q2 (-1) 1 (0))
def d2Transfer79C1 : ℚ := (d2LitsNearTransfers009.q2 (-1) 55 (-3))
def d2Transfer79S1 : ℚ := (d2LitsNearTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer79Arithmetic : weightedUpper d2Transfer79C0 d2Log170Lo d2Log170Hi + weightedUpper d2Transfer79C1 d2Log4Lo d2Log4Hi ≤ d2Transfer79Cap := by decide +kernel
theorem d2Transfer79Bound : ∀ x ∈ Set.Icc ((d2Transfer79Lo:ℚ):ℝ) ((d2Transfer79Hi:ℚ):ℝ), ((d2Transfer79C0:ℚ):ℝ)*Real.log |x-((d2Transfer79S0:ℚ):ℝ)| + ((d2Transfer79C1:ℚ):ℝ)*Real.log |x-((d2Transfer79S1:ℚ):ℝ)| ≤ ((d2Transfer79Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer79S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79S0,d2Transfer79Lo,d2Transfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer79C0 then |x-((d2Transfer79S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer79S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer79S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79S0,d2Transfer79Lo,d2Transfer79Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79C0,d2Log170Q,d2Transfer79S0,d2Transfer79Lo,d2Transfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer79C0 d2Transfer79S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2Transfer79S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79S1,d2Transfer79Lo,d2Transfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer79C1 then |x-((d2Transfer79S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2Transfer79S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer79S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79S1,d2Transfer79Lo,d2Transfer79Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers009.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer79C1,d2Log4Q,d2Transfer79S1,d2Transfer79Lo,d2Transfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer79C1 d2Transfer79S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2Transfer79C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2Transfer79C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2Transfer79Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer79Arithmetic
  linarith
#print axioms d2Transfer79Arithmetic
#print axioms d2Transfer79Bound
end CatalanMeasure.GenD.Signed.Data.Cells

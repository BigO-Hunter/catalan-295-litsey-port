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
namespace d2LitsNearWiderTransfers028
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers028
open D72.LogTransfer
def d2WiderTransfer224Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (25123841) 1 (-25))
def d2WiderTransfer224Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer224Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (40712619998285578161861) 1 (-80))
def d2WiderTransfer224C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (-5))
def d2WiderTransfer224S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer224Arithmetic : weightedUpper d2WiderTransfer224C0 d2Log168Lo d2Log168Hi ≤ d2WiderTransfer224Cap := by decide +kernel
theorem d2WiderTransfer224Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer224Lo:ℚ):ℝ) ((d2WiderTransfer224Hi:ℚ):ℝ), ((d2WiderTransfer224C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer224S0:ℚ):ℝ)| ≤ ((d2WiderTransfer224Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer224S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer224S0,d2WiderTransfer224Lo,d2WiderTransfer224Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer224C0 then |x-((d2WiderTransfer224S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer224S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer224S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer224S0,d2WiderTransfer224Lo,d2WiderTransfer224Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer224C0,d2Log168Q,d2WiderTransfer224S0,d2WiderTransfer224Lo,d2WiderTransfer224Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer224C0 d2WiderTransfer224S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2WiderTransfer224C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer224Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer224Arithmetic
  linarith
#print axioms d2WiderTransfer224Arithmetic
#print axioms d2WiderTransfer224Bound
def d2WiderTransfer225Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (25123841) 1 (-25))
def d2WiderTransfer225Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer225Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (57077457320577085525701) 1 (-80))
def d2WiderTransfer225C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 11 (-5))
def d2WiderTransfer225S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
def d2WiderTransfer225C1 : ℚ := (d2LitsNearWiderTransfers028.q2 (-5) 11 (-4))
def d2WiderTransfer225S1 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer225Arithmetic : weightedUpper d2WiderTransfer225C0 d2Log168Lo d2Log168Hi + weightedUpper d2WiderTransfer225C1 d2Log6Lo d2Log6Hi ≤ d2WiderTransfer225Cap := by decide +kernel
theorem d2WiderTransfer225Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer225Lo:ℚ):ℝ) ((d2WiderTransfer225Hi:ℚ):ℝ), ((d2WiderTransfer225C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer225S0:ℚ):ℝ)| + ((d2WiderTransfer225C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer225S1:ℚ):ℝ)| ≤ ((d2WiderTransfer225Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer225S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225S0,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer225C0 then |x-((d2WiderTransfer225S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer225S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer225S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225S0,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225C0,d2Log168Q,d2WiderTransfer225S0,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer225C0 d2WiderTransfer225S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2WiderTransfer225S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225S1,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer225C1 then |x-((d2WiderTransfer225S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer225S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer225S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225S1,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer225C1,d2Log6Q,d2WiderTransfer225S1,d2WiderTransfer225Lo,d2WiderTransfer225Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer225C1 d2WiderTransfer225S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2WiderTransfer225C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer225C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer225Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer225Arithmetic
  linarith
#print axioms d2WiderTransfer225Arithmetic
#print axioms d2WiderTransfer225Bound
def d2WiderTransfer226Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer226Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer226Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (48017980514036806306389) 1 (-80))
def d2WiderTransfer226C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 25 (-4))
def d2WiderTransfer226S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer226Arithmetic : weightedUpper d2WiderTransfer226C0 d2Log169Lo d2Log169Hi ≤ d2WiderTransfer226Cap := by decide +kernel
theorem d2WiderTransfer226Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer226Lo:ℚ):ℝ) ((d2WiderTransfer226Hi:ℚ):ℝ), ((d2WiderTransfer226C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer226S0:ℚ):ℝ)| ≤ ((d2WiderTransfer226Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer226S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer226S0,d2WiderTransfer226Lo,d2WiderTransfer226Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer226C0 then |x-((d2WiderTransfer226S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer226S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer226S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer226S0,d2WiderTransfer226Lo,d2WiderTransfer226Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer226C0,d2Log169Q,d2WiderTransfer226S0,d2WiderTransfer226Lo,d2WiderTransfer226Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer226C0 d2WiderTransfer226S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2WiderTransfer226C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer226Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer226Arithmetic
  linarith
#print axioms d2WiderTransfer226Arithmetic
#print axioms d2WiderTransfer226Bound
def d2WiderTransfer227Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer227Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer227Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (49268280682672541649493) 1 (-80))
def d2WiderTransfer227C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 275 (-4))
def d2WiderTransfer227S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
def d2WiderTransfer227C1 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 55 (-3))
def d2WiderTransfer227S1 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer227Arithmetic : weightedUpper d2WiderTransfer227C0 d2Log169Lo d2Log169Hi + weightedUpper d2WiderTransfer227C1 d2Log5Lo d2Log5Hi ≤ d2WiderTransfer227Cap := by decide +kernel
theorem d2WiderTransfer227Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer227Lo:ℚ):ℝ) ((d2WiderTransfer227Hi:ℚ):ℝ), ((d2WiderTransfer227C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer227S0:ℚ):ℝ)| + ((d2WiderTransfer227C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer227S1:ℚ):ℝ)| ≤ ((d2WiderTransfer227Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer227S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227S0,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer227C0 then |x-((d2WiderTransfer227S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer227S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer227S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227S0,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227C0,d2Log169Q,d2WiderTransfer227S0,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer227C0 d2WiderTransfer227S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2WiderTransfer227S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227S1,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer227C1 then |x-((d2WiderTransfer227S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer227S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer227S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227S1,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer227C1,d2Log5Q,d2WiderTransfer227S1,d2WiderTransfer227Lo,d2WiderTransfer227Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer227C1 d2WiderTransfer227S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2WiderTransfer227C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer227C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer227Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer227Arithmetic
  linarith
#print axioms d2WiderTransfer227Arithmetic
#print axioms d2WiderTransfer227Bound
def d2WiderTransfer228Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer228Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer228Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (64491342773095502170709) 1 (-80))
def d2WiderTransfer228C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (-5))
def d2WiderTransfer228S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer228Arithmetic : weightedUpper d2WiderTransfer228C0 d2Log169Lo d2Log169Hi ≤ d2WiderTransfer228Cap := by decide +kernel
theorem d2WiderTransfer228Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer228Lo:ℚ):ℝ) ((d2WiderTransfer228Hi:ℚ):ℝ), ((d2WiderTransfer228C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer228S0:ℚ):ℝ)| ≤ ((d2WiderTransfer228Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer228S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer228S0,d2WiderTransfer228Lo,d2WiderTransfer228Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer228C0 then |x-((d2WiderTransfer228S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer228S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer228S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer228S0,d2WiderTransfer228Lo,d2WiderTransfer228Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer228C0,d2Log169Q,d2WiderTransfer228S0,d2WiderTransfer228Lo,d2WiderTransfer228Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer228C0 d2WiderTransfer228S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2WiderTransfer228C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer228Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer228Arithmetic
  linarith
#print axioms d2WiderTransfer228Arithmetic
#print axioms d2WiderTransfer228Bound
def d2WiderTransfer229Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (13400781) 1 (-24))
def d2WiderTransfer229Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer229Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (80856180095387009534549) 1 (-80))
def d2WiderTransfer229C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 11 (-5))
def d2WiderTransfer229S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
def d2WiderTransfer229C1 : ℚ := (d2LitsNearWiderTransfers028.q2 (-5) 11 (-4))
def d2WiderTransfer229S1 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer229Arithmetic : weightedUpper d2WiderTransfer229C0 d2Log169Lo d2Log169Hi + weightedUpper d2WiderTransfer229C1 d2Log5Lo d2Log5Hi ≤ d2WiderTransfer229Cap := by decide +kernel
theorem d2WiderTransfer229Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer229Lo:ℚ):ℝ) ((d2WiderTransfer229Hi:ℚ):ℝ), ((d2WiderTransfer229C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer229S0:ℚ):ℝ)| + ((d2WiderTransfer229C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer229S1:ℚ):ℝ)| ≤ ((d2WiderTransfer229Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer229S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229S0,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer229C0 then |x-((d2WiderTransfer229S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer229S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer229S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229S0,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229C0,d2Log169Q,d2WiderTransfer229S0,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer229C0 d2WiderTransfer229S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2WiderTransfer229S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229S1,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer229C1 then |x-((d2WiderTransfer229S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer229S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer229S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229S1,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer229C1,d2Log5Q,d2WiderTransfer229S1,d2WiderTransfer229Lo,d2WiderTransfer229Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer229C1 d2WiderTransfer229S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2WiderTransfer229C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer229C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer229Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer229Arithmetic
  linarith
#print axioms d2WiderTransfer229Arithmetic
#print axioms d2WiderTransfer229Bound
def d2WiderTransfer230Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer230Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (31834725) 1 (-25))
def d2WiderTransfer230Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (35745599033710447825519) 1 (-79))
def d2WiderTransfer230C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 25 (-4))
def d2WiderTransfer230S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer230Arithmetic : weightedUpper d2WiderTransfer230C0 d2Log170Lo d2Log170Hi ≤ d2WiderTransfer230Cap := by decide +kernel
theorem d2WiderTransfer230Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer230Lo:ℚ):ℝ) ((d2WiderTransfer230Hi:ℚ):ℝ), ((d2WiderTransfer230C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer230S0:ℚ):ℝ)| ≤ ((d2WiderTransfer230Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer230S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer230S0,d2WiderTransfer230Lo,d2WiderTransfer230Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer230C0 then |x-((d2WiderTransfer230S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer230S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer230S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer230S0,d2WiderTransfer230Lo,d2WiderTransfer230Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer230C0,d2Log170Q,d2WiderTransfer230S0,d2WiderTransfer230Lo,d2WiderTransfer230Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer230C0 d2WiderTransfer230S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2WiderTransfer230C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer230Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer230Arithmetic
  linarith
#print axioms d2WiderTransfer230Arithmetic
#print axioms d2WiderTransfer230Bound
def d2WiderTransfer231Lo : ℚ := (d2LitsNearWiderTransfers028.q2 (7539251) 1 (-23))
def d2WiderTransfer231Hi : ℚ := (d2LitsNearWiderTransfers028.q2 (31834725) 1 (-25))
def d2WiderTransfer231Cap : ℚ := (d2LitsNearWiderTransfers028.q2 (36370749118028315497071) 1 (-79))
def d2WiderTransfer231C0 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 275 (-4))
def d2WiderTransfer231S0 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 1 (0))
def d2WiderTransfer231C1 : ℚ := (d2LitsNearWiderTransfers028.q2 (-1) 55 (-3))
def d2WiderTransfer231S1 : ℚ := (d2LitsNearWiderTransfers028.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer231Arithmetic : weightedUpper d2WiderTransfer231C0 d2Log170Lo d2Log170Hi + weightedUpper d2WiderTransfer231C1 d2Log4Lo d2Log4Hi ≤ d2WiderTransfer231Cap := by decide +kernel
theorem d2WiderTransfer231Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer231Lo:ℚ):ℝ) ((d2WiderTransfer231Hi:ℚ):ℝ), ((d2WiderTransfer231C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer231S0:ℚ):ℝ)| + ((d2WiderTransfer231C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer231S1:ℚ):ℝ)| ≤ ((d2WiderTransfer231Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer231S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231S0,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer231C0 then |x-((d2WiderTransfer231S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer231S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer231S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231S0,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231C0,d2Log170Q,d2WiderTransfer231S0,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer231C0 d2WiderTransfer231S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2WiderTransfer231S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231S1,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer231C1 then |x-((d2WiderTransfer231S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer231S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer231S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231S1,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers028.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer231C1,d2Log4Q,d2WiderTransfer231S1,d2WiderTransfer231Lo,d2WiderTransfer231Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer231C1 d2WiderTransfer231S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2WiderTransfer231C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer231C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer231Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer231Arithmetic
  linarith
#print axioms d2WiderTransfer231Arithmetic
#print axioms d2WiderTransfer231Bound
end CatalanMeasure.GenD.Signed.Data.Cells

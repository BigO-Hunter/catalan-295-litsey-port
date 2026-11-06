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
namespace d2LitsNearWiderTransfers048
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers048
open D72.LogTransfer
def d2WiderTransfer384Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (25123841) 1 (-25))
def d2WiderTransfer384Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (13400781) 1 (-24))
def d2WiderTransfer384Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (55303082721192846961955) 1 (-80))
def d2WiderTransfer384C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (3) 275 (-5))
def d2WiderTransfer384S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer384C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-5) 11 (-4))
def d2WiderTransfer384S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer384Arithmetic : weightedUpper d2WiderTransfer384C0 d2Log168Lo d2Log168Hi + weightedUpper d2WiderTransfer384C1 d2Log6Lo d2Log6Hi ≤ d2WiderTransfer384Cap := by decide +kernel
theorem d2WiderTransfer384Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer384Lo:ℚ):ℝ) ((d2WiderTransfer384Hi:ℚ):ℝ), ((d2WiderTransfer384C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer384S0:ℚ):ℝ)| + ((d2WiderTransfer384C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer384S1:ℚ):ℝ)| ≤ ((d2WiderTransfer384Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer384S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384S0,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer384C0 then |x-((d2WiderTransfer384S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer384S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer384S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384S0,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384C0,d2Log168Q,d2WiderTransfer384S0,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer384C0 d2WiderTransfer384S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2WiderTransfer384S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384S1,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer384C1 then |x-((d2WiderTransfer384S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer384S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer384S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384S1,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer384C1,d2Log6Q,d2WiderTransfer384S1,d2WiderTransfer384Lo,d2WiderTransfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer384C1 d2WiderTransfer384S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2WiderTransfer384C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer384C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer384Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer384Arithmetic
  linarith
#print axioms d2WiderTransfer384Arithmetic
#print axioms d2WiderTransfer384Bound
def d2WiderTransfer385Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (13400781) 1 (-24))
def d2WiderTransfer385Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer385Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (23367751745919880545269) 1 (-79))
def d2WiderTransfer385C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer385S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer385C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer385S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer385Arithmetic : weightedUpper d2WiderTransfer385C0 d2Log168Lo d2Log168Hi + weightedUpper d2WiderTransfer385C1 d2Log5Lo d2Log5Hi ≤ d2WiderTransfer385Cap := by decide +kernel
theorem d2WiderTransfer385Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer385Lo:ℚ):ℝ) ((d2WiderTransfer385Hi:ℚ):ℝ), ((d2WiderTransfer385C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer385S0:ℚ):ℝ)| + ((d2WiderTransfer385C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer385S1:ℚ):ℝ)| ≤ ((d2WiderTransfer385Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer385S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385S0,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer385C0 then |x-((d2WiderTransfer385S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer385S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer385S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385S0,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385C0,d2Log168Q,d2WiderTransfer385S0,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer385C0 d2WiderTransfer385S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2WiderTransfer385S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385S1,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer385C1 then |x-((d2WiderTransfer385S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer385S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer385S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385S1,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer385C1,d2Log5Q,d2WiderTransfer385S1,d2WiderTransfer385Lo,d2WiderTransfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer385C1 d2WiderTransfer385S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2WiderTransfer385C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer385C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer385Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer385Arithmetic
  linarith
#print axioms d2WiderTransfer385Arithmetic
#print axioms d2WiderTransfer385Bound
def d2WiderTransfer386Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (13400781) 1 (-24))
def d2WiderTransfer386Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer386Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (31033649682883024012277) 1 (-79))
def d2WiderTransfer386C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (23) 25 (-5))
def d2WiderTransfer386S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer386Arithmetic : weightedUpper d2WiderTransfer386C0 d2Log169Lo d2Log169Hi ≤ d2WiderTransfer386Cap := by decide +kernel
theorem d2WiderTransfer386Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer386Lo:ℚ):ℝ) ((d2WiderTransfer386Hi:ℚ):ℝ), ((d2WiderTransfer386C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer386S0:ℚ):ℝ)| ≤ ((d2WiderTransfer386Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer386S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer386S0,d2WiderTransfer386Lo,d2WiderTransfer386Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer386C0 then |x-((d2WiderTransfer386S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer386S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer386S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer386S0,d2WiderTransfer386Lo,d2WiderTransfer386Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer386C0,d2Log169Q,d2WiderTransfer386S0,d2WiderTransfer386Lo,d2WiderTransfer386Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer386C0 d2WiderTransfer386S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2WiderTransfer386C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer386Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer386Arithmetic
  linarith
#print axioms d2WiderTransfer386Arithmetic
#print axioms d2WiderTransfer386Bound
def d2WiderTransfer387Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (13400781) 1 (-24))
def d2WiderTransfer387Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer387Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (39459143378516659160053) 1 (-79))
def d2WiderTransfer387C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (3) 275 (-5))
def d2WiderTransfer387S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer387C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-5) 11 (-4))
def d2WiderTransfer387S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer387Arithmetic : weightedUpper d2WiderTransfer387C0 d2Log169Lo d2Log169Hi + weightedUpper d2WiderTransfer387C1 d2Log5Lo d2Log5Hi ≤ d2WiderTransfer387Cap := by decide +kernel
theorem d2WiderTransfer387Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer387Lo:ℚ):ℝ) ((d2WiderTransfer387Hi:ℚ):ℝ), ((d2WiderTransfer387C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer387S0:ℚ):ℝ)| + ((d2WiderTransfer387C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer387S1:ℚ):ℝ)| ≤ ((d2WiderTransfer387Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer387S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387S0,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer387C0 then |x-((d2WiderTransfer387S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer387S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer387S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387S0,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387C0,d2Log169Q,d2WiderTransfer387S0,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer387C0 d2WiderTransfer387S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2WiderTransfer387S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387S1,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer387C1 then |x-((d2WiderTransfer387S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer387S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer387S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387S1,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer387C1,d2Log5Q,d2WiderTransfer387S1,d2WiderTransfer387Lo,d2WiderTransfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer387C1 d2WiderTransfer387S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2WiderTransfer387C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer387C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer387Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer387Arithmetic
  linarith
#print axioms d2WiderTransfer387Arithmetic
#print axioms d2WiderTransfer387Bound
def d2WiderTransfer388Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer388Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (31834725) 1 (-25))
def d2WiderTransfer388Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (70130163914806848594295) 1 (-80))
def d2WiderTransfer388C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer388S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer388C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer388S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer388Arithmetic : weightedUpper d2WiderTransfer388C0 d2Log169Lo d2Log169Hi + weightedUpper d2WiderTransfer388C1 d2Log4Lo d2Log4Hi ≤ d2WiderTransfer388Cap := by decide +kernel
theorem d2WiderTransfer388Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer388Lo:ℚ):ℝ) ((d2WiderTransfer388Hi:ℚ):ℝ), ((d2WiderTransfer388C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer388S0:ℚ):ℝ)| + ((d2WiderTransfer388C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer388S1:ℚ):ℝ)| ≤ ((d2WiderTransfer388Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer388S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388S0,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer388C0 then |x-((d2WiderTransfer388S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer388S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer388S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388S0,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388C0,d2Log169Q,d2WiderTransfer388S0,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer388C0 d2WiderTransfer388S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2WiderTransfer388S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388S1,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer388C1 then |x-((d2WiderTransfer388S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer388S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer388S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388S1,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer388C1,d2Log4Q,d2WiderTransfer388S1,d2WiderTransfer388Lo,d2WiderTransfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer388C1 d2WiderTransfer388S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2WiderTransfer388C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer388C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer388Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer388Arithmetic
  linarith
#print axioms d2WiderTransfer388Arithmetic
#print axioms d2WiderTransfer388Bound
def d2WiderTransfer389Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer389Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (31834725) 1 (-25))
def d2WiderTransfer389Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (85461959788733135528311) 1 (-80))
def d2WiderTransfer389C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (23) 25 (-5))
def d2WiderTransfer389S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer389Arithmetic : weightedUpper d2WiderTransfer389C0 d2Log170Lo d2Log170Hi ≤ d2WiderTransfer389Cap := by decide +kernel
theorem d2WiderTransfer389Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer389Lo:ℚ):ℝ) ((d2WiderTransfer389Hi:ℚ):ℝ), ((d2WiderTransfer389C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer389S0:ℚ):ℝ)| ≤ ((d2WiderTransfer389Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer389S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer389S0,d2WiderTransfer389Lo,d2WiderTransfer389Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer389C0 then |x-((d2WiderTransfer389S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer389S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer389S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer389S0,d2WiderTransfer389Lo,d2WiderTransfer389Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer389C0,d2Log170Q,d2WiderTransfer389S0,d2WiderTransfer389Lo,d2WiderTransfer389Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer389C0 d2WiderTransfer389S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2WiderTransfer389C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer389Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer389Arithmetic
  linarith
#print axioms d2WiderTransfer389Arithmetic
#print axioms d2WiderTransfer389Bound
def d2WiderTransfer390Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (7539251) 1 (-23))
def d2WiderTransfer390Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (31834725) 1 (-25))
def d2WiderTransfer390Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (102312947180000405823863) 1 (-80))
def d2WiderTransfer390C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (3) 275 (-5))
def d2WiderTransfer390S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer390C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-5) 11 (-4))
def d2WiderTransfer390S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer390Arithmetic : weightedUpper d2WiderTransfer390C0 d2Log170Lo d2Log170Hi + weightedUpper d2WiderTransfer390C1 d2Log4Lo d2Log4Hi ≤ d2WiderTransfer390Cap := by decide +kernel
theorem d2WiderTransfer390Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer390Lo:ℚ):ℝ) ((d2WiderTransfer390Hi:ℚ):ℝ), ((d2WiderTransfer390C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer390S0:ℚ):ℝ)| + ((d2WiderTransfer390C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer390S1:ℚ):ℝ)| ≤ ((d2WiderTransfer390Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer390S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390S0,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer390C0 then |x-((d2WiderTransfer390S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer390S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer390S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390S0,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390C0,d2Log170Q,d2WiderTransfer390S0,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer390C0 d2WiderTransfer390S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2WiderTransfer390S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390S1,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer390C1 then |x-((d2WiderTransfer390S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer390S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer390S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390S1,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer390C1,d2Log4Q,d2WiderTransfer390S1,d2WiderTransfer390Lo,d2WiderTransfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer390C1 d2WiderTransfer390S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2WiderTransfer390C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer390C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer390Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer390Arithmetic
  linarith
#print axioms d2WiderTransfer390Arithmetic
#print axioms d2WiderTransfer390Bound
def d2WiderTransfer391Lo : ℚ := (d2LitsNearWiderTransfers048.q2 (31834725) 1 (-25))
def d2WiderTransfer391Hi : ℚ := (d2LitsNearWiderTransfers048.q2 (65347171) 1 (-26))
def d2WiderTransfer391Cap : ℚ := (d2LitsNearWiderTransfers048.q2 (93112764016943910637209) 1 (-80))
def d2WiderTransfer391C0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer391S0 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 1 (0))
def d2WiderTransfer391C1 : ℚ := (d2LitsNearWiderTransfers048.q2 (-1) 55 (-3))
def d2WiderTransfer391S1 : ℚ := (d2LitsNearWiderTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer391Arithmetic : weightedUpper d2WiderTransfer391C0 d2Log170Lo d2Log170Hi + weightedUpper d2WiderTransfer391C1 d2Log3Lo d2Log3Hi ≤ d2WiderTransfer391Cap := by decide +kernel
theorem d2WiderTransfer391Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer391Lo:ℚ):ℝ) ((d2WiderTransfer391Hi:ℚ):ℝ), ((d2WiderTransfer391C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer391S0:ℚ):ℝ)| + ((d2WiderTransfer391C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer391S1:ℚ):ℝ)| ≤ ((d2WiderTransfer391Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer391S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391S0,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer391C0 then |x-((d2WiderTransfer391S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer391S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer391S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391S0,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391C0,d2Log170Q,d2WiderTransfer391S0,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer391C0 d2WiderTransfer391S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2WiderTransfer391S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391S1,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer391C1 then |x-((d2WiderTransfer391S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer391S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer391S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391S1,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers048.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer391C1,d2Log3Q,d2WiderTransfer391S1,d2WiderTransfer391Lo,d2WiderTransfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer391C1 d2WiderTransfer391S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2WiderTransfer391C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer391C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer391Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer391Arithmetic
  linarith
#print axioms d2WiderTransfer391Arithmetic
#print axioms d2WiderTransfer391Bound
end CatalanMeasure.GenD.Signed.Data.Cells

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
namespace d2LitsNearTransfers074
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers074
open D72.LogTransfer
def d2Transfer592Lo : ℚ := (d2LitsNearTransfers074.q2 (25123841) 1 (-25))
def d2Transfer592Hi : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer592Cap : ℚ := (d2LitsNearTransfers074.q2 (23120299455999289732387) 1 (-80))
def d2Transfer592C0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer592S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
def d2Transfer592C1 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer592S1 : ℚ := (d2LitsNearTransfers074.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer592Arithmetic : weightedUpper d2Transfer592C0 d2Log167Lo d2Log167Hi + weightedUpper d2Transfer592C1 d2Log6Lo d2Log6Hi ≤ d2Transfer592Cap := by decide +kernel
theorem d2Transfer592Bound : ∀ x ∈ Set.Icc ((d2Transfer592Lo:ℚ):ℝ) ((d2Transfer592Hi:ℚ):ℝ), ((d2Transfer592C0:ℚ):ℝ)*Real.log |x-((d2Transfer592S0:ℚ):ℝ)| + ((d2Transfer592C1:ℚ):ℝ)*Real.log |x-((d2Transfer592S1:ℚ):ℝ)| ≤ ((d2Transfer592Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer592S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592S0,d2Transfer592Lo,d2Transfer592Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer592C0 then |x-((d2Transfer592S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer592S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer592S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592S0,d2Transfer592Lo,d2Transfer592Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592C0,d2Log167Q,d2Transfer592S0,d2Transfer592Lo,d2Transfer592Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer592C0 d2Transfer592S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2Transfer592S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592S1,d2Transfer592Lo,d2Transfer592Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer592C1 then |x-((d2Transfer592S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2Transfer592S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer592S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592S1,d2Transfer592Lo,d2Transfer592Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer592C1,d2Log6Q,d2Transfer592S1,d2Transfer592Lo,d2Transfer592Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer592C1 d2Transfer592S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2Transfer592C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2Transfer592C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2Transfer592Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer592Arithmetic
  linarith
#print axioms d2Transfer592Arithmetic
#print axioms d2Transfer592Bound
def d2Transfer593Lo : ℚ := (d2LitsNearTransfers074.q2 (25123841) 1 (-25))
def d2Transfer593Hi : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer593Cap : ℚ := (d2LitsNearTransfers074.q2 (38452095329925576666403) 1 (-80))
def d2Transfer593C0 : ℚ := (d2LitsNearTransfers074.q2 (23) 25 (-5))
def d2Transfer593S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer593Arithmetic : weightedUpper d2Transfer593C0 d2Log168Lo d2Log168Hi ≤ d2Transfer593Cap := by decide +kernel
theorem d2Transfer593Bound : ∀ x ∈ Set.Icc ((d2Transfer593Lo:ℚ):ℝ) ((d2Transfer593Hi:ℚ):ℝ), ((d2Transfer593C0:ℚ):ℝ)*Real.log |x-((d2Transfer593S0:ℚ):ℝ)| ≤ ((d2Transfer593Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer593S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer593S0,d2Transfer593Lo,d2Transfer593Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer593C0 then |x-((d2Transfer593S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer593S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer593S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer593S0,d2Transfer593Lo,d2Transfer593Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer593C0,d2Log168Q,d2Transfer593S0,d2Transfer593Lo,d2Transfer593Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer593C0 d2Transfer593S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2Transfer593C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2Transfer593Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer593Arithmetic
  linarith
#print axioms d2Transfer593Arithmetic
#print axioms d2Transfer593Bound
def d2Transfer594Lo : ℚ := (d2LitsNearTransfers074.q2 (25123841) 1 (-25))
def d2Transfer594Hi : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer594Cap : ℚ := (d2LitsNearTransfers074.q2 (55303082721192846961955) 1 (-80))
def d2Transfer594C0 : ℚ := (d2LitsNearTransfers074.q2 (3) 275 (-5))
def d2Transfer594S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
def d2Transfer594C1 : ℚ := (d2LitsNearTransfers074.q2 (-5) 11 (-4))
def d2Transfer594S1 : ℚ := (d2LitsNearTransfers074.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer594Arithmetic : weightedUpper d2Transfer594C0 d2Log168Lo d2Log168Hi + weightedUpper d2Transfer594C1 d2Log6Lo d2Log6Hi ≤ d2Transfer594Cap := by decide +kernel
theorem d2Transfer594Bound : ∀ x ∈ Set.Icc ((d2Transfer594Lo:ℚ):ℝ) ((d2Transfer594Hi:ℚ):ℝ), ((d2Transfer594C0:ℚ):ℝ)*Real.log |x-((d2Transfer594S0:ℚ):ℝ)| + ((d2Transfer594C1:ℚ):ℝ)*Real.log |x-((d2Transfer594S1:ℚ):ℝ)| ≤ ((d2Transfer594Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer594S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594S0,d2Transfer594Lo,d2Transfer594Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer594C0 then |x-((d2Transfer594S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer594S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer594S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594S0,d2Transfer594Lo,d2Transfer594Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594C0,d2Log168Q,d2Transfer594S0,d2Transfer594Lo,d2Transfer594Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer594C0 d2Transfer594S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2Transfer594S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594S1,d2Transfer594Lo,d2Transfer594Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer594C1 then |x-((d2Transfer594S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2Transfer594S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer594S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594S1,d2Transfer594Lo,d2Transfer594Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer594C1,d2Log6Q,d2Transfer594S1,d2Transfer594Lo,d2Transfer594Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer594C1 d2Transfer594S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2Transfer594C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2Transfer594C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2Transfer594Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer594Arithmetic
  linarith
#print axioms d2Transfer594Arithmetic
#print axioms d2Transfer594Bound
def d2Transfer595Lo : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer595Hi : ℚ := (d2LitsNearTransfers074.q2 (7539251) 1 (-23))
def d2Transfer595Cap : ℚ := (d2LitsNearTransfers074.q2 (23367751745919880545269) 1 (-79))
def d2Transfer595C0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer595S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
def d2Transfer595C1 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer595S1 : ℚ := (d2LitsNearTransfers074.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer595Arithmetic : weightedUpper d2Transfer595C0 d2Log168Lo d2Log168Hi + weightedUpper d2Transfer595C1 d2Log5Lo d2Log5Hi ≤ d2Transfer595Cap := by decide +kernel
theorem d2Transfer595Bound : ∀ x ∈ Set.Icc ((d2Transfer595Lo:ℚ):ℝ) ((d2Transfer595Hi:ℚ):ℝ), ((d2Transfer595C0:ℚ):ℝ)*Real.log |x-((d2Transfer595S0:ℚ):ℝ)| + ((d2Transfer595C1:ℚ):ℝ)*Real.log |x-((d2Transfer595S1:ℚ):ℝ)| ≤ ((d2Transfer595Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer595S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595S0,d2Transfer595Lo,d2Transfer595Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer595C0 then |x-((d2Transfer595S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer595S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer595S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595S0,d2Transfer595Lo,d2Transfer595Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595C0,d2Log168Q,d2Transfer595S0,d2Transfer595Lo,d2Transfer595Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer595C0 d2Transfer595S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2Transfer595S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595S1,d2Transfer595Lo,d2Transfer595Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer595C1 then |x-((d2Transfer595S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2Transfer595S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer595S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595S1,d2Transfer595Lo,d2Transfer595Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer595C1,d2Log5Q,d2Transfer595S1,d2Transfer595Lo,d2Transfer595Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer595C1 d2Transfer595S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2Transfer595C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2Transfer595C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2Transfer595Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer595Arithmetic
  linarith
#print axioms d2Transfer595Arithmetic
#print axioms d2Transfer595Bound
def d2Transfer596Lo : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer596Hi : ℚ := (d2LitsNearTransfers074.q2 (7539251) 1 (-23))
def d2Transfer596Cap : ℚ := (d2LitsNearTransfers074.q2 (31033649682883024012277) 1 (-79))
def d2Transfer596C0 : ℚ := (d2LitsNearTransfers074.q2 (23) 25 (-5))
def d2Transfer596S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer596Arithmetic : weightedUpper d2Transfer596C0 d2Log169Lo d2Log169Hi ≤ d2Transfer596Cap := by decide +kernel
theorem d2Transfer596Bound : ∀ x ∈ Set.Icc ((d2Transfer596Lo:ℚ):ℝ) ((d2Transfer596Hi:ℚ):ℝ), ((d2Transfer596C0:ℚ):ℝ)*Real.log |x-((d2Transfer596S0:ℚ):ℝ)| ≤ ((d2Transfer596Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer596S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer596S0,d2Transfer596Lo,d2Transfer596Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer596C0 then |x-((d2Transfer596S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer596S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer596S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer596S0,d2Transfer596Lo,d2Transfer596Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer596C0,d2Log169Q,d2Transfer596S0,d2Transfer596Lo,d2Transfer596Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer596C0 d2Transfer596S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2Transfer596C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2Transfer596Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer596Arithmetic
  linarith
#print axioms d2Transfer596Arithmetic
#print axioms d2Transfer596Bound
def d2Transfer597Lo : ℚ := (d2LitsNearTransfers074.q2 (13400781) 1 (-24))
def d2Transfer597Hi : ℚ := (d2LitsNearTransfers074.q2 (7539251) 1 (-23))
def d2Transfer597Cap : ℚ := (d2LitsNearTransfers074.q2 (39459143378516659160053) 1 (-79))
def d2Transfer597C0 : ℚ := (d2LitsNearTransfers074.q2 (3) 275 (-5))
def d2Transfer597S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
def d2Transfer597C1 : ℚ := (d2LitsNearTransfers074.q2 (-5) 11 (-4))
def d2Transfer597S1 : ℚ := (d2LitsNearTransfers074.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer597Arithmetic : weightedUpper d2Transfer597C0 d2Log169Lo d2Log169Hi + weightedUpper d2Transfer597C1 d2Log5Lo d2Log5Hi ≤ d2Transfer597Cap := by decide +kernel
theorem d2Transfer597Bound : ∀ x ∈ Set.Icc ((d2Transfer597Lo:ℚ):ℝ) ((d2Transfer597Hi:ℚ):ℝ), ((d2Transfer597C0:ℚ):ℝ)*Real.log |x-((d2Transfer597S0:ℚ):ℝ)| + ((d2Transfer597C1:ℚ):ℝ)*Real.log |x-((d2Transfer597S1:ℚ):ℝ)| ≤ ((d2Transfer597Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer597S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597S0,d2Transfer597Lo,d2Transfer597Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer597C0 then |x-((d2Transfer597S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer597S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer597S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597S0,d2Transfer597Lo,d2Transfer597Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597C0,d2Log169Q,d2Transfer597S0,d2Transfer597Lo,d2Transfer597Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer597C0 d2Transfer597S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2Transfer597S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597S1,d2Transfer597Lo,d2Transfer597Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer597C1 then |x-((d2Transfer597S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2Transfer597S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer597S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597S1,d2Transfer597Lo,d2Transfer597Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer597C1,d2Log5Q,d2Transfer597S1,d2Transfer597Lo,d2Transfer597Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer597C1 d2Transfer597S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2Transfer597C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2Transfer597C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2Transfer597Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer597Arithmetic
  linarith
#print axioms d2Transfer597Arithmetic
#print axioms d2Transfer597Bound
def d2Transfer598Lo : ℚ := (d2LitsNearTransfers074.q2 (7539251) 1 (-23))
def d2Transfer598Hi : ℚ := (d2LitsNearTransfers074.q2 (31834725) 1 (-25))
def d2Transfer598Cap : ℚ := (d2LitsNearTransfers074.q2 (70130163914806848594295) 1 (-80))
def d2Transfer598C0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer598S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
def d2Transfer598C1 : ℚ := (d2LitsNearTransfers074.q2 (-1) 55 (-3))
def d2Transfer598S1 : ℚ := (d2LitsNearTransfers074.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer598Arithmetic : weightedUpper d2Transfer598C0 d2Log169Lo d2Log169Hi + weightedUpper d2Transfer598C1 d2Log4Lo d2Log4Hi ≤ d2Transfer598Cap := by decide +kernel
theorem d2Transfer598Bound : ∀ x ∈ Set.Icc ((d2Transfer598Lo:ℚ):ℝ) ((d2Transfer598Hi:ℚ):ℝ), ((d2Transfer598C0:ℚ):ℝ)*Real.log |x-((d2Transfer598S0:ℚ):ℝ)| + ((d2Transfer598C1:ℚ):ℝ)*Real.log |x-((d2Transfer598S1:ℚ):ℝ)| ≤ ((d2Transfer598Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer598S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598S0,d2Transfer598Lo,d2Transfer598Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer598C0 then |x-((d2Transfer598S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer598S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer598S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598S0,d2Transfer598Lo,d2Transfer598Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598C0,d2Log169Q,d2Transfer598S0,d2Transfer598Lo,d2Transfer598Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer598C0 d2Transfer598S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2Transfer598S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598S1,d2Transfer598Lo,d2Transfer598Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer598C1 then |x-((d2Transfer598S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2Transfer598S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer598S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598S1,d2Transfer598Lo,d2Transfer598Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer598C1,d2Log4Q,d2Transfer598S1,d2Transfer598Lo,d2Transfer598Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer598C1 d2Transfer598S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2Transfer598C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2Transfer598C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2Transfer598Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer598Arithmetic
  linarith
#print axioms d2Transfer598Arithmetic
#print axioms d2Transfer598Bound
def d2Transfer599Lo : ℚ := (d2LitsNearTransfers074.q2 (7539251) 1 (-23))
def d2Transfer599Hi : ℚ := (d2LitsNearTransfers074.q2 (31834725) 1 (-25))
def d2Transfer599Cap : ℚ := (d2LitsNearTransfers074.q2 (85461959788733135528311) 1 (-80))
def d2Transfer599C0 : ℚ := (d2LitsNearTransfers074.q2 (23) 25 (-5))
def d2Transfer599S0 : ℚ := (d2LitsNearTransfers074.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer599Arithmetic : weightedUpper d2Transfer599C0 d2Log170Lo d2Log170Hi ≤ d2Transfer599Cap := by decide +kernel
theorem d2Transfer599Bound : ∀ x ∈ Set.Icc ((d2Transfer599Lo:ℚ):ℝ) ((d2Transfer599Hi:ℚ):ℝ), ((d2Transfer599C0:ℚ):ℝ)*Real.log |x-((d2Transfer599S0:ℚ):ℝ)| ≤ ((d2Transfer599Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer599S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer599S0,d2Transfer599Lo,d2Transfer599Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer599C0 then |x-((d2Transfer599S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer599S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer599S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer599S0,d2Transfer599Lo,d2Transfer599Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers074.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer599C0,d2Log170Q,d2Transfer599S0,d2Transfer599Lo,d2Transfer599Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer599C0 d2Transfer599S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2Transfer599C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2Transfer599Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer599Arithmetic
  linarith
#print axioms d2Transfer599Arithmetic
#print axioms d2Transfer599Bound
end CatalanMeasure.GenD.Signed.Data.Cells

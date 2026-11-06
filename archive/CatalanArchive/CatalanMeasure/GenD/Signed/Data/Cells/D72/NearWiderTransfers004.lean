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
namespace d2LitsNearWiderTransfers004
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers004
open D72.LogTransfer
def d2WiderTransfer32Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (21768399) 1 (-25))
def d2WiderTransfer32Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (2930765) 1 (-22))
def d2WiderTransfer32Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (2194498745222390080969) 1 (-80))
def d2WiderTransfer32C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 25 (-4))
def d2WiderTransfer32S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer32Arithmetic : weightedUpper d2WiderTransfer32C0 d2Log166Lo d2Log166Hi ≤ d2WiderTransfer32Cap := by decide +kernel
theorem d2WiderTransfer32Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer32Lo:ℚ):ℝ) ((d2WiderTransfer32Hi:ℚ):ℝ), ((d2WiderTransfer32C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer32S0:ℚ):ℝ)| ≤ ((d2WiderTransfer32Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer32S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer32S0,d2WiderTransfer32Lo,d2WiderTransfer32Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer32C0 then |x-((d2WiderTransfer32S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer32S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer32S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer32S0,d2WiderTransfer32Lo,d2WiderTransfer32Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer32C0,d2Log166Q,d2WiderTransfer32S0,d2WiderTransfer32Lo,d2WiderTransfer32Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer32C0 d2WiderTransfer32S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have har : (((weightedUpper d2WiderTransfer32C0 d2Log166Lo d2Log166Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer32Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer32Arithmetic
  linarith
#print axioms d2WiderTransfer32Arithmetic
#print axioms d2WiderTransfer32Bound
def d2WiderTransfer33Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (21768399) 1 (-25))
def d2WiderTransfer33Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (2930765) 1 (-22))
def d2WiderTransfer33Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (3442141790077976831433) 1 (-80))
def d2WiderTransfer33C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 275 (-4))
def d2WiderTransfer33S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
def d2WiderTransfer33C1 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 55 (-3))
def d2WiderTransfer33S1 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer33Arithmetic : weightedUpper d2WiderTransfer33C0 d2Log166Lo d2Log166Hi + weightedUpper d2WiderTransfer33C1 d2Log8Lo d2Log8Hi ≤ d2WiderTransfer33Cap := by decide +kernel
theorem d2WiderTransfer33Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer33Lo:ℚ):ℝ) ((d2WiderTransfer33Hi:ℚ):ℝ), ((d2WiderTransfer33C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer33S0:ℚ):ℝ)| + ((d2WiderTransfer33C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer33S1:ℚ):ℝ)| ≤ ((d2WiderTransfer33Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer33S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33S0,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer33C0 then |x-((d2WiderTransfer33S0:ℚ):ℝ)| ≤ ((d2Log166Q:ℚ):ℝ) else ((d2Log166Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer33S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer33S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33S0,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33C0,d2Log166Q,d2WiderTransfer33S0,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer33C0 d2WiderTransfer33S0 d2Log166Q d2Log166Lo d2Log166Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log166Bounds
  have hn1 : x-((d2WiderTransfer33S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33S1,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer33C1 then |x-((d2WiderTransfer33S1:ℚ):ℝ)| ≤ ((d2Log8Q:ℚ):ℝ) else ((d2Log8Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer33S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer33S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33S1,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer33C1,d2Log8Q,d2WiderTransfer33S1,d2WiderTransfer33Lo,d2WiderTransfer33Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer33C1 d2WiderTransfer33S1 d2Log8Q d2Log8Lo d2Log8Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log8Bounds
  have har : (((weightedUpper d2WiderTransfer33C0 d2Log166Lo d2Log166Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer33C1 d2Log8Lo d2Log8Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer33Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer33Arithmetic
  linarith
#print axioms d2WiderTransfer33Arithmetic
#print axioms d2WiderTransfer33Bound
def d2WiderTransfer34Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (2930765) 1 (-22))
def d2WiderTransfer34Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (13400781) 1 (-24))
def d2WiderTransfer34Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (3318553540790580091593) 1 (-80))
def d2WiderTransfer34C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 25 (-4))
def d2WiderTransfer34S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer34Arithmetic : weightedUpper d2WiderTransfer34C0 d2Log168Lo d2Log168Hi ≤ d2WiderTransfer34Cap := by decide +kernel
theorem d2WiderTransfer34Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer34Lo:ℚ):ℝ) ((d2WiderTransfer34Hi:ℚ):ℝ), ((d2WiderTransfer34C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer34S0:ℚ):ℝ)| ≤ ((d2WiderTransfer34Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer34S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer34S0,d2WiderTransfer34Lo,d2WiderTransfer34Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer34C0 then |x-((d2WiderTransfer34S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer34S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer34S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer34S0,d2WiderTransfer34Lo,d2WiderTransfer34Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer34C0,d2Log168Q,d2WiderTransfer34S0,d2WiderTransfer34Lo,d2WiderTransfer34Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer34C0 d2WiderTransfer34S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2WiderTransfer34C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer34Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer34Arithmetic
  linarith
#print axioms d2WiderTransfer34Arithmetic
#print axioms d2WiderTransfer34Bound
def d2WiderTransfer35Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (2930765) 1 (-22))
def d2WiderTransfer35Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (13400781) 1 (-24))
def d2WiderTransfer35Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (4566196585646166842057) 1 (-80))
def d2WiderTransfer35C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 275 (-4))
def d2WiderTransfer35S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
def d2WiderTransfer35C1 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 55 (-3))
def d2WiderTransfer35S1 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer35Arithmetic : weightedUpper d2WiderTransfer35C0 d2Log168Lo d2Log168Hi + weightedUpper d2WiderTransfer35C1 d2Log6Lo d2Log6Hi ≤ d2WiderTransfer35Cap := by decide +kernel
theorem d2WiderTransfer35Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer35Lo:ℚ):ℝ) ((d2WiderTransfer35Hi:ℚ):ℝ), ((d2WiderTransfer35C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer35S0:ℚ):ℝ)| + ((d2WiderTransfer35C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer35S1:ℚ):ℝ)| ≤ ((d2WiderTransfer35Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer35S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35S0,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer35C0 then |x-((d2WiderTransfer35S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer35S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer35S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35S0,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35C0,d2Log168Q,d2WiderTransfer35S0,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer35C0 d2WiderTransfer35S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2WiderTransfer35S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35S1,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer35C1 then |x-((d2WiderTransfer35S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer35S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer35S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35S1,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer35C1,d2Log6Q,d2WiderTransfer35S1,d2WiderTransfer35Lo,d2WiderTransfer35Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer35C1 d2WiderTransfer35S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2WiderTransfer35C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer35C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer35Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer35Arithmetic
  linarith
#print axioms d2WiderTransfer35Arithmetic
#print axioms d2WiderTransfer35Bound
def d2WiderTransfer36Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (13400781) 1 (-24))
def d2WiderTransfer36Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (7539251) 1 (-23))
def d2WiderTransfer36Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (1305212840693843503075) 1 (-78))
def d2WiderTransfer36C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 25 (-4))
def d2WiderTransfer36S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer36Arithmetic : weightedUpper d2WiderTransfer36C0 d2Log169Lo d2Log169Hi ≤ d2WiderTransfer36Cap := by decide +kernel
theorem d2WiderTransfer36Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer36Lo:ℚ):ℝ) ((d2WiderTransfer36Hi:ℚ):ℝ), ((d2WiderTransfer36C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer36S0:ℚ):ℝ)| ≤ ((d2WiderTransfer36Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer36S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer36S0,d2WiderTransfer36Lo,d2WiderTransfer36Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer36C0 then |x-((d2WiderTransfer36S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer36S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer36S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer36S0,d2WiderTransfer36Lo,d2WiderTransfer36Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer36C0,d2Log169Q,d2WiderTransfer36S0,d2WiderTransfer36Lo,d2WiderTransfer36Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer36C0 d2WiderTransfer36S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2WiderTransfer36C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer36Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer36Arithmetic
  linarith
#print axioms d2WiderTransfer36Arithmetic
#print axioms d2WiderTransfer36Bound
def d2WiderTransfer37Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (13400781) 1 (-24))
def d2WiderTransfer37Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (7539251) 1 (-23))
def d2WiderTransfer37Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (1617123601907740190691) 1 (-78))
def d2WiderTransfer37C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 275 (-4))
def d2WiderTransfer37S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
def d2WiderTransfer37C1 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 55 (-3))
def d2WiderTransfer37S1 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer37Arithmetic : weightedUpper d2WiderTransfer37C0 d2Log169Lo d2Log169Hi + weightedUpper d2WiderTransfer37C1 d2Log5Lo d2Log5Hi ≤ d2WiderTransfer37Cap := by decide +kernel
theorem d2WiderTransfer37Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer37Lo:ℚ):ℝ) ((d2WiderTransfer37Hi:ℚ):ℝ), ((d2WiderTransfer37C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer37S0:ℚ):ℝ)| + ((d2WiderTransfer37C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer37S1:ℚ):ℝ)| ≤ ((d2WiderTransfer37Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer37S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37S0,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer37C0 then |x-((d2WiderTransfer37S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer37S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer37S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37S0,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37C0,d2Log169Q,d2WiderTransfer37S0,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer37C0 d2WiderTransfer37S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2WiderTransfer37S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37S1,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer37C1 then |x-((d2WiderTransfer37S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer37S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer37S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37S1,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer37C1,d2Log5Q,d2WiderTransfer37S1,d2WiderTransfer37Lo,d2WiderTransfer37Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer37C1 d2WiderTransfer37S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2WiderTransfer37C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer37C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer37Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer37Arithmetic
  linarith
#print axioms d2WiderTransfer37Arithmetic
#print axioms d2WiderTransfer37Bound
def d2WiderTransfer38Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (7539251) 1 (-23))
def d2WiderTransfer38Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (31834725) 1 (-25))
def d2WiderTransfer38Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (110917324485095330623) 1 (-74))
def d2WiderTransfer38C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 25 (-4))
def d2WiderTransfer38S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer38Arithmetic : weightedUpper d2WiderTransfer38C0 d2Log170Lo d2Log170Hi ≤ d2WiderTransfer38Cap := by decide +kernel
theorem d2WiderTransfer38Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer38Lo:ℚ):ℝ) ((d2WiderTransfer38Hi:ℚ):ℝ), ((d2WiderTransfer38C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer38S0:ℚ):ℝ)| ≤ ((d2WiderTransfer38Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer38S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer38S0,d2WiderTransfer38Lo,d2WiderTransfer38Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer38C0 then |x-((d2WiderTransfer38S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer38S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer38S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer38S0,d2WiderTransfer38Lo,d2WiderTransfer38Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer38C0,d2Log170Q,d2WiderTransfer38S0,d2WiderTransfer38Lo,d2WiderTransfer38Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer38C0 d2WiderTransfer38S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2WiderTransfer38C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer38Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer38Arithmetic
  linarith
#print axioms d2WiderTransfer38Arithmetic
#print axioms d2WiderTransfer38Bound
def d2WiderTransfer39Lo : ℚ := (d2LitsNearWiderTransfers004.q2 (7539251) 1 (-23))
def d2WiderTransfer39Hi : ℚ := (d2LitsNearWiderTransfers004.q2 (31834725) 1 (-25))
def d2WiderTransfer39Cap : ℚ := (d2LitsNearWiderTransfers004.q2 (130411747060963873599) 1 (-74))
def d2WiderTransfer39C0 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 275 (-4))
def d2WiderTransfer39S0 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 1 (0))
def d2WiderTransfer39C1 : ℚ := (d2LitsNearWiderTransfers004.q2 (-1) 55 (-3))
def d2WiderTransfer39S1 : ℚ := (d2LitsNearWiderTransfers004.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer39Arithmetic : weightedUpper d2WiderTransfer39C0 d2Log170Lo d2Log170Hi + weightedUpper d2WiderTransfer39C1 d2Log4Lo d2Log4Hi ≤ d2WiderTransfer39Cap := by decide +kernel
theorem d2WiderTransfer39Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer39Lo:ℚ):ℝ) ((d2WiderTransfer39Hi:ℚ):ℝ), ((d2WiderTransfer39C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer39S0:ℚ):ℝ)| + ((d2WiderTransfer39C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer39S1:ℚ):ℝ)| ≤ ((d2WiderTransfer39Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer39S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39S0,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer39C0 then |x-((d2WiderTransfer39S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer39S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer39S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39S0,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39C0,d2Log170Q,d2WiderTransfer39S0,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer39C0 d2WiderTransfer39S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2WiderTransfer39S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39S1,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer39C1 then |x-((d2WiderTransfer39S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer39S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer39S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39S1,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers004.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer39C1,d2Log4Q,d2WiderTransfer39S1,d2WiderTransfer39Lo,d2WiderTransfer39Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer39C1 d2WiderTransfer39S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2WiderTransfer39C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer39C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer39Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer39Arithmetic
  linarith
#print axioms d2WiderTransfer39Arithmetic
#print axioms d2WiderTransfer39Bound
end CatalanMeasure.GenD.Signed.Data.Cells

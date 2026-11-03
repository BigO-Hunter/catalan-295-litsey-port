module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers019
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers019
open D72.LogTransfer
def d2WiderTransfer152Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (41859077) 1 (-26))
def d2WiderTransfer152Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer152Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (18944686365821006639269) 1 (-80))
def d2WiderTransfer152C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (-5))
def d2WiderTransfer152S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer152Arithmetic : weightedUpper d2WiderTransfer152C0 d2Log140Lo d2Log140Hi ≤ d2WiderTransfer152Cap := by decide +kernel
theorem d2WiderTransfer152Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer152Lo:ℚ):ℝ) ((d2WiderTransfer152Hi:ℚ):ℝ), ((d2WiderTransfer152C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer152S0:ℚ):ℝ)| ≤ ((d2WiderTransfer152Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer152S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer152S0,d2WiderTransfer152Lo,d2WiderTransfer152Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer152C0 then |x-((d2WiderTransfer152S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer152S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer152S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer152S0,d2WiderTransfer152Lo,d2WiderTransfer152Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer152C0,d2Log140Q,d2WiderTransfer152S0,d2WiderTransfer152Lo,d2WiderTransfer152Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer152C0 d2WiderTransfer152S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have har : (((weightedUpper d2WiderTransfer152C0 d2Log140Lo d2Log140Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer152Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer152Arithmetic
  linarith
#print axioms d2WiderTransfer152Arithmetic
#print axioms d2WiderTransfer152Bound
def d2WiderTransfer153Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (41859077) 1 (-26))
def d2WiderTransfer153Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer153Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (35309523688112514003109) 1 (-80))
def d2WiderTransfer153C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 11 (-5))
def d2WiderTransfer153S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
def d2WiderTransfer153C1 : ℚ := (d2LitsNearWiderTransfers019.q2 (-5) 11 (-4))
def d2WiderTransfer153S1 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer153Arithmetic : weightedUpper d2WiderTransfer153C0 d2Log140Lo d2Log140Hi + weightedUpper d2WiderTransfer153C1 d2Log34Lo d2Log34Hi ≤ d2WiderTransfer153Cap := by decide +kernel
theorem d2WiderTransfer153Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer153Lo:ℚ):ℝ) ((d2WiderTransfer153Hi:ℚ):ℝ), ((d2WiderTransfer153C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer153S0:ℚ):ℝ)| + ((d2WiderTransfer153C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer153S1:ℚ):ℝ)| ≤ ((d2WiderTransfer153Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer153S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153S0,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer153C0 then |x-((d2WiderTransfer153S0:ℚ):ℝ)| ≤ ((d2Log140Q:ℚ):ℝ) else ((d2Log140Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer153S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer153S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153S0,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153C0,d2Log140Q,d2WiderTransfer153S0,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer153C0 d2WiderTransfer153S0 d2Log140Q d2Log140Lo d2Log140Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log140Bounds
  have hn1 : x-((d2WiderTransfer153S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153S1,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer153C1 then |x-((d2WiderTransfer153S1:ℚ):ℝ)| ≤ ((d2Log34Q:ℚ):ℝ) else ((d2Log34Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer153S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer153S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153S1,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer153C1,d2Log34Q,d2WiderTransfer153S1,d2WiderTransfer153Lo,d2WiderTransfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer153C1 d2WiderTransfer153S1 d2Log34Q d2Log34Lo d2Log34Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log34Bounds
  have har : (((weightedUpper d2WiderTransfer153C0 d2Log140Lo d2Log140Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer153C1 d2Log34Lo d2Log34Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer153Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer153Arithmetic
  linarith
#print axioms d2WiderTransfer153Arithmetic
#print axioms d2WiderTransfer153Bound
def d2WiderTransfer154Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer154Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer154Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (318063906175397004093) 1 (-77))
def d2WiderTransfer154C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 25 (-4))
def d2WiderTransfer154S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer154Arithmetic : weightedUpper d2WiderTransfer154C0 d2Log141Lo d2Log141Hi ≤ d2WiderTransfer154Cap := by decide +kernel
theorem d2WiderTransfer154Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer154Lo:ℚ):ℝ) ((d2WiderTransfer154Hi:ℚ):ℝ), ((d2WiderTransfer154C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer154S0:ℚ):ℝ)| ≤ ((d2WiderTransfer154Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer154S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer154S0,d2WiderTransfer154Lo,d2WiderTransfer154Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer154C0 then |x-((d2WiderTransfer154S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer154S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer154S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer154S0,d2WiderTransfer154Lo,d2WiderTransfer154Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer154C0,d2Log141Q,d2WiderTransfer154S0,d2WiderTransfer154Lo,d2WiderTransfer154Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer154C0 d2WiderTransfer154S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2WiderTransfer154C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer154Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer154Arithmetic
  linarith
#print axioms d2WiderTransfer154Arithmetic
#print axioms d2WiderTransfer154Bound
def d2WiderTransfer155Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer155Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer155Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (474351427254863921981) 1 (-77))
def d2WiderTransfer155C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 275 (-4))
def d2WiderTransfer155S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
def d2WiderTransfer155C1 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 55 (-3))
def d2WiderTransfer155S1 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer155Arithmetic : weightedUpper d2WiderTransfer155C0 d2Log141Lo d2Log141Hi + weightedUpper d2WiderTransfer155C1 d2Log33Lo d2Log33Hi ≤ d2WiderTransfer155Cap := by decide +kernel
theorem d2WiderTransfer155Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer155Lo:ℚ):ℝ) ((d2WiderTransfer155Hi:ℚ):ℝ), ((d2WiderTransfer155C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer155S0:ℚ):ℝ)| + ((d2WiderTransfer155C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer155S1:ℚ):ℝ)| ≤ ((d2WiderTransfer155Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer155S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155S0,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer155C0 then |x-((d2WiderTransfer155S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer155S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer155S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155S0,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155C0,d2Log141Q,d2WiderTransfer155S0,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer155C0 d2WiderTransfer155S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2WiderTransfer155S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155S1,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer155C1 then |x-((d2WiderTransfer155S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer155S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer155S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155S1,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer155C1,d2Log33Q,d2WiderTransfer155S1,d2WiderTransfer155Lo,d2WiderTransfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer155C1 d2WiderTransfer155S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2WiderTransfer155C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer155C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer155Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer155Arithmetic
  linarith
#print axioms d2WiderTransfer155Arithmetic
#print axioms d2WiderTransfer155Bound
def d2WiderTransfer156Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer156Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer156Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (2377234188557733987133) 1 (-77))
def d2WiderTransfer156C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (-5))
def d2WiderTransfer156S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer156Arithmetic : weightedUpper d2WiderTransfer156C0 d2Log141Lo d2Log141Hi ≤ d2WiderTransfer156Cap := by decide +kernel
theorem d2WiderTransfer156Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer156Lo:ℚ):ℝ) ((d2WiderTransfer156Hi:ℚ):ℝ), ((d2WiderTransfer156C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer156S0:ℚ):ℝ)| ≤ ((d2WiderTransfer156Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer156S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer156S0,d2WiderTransfer156Lo,d2WiderTransfer156Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer156C0 then |x-((d2WiderTransfer156S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer156S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer156S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer156S0,d2WiderTransfer156Lo,d2WiderTransfer156Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer156C0,d2Log141Q,d2WiderTransfer156S0,d2WiderTransfer156Lo,d2WiderTransfer156Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer156C0 d2WiderTransfer156S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2WiderTransfer156C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer156Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer156Arithmetic
  linarith
#print axioms d2WiderTransfer156Arithmetic
#print axioms d2WiderTransfer156Bound
def d2WiderTransfer157Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (1341168185) 1 (-31))
def d2WiderTransfer157Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer157Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (4422838853844172407613) 1 (-77))
def d2WiderTransfer157C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 11 (-5))
def d2WiderTransfer157S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
def d2WiderTransfer157C1 : ℚ := (d2LitsNearWiderTransfers019.q2 (-5) 11 (-4))
def d2WiderTransfer157S1 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer157Arithmetic : weightedUpper d2WiderTransfer157C0 d2Log141Lo d2Log141Hi + weightedUpper d2WiderTransfer157C1 d2Log33Lo d2Log33Hi ≤ d2WiderTransfer157Cap := by decide +kernel
theorem d2WiderTransfer157Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer157Lo:ℚ):ℝ) ((d2WiderTransfer157Hi:ℚ):ℝ), ((d2WiderTransfer157C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer157S0:ℚ):ℝ)| + ((d2WiderTransfer157C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer157S1:ℚ):ℝ)| ≤ ((d2WiderTransfer157Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer157S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157S0,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer157C0 then |x-((d2WiderTransfer157S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer157S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer157S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157S0,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157C0,d2Log141Q,d2WiderTransfer157S0,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer157C0 d2WiderTransfer157S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2WiderTransfer157S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157S1,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer157C1 then |x-((d2WiderTransfer157S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer157S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer157S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157S1,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer157C1,d2Log33Q,d2WiderTransfer157S1,d2WiderTransfer157Lo,d2WiderTransfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer157C1 d2WiderTransfer157S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2WiderTransfer157C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer157C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer157Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer157Arithmetic
  linarith
#print axioms d2WiderTransfer157Arithmetic
#print axioms d2WiderTransfer157Bound
def d2WiderTransfer158Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer158Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (1344523627) 1 (-31))
def d2WiderTransfer158Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (2617846911167768580485) 1 (-80))
def d2WiderTransfer158C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 25 (-4))
def d2WiderTransfer158S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer158Arithmetic : weightedUpper d2WiderTransfer158C0 d2Log142Lo d2Log142Hi ≤ d2WiderTransfer158Cap := by decide +kernel
theorem d2WiderTransfer158Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer158Lo:ℚ):ℝ) ((d2WiderTransfer158Hi:ℚ):ℝ), ((d2WiderTransfer158C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer158S0:ℚ):ℝ)| ≤ ((d2WiderTransfer158Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer158S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer158S0,d2WiderTransfer158Lo,d2WiderTransfer158Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer158C0 then |x-((d2WiderTransfer158S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer158S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer158S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer158S0,d2WiderTransfer158Lo,d2WiderTransfer158Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer158C0,d2Log142Q,d2WiderTransfer158S0,d2WiderTransfer158Lo,d2WiderTransfer158Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer158C0 d2WiderTransfer158S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2WiderTransfer158C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer158Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer158Arithmetic
  linarith
#print axioms d2WiderTransfer158Arithmetic
#print axioms d2WiderTransfer158Bound
def d2WiderTransfer159Lo : ℚ := (d2LitsNearWiderTransfers019.q2 (671422953) 1 (-30))
def d2WiderTransfer159Hi : ℚ := (d2LitsNearWiderTransfers019.q2 (1344523627) 1 (-31))
def d2WiderTransfer159Cap : ℚ := (d2LitsNearWiderTransfers019.q2 (3868147079803503923589) 1 (-80))
def d2WiderTransfer159C0 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 275 (-4))
def d2WiderTransfer159S0 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 1 (0))
def d2WiderTransfer159C1 : ℚ := (d2LitsNearWiderTransfers019.q2 (-1) 55 (-3))
def d2WiderTransfer159S1 : ℚ := (d2LitsNearWiderTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer159Arithmetic : weightedUpper d2WiderTransfer159C0 d2Log142Lo d2Log142Hi + weightedUpper d2WiderTransfer159C1 d2Log32Lo d2Log32Hi ≤ d2WiderTransfer159Cap := by decide +kernel
theorem d2WiderTransfer159Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer159Lo:ℚ):ℝ) ((d2WiderTransfer159Hi:ℚ):ℝ), ((d2WiderTransfer159C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer159S0:ℚ):ℝ)| + ((d2WiderTransfer159C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer159S1:ℚ):ℝ)| ≤ ((d2WiderTransfer159Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer159S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159S0,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer159C0 then |x-((d2WiderTransfer159S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer159S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer159S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159S0,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159C0,d2Log142Q,d2WiderTransfer159S0,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer159C0 d2WiderTransfer159S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2WiderTransfer159S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159S1,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer159C1 then |x-((d2WiderTransfer159S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer159S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer159S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159S1,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers019.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer159C1,d2Log32Q,d2WiderTransfer159S1,d2WiderTransfer159Lo,d2WiderTransfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer159C1 d2WiderTransfer159S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2WiderTransfer159C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer159C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer159Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer159Arithmetic
  linarith
#print axioms d2WiderTransfer159Arithmetic
#print axioms d2WiderTransfer159Bound
end CatalanMeasure.GenD.Signed.Data.Cells

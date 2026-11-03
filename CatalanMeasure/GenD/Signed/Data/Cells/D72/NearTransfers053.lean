module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers053
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers053
open D72.LogTransfer
def d2Transfer424Lo : ℚ := (d2LitsNearTransfers053.q2 (21642477) 1 (-27))
def d2Transfer424Hi : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer424Cap : ℚ := (d2LitsNearTransfers053.q2 (1169469059) 1 (-40))
def d2Transfer424C0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer424S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
def d2Transfer424C1 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer424S1 : ℚ := (d2LitsNearTransfers053.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer424Arithmetic : weightedUpper d2Transfer424C0 d2Log101Lo d2Log101Hi + weightedUpper d2Transfer424C1 d2Log72Lo d2Log72Hi ≤ d2Transfer424Cap := by decide +kernel
theorem d2Transfer424Bound : ∀ x ∈ Set.Icc ((d2Transfer424Lo:ℚ):ℝ) ((d2Transfer424Hi:ℚ):ℝ), ((d2Transfer424C0:ℚ):ℝ)*Real.log |x-((d2Transfer424S0:ℚ):ℝ)| + ((d2Transfer424C1:ℚ):ℝ)*Real.log |x-((d2Transfer424S1:ℚ):ℝ)| ≤ ((d2Transfer424Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer424S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424S0,d2Transfer424Lo,d2Transfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer424C0 then |x-((d2Transfer424S0:ℚ):ℝ)| ≤ ((d2Log101Q:ℚ):ℝ) else ((d2Log101Q:ℚ):ℝ) ≤ |x-((d2Transfer424S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer424S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424S0,d2Transfer424Lo,d2Transfer424Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424C0,d2Log101Q,d2Transfer424S0,d2Transfer424Lo,d2Transfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer424C0 d2Transfer424S0 d2Log101Q d2Log101Lo d2Log101Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log101Bounds
  have hn1 : x-((d2Transfer424S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424S1,d2Transfer424Lo,d2Transfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer424C1 then |x-((d2Transfer424S1:ℚ):ℝ)| ≤ ((d2Log72Q:ℚ):ℝ) else ((d2Log72Q:ℚ):ℝ) ≤ |x-((d2Transfer424S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer424S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424S1,d2Transfer424Lo,d2Transfer424Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer424C1,d2Log72Q,d2Transfer424S1,d2Transfer424Lo,d2Transfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer424C1 d2Transfer424S1 d2Log72Q d2Log72Lo d2Log72Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log72Bounds
  have har : (((weightedUpper d2Transfer424C0 d2Log101Lo d2Log101Hi:ℚ):ℝ) + ((weightedUpper d2Transfer424C1 d2Log72Lo d2Log72Hi:ℚ):ℝ)) ≤ ((d2Transfer424Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer424Arithmetic
  linarith
#print axioms d2Transfer424Arithmetic
#print axioms d2Transfer424Bound
def d2Transfer425Lo : ℚ := (d2LitsNearTransfers053.q2 (21642477) 1 (-27))
def d2Transfer425Hi : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer425Cap : ℚ := (d2LitsNearTransfers053.q2 (15113656175) 1 (-40))
def d2Transfer425C0 : ℚ := (d2LitsNearTransfers053.q2 (23) 25 (-5))
def d2Transfer425S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer425Arithmetic : weightedUpper d2Transfer425C0 d2Log102Lo d2Log102Hi ≤ d2Transfer425Cap := by decide +kernel
theorem d2Transfer425Bound : ∀ x ∈ Set.Icc ((d2Transfer425Lo:ℚ):ℝ) ((d2Transfer425Hi:ℚ):ℝ), ((d2Transfer425C0:ℚ):ℝ)*Real.log |x-((d2Transfer425S0:ℚ):ℝ)| ≤ ((d2Transfer425Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer425S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer425S0,d2Transfer425Lo,d2Transfer425Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer425C0 then |x-((d2Transfer425S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer425S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer425S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer425S0,d2Transfer425Lo,d2Transfer425Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer425C0,d2Log102Q,d2Transfer425S0,d2Transfer425Lo,d2Transfer425Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer425C0 d2Transfer425S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have har : (((weightedUpper d2Transfer425C0 d2Log102Lo d2Log102Hi:ℚ):ℝ)) ≤ ((d2Transfer425Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer425Arithmetic
  linarith
#print axioms d2Transfer425Arithmetic
#print axioms d2Transfer425Bound
def d2Transfer426Lo : ℚ := (d2LitsNearTransfers053.q2 (21642477) 1 (-27))
def d2Transfer426Hi : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer426Cap : ℚ := (d2LitsNearTransfers053.q2 (30439539927) 1 (-40))
def d2Transfer426C0 : ℚ := (d2LitsNearTransfers053.q2 (3) 275 (-5))
def d2Transfer426S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
def d2Transfer426C1 : ℚ := (d2LitsNearTransfers053.q2 (-5) 11 (-4))
def d2Transfer426S1 : ℚ := (d2LitsNearTransfers053.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer426Arithmetic : weightedUpper d2Transfer426C0 d2Log102Lo d2Log102Hi + weightedUpper d2Transfer426C1 d2Log72Lo d2Log72Hi ≤ d2Transfer426Cap := by decide +kernel
theorem d2Transfer426Bound : ∀ x ∈ Set.Icc ((d2Transfer426Lo:ℚ):ℝ) ((d2Transfer426Hi:ℚ):ℝ), ((d2Transfer426C0:ℚ):ℝ)*Real.log |x-((d2Transfer426S0:ℚ):ℝ)| + ((d2Transfer426C1:ℚ):ℝ)*Real.log |x-((d2Transfer426S1:ℚ):ℝ)| ≤ ((d2Transfer426Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer426S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426S0,d2Transfer426Lo,d2Transfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer426C0 then |x-((d2Transfer426S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer426S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer426S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426S0,d2Transfer426Lo,d2Transfer426Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426C0,d2Log102Q,d2Transfer426S0,d2Transfer426Lo,d2Transfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer426C0 d2Transfer426S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have hn1 : x-((d2Transfer426S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426S1,d2Transfer426Lo,d2Transfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer426C1 then |x-((d2Transfer426S1:ℚ):ℝ)| ≤ ((d2Log72Q:ℚ):ℝ) else ((d2Log72Q:ℚ):ℝ) ≤ |x-((d2Transfer426S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer426S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426S1,d2Transfer426Lo,d2Transfer426Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer426C1,d2Log72Q,d2Transfer426S1,d2Transfer426Lo,d2Transfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer426C1 d2Transfer426S1 d2Log72Q d2Log72Lo d2Log72Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log72Bounds
  have har : (((weightedUpper d2Transfer426C0 d2Log102Lo d2Log102Hi:ℚ):ℝ) + ((weightedUpper d2Transfer426C1 d2Log72Lo d2Log72Hi:ℚ):ℝ)) ≤ ((d2Transfer426Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer426Arithmetic
  linarith
#print axioms d2Transfer426Arithmetic
#print axioms d2Transfer426Bound
def d2Transfer427Lo : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer427Hi : ℚ := (d2LitsNearTransfers053.q2 (11660099) 1 (-26))
def d2Transfer427Cap : ℚ := (d2LitsNearTransfers053.q2 (1169469059) 1 (-40))
def d2Transfer427C0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer427S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
def d2Transfer427C1 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer427S1 : ℚ := (d2LitsNearTransfers053.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer427Arithmetic : weightedUpper d2Transfer427C0 d2Log102Lo d2Log102Hi + weightedUpper d2Transfer427C1 d2Log71Lo d2Log71Hi ≤ d2Transfer427Cap := by decide +kernel
theorem d2Transfer427Bound : ∀ x ∈ Set.Icc ((d2Transfer427Lo:ℚ):ℝ) ((d2Transfer427Hi:ℚ):ℝ), ((d2Transfer427C0:ℚ):ℝ)*Real.log |x-((d2Transfer427S0:ℚ):ℝ)| + ((d2Transfer427C1:ℚ):ℝ)*Real.log |x-((d2Transfer427S1:ℚ):ℝ)| ≤ ((d2Transfer427Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer427S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427S0,d2Transfer427Lo,d2Transfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer427C0 then |x-((d2Transfer427S0:ℚ):ℝ)| ≤ ((d2Log102Q:ℚ):ℝ) else ((d2Log102Q:ℚ):ℝ) ≤ |x-((d2Transfer427S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer427S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427S0,d2Transfer427Lo,d2Transfer427Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427C0,d2Log102Q,d2Transfer427S0,d2Transfer427Lo,d2Transfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer427C0 d2Transfer427S0 d2Log102Q d2Log102Lo d2Log102Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log102Bounds
  have hn1 : x-((d2Transfer427S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427S1,d2Transfer427Lo,d2Transfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer427C1 then |x-((d2Transfer427S1:ℚ):ℝ)| ≤ ((d2Log71Q:ℚ):ℝ) else ((d2Log71Q:ℚ):ℝ) ≤ |x-((d2Transfer427S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer427S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427S1,d2Transfer427Lo,d2Transfer427Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer427C1,d2Log71Q,d2Transfer427S1,d2Transfer427Lo,d2Transfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer427C1 d2Transfer427S1 d2Log71Q d2Log71Lo d2Log71Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log71Bounds
  have har : (((weightedUpper d2Transfer427C0 d2Log102Lo d2Log102Hi:ℚ):ℝ) + ((weightedUpper d2Transfer427C1 d2Log71Lo d2Log71Hi:ℚ):ℝ)) ≤ ((d2Transfer427Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer427Arithmetic
  linarith
#print axioms d2Transfer427Arithmetic
#print axioms d2Transfer427Bound
def d2Transfer428Lo : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer428Hi : ℚ := (d2LitsNearTransfers053.q2 (11660099) 1 (-26))
def d2Transfer428Cap : ℚ := (d2LitsNearTransfers053.q2 (15113656175) 1 (-40))
def d2Transfer428C0 : ℚ := (d2LitsNearTransfers053.q2 (23) 25 (-5))
def d2Transfer428S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer428Arithmetic : weightedUpper d2Transfer428C0 d2Log103Lo d2Log103Hi ≤ d2Transfer428Cap := by decide +kernel
theorem d2Transfer428Bound : ∀ x ∈ Set.Icc ((d2Transfer428Lo:ℚ):ℝ) ((d2Transfer428Hi:ℚ):ℝ), ((d2Transfer428C0:ℚ):ℝ)*Real.log |x-((d2Transfer428S0:ℚ):ℝ)| ≤ ((d2Transfer428Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer428S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer428S0,d2Transfer428Lo,d2Transfer428Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer428C0 then |x-((d2Transfer428S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer428S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer428S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer428S0,d2Transfer428Lo,d2Transfer428Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer428C0,d2Log103Q,d2Transfer428S0,d2Transfer428Lo,d2Transfer428Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer428C0 d2Transfer428S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have har : (((weightedUpper d2Transfer428C0 d2Log103Lo d2Log103Hi:ℚ):ℝ)) ≤ ((d2Transfer428Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer428Arithmetic
  linarith
#print axioms d2Transfer428Arithmetic
#print axioms d2Transfer428Bound
def d2Transfer429Lo : ℚ := (d2LitsNearTransfers053.q2 (44962675) 1 (-28))
def d2Transfer429Hi : ℚ := (d2LitsNearTransfers053.q2 (11660099) 1 (-26))
def d2Transfer429Cap : ℚ := (d2LitsNearTransfers053.q2 (30439539927) 1 (-40))
def d2Transfer429C0 : ℚ := (d2LitsNearTransfers053.q2 (3) 275 (-5))
def d2Transfer429S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
def d2Transfer429C1 : ℚ := (d2LitsNearTransfers053.q2 (-5) 11 (-4))
def d2Transfer429S1 : ℚ := (d2LitsNearTransfers053.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer429Arithmetic : weightedUpper d2Transfer429C0 d2Log103Lo d2Log103Hi + weightedUpper d2Transfer429C1 d2Log71Lo d2Log71Hi ≤ d2Transfer429Cap := by decide +kernel
theorem d2Transfer429Bound : ∀ x ∈ Set.Icc ((d2Transfer429Lo:ℚ):ℝ) ((d2Transfer429Hi:ℚ):ℝ), ((d2Transfer429C0:ℚ):ℝ)*Real.log |x-((d2Transfer429S0:ℚ):ℝ)| + ((d2Transfer429C1:ℚ):ℝ)*Real.log |x-((d2Transfer429S1:ℚ):ℝ)| ≤ ((d2Transfer429Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer429S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429S0,d2Transfer429Lo,d2Transfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer429C0 then |x-((d2Transfer429S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer429S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer429S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429S0,d2Transfer429Lo,d2Transfer429Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429C0,d2Log103Q,d2Transfer429S0,d2Transfer429Lo,d2Transfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer429C0 d2Transfer429S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have hn1 : x-((d2Transfer429S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429S1,d2Transfer429Lo,d2Transfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer429C1 then |x-((d2Transfer429S1:ℚ):ℝ)| ≤ ((d2Log71Q:ℚ):ℝ) else ((d2Log71Q:ℚ):ℝ) ≤ |x-((d2Transfer429S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer429S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429S1,d2Transfer429Lo,d2Transfer429Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer429C1,d2Log71Q,d2Transfer429S1,d2Transfer429Lo,d2Transfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer429C1 d2Transfer429S1 d2Log71Q d2Log71Lo d2Log71Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log71Bounds
  have har : (((weightedUpper d2Transfer429C0 d2Log103Lo d2Log103Hi:ℚ):ℝ) + ((weightedUpper d2Transfer429C1 d2Log71Lo d2Log71Hi:ℚ):ℝ)) ≤ ((d2Transfer429Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer429Arithmetic
  linarith
#print axioms d2Transfer429Arithmetic
#print axioms d2Transfer429Bound
def d2Transfer430Lo : ℚ := (d2LitsNearTransfers053.q2 (11660099) 1 (-26))
def d2Transfer430Hi : ℚ := (d2LitsNearTransfers053.q2 (48318117) 1 (-28))
def d2Transfer430Cap : ℚ := (d2LitsNearTransfers053.q2 (1169469059) 1 (-40))
def d2Transfer430C0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer430S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
def d2Transfer430C1 : ℚ := (d2LitsNearTransfers053.q2 (-1) 55 (-3))
def d2Transfer430S1 : ℚ := (d2LitsNearTransfers053.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer430Arithmetic : weightedUpper d2Transfer430C0 d2Log103Lo d2Log103Hi + weightedUpper d2Transfer430C1 d2Log70Lo d2Log70Hi ≤ d2Transfer430Cap := by decide +kernel
theorem d2Transfer430Bound : ∀ x ∈ Set.Icc ((d2Transfer430Lo:ℚ):ℝ) ((d2Transfer430Hi:ℚ):ℝ), ((d2Transfer430C0:ℚ):ℝ)*Real.log |x-((d2Transfer430S0:ℚ):ℝ)| + ((d2Transfer430C1:ℚ):ℝ)*Real.log |x-((d2Transfer430S1:ℚ):ℝ)| ≤ ((d2Transfer430Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer430S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430S0,d2Transfer430Lo,d2Transfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer430C0 then |x-((d2Transfer430S0:ℚ):ℝ)| ≤ ((d2Log103Q:ℚ):ℝ) else ((d2Log103Q:ℚ):ℝ) ≤ |x-((d2Transfer430S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer430S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430S0,d2Transfer430Lo,d2Transfer430Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430C0,d2Log103Q,d2Transfer430S0,d2Transfer430Lo,d2Transfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer430C0 d2Transfer430S0 d2Log103Q d2Log103Lo d2Log103Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log103Bounds
  have hn1 : x-((d2Transfer430S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430S1,d2Transfer430Lo,d2Transfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer430C1 then |x-((d2Transfer430S1:ℚ):ℝ)| ≤ ((d2Log70Q:ℚ):ℝ) else ((d2Log70Q:ℚ):ℝ) ≤ |x-((d2Transfer430S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer430S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430S1,d2Transfer430Lo,d2Transfer430Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer430C1,d2Log70Q,d2Transfer430S1,d2Transfer430Lo,d2Transfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer430C1 d2Transfer430S1 d2Log70Q d2Log70Lo d2Log70Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log70Bounds
  have har : (((weightedUpper d2Transfer430C0 d2Log103Lo d2Log103Hi:ℚ):ℝ) + ((weightedUpper d2Transfer430C1 d2Log70Lo d2Log70Hi:ℚ):ℝ)) ≤ ((d2Transfer430Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer430Arithmetic
  linarith
#print axioms d2Transfer430Arithmetic
#print axioms d2Transfer430Bound
def d2Transfer431Lo : ℚ := (d2LitsNearTransfers053.q2 (11660099) 1 (-26))
def d2Transfer431Hi : ℚ := (d2LitsNearTransfers053.q2 (48318117) 1 (-28))
def d2Transfer431Cap : ℚ := (d2LitsNearTransfers053.q2 (15113656175) 1 (-40))
def d2Transfer431C0 : ℚ := (d2LitsNearTransfers053.q2 (23) 25 (-5))
def d2Transfer431S0 : ℚ := (d2LitsNearTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer431Arithmetic : weightedUpper d2Transfer431C0 d2Log104Lo d2Log104Hi ≤ d2Transfer431Cap := by decide +kernel
theorem d2Transfer431Bound : ∀ x ∈ Set.Icc ((d2Transfer431Lo:ℚ):ℝ) ((d2Transfer431Hi:ℚ):ℝ), ((d2Transfer431C0:ℚ):ℝ)*Real.log |x-((d2Transfer431S0:ℚ):ℝ)| ≤ ((d2Transfer431Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer431S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer431S0,d2Transfer431Lo,d2Transfer431Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer431C0 then |x-((d2Transfer431S0:ℚ):ℝ)| ≤ ((d2Log104Q:ℚ):ℝ) else ((d2Log104Q:ℚ):ℝ) ≤ |x-((d2Transfer431S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer431S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer431S0,d2Transfer431Lo,d2Transfer431Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers053.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer431C0,d2Log104Q,d2Transfer431S0,d2Transfer431Lo,d2Transfer431Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer431C0 d2Transfer431S0 d2Log104Q d2Log104Lo d2Log104Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log104Bounds
  have har : (((weightedUpper d2Transfer431C0 d2Log104Lo d2Log104Hi:ℚ):ℝ)) ≤ ((d2Transfer431Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer431Arithmetic
  linarith
#print axioms d2Transfer431Arithmetic
#print axioms d2Transfer431Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers053
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers053
open D72.LogTransfer
def d2WiderTransfer424Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (262143) 1 (-18))
def d2WiderTransfer424Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (524287) 1 (-19))
def d2WiderTransfer424Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (1047452963062433597887) 1 (-79))
def d2WiderTransfer424C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer424S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer424Arithmetic : weightedUpper d2WiderTransfer424C0 d2Log185Lo d2Log185Hi ≤ d2WiderTransfer424Cap := by decide +kernel
theorem d2WiderTransfer424Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer424Lo:ℚ):ℝ) ((d2WiderTransfer424Hi:ℚ):ℝ), ((d2WiderTransfer424C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer424S0:ℚ):ℝ)| ≤ ((d2WiderTransfer424Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer424S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer424S0,d2WiderTransfer424Lo,d2WiderTransfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer424C0 then |x-((d2WiderTransfer424S0:ℚ):ℝ)| ≤ ((d2Log185Q:ℚ):ℝ) else ((d2Log185Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer424S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer424S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer424S0,d2WiderTransfer424Lo,d2WiderTransfer424Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer424C0,d2Log185Q,d2WiderTransfer424S0,d2WiderTransfer424Lo,d2WiderTransfer424Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer424C0 d2WiderTransfer424S0 d2Log185Q d2Log185Lo d2Log185Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log185Bounds
  have har : (((weightedUpper d2WiderTransfer424C0 d2Log185Lo d2Log185Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer424Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer424Arithmetic
  linarith
#print axioms d2WiderTransfer424Arithmetic
#print axioms d2WiderTransfer424Bound
def d2WiderTransfer425Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (524287) 1 (-19))
def d2WiderTransfer425Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 1 (0))
def d2WiderTransfer425Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (523727306835983321489) 1 (-78))
def d2WiderTransfer425C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer425S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer425Arithmetic : weightedUpper d2WiderTransfer425C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer425Cap := by decide +kernel
theorem d2WiderTransfer425Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer425Lo:ℚ):ℝ) ((d2WiderTransfer425Hi:ℚ):ℝ), ((d2WiderTransfer425C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer425S0:ℚ):ℝ)| ≤ ((d2WiderTransfer425Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer425S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer425S0,d2WiderTransfer425Lo,d2WiderTransfer425Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer425C0 then |x-((d2WiderTransfer425S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer425S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer425S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer425S0,d2WiderTransfer425Lo,d2WiderTransfer425Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer425C0,d2Log186Q,d2WiderTransfer425S0,d2WiderTransfer425Lo,d2WiderTransfer425Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer425C0 d2WiderTransfer425S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer425C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer425Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer425Arithmetic
  linarith
#print axioms d2WiderTransfer425Arithmetic
#print axioms d2WiderTransfer425Bound
def d2WiderTransfer426Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (524287) 1 (-19))
def d2WiderTransfer426Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 1 (0))
def d2WiderTransfer426Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (523727202107500775825) 1 (-78))
def d2WiderTransfer426C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer426S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer426Arithmetic : weightedUpper d2WiderTransfer426C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer426Cap := by decide +kernel
theorem d2WiderTransfer426Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer426Lo:ℚ):ℝ) ((d2WiderTransfer426Hi:ℚ):ℝ), ((d2WiderTransfer426C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer426S0:ℚ):ℝ)| ≤ ((d2WiderTransfer426Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer426S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer426S0,d2WiderTransfer426Lo,d2WiderTransfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer426C0 then |x-((d2WiderTransfer426S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer426S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer426S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer426S0,d2WiderTransfer426Lo,d2WiderTransfer426Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer426C0,d2Log186Q,d2WiderTransfer426S0,d2WiderTransfer426Lo,d2WiderTransfer426Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer426C0 d2WiderTransfer426S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer426C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer426Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer426Arithmetic
  linarith
#print axioms d2WiderTransfer426Arithmetic
#print axioms d2WiderTransfer426Bound
def d2WiderTransfer427Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (999) 125 (-3))
def d2WiderTransfer427Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (16760439) 1 (-24))
def d2WiderTransfer427Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (1046698974472468061133) 1 (-79))
def d2WiderTransfer427C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer427S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer427Arithmetic : weightedUpper d2WiderTransfer427C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer427Cap := by decide +kernel
theorem d2WiderTransfer427Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer427Lo:ℚ):ℝ) ((d2WiderTransfer427Hi:ℚ):ℝ), ((d2WiderTransfer427C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer427S0:ℚ):ℝ)| ≤ ((d2WiderTransfer427Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer427S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer427S0,d2WiderTransfer427Lo,d2WiderTransfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer427C0 then |x-((d2WiderTransfer427S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer427S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer427S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer427S0,d2WiderTransfer427Lo,d2WiderTransfer427Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer427C0,d2Log175Q,d2WiderTransfer427S0,d2WiderTransfer427Lo,d2WiderTransfer427Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer427C0 d2WiderTransfer427S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer427C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer427Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer427Arithmetic
  linarith
#print axioms d2WiderTransfer427Arithmetic
#print axioms d2WiderTransfer427Bound
def d2WiderTransfer428Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (999) 125 (-3))
def d2WiderTransfer428Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (16760439) 1 (-24))
def d2WiderTransfer428Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (1046698765015502969805) 1 (-79))
def d2WiderTransfer428C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer428S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer428Arithmetic : weightedUpper d2WiderTransfer428C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer428Cap := by decide +kernel
theorem d2WiderTransfer428Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer428Lo:ℚ):ℝ) ((d2WiderTransfer428Hi:ℚ):ℝ), ((d2WiderTransfer428C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer428S0:ℚ):ℝ)| ≤ ((d2WiderTransfer428Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer428S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer428S0,d2WiderTransfer428Lo,d2WiderTransfer428Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer428C0 then |x-((d2WiderTransfer428S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer428S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer428S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer428S0,d2WiderTransfer428Lo,d2WiderTransfer428Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer428C0,d2Log175Q,d2WiderTransfer428S0,d2WiderTransfer428Lo,d2WiderTransfer428Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer428C0 d2WiderTransfer428S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer428C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer428Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer428Arithmetic
  linarith
#print axioms d2WiderTransfer428Arithmetic
#print axioms d2WiderTransfer428Bound
def d2WiderTransfer429Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (999) 125 (-3))
def d2WiderTransfer429Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (16760439) 1 (-24))
def d2WiderTransfer429Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (13083733079409200880589) 1 (-79))
def d2WiderTransfer429C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 1 (-5))
def d2WiderTransfer429S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer429Arithmetic : weightedUpper d2WiderTransfer429C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer429Cap := by decide +kernel
theorem d2WiderTransfer429Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer429Lo:ℚ):ℝ) ((d2WiderTransfer429Hi:ℚ):ℝ), ((d2WiderTransfer429C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer429S0:ℚ):ℝ)| ≤ ((d2WiderTransfer429Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer429S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer429S0,d2WiderTransfer429Lo,d2WiderTransfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer429C0 then |x-((d2WiderTransfer429S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer429S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer429S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer429S0,d2WiderTransfer429Lo,d2WiderTransfer429Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer429C0,d2Log175Q,d2WiderTransfer429S0,d2WiderTransfer429Lo,d2WiderTransfer429Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer429C0 d2WiderTransfer429S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer429C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer429Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer429Arithmetic
  linarith
#print axioms d2WiderTransfer429Arithmetic
#print axioms d2WiderTransfer429Bound
def d2WiderTransfer430Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (999) 125 (-3))
def d2WiderTransfer430Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (16760439) 1 (-24))
def d2WiderTransfer430Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (13083733277321293880269) 1 (-79))
def d2WiderTransfer430C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 1 (-5))
def d2WiderTransfer430S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer430Arithmetic : weightedUpper d2WiderTransfer430C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer430Cap := by decide +kernel
theorem d2WiderTransfer430Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer430Lo:ℚ):ℝ) ((d2WiderTransfer430Hi:ℚ):ℝ), ((d2WiderTransfer430C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer430S0:ℚ):ℝ)| ≤ ((d2WiderTransfer430Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer430S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer430S0,d2WiderTransfer430Lo,d2WiderTransfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer430C0 then |x-((d2WiderTransfer430S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer430S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer430S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer430S0,d2WiderTransfer430Lo,d2WiderTransfer430Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer430C0,d2Log175Q,d2WiderTransfer430S0,d2WiderTransfer430Lo,d2WiderTransfer430Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer430C0 d2WiderTransfer430S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer430C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer430Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer430Arithmetic
  linarith
#print axioms d2WiderTransfer430Arithmetic
#print axioms d2WiderTransfer430Bound
def d2WiderTransfer431Lo : ℚ := (d2LitsNearWiderTransfers053.q2 (16760439) 1 (-24))
def d2WiderTransfer431Hi : ℚ := (d2LitsNearWiderTransfers053.q2 (1023) 1 (-10))
def d2WiderTransfer431Cap : ℚ := (d2LitsNearWiderTransfers053.q2 (1046920323180841822905) 1 (-79))
def d2WiderTransfer431C0 : ℚ := (d2LitsNearWiderTransfers053.q2 (1) 25 (-4))
def d2WiderTransfer431S0 : ℚ := (d2LitsNearWiderTransfers053.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer431Arithmetic : weightedUpper d2WiderTransfer431C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer431Cap := by decide +kernel
theorem d2WiderTransfer431Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer431Lo:ℚ):ℝ) ((d2WiderTransfer431Hi:ℚ):ℝ), ((d2WiderTransfer431C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer431S0:ℚ):ℝ)| ≤ ((d2WiderTransfer431Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer431S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer431S0,d2WiderTransfer431Lo,d2WiderTransfer431Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer431C0 then |x-((d2WiderTransfer431S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer431S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer431S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer431S0,d2WiderTransfer431Lo,d2WiderTransfer431Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers053.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer431C0,d2Log176Q,d2WiderTransfer431S0,d2WiderTransfer431Lo,d2WiderTransfer431Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer431C0 d2WiderTransfer431S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer431C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer431Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer431Arithmetic
  linarith
#print axioms d2WiderTransfer431Arithmetic
#print axioms d2WiderTransfer431Bound
end CatalanMeasure.GenD.Signed.Data.Cells

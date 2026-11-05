module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers026
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers026
open D72.LogTransfer
def d2Transfer208Lo : ℚ := (d2LitsNearTransfers026.q2 (4183809) 1 (-23))
def d2Transfer208Hi : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer208Cap : ℚ := (d2LitsNearTransfers026.q2 (16281318465) 1 (-40))
def d2Transfer208C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (-5))
def d2Transfer208S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer208Arithmetic : weightedUpper d2Transfer208C0 d2Log121Lo d2Log121Hi ≤ d2Transfer208Cap := by decide +kernel
theorem d2Transfer208Bound : ∀ x ∈ Set.Icc ((d2Transfer208Lo:ℚ):ℝ) ((d2Transfer208Hi:ℚ):ℝ), ((d2Transfer208C0:ℚ):ℝ)*Real.log |x-((d2Transfer208S0:ℚ):ℝ)| ≤ ((d2Transfer208Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer208S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer208S0,d2Transfer208Lo,d2Transfer208Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer208C0 then |x-((d2Transfer208S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer208S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer208S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer208S0,d2Transfer208Lo,d2Transfer208Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer208C0,d2Log121Q,d2Transfer208S0,d2Transfer208Lo,d2Transfer208Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer208C0 d2Transfer208S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2Transfer208C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2Transfer208Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer208Arithmetic
  linarith
#print axioms d2Transfer208Arithmetic
#print axioms d2Transfer208Bound
def d2Transfer209Lo : ℚ := (d2LitsNearTransfers026.q2 (4183809) 1 (-23))
def d2Transfer209Hi : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer209Cap : ℚ := (d2LitsNearTransfers026.q2 (31165051305) 1 (-40))
def d2Transfer209C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 11 (-5))
def d2Transfer209S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
def d2Transfer209C1 : ℚ := (d2LitsNearTransfers026.q2 (-5) 11 (-4))
def d2Transfer209S1 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer209Arithmetic : weightedUpper d2Transfer209C0 d2Log121Lo d2Log121Hi + weightedUpper d2Transfer209C1 d2Log53Lo d2Log53Hi ≤ d2Transfer209Cap := by decide +kernel
theorem d2Transfer209Bound : ∀ x ∈ Set.Icc ((d2Transfer209Lo:ℚ):ℝ) ((d2Transfer209Hi:ℚ):ℝ), ((d2Transfer209C0:ℚ):ℝ)*Real.log |x-((d2Transfer209S0:ℚ):ℝ)| + ((d2Transfer209C1:ℚ):ℝ)*Real.log |x-((d2Transfer209S1:ℚ):ℝ)| ≤ ((d2Transfer209Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer209S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209S0,d2Transfer209Lo,d2Transfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer209C0 then |x-((d2Transfer209S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer209S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer209S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209S0,d2Transfer209Lo,d2Transfer209Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209C0,d2Log121Q,d2Transfer209S0,d2Transfer209Lo,d2Transfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer209C0 d2Transfer209S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2Transfer209S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209S1,d2Transfer209Lo,d2Transfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer209C1 then |x-((d2Transfer209S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2Transfer209S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer209S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209S1,d2Transfer209Lo,d2Transfer209Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer209C1,d2Log53Q,d2Transfer209S1,d2Transfer209Lo,d2Transfer209Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer209C1 d2Transfer209S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2Transfer209C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2Transfer209C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2Transfer209Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer209Arithmetic
  linarith
#print axioms d2Transfer209Arithmetic
#print axioms d2Transfer209Bound
def d2Transfer210Lo : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer210Hi : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer210Cap : ℚ := (d2LitsNearTransfers026.q2 (649441385) 1 (-39))
def d2Transfer210C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 25 (-4))
def d2Transfer210S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer210Arithmetic : weightedUpper d2Transfer210C0 d2Log122Lo d2Log122Hi ≤ d2Transfer210Cap := by decide +kernel
theorem d2Transfer210Bound : ∀ x ∈ Set.Icc ((d2Transfer210Lo:ℚ):ℝ) ((d2Transfer210Hi:ℚ):ℝ), ((d2Transfer210C0:ℚ):ℝ)*Real.log |x-((d2Transfer210S0:ℚ):ℝ)| ≤ ((d2Transfer210Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer210S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer210S0,d2Transfer210Lo,d2Transfer210Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer210C0 then |x-((d2Transfer210S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer210S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer210S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer210S0,d2Transfer210Lo,d2Transfer210Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer210C0,d2Log122Q,d2Transfer210S0,d2Transfer210Lo,d2Transfer210Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer210C0 d2Transfer210S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2Transfer210C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2Transfer210Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer210Arithmetic
  linarith
#print axioms d2Transfer210Arithmetic
#print axioms d2Transfer210Bound
def d2Transfer211Lo : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer211Hi : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer211Cap : ℚ := (d2LitsNearTransfers026.q2 (2436024149) 1 (-40))
def d2Transfer211C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 275 (-4))
def d2Transfer211S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
def d2Transfer211C1 : ℚ := (d2LitsNearTransfers026.q2 (-1) 55 (-3))
def d2Transfer211S1 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer211Arithmetic : weightedUpper d2Transfer211C0 d2Log122Lo d2Log122Hi + weightedUpper d2Transfer211C1 d2Log52Lo d2Log52Hi ≤ d2Transfer211Cap := by decide +kernel
theorem d2Transfer211Bound : ∀ x ∈ Set.Icc ((d2Transfer211Lo:ℚ):ℝ) ((d2Transfer211Hi:ℚ):ℝ), ((d2Transfer211C0:ℚ):ℝ)*Real.log |x-((d2Transfer211S0:ℚ):ℝ)| + ((d2Transfer211C1:ℚ):ℝ)*Real.log |x-((d2Transfer211S1:ℚ):ℝ)| ≤ ((d2Transfer211Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer211S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211S0,d2Transfer211Lo,d2Transfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer211C0 then |x-((d2Transfer211S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer211S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer211S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211S0,d2Transfer211Lo,d2Transfer211Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211C0,d2Log122Q,d2Transfer211S0,d2Transfer211Lo,d2Transfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer211C0 d2Transfer211S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2Transfer211S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211S1,d2Transfer211Lo,d2Transfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer211C1 then |x-((d2Transfer211S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2Transfer211S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer211S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211S1,d2Transfer211Lo,d2Transfer211Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer211C1,d2Log52Q,d2Transfer211S1,d2Transfer211Lo,d2Transfer211Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer211C1 d2Transfer211S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2Transfer211C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2Transfer211C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2Transfer211Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer211Arithmetic
  linarith
#print axioms d2Transfer211Arithmetic
#print axioms d2Transfer211Bound
def d2Transfer212Lo : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer212Hi : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer212Cap : ℚ := (d2LitsNearTransfers026.q2 (16281318465) 1 (-40))
def d2Transfer212C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (-5))
def d2Transfer212S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer212Arithmetic : weightedUpper d2Transfer212C0 d2Log122Lo d2Log122Hi ≤ d2Transfer212Cap := by decide +kernel
theorem d2Transfer212Bound : ∀ x ∈ Set.Icc ((d2Transfer212Lo:ℚ):ℝ) ((d2Transfer212Hi:ℚ):ℝ), ((d2Transfer212C0:ℚ):ℝ)*Real.log |x-((d2Transfer212S0:ℚ):ℝ)| ≤ ((d2Transfer212Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer212S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer212S0,d2Transfer212Lo,d2Transfer212Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer212C0 then |x-((d2Transfer212S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer212S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer212S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer212S0,d2Transfer212Lo,d2Transfer212Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer212C0,d2Log122Q,d2Transfer212S0,d2Transfer212Lo,d2Transfer212Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer212C0 d2Transfer212S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2Transfer212C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2Transfer212Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer212Arithmetic
  linarith
#print axioms d2Transfer212Arithmetic
#print axioms d2Transfer212Bound
def d2Transfer213Lo : ℚ := (d2LitsNearTransfers026.q2 (18412957) 1 (-25))
def d2Transfer213Hi : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer213Cap : ℚ := (d2LitsNearTransfers026.q2 (31165051305) 1 (-40))
def d2Transfer213C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 11 (-5))
def d2Transfer213S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
def d2Transfer213C1 : ℚ := (d2LitsNearTransfers026.q2 (-5) 11 (-4))
def d2Transfer213S1 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer213Arithmetic : weightedUpper d2Transfer213C0 d2Log122Lo d2Log122Hi + weightedUpper d2Transfer213C1 d2Log52Lo d2Log52Hi ≤ d2Transfer213Cap := by decide +kernel
theorem d2Transfer213Bound : ∀ x ∈ Set.Icc ((d2Transfer213Lo:ℚ):ℝ) ((d2Transfer213Hi:ℚ):ℝ), ((d2Transfer213C0:ℚ):ℝ)*Real.log |x-((d2Transfer213S0:ℚ):ℝ)| + ((d2Transfer213C1:ℚ):ℝ)*Real.log |x-((d2Transfer213S1:ℚ):ℝ)| ≤ ((d2Transfer213Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer213S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213S0,d2Transfer213Lo,d2Transfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer213C0 then |x-((d2Transfer213S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer213S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer213S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213S0,d2Transfer213Lo,d2Transfer213Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213C0,d2Log122Q,d2Transfer213S0,d2Transfer213Lo,d2Transfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer213C0 d2Transfer213S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2Transfer213S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213S1,d2Transfer213Lo,d2Transfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer213C1 then |x-((d2Transfer213S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2Transfer213S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer213S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213S1,d2Transfer213Lo,d2Transfer213Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer213C1,d2Log52Q,d2Transfer213S1,d2Transfer213Lo,d2Transfer213Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer213C1 d2Transfer213S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2Transfer213C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2Transfer213C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2Transfer213Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer213Arithmetic
  linarith
#print axioms d2Transfer213Arithmetic
#print axioms d2Transfer213Bound
def d2Transfer214Lo : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer214Hi : ℚ := (d2LitsNearTransfers026.q2 (78684991) 1 (-27))
def d2Transfer214Cap : ℚ := (d2LitsNearTransfers026.q2 (649441385) 1 (-39))
def d2Transfer214C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 25 (-4))
def d2Transfer214S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer214Arithmetic : weightedUpper d2Transfer214C0 d2Log123Lo d2Log123Hi ≤ d2Transfer214Cap := by decide +kernel
theorem d2Transfer214Bound : ∀ x ∈ Set.Icc ((d2Transfer214Lo:ℚ):ℝ) ((d2Transfer214Hi:ℚ):ℝ), ((d2Transfer214C0:ℚ):ℝ)*Real.log |x-((d2Transfer214S0:ℚ):ℝ)| ≤ ((d2Transfer214Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer214S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer214S0,d2Transfer214Lo,d2Transfer214Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer214C0 then |x-((d2Transfer214S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer214S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer214S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer214S0,d2Transfer214Lo,d2Transfer214Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer214C0,d2Log123Q,d2Transfer214S0,d2Transfer214Lo,d2Transfer214Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer214C0 d2Transfer214S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have har : (((weightedUpper d2Transfer214C0 d2Log123Lo d2Log123Hi:ℚ):ℝ)) ≤ ((d2Transfer214Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer214Arithmetic
  linarith
#print axioms d2Transfer214Arithmetic
#print axioms d2Transfer214Bound
def d2Transfer215Lo : ℚ := (d2LitsNearTransfers026.q2 (38503635) 1 (-26))
def d2Transfer215Hi : ℚ := (d2LitsNearTransfers026.q2 (78684991) 1 (-27))
def d2Transfer215Cap : ℚ := (d2LitsNearTransfers026.q2 (2436024149) 1 (-40))
def d2Transfer215C0 : ℚ := (d2LitsNearTransfers026.q2 (1) 275 (-4))
def d2Transfer215S0 : ℚ := (d2LitsNearTransfers026.q2 (-1) 1 (0))
def d2Transfer215C1 : ℚ := (d2LitsNearTransfers026.q2 (-1) 55 (-3))
def d2Transfer215S1 : ℚ := (d2LitsNearTransfers026.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer215Arithmetic : weightedUpper d2Transfer215C0 d2Log123Lo d2Log123Hi + weightedUpper d2Transfer215C1 d2Log51Lo d2Log51Hi ≤ d2Transfer215Cap := by decide +kernel
theorem d2Transfer215Bound : ∀ x ∈ Set.Icc ((d2Transfer215Lo:ℚ):ℝ) ((d2Transfer215Hi:ℚ):ℝ), ((d2Transfer215C0:ℚ):ℝ)*Real.log |x-((d2Transfer215S0:ℚ):ℝ)| + ((d2Transfer215C1:ℚ):ℝ)*Real.log |x-((d2Transfer215S1:ℚ):ℝ)| ≤ ((d2Transfer215Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer215S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215S0,d2Transfer215Lo,d2Transfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer215C0 then |x-((d2Transfer215S0:ℚ):ℝ)| ≤ ((d2Log123Q:ℚ):ℝ) else ((d2Log123Q:ℚ):ℝ) ≤ |x-((d2Transfer215S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer215S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215S0,d2Transfer215Lo,d2Transfer215Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215C0,d2Log123Q,d2Transfer215S0,d2Transfer215Lo,d2Transfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer215C0 d2Transfer215S0 d2Log123Q d2Log123Lo d2Log123Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log123Bounds
  have hn1 : x-((d2Transfer215S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215S1,d2Transfer215Lo,d2Transfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer215C1 then |x-((d2Transfer215S1:ℚ):ℝ)| ≤ ((d2Log51Q:ℚ):ℝ) else ((d2Log51Q:ℚ):ℝ) ≤ |x-((d2Transfer215S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer215S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215S1,d2Transfer215Lo,d2Transfer215Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers026.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer215C1,d2Log51Q,d2Transfer215S1,d2Transfer215Lo,d2Transfer215Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer215C1 d2Transfer215S1 d2Log51Q d2Log51Lo d2Log51Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log51Bounds
  have har : (((weightedUpper d2Transfer215C0 d2Log123Lo d2Log123Hi:ℚ):ℝ) + ((weightedUpper d2Transfer215C1 d2Log51Lo d2Log51Hi:ℚ):ℝ)) ≤ ((d2Transfer215Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer215Arithmetic
  linarith
#print axioms d2Transfer215Arithmetic
#print axioms d2Transfer215Bound
end CatalanMeasure.GenD.Signed.Data.Cells

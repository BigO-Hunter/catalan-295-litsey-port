module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers009
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers009
open D72.LogTransfer
def d2WiderTransfer72Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (6689897) 1 (-24))
def d2WiderTransfer72Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer72Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (16281318465) 1 (-40))
def d2WiderTransfer72C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (-5))
def d2WiderTransfer72S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer72Arithmetic : weightedUpper d2WiderTransfer72C0 d2Log120Lo d2Log120Hi ≤ d2WiderTransfer72Cap := by decide +kernel
theorem d2WiderTransfer72Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer72Lo:ℚ):ℝ) ((d2WiderTransfer72Hi:ℚ):ℝ), ((d2WiderTransfer72C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer72S0:ℚ):ℝ)| ≤ ((d2WiderTransfer72Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer72S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer72S0,d2WiderTransfer72Lo,d2WiderTransfer72Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer72C0 then |x-((d2WiderTransfer72S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer72S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer72S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer72S0,d2WiderTransfer72Lo,d2WiderTransfer72Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer72C0,d2Log120Q,d2WiderTransfer72S0,d2WiderTransfer72Lo,d2WiderTransfer72Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer72C0 d2WiderTransfer72S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2WiderTransfer72C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer72Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer72Arithmetic
  linarith
#print axioms d2WiderTransfer72Arithmetic
#print axioms d2WiderTransfer72Bound
def d2WiderTransfer73Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (6689897) 1 (-24))
def d2WiderTransfer73Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer73Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (31165051305) 1 (-40))
def d2WiderTransfer73C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 11 (-5))
def d2WiderTransfer73S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
def d2WiderTransfer73C1 : ℚ := (d2LitsNearWiderTransfers009.q2 (-5) 11 (-4))
def d2WiderTransfer73S1 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer73Arithmetic : weightedUpper d2WiderTransfer73C0 d2Log120Lo d2Log120Hi + weightedUpper d2WiderTransfer73C1 d2Log54Lo d2Log54Hi ≤ d2WiderTransfer73Cap := by decide +kernel
theorem d2WiderTransfer73Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer73Lo:ℚ):ℝ) ((d2WiderTransfer73Hi:ℚ):ℝ), ((d2WiderTransfer73C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer73S0:ℚ):ℝ)| + ((d2WiderTransfer73C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer73S1:ℚ):ℝ)| ≤ ((d2WiderTransfer73Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer73S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73S0,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer73C0 then |x-((d2WiderTransfer73S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer73S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer73S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73S0,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73C0,d2Log120Q,d2WiderTransfer73S0,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer73C0 d2WiderTransfer73S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2WiderTransfer73S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73S1,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer73C1 then |x-((d2WiderTransfer73S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer73S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer73S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73S1,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer73C1,d2Log54Q,d2WiderTransfer73S1,d2WiderTransfer73Lo,d2WiderTransfer73Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer73C1 d2WiderTransfer73S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2WiderTransfer73C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer73C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer73Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer73Arithmetic
  linarith
#print axioms d2WiderTransfer73Arithmetic
#print axioms d2WiderTransfer73Bound
def d2WiderTransfer74Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer74Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer74Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (649441385) 1 (-39))
def d2WiderTransfer74C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 25 (-4))
def d2WiderTransfer74S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer74Arithmetic : weightedUpper d2WiderTransfer74C0 d2Log121Lo d2Log121Hi ≤ d2WiderTransfer74Cap := by decide +kernel
theorem d2WiderTransfer74Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer74Lo:ℚ):ℝ) ((d2WiderTransfer74Hi:ℚ):ℝ), ((d2WiderTransfer74C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer74S0:ℚ):ℝ)| ≤ ((d2WiderTransfer74Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer74S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer74S0,d2WiderTransfer74Lo,d2WiderTransfer74Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer74C0 then |x-((d2WiderTransfer74S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer74S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer74S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer74S0,d2WiderTransfer74Lo,d2WiderTransfer74Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer74C0,d2Log121Q,d2WiderTransfer74S0,d2WiderTransfer74Lo,d2WiderTransfer74Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer74C0 d2WiderTransfer74S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2WiderTransfer74C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer74Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer74Arithmetic
  linarith
#print axioms d2WiderTransfer74Arithmetic
#print axioms d2WiderTransfer74Bound
def d2WiderTransfer75Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer75Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer75Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (2436024149) 1 (-40))
def d2WiderTransfer75C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 275 (-4))
def d2WiderTransfer75S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
def d2WiderTransfer75C1 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 55 (-3))
def d2WiderTransfer75S1 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer75Arithmetic : weightedUpper d2WiderTransfer75C0 d2Log121Lo d2Log121Hi + weightedUpper d2WiderTransfer75C1 d2Log53Lo d2Log53Hi ≤ d2WiderTransfer75Cap := by decide +kernel
theorem d2WiderTransfer75Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer75Lo:ℚ):ℝ) ((d2WiderTransfer75Hi:ℚ):ℝ), ((d2WiderTransfer75C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer75S0:ℚ):ℝ)| + ((d2WiderTransfer75C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer75S1:ℚ):ℝ)| ≤ ((d2WiderTransfer75Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer75S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75S0,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer75C0 then |x-((d2WiderTransfer75S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer75S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer75S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75S0,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75C0,d2Log121Q,d2WiderTransfer75S0,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer75C0 d2WiderTransfer75S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2WiderTransfer75S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75S1,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer75C1 then |x-((d2WiderTransfer75S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer75S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer75S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75S1,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer75C1,d2Log53Q,d2WiderTransfer75S1,d2WiderTransfer75Lo,d2WiderTransfer75Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer75C1 d2WiderTransfer75S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2WiderTransfer75C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer75C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer75Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer75Arithmetic
  linarith
#print axioms d2WiderTransfer75Arithmetic
#print axioms d2WiderTransfer75Bound
def d2WiderTransfer76Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer76Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer76Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (16281318465) 1 (-40))
def d2WiderTransfer76C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (-5))
def d2WiderTransfer76S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer76Arithmetic : weightedUpper d2WiderTransfer76C0 d2Log121Lo d2Log121Hi ≤ d2WiderTransfer76Cap := by decide +kernel
theorem d2WiderTransfer76Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer76Lo:ℚ):ℝ) ((d2WiderTransfer76Hi:ℚ):ℝ), ((d2WiderTransfer76C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer76S0:ℚ):ℝ)| ≤ ((d2WiderTransfer76Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer76S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer76S0,d2WiderTransfer76Lo,d2WiderTransfer76Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer76C0 then |x-((d2WiderTransfer76S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer76S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer76S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer76S0,d2WiderTransfer76Lo,d2WiderTransfer76Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer76C0,d2Log121Q,d2WiderTransfer76S0,d2WiderTransfer76Lo,d2WiderTransfer76Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer76C0 d2WiderTransfer76S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2WiderTransfer76C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer76Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer76Arithmetic
  linarith
#print axioms d2WiderTransfer76Arithmetic
#print axioms d2WiderTransfer76Bound
def d2WiderTransfer77Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (4183809) 1 (-23))
def d2WiderTransfer77Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer77Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (31165051305) 1 (-40))
def d2WiderTransfer77C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 11 (-5))
def d2WiderTransfer77S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
def d2WiderTransfer77C1 : ℚ := (d2LitsNearWiderTransfers009.q2 (-5) 11 (-4))
def d2WiderTransfer77S1 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer77Arithmetic : weightedUpper d2WiderTransfer77C0 d2Log121Lo d2Log121Hi + weightedUpper d2WiderTransfer77C1 d2Log53Lo d2Log53Hi ≤ d2WiderTransfer77Cap := by decide +kernel
theorem d2WiderTransfer77Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer77Lo:ℚ):ℝ) ((d2WiderTransfer77Hi:ℚ):ℝ), ((d2WiderTransfer77C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer77S0:ℚ):ℝ)| + ((d2WiderTransfer77C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer77S1:ℚ):ℝ)| ≤ ((d2WiderTransfer77Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer77S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77S0,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer77C0 then |x-((d2WiderTransfer77S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer77S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer77S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77S0,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77C0,d2Log121Q,d2WiderTransfer77S0,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer77C0 d2WiderTransfer77S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2WiderTransfer77S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77S1,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer77C1 then |x-((d2WiderTransfer77S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer77S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer77S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77S1,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer77C1,d2Log53Q,d2WiderTransfer77S1,d2WiderTransfer77Lo,d2WiderTransfer77Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer77C1 d2WiderTransfer77S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2WiderTransfer77C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer77C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer77Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer77Arithmetic
  linarith
#print axioms d2WiderTransfer77Arithmetic
#print axioms d2WiderTransfer77Bound
def d2WiderTransfer78Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer78Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (38503635) 1 (-26))
def d2WiderTransfer78Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (649441385) 1 (-39))
def d2WiderTransfer78C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 25 (-4))
def d2WiderTransfer78S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer78Arithmetic : weightedUpper d2WiderTransfer78C0 d2Log122Lo d2Log122Hi ≤ d2WiderTransfer78Cap := by decide +kernel
theorem d2WiderTransfer78Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer78Lo:ℚ):ℝ) ((d2WiderTransfer78Hi:ℚ):ℝ), ((d2WiderTransfer78C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer78S0:ℚ):ℝ)| ≤ ((d2WiderTransfer78Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer78S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer78S0,d2WiderTransfer78Lo,d2WiderTransfer78Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer78C0 then |x-((d2WiderTransfer78S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer78S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer78S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer78S0,d2WiderTransfer78Lo,d2WiderTransfer78Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer78C0,d2Log122Q,d2WiderTransfer78S0,d2WiderTransfer78Lo,d2WiderTransfer78Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer78C0 d2WiderTransfer78S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2WiderTransfer78C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer78Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer78Arithmetic
  linarith
#print axioms d2WiderTransfer78Arithmetic
#print axioms d2WiderTransfer78Bound
def d2WiderTransfer79Lo : ℚ := (d2LitsNearWiderTransfers009.q2 (18412957) 1 (-25))
def d2WiderTransfer79Hi : ℚ := (d2LitsNearWiderTransfers009.q2 (38503635) 1 (-26))
def d2WiderTransfer79Cap : ℚ := (d2LitsNearWiderTransfers009.q2 (2436024149) 1 (-40))
def d2WiderTransfer79C0 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 275 (-4))
def d2WiderTransfer79S0 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 1 (0))
def d2WiderTransfer79C1 : ℚ := (d2LitsNearWiderTransfers009.q2 (-1) 55 (-3))
def d2WiderTransfer79S1 : ℚ := (d2LitsNearWiderTransfers009.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer79Arithmetic : weightedUpper d2WiderTransfer79C0 d2Log122Lo d2Log122Hi + weightedUpper d2WiderTransfer79C1 d2Log52Lo d2Log52Hi ≤ d2WiderTransfer79Cap := by decide +kernel
theorem d2WiderTransfer79Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer79Lo:ℚ):ℝ) ((d2WiderTransfer79Hi:ℚ):ℝ), ((d2WiderTransfer79C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer79S0:ℚ):ℝ)| + ((d2WiderTransfer79C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer79S1:ℚ):ℝ)| ≤ ((d2WiderTransfer79Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer79S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79S0,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer79C0 then |x-((d2WiderTransfer79S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer79S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer79S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79S0,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79C0,d2Log122Q,d2WiderTransfer79S0,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer79C0 d2WiderTransfer79S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2WiderTransfer79S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79S1,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer79C1 then |x-((d2WiderTransfer79S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer79S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer79S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79S1,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers009.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer79C1,d2Log52Q,d2WiderTransfer79S1,d2WiderTransfer79Lo,d2WiderTransfer79Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer79C1 d2WiderTransfer79S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2WiderTransfer79C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer79C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer79Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer79Arithmetic
  linarith
#print axioms d2WiderTransfer79Arithmetic
#print axioms d2WiderTransfer79Bound
end CatalanMeasure.GenD.Signed.Data.Cells

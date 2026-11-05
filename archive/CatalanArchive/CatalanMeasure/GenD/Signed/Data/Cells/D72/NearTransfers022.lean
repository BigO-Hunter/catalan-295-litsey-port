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
namespace d2LitsNearTransfers022
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers022
open D72.LogTransfer
def d2Transfer176Lo : ℚ := (d2LitsNearTransfers022.q2 (35064245) 1 (-27))
def d2Transfer176Hi : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer176Cap : ℚ := (d2LitsNearTransfers022.q2 (16281318465) 1 (-40))
def d2Transfer176C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (-5))
def d2Transfer176S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer176Arithmetic : weightedUpper d2Transfer176C0 d2Log112Lo d2Log112Hi ≤ d2Transfer176Cap := by decide +kernel
theorem d2Transfer176Bound : ∀ x ∈ Set.Icc ((d2Transfer176Lo:ℚ):ℝ) ((d2Transfer176Hi:ℚ):ℝ), ((d2Transfer176C0:ℚ):ℝ)*Real.log |x-((d2Transfer176S0:ℚ):ℝ)| ≤ ((d2Transfer176Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer176S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer176S0,d2Transfer176Lo,d2Transfer176Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer176C0 then |x-((d2Transfer176S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer176S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer176S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer176S0,d2Transfer176Lo,d2Transfer176Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer176C0,d2Log112Q,d2Transfer176S0,d2Transfer176Lo,d2Transfer176Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer176C0 d2Transfer176S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have har : (((weightedUpper d2Transfer176C0 d2Log112Lo d2Log112Hi:ℚ):ℝ)) ≤ ((d2Transfer176Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer176Arithmetic
  linarith
#print axioms d2Transfer176Arithmetic
#print axioms d2Transfer176Bound
def d2Transfer177Lo : ℚ := (d2LitsNearTransfers022.q2 (35064245) 1 (-27))
def d2Transfer177Hi : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer177Cap : ℚ := (d2LitsNearTransfers022.q2 (31165051305) 1 (-40))
def d2Transfer177C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 11 (-5))
def d2Transfer177S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
def d2Transfer177C1 : ℚ := (d2LitsNearTransfers022.q2 (-5) 11 (-4))
def d2Transfer177S1 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer177Arithmetic : weightedUpper d2Transfer177C0 d2Log112Lo d2Log112Hi + weightedUpper d2Transfer177C1 d2Log62Lo d2Log62Hi ≤ d2Transfer177Cap := by decide +kernel
theorem d2Transfer177Bound : ∀ x ∈ Set.Icc ((d2Transfer177Lo:ℚ):ℝ) ((d2Transfer177Hi:ℚ):ℝ), ((d2Transfer177C0:ℚ):ℝ)*Real.log |x-((d2Transfer177S0:ℚ):ℝ)| + ((d2Transfer177C1:ℚ):ℝ)*Real.log |x-((d2Transfer177S1:ℚ):ℝ)| ≤ ((d2Transfer177Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer177S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177S0,d2Transfer177Lo,d2Transfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer177C0 then |x-((d2Transfer177S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer177S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer177S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177S0,d2Transfer177Lo,d2Transfer177Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177C0,d2Log112Q,d2Transfer177S0,d2Transfer177Lo,d2Transfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer177C0 d2Transfer177S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have hn1 : x-((d2Transfer177S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177S1,d2Transfer177Lo,d2Transfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer177C1 then |x-((d2Transfer177S1:ℚ):ℝ)| ≤ ((d2Log62Q:ℚ):ℝ) else ((d2Log62Q:ℚ):ℝ) ≤ |x-((d2Transfer177S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer177S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177S1,d2Transfer177Lo,d2Transfer177Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer177C1,d2Log62Q,d2Transfer177S1,d2Transfer177Lo,d2Transfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer177C1 d2Transfer177S1 d2Log62Q d2Log62Lo d2Log62Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log62Bounds
  have har : (((weightedUpper d2Transfer177C0 d2Log112Lo d2Log112Hi:ℚ):ℝ) + ((weightedUpper d2Transfer177C1 d2Log62Lo d2Log62Hi:ℚ):ℝ)) ≤ ((d2Transfer177Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer177Arithmetic
  linarith
#print axioms d2Transfer177Arithmetic
#print axioms d2Transfer177Bound
def d2Transfer178Lo : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer178Hi : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer178Cap : ℚ := (d2LitsNearTransfers022.q2 (649441385) 1 (-39))
def d2Transfer178C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 25 (-4))
def d2Transfer178S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer178Arithmetic : weightedUpper d2Transfer178C0 d2Log113Lo d2Log113Hi ≤ d2Transfer178Cap := by decide +kernel
theorem d2Transfer178Bound : ∀ x ∈ Set.Icc ((d2Transfer178Lo:ℚ):ℝ) ((d2Transfer178Hi:ℚ):ℝ), ((d2Transfer178C0:ℚ):ℝ)*Real.log |x-((d2Transfer178S0:ℚ):ℝ)| ≤ ((d2Transfer178Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer178S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer178S0,d2Transfer178Lo,d2Transfer178Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer178C0 then |x-((d2Transfer178S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer178S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer178S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer178S0,d2Transfer178Lo,d2Transfer178Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer178C0,d2Log113Q,d2Transfer178S0,d2Transfer178Lo,d2Transfer178Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer178C0 d2Transfer178S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2Transfer178C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2Transfer178Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer178Arithmetic
  linarith
#print axioms d2Transfer178Arithmetic
#print axioms d2Transfer178Bound
def d2Transfer179Lo : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer179Hi : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer179Cap : ℚ := (d2LitsNearTransfers022.q2 (2436024149) 1 (-40))
def d2Transfer179C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 275 (-4))
def d2Transfer179S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
def d2Transfer179C1 : ℚ := (d2LitsNearTransfers022.q2 (-1) 55 (-3))
def d2Transfer179S1 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer179Arithmetic : weightedUpper d2Transfer179C0 d2Log113Lo d2Log113Hi + weightedUpper d2Transfer179C1 d2Log61Lo d2Log61Hi ≤ d2Transfer179Cap := by decide +kernel
theorem d2Transfer179Bound : ∀ x ∈ Set.Icc ((d2Transfer179Lo:ℚ):ℝ) ((d2Transfer179Hi:ℚ):ℝ), ((d2Transfer179C0:ℚ):ℝ)*Real.log |x-((d2Transfer179S0:ℚ):ℝ)| + ((d2Transfer179C1:ℚ):ℝ)*Real.log |x-((d2Transfer179S1:ℚ):ℝ)| ≤ ((d2Transfer179Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer179S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179S0,d2Transfer179Lo,d2Transfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer179C0 then |x-((d2Transfer179S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer179S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer179S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179S0,d2Transfer179Lo,d2Transfer179Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179C0,d2Log113Q,d2Transfer179S0,d2Transfer179Lo,d2Transfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer179C0 d2Transfer179S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2Transfer179S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179S1,d2Transfer179Lo,d2Transfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer179C1 then |x-((d2Transfer179S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2Transfer179S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer179S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179S1,d2Transfer179Lo,d2Transfer179Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer179C1,d2Log61Q,d2Transfer179S1,d2Transfer179Lo,d2Transfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer179C1 d2Transfer179S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2Transfer179C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2Transfer179C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2Transfer179Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer179Arithmetic
  linarith
#print axioms d2Transfer179Arithmetic
#print axioms d2Transfer179Bound
def d2Transfer180Lo : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer180Hi : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer180Cap : ℚ := (d2LitsNearTransfers022.q2 (16281318465) 1 (-40))
def d2Transfer180C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (-5))
def d2Transfer180S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer180Arithmetic : weightedUpper d2Transfer180C0 d2Log113Lo d2Log113Hi ≤ d2Transfer180Cap := by decide +kernel
theorem d2Transfer180Bound : ∀ x ∈ Set.Icc ((d2Transfer180Lo:ℚ):ℝ) ((d2Transfer180Hi:ℚ):ℝ), ((d2Transfer180C0:ℚ):ℝ)*Real.log |x-((d2Transfer180S0:ℚ):ℝ)| ≤ ((d2Transfer180Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer180S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer180S0,d2Transfer180Lo,d2Transfer180Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer180C0 then |x-((d2Transfer180S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer180S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer180S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer180S0,d2Transfer180Lo,d2Transfer180Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer180C0,d2Log113Q,d2Transfer180S0,d2Transfer180Lo,d2Transfer180Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer180C0 d2Transfer180S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2Transfer180C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2Transfer180Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer180Arithmetic
  linarith
#print axioms d2Transfer180Arithmetic
#print axioms d2Transfer180Bound
def d2Transfer181Lo : ℚ := (d2LitsNearTransfers022.q2 (18370983) 1 (-26))
def d2Transfer181Hi : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer181Cap : ℚ := (d2LitsNearTransfers022.q2 (31165051305) 1 (-40))
def d2Transfer181C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 11 (-5))
def d2Transfer181S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
def d2Transfer181C1 : ℚ := (d2LitsNearTransfers022.q2 (-5) 11 (-4))
def d2Transfer181S1 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer181Arithmetic : weightedUpper d2Transfer181C0 d2Log113Lo d2Log113Hi + weightedUpper d2Transfer181C1 d2Log61Lo d2Log61Hi ≤ d2Transfer181Cap := by decide +kernel
theorem d2Transfer181Bound : ∀ x ∈ Set.Icc ((d2Transfer181Lo:ℚ):ℝ) ((d2Transfer181Hi:ℚ):ℝ), ((d2Transfer181C0:ℚ):ℝ)*Real.log |x-((d2Transfer181S0:ℚ):ℝ)| + ((d2Transfer181C1:ℚ):ℝ)*Real.log |x-((d2Transfer181S1:ℚ):ℝ)| ≤ ((d2Transfer181Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer181S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181S0,d2Transfer181Lo,d2Transfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer181C0 then |x-((d2Transfer181S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer181S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer181S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181S0,d2Transfer181Lo,d2Transfer181Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181C0,d2Log113Q,d2Transfer181S0,d2Transfer181Lo,d2Transfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer181C0 d2Transfer181S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2Transfer181S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181S1,d2Transfer181Lo,d2Transfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer181C1 then |x-((d2Transfer181S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2Transfer181S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer181S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181S1,d2Transfer181Lo,d2Transfer181Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer181C1,d2Log61Q,d2Transfer181S1,d2Transfer181Lo,d2Transfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer181C1 d2Transfer181S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2Transfer181C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2Transfer181C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2Transfer181Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer181Arithmetic
  linarith
#print axioms d2Transfer181Arithmetic
#print axioms d2Transfer181Bound
def d2Transfer182Lo : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer182Hi : ℚ := (d2LitsNearTransfers022.q2 (21726425) 1 (-26))
def d2Transfer182Cap : ℚ := (d2LitsNearTransfers022.q2 (649441385) 1 (-39))
def d2Transfer182C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 25 (-4))
def d2Transfer182S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer182Arithmetic : weightedUpper d2Transfer182C0 d2Log114Lo d2Log114Hi ≤ d2Transfer182Cap := by decide +kernel
theorem d2Transfer182Bound : ∀ x ∈ Set.Icc ((d2Transfer182Lo:ℚ):ℝ) ((d2Transfer182Hi:ℚ):ℝ), ((d2Transfer182C0:ℚ):ℝ)*Real.log |x-((d2Transfer182S0:ℚ):ℝ)| ≤ ((d2Transfer182Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer182S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer182S0,d2Transfer182Lo,d2Transfer182Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer182C0 then |x-((d2Transfer182S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer182S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer182S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer182S0,d2Transfer182Lo,d2Transfer182Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer182C0,d2Log114Q,d2Transfer182S0,d2Transfer182Lo,d2Transfer182Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer182C0 d2Transfer182S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have har : (((weightedUpper d2Transfer182C0 d2Log114Lo d2Log114Hi:ℚ):ℝ)) ≤ ((d2Transfer182Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer182Arithmetic
  linarith
#print axioms d2Transfer182Arithmetic
#print axioms d2Transfer182Bound
def d2Transfer183Lo : ℚ := (d2LitsNearTransfers022.q2 (313261) 1 (-20))
def d2Transfer183Hi : ℚ := (d2LitsNearTransfers022.q2 (21726425) 1 (-26))
def d2Transfer183Cap : ℚ := (d2LitsNearTransfers022.q2 (2436024149) 1 (-40))
def d2Transfer183C0 : ℚ := (d2LitsNearTransfers022.q2 (1) 275 (-4))
def d2Transfer183S0 : ℚ := (d2LitsNearTransfers022.q2 (-1) 1 (0))
def d2Transfer183C1 : ℚ := (d2LitsNearTransfers022.q2 (-1) 55 (-3))
def d2Transfer183S1 : ℚ := (d2LitsNearTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer183Arithmetic : weightedUpper d2Transfer183C0 d2Log114Lo d2Log114Hi + weightedUpper d2Transfer183C1 d2Log60Lo d2Log60Hi ≤ d2Transfer183Cap := by decide +kernel
theorem d2Transfer183Bound : ∀ x ∈ Set.Icc ((d2Transfer183Lo:ℚ):ℝ) ((d2Transfer183Hi:ℚ):ℝ), ((d2Transfer183C0:ℚ):ℝ)*Real.log |x-((d2Transfer183S0:ℚ):ℝ)| + ((d2Transfer183C1:ℚ):ℝ)*Real.log |x-((d2Transfer183S1:ℚ):ℝ)| ≤ ((d2Transfer183Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer183S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183S0,d2Transfer183Lo,d2Transfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer183C0 then |x-((d2Transfer183S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer183S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer183S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183S0,d2Transfer183Lo,d2Transfer183Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183C0,d2Log114Q,d2Transfer183S0,d2Transfer183Lo,d2Transfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer183C0 d2Transfer183S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have hn1 : x-((d2Transfer183S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183S1,d2Transfer183Lo,d2Transfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer183C1 then |x-((d2Transfer183S1:ℚ):ℝ)| ≤ ((d2Log60Q:ℚ):ℝ) else ((d2Log60Q:ℚ):ℝ) ≤ |x-((d2Transfer183S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer183S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183S1,d2Transfer183Lo,d2Transfer183Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers022.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer183C1,d2Log60Q,d2Transfer183S1,d2Transfer183Lo,d2Transfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer183C1 d2Transfer183S1 d2Log60Q d2Log60Lo d2Log60Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log60Bounds
  have har : (((weightedUpper d2Transfer183C0 d2Log114Lo d2Log114Hi:ℚ):ℝ) + ((weightedUpper d2Transfer183C1 d2Log60Lo d2Log60Hi:ℚ):ℝ)) ≤ ((d2Transfer183Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer183Arithmetic
  linarith
#print axioms d2Transfer183Arithmetic
#print axioms d2Transfer183Bound
end CatalanMeasure.GenD.Signed.Data.Cells

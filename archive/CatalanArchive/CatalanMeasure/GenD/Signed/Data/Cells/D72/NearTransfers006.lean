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
namespace d2LitsNearTransfers006
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers006
open D72.LogTransfer
def d2Transfer48Lo : ℚ := (d2LitsNearTransfers006.q2 (25081867) 1 (-26))
def d2Transfer48Hi : ℚ := (d2LitsNearTransfers006.q2 (6689897) 1 (-24))
def d2Transfer48Cap : ℚ := (d2LitsNearTransfers006.q2 (648894057) 1 (-39))
def d2Transfer48C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 25 (-4))
def d2Transfer48S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer48Arithmetic : weightedUpper d2Transfer48C0 d2Log117Lo d2Log117Hi ≤ d2Transfer48Cap := by decide +kernel
theorem d2Transfer48Bound : ∀ x ∈ Set.Icc ((d2Transfer48Lo:ℚ):ℝ) ((d2Transfer48Hi:ℚ):ℝ), ((d2Transfer48C0:ℚ):ℝ)*Real.log |x-((d2Transfer48S0:ℚ):ℝ)| ≤ ((d2Transfer48Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer48S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer48S0,d2Transfer48Lo,d2Transfer48Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer48C0 then |x-((d2Transfer48S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer48S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer48S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer48S0,d2Transfer48Lo,d2Transfer48Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer48C0,d2Log117Q,d2Transfer48S0,d2Transfer48Lo,d2Transfer48Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer48C0 d2Transfer48S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2Transfer48C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2Transfer48Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer48Arithmetic
  linarith
#print axioms d2Transfer48Arithmetic
#print axioms d2Transfer48Bound
def d2Transfer49Lo : ℚ := (d2LitsNearTransfers006.q2 (25081867) 1 (-26))
def d2Transfer49Hi : ℚ := (d2LitsNearTransfers006.q2 (6689897) 1 (-24))
def d2Transfer49Cap : ℚ := (d2LitsNearTransfers006.q2 (2432512853) 1 (-40))
def d2Transfer49C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 275 (-4))
def d2Transfer49S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
def d2Transfer49C1 : ℚ := (d2LitsNearTransfers006.q2 (-1) 55 (-3))
def d2Transfer49S1 : ℚ := (d2LitsNearTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer49Arithmetic : weightedUpper d2Transfer49C0 d2Log117Lo d2Log117Hi + weightedUpper d2Transfer49C1 d2Log57Lo d2Log57Hi ≤ d2Transfer49Cap := by decide +kernel
theorem d2Transfer49Bound : ∀ x ∈ Set.Icc ((d2Transfer49Lo:ℚ):ℝ) ((d2Transfer49Hi:ℚ):ℝ), ((d2Transfer49C0:ℚ):ℝ)*Real.log |x-((d2Transfer49S0:ℚ):ℝ)| + ((d2Transfer49C1:ℚ):ℝ)*Real.log |x-((d2Transfer49S1:ℚ):ℝ)| ≤ ((d2Transfer49Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer49S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49S0,d2Transfer49Lo,d2Transfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer49C0 then |x-((d2Transfer49S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer49S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer49S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49S0,d2Transfer49Lo,d2Transfer49Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49C0,d2Log117Q,d2Transfer49S0,d2Transfer49Lo,d2Transfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer49C0 d2Transfer49S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2Transfer49S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49S1,d2Transfer49Lo,d2Transfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer49C1 then |x-((d2Transfer49S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2Transfer49S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer49S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49S1,d2Transfer49Lo,d2Transfer49Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer49C1,d2Log57Q,d2Transfer49S1,d2Transfer49Lo,d2Transfer49Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer49C1 d2Transfer49S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2Transfer49C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2Transfer49C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2Transfer49Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer49Arithmetic
  linarith
#print axioms d2Transfer49Arithmetic
#print axioms d2Transfer49Bound
def d2Transfer50Lo : ℚ := (d2LitsNearTransfers006.q2 (6689897) 1 (-24))
def d2Transfer50Hi : ℚ := (d2LitsNearTransfers006.q2 (15057515) 1 (-25))
def d2Transfer50Cap : ℚ := (d2LitsNearTransfers006.q2 (648894057) 1 (-39))
def d2Transfer50C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 25 (-4))
def d2Transfer50S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer50Arithmetic : weightedUpper d2Transfer50C0 d2Log119Lo d2Log119Hi ≤ d2Transfer50Cap := by decide +kernel
theorem d2Transfer50Bound : ∀ x ∈ Set.Icc ((d2Transfer50Lo:ℚ):ℝ) ((d2Transfer50Hi:ℚ):ℝ), ((d2Transfer50C0:ℚ):ℝ)*Real.log |x-((d2Transfer50S0:ℚ):ℝ)| ≤ ((d2Transfer50Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer50S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer50S0,d2Transfer50Lo,d2Transfer50Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer50C0 then |x-((d2Transfer50S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer50S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer50S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer50S0,d2Transfer50Lo,d2Transfer50Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer50C0,d2Log119Q,d2Transfer50S0,d2Transfer50Lo,d2Transfer50Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer50C0 d2Transfer50S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have har : (((weightedUpper d2Transfer50C0 d2Log119Lo d2Log119Hi:ℚ):ℝ)) ≤ ((d2Transfer50Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer50Arithmetic
  linarith
#print axioms d2Transfer50Arithmetic
#print axioms d2Transfer50Bound
def d2Transfer51Lo : ℚ := (d2LitsNearTransfers006.q2 (6689897) 1 (-24))
def d2Transfer51Hi : ℚ := (d2LitsNearTransfers006.q2 (15057515) 1 (-25))
def d2Transfer51Cap : ℚ := (d2LitsNearTransfers006.q2 (2432512853) 1 (-40))
def d2Transfer51C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 275 (-4))
def d2Transfer51S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
def d2Transfer51C1 : ℚ := (d2LitsNearTransfers006.q2 (-1) 55 (-3))
def d2Transfer51S1 : ℚ := (d2LitsNearTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer51Arithmetic : weightedUpper d2Transfer51C0 d2Log119Lo d2Log119Hi + weightedUpper d2Transfer51C1 d2Log55Lo d2Log55Hi ≤ d2Transfer51Cap := by decide +kernel
theorem d2Transfer51Bound : ∀ x ∈ Set.Icc ((d2Transfer51Lo:ℚ):ℝ) ((d2Transfer51Hi:ℚ):ℝ), ((d2Transfer51C0:ℚ):ℝ)*Real.log |x-((d2Transfer51S0:ℚ):ℝ)| + ((d2Transfer51C1:ℚ):ℝ)*Real.log |x-((d2Transfer51S1:ℚ):ℝ)| ≤ ((d2Transfer51Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer51S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51S0,d2Transfer51Lo,d2Transfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer51C0 then |x-((d2Transfer51S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer51S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer51S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51S0,d2Transfer51Lo,d2Transfer51Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51C0,d2Log119Q,d2Transfer51S0,d2Transfer51Lo,d2Transfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer51C0 d2Transfer51S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have hn1 : x-((d2Transfer51S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51S1,d2Transfer51Lo,d2Transfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer51C1 then |x-((d2Transfer51S1:ℚ):ℝ)| ≤ ((d2Log55Q:ℚ):ℝ) else ((d2Log55Q:ℚ):ℝ) ≤ |x-((d2Transfer51S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer51S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51S1,d2Transfer51Lo,d2Transfer51Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer51C1,d2Log55Q,d2Transfer51S1,d2Transfer51Lo,d2Transfer51Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer51C1 d2Transfer51S1 d2Log55Q d2Log55Lo d2Log55Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log55Bounds
  have har : (((weightedUpper d2Transfer51C0 d2Log119Lo d2Log119Hi:ℚ):ℝ) + ((weightedUpper d2Transfer51C1 d2Log55Lo d2Log55Hi:ℚ):ℝ)) ≤ ((d2Transfer51Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer51Arithmetic
  linarith
#print axioms d2Transfer51Arithmetic
#print axioms d2Transfer51Bound
def d2Transfer52Lo : ℚ := (d2LitsNearTransfers006.q2 (15057515) 1 (-25))
def d2Transfer52Hi : ℚ := (d2LitsNearTransfers006.q2 (4183809) 1 (-23))
def d2Transfer52Cap : ℚ := (d2LitsNearTransfers006.q2 (648894057) 1 (-39))
def d2Transfer52C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 25 (-4))
def d2Transfer52S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer52Arithmetic : weightedUpper d2Transfer52C0 d2Log120Lo d2Log120Hi ≤ d2Transfer52Cap := by decide +kernel
theorem d2Transfer52Bound : ∀ x ∈ Set.Icc ((d2Transfer52Lo:ℚ):ℝ) ((d2Transfer52Hi:ℚ):ℝ), ((d2Transfer52C0:ℚ):ℝ)*Real.log |x-((d2Transfer52S0:ℚ):ℝ)| ≤ ((d2Transfer52Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer52S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer52S0,d2Transfer52Lo,d2Transfer52Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer52C0 then |x-((d2Transfer52S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer52S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer52S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer52S0,d2Transfer52Lo,d2Transfer52Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer52C0,d2Log120Q,d2Transfer52S0,d2Transfer52Lo,d2Transfer52Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer52C0 d2Transfer52S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2Transfer52C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2Transfer52Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer52Arithmetic
  linarith
#print axioms d2Transfer52Arithmetic
#print axioms d2Transfer52Bound
def d2Transfer53Lo : ℚ := (d2LitsNearTransfers006.q2 (15057515) 1 (-25))
def d2Transfer53Hi : ℚ := (d2LitsNearTransfers006.q2 (4183809) 1 (-23))
def d2Transfer53Cap : ℚ := (d2LitsNearTransfers006.q2 (2432512853) 1 (-40))
def d2Transfer53C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 275 (-4))
def d2Transfer53S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
def d2Transfer53C1 : ℚ := (d2LitsNearTransfers006.q2 (-1) 55 (-3))
def d2Transfer53S1 : ℚ := (d2LitsNearTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer53Arithmetic : weightedUpper d2Transfer53C0 d2Log120Lo d2Log120Hi + weightedUpper d2Transfer53C1 d2Log54Lo d2Log54Hi ≤ d2Transfer53Cap := by decide +kernel
theorem d2Transfer53Bound : ∀ x ∈ Set.Icc ((d2Transfer53Lo:ℚ):ℝ) ((d2Transfer53Hi:ℚ):ℝ), ((d2Transfer53C0:ℚ):ℝ)*Real.log |x-((d2Transfer53S0:ℚ):ℝ)| + ((d2Transfer53C1:ℚ):ℝ)*Real.log |x-((d2Transfer53S1:ℚ):ℝ)| ≤ ((d2Transfer53Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer53S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53S0,d2Transfer53Lo,d2Transfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer53C0 then |x-((d2Transfer53S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer53S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer53S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53S0,d2Transfer53Lo,d2Transfer53Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53C0,d2Log120Q,d2Transfer53S0,d2Transfer53Lo,d2Transfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer53C0 d2Transfer53S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2Transfer53S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53S1,d2Transfer53Lo,d2Transfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer53C1 then |x-((d2Transfer53S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2Transfer53S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer53S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53S1,d2Transfer53Lo,d2Transfer53Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer53C1,d2Log54Q,d2Transfer53S1,d2Transfer53Lo,d2Transfer53Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer53C1 d2Transfer53S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2Transfer53C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2Transfer53C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2Transfer53Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer53Arithmetic
  linarith
#print axioms d2Transfer53Arithmetic
#print axioms d2Transfer53Bound
def d2Transfer54Lo : ℚ := (d2LitsNearTransfers006.q2 (4183809) 1 (-23))
def d2Transfer54Hi : ℚ := (d2LitsNearTransfers006.q2 (18412957) 1 (-25))
def d2Transfer54Cap : ℚ := (d2LitsNearTransfers006.q2 (648894057) 1 (-39))
def d2Transfer54C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 25 (-4))
def d2Transfer54S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer54Arithmetic : weightedUpper d2Transfer54C0 d2Log121Lo d2Log121Hi ≤ d2Transfer54Cap := by decide +kernel
theorem d2Transfer54Bound : ∀ x ∈ Set.Icc ((d2Transfer54Lo:ℚ):ℝ) ((d2Transfer54Hi:ℚ):ℝ), ((d2Transfer54C0:ℚ):ℝ)*Real.log |x-((d2Transfer54S0:ℚ):ℝ)| ≤ ((d2Transfer54Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer54S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer54S0,d2Transfer54Lo,d2Transfer54Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer54C0 then |x-((d2Transfer54S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer54S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer54S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer54S0,d2Transfer54Lo,d2Transfer54Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer54C0,d2Log121Q,d2Transfer54S0,d2Transfer54Lo,d2Transfer54Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer54C0 d2Transfer54S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2Transfer54C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2Transfer54Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer54Arithmetic
  linarith
#print axioms d2Transfer54Arithmetic
#print axioms d2Transfer54Bound
def d2Transfer55Lo : ℚ := (d2LitsNearTransfers006.q2 (4183809) 1 (-23))
def d2Transfer55Hi : ℚ := (d2LitsNearTransfers006.q2 (18412957) 1 (-25))
def d2Transfer55Cap : ℚ := (d2LitsNearTransfers006.q2 (2432512853) 1 (-40))
def d2Transfer55C0 : ℚ := (d2LitsNearTransfers006.q2 (1) 275 (-4))
def d2Transfer55S0 : ℚ := (d2LitsNearTransfers006.q2 (-1) 1 (0))
def d2Transfer55C1 : ℚ := (d2LitsNearTransfers006.q2 (-1) 55 (-3))
def d2Transfer55S1 : ℚ := (d2LitsNearTransfers006.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer55Arithmetic : weightedUpper d2Transfer55C0 d2Log121Lo d2Log121Hi + weightedUpper d2Transfer55C1 d2Log53Lo d2Log53Hi ≤ d2Transfer55Cap := by decide +kernel
theorem d2Transfer55Bound : ∀ x ∈ Set.Icc ((d2Transfer55Lo:ℚ):ℝ) ((d2Transfer55Hi:ℚ):ℝ), ((d2Transfer55C0:ℚ):ℝ)*Real.log |x-((d2Transfer55S0:ℚ):ℝ)| + ((d2Transfer55C1:ℚ):ℝ)*Real.log |x-((d2Transfer55S1:ℚ):ℝ)| ≤ ((d2Transfer55Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer55S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55S0,d2Transfer55Lo,d2Transfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer55C0 then |x-((d2Transfer55S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer55S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer55S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55S0,d2Transfer55Lo,d2Transfer55Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55C0,d2Log121Q,d2Transfer55S0,d2Transfer55Lo,d2Transfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer55C0 d2Transfer55S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2Transfer55S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55S1,d2Transfer55Lo,d2Transfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer55C1 then |x-((d2Transfer55S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2Transfer55S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer55S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55S1,d2Transfer55Lo,d2Transfer55Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers006.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer55C1,d2Log53Q,d2Transfer55S1,d2Transfer55Lo,d2Transfer55Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer55C1 d2Transfer55S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2Transfer55C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2Transfer55C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2Transfer55Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer55Arithmetic
  linarith
#print axioms d2Transfer55Arithmetic
#print axioms d2Transfer55Bound
end CatalanMeasure.GenD.Signed.Data.Cells

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
namespace d2LitsNearWiderTransfers034
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers034
open D72.LogTransfer
def d2WiderTransfer272Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (4183809) 1 (-23))
def d2WiderTransfer272Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (18412957) 1 (-25))
def d2WiderTransfer272Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (15113656175) 1 (-40))
def d2WiderTransfer272C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (23) 25 (-5))
def d2WiderTransfer272S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer272Arithmetic : weightedUpper d2WiderTransfer272C0 d2Log121Lo d2Log121Hi ≤ d2WiderTransfer272Cap := by decide +kernel
theorem d2WiderTransfer272Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer272Lo:ℚ):ℝ) ((d2WiderTransfer272Hi:ℚ):ℝ), ((d2WiderTransfer272C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer272S0:ℚ):ℝ)| ≤ ((d2WiderTransfer272Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer272S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer272S0,d2WiderTransfer272Lo,d2WiderTransfer272Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer272C0 then |x-((d2WiderTransfer272S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer272S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer272S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer272S0,d2WiderTransfer272Lo,d2WiderTransfer272Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer272C0,d2Log121Q,d2WiderTransfer272S0,d2WiderTransfer272Lo,d2WiderTransfer272Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer272C0 d2WiderTransfer272S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2WiderTransfer272C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer272Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer272Arithmetic
  linarith
#print axioms d2WiderTransfer272Arithmetic
#print axioms d2WiderTransfer272Bound
def d2WiderTransfer273Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (4183809) 1 (-23))
def d2WiderTransfer273Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (18412957) 1 (-25))
def d2WiderTransfer273Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (30439539927) 1 (-40))
def d2WiderTransfer273C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (3) 275 (-5))
def d2WiderTransfer273S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
def d2WiderTransfer273C1 : ℚ := (d2LitsNearWiderTransfers034.q2 (-5) 11 (-4))
def d2WiderTransfer273S1 : ℚ := (d2LitsNearWiderTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer273Arithmetic : weightedUpper d2WiderTransfer273C0 d2Log121Lo d2Log121Hi + weightedUpper d2WiderTransfer273C1 d2Log53Lo d2Log53Hi ≤ d2WiderTransfer273Cap := by decide +kernel
theorem d2WiderTransfer273Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer273Lo:ℚ):ℝ) ((d2WiderTransfer273Hi:ℚ):ℝ), ((d2WiderTransfer273C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer273S0:ℚ):ℝ)| + ((d2WiderTransfer273C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer273S1:ℚ):ℝ)| ≤ ((d2WiderTransfer273Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer273S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273S0,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer273C0 then |x-((d2WiderTransfer273S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer273S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer273S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273S0,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273C0,d2Log121Q,d2WiderTransfer273S0,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer273C0 d2WiderTransfer273S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2WiderTransfer273S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273S1,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer273C1 then |x-((d2WiderTransfer273S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer273S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer273S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273S1,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer273C1,d2Log53Q,d2WiderTransfer273S1,d2WiderTransfer273Lo,d2WiderTransfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer273C1 d2WiderTransfer273S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2WiderTransfer273C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer273C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer273Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer273Arithmetic
  linarith
#print axioms d2WiderTransfer273Arithmetic
#print axioms d2WiderTransfer273Bound
def d2WiderTransfer274Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (18412957) 1 (-25))
def d2WiderTransfer274Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer274Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (1169469059) 1 (-40))
def d2WiderTransfer274C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 55 (-3))
def d2WiderTransfer274S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
def d2WiderTransfer274C1 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 55 (-3))
def d2WiderTransfer274S1 : ℚ := (d2LitsNearWiderTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer274Arithmetic : weightedUpper d2WiderTransfer274C0 d2Log121Lo d2Log121Hi + weightedUpper d2WiderTransfer274C1 d2Log52Lo d2Log52Hi ≤ d2WiderTransfer274Cap := by decide +kernel
theorem d2WiderTransfer274Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer274Lo:ℚ):ℝ) ((d2WiderTransfer274Hi:ℚ):ℝ), ((d2WiderTransfer274C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer274S0:ℚ):ℝ)| + ((d2WiderTransfer274C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer274S1:ℚ):ℝ)| ≤ ((d2WiderTransfer274Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer274S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274S0,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer274C0 then |x-((d2WiderTransfer274S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer274S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer274S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274S0,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274C0,d2Log121Q,d2WiderTransfer274S0,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer274C0 d2WiderTransfer274S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2WiderTransfer274S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274S1,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer274C1 then |x-((d2WiderTransfer274S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer274S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer274S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274S1,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer274C1,d2Log52Q,d2WiderTransfer274S1,d2WiderTransfer274Lo,d2WiderTransfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer274C1 d2WiderTransfer274S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2WiderTransfer274C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer274C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer274Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer274Arithmetic
  linarith
#print axioms d2WiderTransfer274Arithmetic
#print axioms d2WiderTransfer274Bound
def d2WiderTransfer275Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (18412957) 1 (-25))
def d2WiderTransfer275Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer275Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (15113656175) 1 (-40))
def d2WiderTransfer275C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (23) 25 (-5))
def d2WiderTransfer275S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer275Arithmetic : weightedUpper d2WiderTransfer275C0 d2Log122Lo d2Log122Hi ≤ d2WiderTransfer275Cap := by decide +kernel
theorem d2WiderTransfer275Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer275Lo:ℚ):ℝ) ((d2WiderTransfer275Hi:ℚ):ℝ), ((d2WiderTransfer275C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer275S0:ℚ):ℝ)| ≤ ((d2WiderTransfer275Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer275S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer275S0,d2WiderTransfer275Lo,d2WiderTransfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer275C0 then |x-((d2WiderTransfer275S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer275S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer275S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer275S0,d2WiderTransfer275Lo,d2WiderTransfer275Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer275C0,d2Log122Q,d2WiderTransfer275S0,d2WiderTransfer275Lo,d2WiderTransfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer275C0 d2WiderTransfer275S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2WiderTransfer275C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer275Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer275Arithmetic
  linarith
#print axioms d2WiderTransfer275Arithmetic
#print axioms d2WiderTransfer275Bound
def d2WiderTransfer276Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (18412957) 1 (-25))
def d2WiderTransfer276Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer276Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (30439539927) 1 (-40))
def d2WiderTransfer276C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (3) 275 (-5))
def d2WiderTransfer276S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
def d2WiderTransfer276C1 : ℚ := (d2LitsNearWiderTransfers034.q2 (-5) 11 (-4))
def d2WiderTransfer276S1 : ℚ := (d2LitsNearWiderTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer276Arithmetic : weightedUpper d2WiderTransfer276C0 d2Log122Lo d2Log122Hi + weightedUpper d2WiderTransfer276C1 d2Log52Lo d2Log52Hi ≤ d2WiderTransfer276Cap := by decide +kernel
theorem d2WiderTransfer276Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer276Lo:ℚ):ℝ) ((d2WiderTransfer276Hi:ℚ):ℝ), ((d2WiderTransfer276C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer276S0:ℚ):ℝ)| + ((d2WiderTransfer276C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer276S1:ℚ):ℝ)| ≤ ((d2WiderTransfer276Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer276S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276S0,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer276C0 then |x-((d2WiderTransfer276S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer276S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer276S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276S0,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276C0,d2Log122Q,d2WiderTransfer276S0,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer276C0 d2WiderTransfer276S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2WiderTransfer276S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276S1,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer276C1 then |x-((d2WiderTransfer276S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer276S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer276S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276S1,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer276C1,d2Log52Q,d2WiderTransfer276S1,d2WiderTransfer276Lo,d2WiderTransfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer276C1 d2WiderTransfer276S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2WiderTransfer276C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer276C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer276Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer276Arithmetic
  linarith
#print axioms d2WiderTransfer276Arithmetic
#print axioms d2WiderTransfer276Bound
def d2WiderTransfer277Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer277Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (10045339) 1 (-24))
def d2WiderTransfer277Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (1169469059) 1 (-40))
def d2WiderTransfer277C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 55 (-3))
def d2WiderTransfer277S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
def d2WiderTransfer277C1 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 55 (-3))
def d2WiderTransfer277S1 : ℚ := (d2LitsNearWiderTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer277Arithmetic : weightedUpper d2WiderTransfer277C0 d2Log122Lo d2Log122Hi + weightedUpper d2WiderTransfer277C1 d2Log50Lo d2Log50Hi ≤ d2WiderTransfer277Cap := by decide +kernel
theorem d2WiderTransfer277Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer277Lo:ℚ):ℝ) ((d2WiderTransfer277Hi:ℚ):ℝ), ((d2WiderTransfer277C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer277S0:ℚ):ℝ)| + ((d2WiderTransfer277C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer277S1:ℚ):ℝ)| ≤ ((d2WiderTransfer277Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer277S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277S0,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer277C0 then |x-((d2WiderTransfer277S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer277S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer277S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277S0,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277C0,d2Log122Q,d2WiderTransfer277S0,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer277C0 d2WiderTransfer277S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2WiderTransfer277S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277S1,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer277C1 then |x-((d2WiderTransfer277S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer277S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer277S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277S1,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer277C1,d2Log50Q,d2WiderTransfer277S1,d2WiderTransfer277Lo,d2WiderTransfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer277C1 d2WiderTransfer277S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2WiderTransfer277C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer277C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer277Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer277Arithmetic
  linarith
#print axioms d2WiderTransfer277Arithmetic
#print axioms d2WiderTransfer277Bound
def d2WiderTransfer278Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer278Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (10045339) 1 (-24))
def d2WiderTransfer278Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (15113656175) 1 (-40))
def d2WiderTransfer278C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (23) 25 (-5))
def d2WiderTransfer278S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer278Arithmetic : weightedUpper d2WiderTransfer278C0 d2Log124Lo d2Log124Hi ≤ d2WiderTransfer278Cap := by decide +kernel
theorem d2WiderTransfer278Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer278Lo:ℚ):ℝ) ((d2WiderTransfer278Hi:ℚ):ℝ), ((d2WiderTransfer278C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer278S0:ℚ):ℝ)| ≤ ((d2WiderTransfer278Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer278S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer278S0,d2WiderTransfer278Lo,d2WiderTransfer278Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer278C0 then |x-((d2WiderTransfer278S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer278S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer278S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer278S0,d2WiderTransfer278Lo,d2WiderTransfer278Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer278C0,d2Log124Q,d2WiderTransfer278S0,d2WiderTransfer278Lo,d2WiderTransfer278Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer278C0 d2WiderTransfer278S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2WiderTransfer278C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer278Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer278Arithmetic
  linarith
#print axioms d2WiderTransfer278Arithmetic
#print axioms d2WiderTransfer278Bound
def d2WiderTransfer279Lo : ℚ := (d2LitsNearWiderTransfers034.q2 (38503635) 1 (-26))
def d2WiderTransfer279Hi : ℚ := (d2LitsNearWiderTransfers034.q2 (10045339) 1 (-24))
def d2WiderTransfer279Cap : ℚ := (d2LitsNearWiderTransfers034.q2 (30439539927) 1 (-40))
def d2WiderTransfer279C0 : ℚ := (d2LitsNearWiderTransfers034.q2 (3) 275 (-5))
def d2WiderTransfer279S0 : ℚ := (d2LitsNearWiderTransfers034.q2 (-1) 1 (0))
def d2WiderTransfer279C1 : ℚ := (d2LitsNearWiderTransfers034.q2 (-5) 11 (-4))
def d2WiderTransfer279S1 : ℚ := (d2LitsNearWiderTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer279Arithmetic : weightedUpper d2WiderTransfer279C0 d2Log124Lo d2Log124Hi + weightedUpper d2WiderTransfer279C1 d2Log50Lo d2Log50Hi ≤ d2WiderTransfer279Cap := by decide +kernel
theorem d2WiderTransfer279Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer279Lo:ℚ):ℝ) ((d2WiderTransfer279Hi:ℚ):ℝ), ((d2WiderTransfer279C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer279S0:ℚ):ℝ)| + ((d2WiderTransfer279C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer279S1:ℚ):ℝ)| ≤ ((d2WiderTransfer279Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer279S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279S0,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer279C0 then |x-((d2WiderTransfer279S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer279S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer279S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279S0,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279C0,d2Log124Q,d2WiderTransfer279S0,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer279C0 d2WiderTransfer279S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2WiderTransfer279S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279S1,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer279C1 then |x-((d2WiderTransfer279S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer279S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer279S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279S1,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers034.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer279C1,d2Log50Q,d2WiderTransfer279S1,d2WiderTransfer279Lo,d2WiderTransfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer279C1 d2WiderTransfer279S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2WiderTransfer279C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer279C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer279Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer279Arithmetic
  linarith
#print axioms d2WiderTransfer279Arithmetic
#print axioms d2WiderTransfer279Bound
end CatalanMeasure.GenD.Signed.Data.Cells

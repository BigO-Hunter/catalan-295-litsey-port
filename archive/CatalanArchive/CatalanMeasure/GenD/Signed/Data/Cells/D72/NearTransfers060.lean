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
namespace d2LitsNearTransfers060
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers060
open D72.LogTransfer
def d2Transfer480Lo : ℚ := (d2LitsNearTransfers060.q2 (15057515) 1 (-25))
def d2Transfer480Hi : ℚ := (d2LitsNearTransfers060.q2 (4183809) 1 (-23))
def d2Transfer480Cap : ℚ := (d2LitsNearTransfers060.q2 (30439539927) 1 (-40))
def d2Transfer480C0 : ℚ := (d2LitsNearTransfers060.q2 (3) 275 (-5))
def d2Transfer480S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer480C1 : ℚ := (d2LitsNearTransfers060.q2 (-5) 11 (-4))
def d2Transfer480S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer480Arithmetic : weightedUpper d2Transfer480C0 d2Log120Lo d2Log120Hi + weightedUpper d2Transfer480C1 d2Log54Lo d2Log54Hi ≤ d2Transfer480Cap := by decide +kernel
theorem d2Transfer480Bound : ∀ x ∈ Set.Icc ((d2Transfer480Lo:ℚ):ℝ) ((d2Transfer480Hi:ℚ):ℝ), ((d2Transfer480C0:ℚ):ℝ)*Real.log |x-((d2Transfer480S0:ℚ):ℝ)| + ((d2Transfer480C1:ℚ):ℝ)*Real.log |x-((d2Transfer480S1:ℚ):ℝ)| ≤ ((d2Transfer480Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer480S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480S0,d2Transfer480Lo,d2Transfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer480C0 then |x-((d2Transfer480S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer480S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer480S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480S0,d2Transfer480Lo,d2Transfer480Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480C0,d2Log120Q,d2Transfer480S0,d2Transfer480Lo,d2Transfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer480C0 d2Transfer480S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2Transfer480S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480S1,d2Transfer480Lo,d2Transfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer480C1 then |x-((d2Transfer480S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2Transfer480S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer480S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480S1,d2Transfer480Lo,d2Transfer480Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer480C1,d2Log54Q,d2Transfer480S1,d2Transfer480Lo,d2Transfer480Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer480C1 d2Transfer480S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2Transfer480C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2Transfer480C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2Transfer480Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer480Arithmetic
  linarith
#print axioms d2Transfer480Arithmetic
#print axioms d2Transfer480Bound
def d2Transfer481Lo : ℚ := (d2LitsNearTransfers060.q2 (4183809) 1 (-23))
def d2Transfer481Hi : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer481Cap : ℚ := (d2LitsNearTransfers060.q2 (1169469059) 1 (-40))
def d2Transfer481C0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer481S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer481C1 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer481S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer481Arithmetic : weightedUpper d2Transfer481C0 d2Log120Lo d2Log120Hi + weightedUpper d2Transfer481C1 d2Log53Lo d2Log53Hi ≤ d2Transfer481Cap := by decide +kernel
theorem d2Transfer481Bound : ∀ x ∈ Set.Icc ((d2Transfer481Lo:ℚ):ℝ) ((d2Transfer481Hi:ℚ):ℝ), ((d2Transfer481C0:ℚ):ℝ)*Real.log |x-((d2Transfer481S0:ℚ):ℝ)| + ((d2Transfer481C1:ℚ):ℝ)*Real.log |x-((d2Transfer481S1:ℚ):ℝ)| ≤ ((d2Transfer481Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer481S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481S0,d2Transfer481Lo,d2Transfer481Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer481C0 then |x-((d2Transfer481S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer481S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer481S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481S0,d2Transfer481Lo,d2Transfer481Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481C0,d2Log120Q,d2Transfer481S0,d2Transfer481Lo,d2Transfer481Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer481C0 d2Transfer481S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2Transfer481S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481S1,d2Transfer481Lo,d2Transfer481Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer481C1 then |x-((d2Transfer481S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2Transfer481S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer481S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481S1,d2Transfer481Lo,d2Transfer481Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer481C1,d2Log53Q,d2Transfer481S1,d2Transfer481Lo,d2Transfer481Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer481C1 d2Transfer481S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2Transfer481C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2Transfer481C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2Transfer481Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer481Arithmetic
  linarith
#print axioms d2Transfer481Arithmetic
#print axioms d2Transfer481Bound
def d2Transfer482Lo : ℚ := (d2LitsNearTransfers060.q2 (4183809) 1 (-23))
def d2Transfer482Hi : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer482Cap : ℚ := (d2LitsNearTransfers060.q2 (15113656175) 1 (-40))
def d2Transfer482C0 : ℚ := (d2LitsNearTransfers060.q2 (23) 25 (-5))
def d2Transfer482S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer482Arithmetic : weightedUpper d2Transfer482C0 d2Log121Lo d2Log121Hi ≤ d2Transfer482Cap := by decide +kernel
theorem d2Transfer482Bound : ∀ x ∈ Set.Icc ((d2Transfer482Lo:ℚ):ℝ) ((d2Transfer482Hi:ℚ):ℝ), ((d2Transfer482C0:ℚ):ℝ)*Real.log |x-((d2Transfer482S0:ℚ):ℝ)| ≤ ((d2Transfer482Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer482S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer482S0,d2Transfer482Lo,d2Transfer482Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer482C0 then |x-((d2Transfer482S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer482S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer482S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer482S0,d2Transfer482Lo,d2Transfer482Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer482C0,d2Log121Q,d2Transfer482S0,d2Transfer482Lo,d2Transfer482Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer482C0 d2Transfer482S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have har : (((weightedUpper d2Transfer482C0 d2Log121Lo d2Log121Hi:ℚ):ℝ)) ≤ ((d2Transfer482Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer482Arithmetic
  linarith
#print axioms d2Transfer482Arithmetic
#print axioms d2Transfer482Bound
def d2Transfer483Lo : ℚ := (d2LitsNearTransfers060.q2 (4183809) 1 (-23))
def d2Transfer483Hi : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer483Cap : ℚ := (d2LitsNearTransfers060.q2 (30439539927) 1 (-40))
def d2Transfer483C0 : ℚ := (d2LitsNearTransfers060.q2 (3) 275 (-5))
def d2Transfer483S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer483C1 : ℚ := (d2LitsNearTransfers060.q2 (-5) 11 (-4))
def d2Transfer483S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer483Arithmetic : weightedUpper d2Transfer483C0 d2Log121Lo d2Log121Hi + weightedUpper d2Transfer483C1 d2Log53Lo d2Log53Hi ≤ d2Transfer483Cap := by decide +kernel
theorem d2Transfer483Bound : ∀ x ∈ Set.Icc ((d2Transfer483Lo:ℚ):ℝ) ((d2Transfer483Hi:ℚ):ℝ), ((d2Transfer483C0:ℚ):ℝ)*Real.log |x-((d2Transfer483S0:ℚ):ℝ)| + ((d2Transfer483C1:ℚ):ℝ)*Real.log |x-((d2Transfer483S1:ℚ):ℝ)| ≤ ((d2Transfer483Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer483S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483S0,d2Transfer483Lo,d2Transfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer483C0 then |x-((d2Transfer483S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer483S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer483S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483S0,d2Transfer483Lo,d2Transfer483Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483C0,d2Log121Q,d2Transfer483S0,d2Transfer483Lo,d2Transfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer483C0 d2Transfer483S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2Transfer483S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483S1,d2Transfer483Lo,d2Transfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer483C1 then |x-((d2Transfer483S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2Transfer483S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer483S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483S1,d2Transfer483Lo,d2Transfer483Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer483C1,d2Log53Q,d2Transfer483S1,d2Transfer483Lo,d2Transfer483Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer483C1 d2Transfer483S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2Transfer483C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2Transfer483C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2Transfer483Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer483Arithmetic
  linarith
#print axioms d2Transfer483Arithmetic
#print axioms d2Transfer483Bound
def d2Transfer484Lo : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer484Hi : ℚ := (d2LitsNearTransfers060.q2 (38503635) 1 (-26))
def d2Transfer484Cap : ℚ := (d2LitsNearTransfers060.q2 (1169469059) 1 (-40))
def d2Transfer484C0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer484S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer484C1 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer484S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer484Arithmetic : weightedUpper d2Transfer484C0 d2Log121Lo d2Log121Hi + weightedUpper d2Transfer484C1 d2Log52Lo d2Log52Hi ≤ d2Transfer484Cap := by decide +kernel
theorem d2Transfer484Bound : ∀ x ∈ Set.Icc ((d2Transfer484Lo:ℚ):ℝ) ((d2Transfer484Hi:ℚ):ℝ), ((d2Transfer484C0:ℚ):ℝ)*Real.log |x-((d2Transfer484S0:ℚ):ℝ)| + ((d2Transfer484C1:ℚ):ℝ)*Real.log |x-((d2Transfer484S1:ℚ):ℝ)| ≤ ((d2Transfer484Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer484S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484S0,d2Transfer484Lo,d2Transfer484Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer484C0 then |x-((d2Transfer484S0:ℚ):ℝ)| ≤ ((d2Log121Q:ℚ):ℝ) else ((d2Log121Q:ℚ):ℝ) ≤ |x-((d2Transfer484S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer484S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484S0,d2Transfer484Lo,d2Transfer484Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484C0,d2Log121Q,d2Transfer484S0,d2Transfer484Lo,d2Transfer484Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer484C0 d2Transfer484S0 d2Log121Q d2Log121Lo d2Log121Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log121Bounds
  have hn1 : x-((d2Transfer484S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484S1,d2Transfer484Lo,d2Transfer484Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer484C1 then |x-((d2Transfer484S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2Transfer484S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer484S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484S1,d2Transfer484Lo,d2Transfer484Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer484C1,d2Log52Q,d2Transfer484S1,d2Transfer484Lo,d2Transfer484Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer484C1 d2Transfer484S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2Transfer484C0 d2Log121Lo d2Log121Hi:ℚ):ℝ) + ((weightedUpper d2Transfer484C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2Transfer484Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer484Arithmetic
  linarith
#print axioms d2Transfer484Arithmetic
#print axioms d2Transfer484Bound
def d2Transfer485Lo : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer485Hi : ℚ := (d2LitsNearTransfers060.q2 (38503635) 1 (-26))
def d2Transfer485Cap : ℚ := (d2LitsNearTransfers060.q2 (15113656175) 1 (-40))
def d2Transfer485C0 : ℚ := (d2LitsNearTransfers060.q2 (23) 25 (-5))
def d2Transfer485S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer485Arithmetic : weightedUpper d2Transfer485C0 d2Log122Lo d2Log122Hi ≤ d2Transfer485Cap := by decide +kernel
theorem d2Transfer485Bound : ∀ x ∈ Set.Icc ((d2Transfer485Lo:ℚ):ℝ) ((d2Transfer485Hi:ℚ):ℝ), ((d2Transfer485C0:ℚ):ℝ)*Real.log |x-((d2Transfer485S0:ℚ):ℝ)| ≤ ((d2Transfer485Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer485S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer485S0,d2Transfer485Lo,d2Transfer485Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer485C0 then |x-((d2Transfer485S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer485S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer485S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer485S0,d2Transfer485Lo,d2Transfer485Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer485C0,d2Log122Q,d2Transfer485S0,d2Transfer485Lo,d2Transfer485Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer485C0 d2Transfer485S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have har : (((weightedUpper d2Transfer485C0 d2Log122Lo d2Log122Hi:ℚ):ℝ)) ≤ ((d2Transfer485Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer485Arithmetic
  linarith
#print axioms d2Transfer485Arithmetic
#print axioms d2Transfer485Bound
def d2Transfer486Lo : ℚ := (d2LitsNearTransfers060.q2 (18412957) 1 (-25))
def d2Transfer486Hi : ℚ := (d2LitsNearTransfers060.q2 (38503635) 1 (-26))
def d2Transfer486Cap : ℚ := (d2LitsNearTransfers060.q2 (30439539927) 1 (-40))
def d2Transfer486C0 : ℚ := (d2LitsNearTransfers060.q2 (3) 275 (-5))
def d2Transfer486S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer486C1 : ℚ := (d2LitsNearTransfers060.q2 (-5) 11 (-4))
def d2Transfer486S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer486Arithmetic : weightedUpper d2Transfer486C0 d2Log122Lo d2Log122Hi + weightedUpper d2Transfer486C1 d2Log52Lo d2Log52Hi ≤ d2Transfer486Cap := by decide +kernel
theorem d2Transfer486Bound : ∀ x ∈ Set.Icc ((d2Transfer486Lo:ℚ):ℝ) ((d2Transfer486Hi:ℚ):ℝ), ((d2Transfer486C0:ℚ):ℝ)*Real.log |x-((d2Transfer486S0:ℚ):ℝ)| + ((d2Transfer486C1:ℚ):ℝ)*Real.log |x-((d2Transfer486S1:ℚ):ℝ)| ≤ ((d2Transfer486Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer486S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486S0,d2Transfer486Lo,d2Transfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer486C0 then |x-((d2Transfer486S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer486S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer486S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486S0,d2Transfer486Lo,d2Transfer486Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486C0,d2Log122Q,d2Transfer486S0,d2Transfer486Lo,d2Transfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer486C0 d2Transfer486S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2Transfer486S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486S1,d2Transfer486Lo,d2Transfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer486C1 then |x-((d2Transfer486S1:ℚ):ℝ)| ≤ ((d2Log52Q:ℚ):ℝ) else ((d2Log52Q:ℚ):ℝ) ≤ |x-((d2Transfer486S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer486S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486S1,d2Transfer486Lo,d2Transfer486Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer486C1,d2Log52Q,d2Transfer486S1,d2Transfer486Lo,d2Transfer486Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer486C1 d2Transfer486S1 d2Log52Q d2Log52Lo d2Log52Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log52Bounds
  have har : (((weightedUpper d2Transfer486C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2Transfer486C1 d2Log52Lo d2Log52Hi:ℚ):ℝ)) ≤ ((d2Transfer486Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer486Arithmetic
  linarith
#print axioms d2Transfer486Arithmetic
#print axioms d2Transfer486Bound
def d2Transfer487Lo : ℚ := (d2LitsNearTransfers060.q2 (38503635) 1 (-26))
def d2Transfer487Hi : ℚ := (d2LitsNearTransfers060.q2 (10045339) 1 (-24))
def d2Transfer487Cap : ℚ := (d2LitsNearTransfers060.q2 (1169469059) 1 (-40))
def d2Transfer487C0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer487S0 : ℚ := (d2LitsNearTransfers060.q2 (-1) 1 (0))
def d2Transfer487C1 : ℚ := (d2LitsNearTransfers060.q2 (-1) 55 (-3))
def d2Transfer487S1 : ℚ := (d2LitsNearTransfers060.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer487Arithmetic : weightedUpper d2Transfer487C0 d2Log122Lo d2Log122Hi + weightedUpper d2Transfer487C1 d2Log50Lo d2Log50Hi ≤ d2Transfer487Cap := by decide +kernel
theorem d2Transfer487Bound : ∀ x ∈ Set.Icc ((d2Transfer487Lo:ℚ):ℝ) ((d2Transfer487Hi:ℚ):ℝ), ((d2Transfer487C0:ℚ):ℝ)*Real.log |x-((d2Transfer487S0:ℚ):ℝ)| + ((d2Transfer487C1:ℚ):ℝ)*Real.log |x-((d2Transfer487S1:ℚ):ℝ)| ≤ ((d2Transfer487Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer487S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487S0,d2Transfer487Lo,d2Transfer487Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer487C0 then |x-((d2Transfer487S0:ℚ):ℝ)| ≤ ((d2Log122Q:ℚ):ℝ) else ((d2Log122Q:ℚ):ℝ) ≤ |x-((d2Transfer487S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer487S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487S0,d2Transfer487Lo,d2Transfer487Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487C0,d2Log122Q,d2Transfer487S0,d2Transfer487Lo,d2Transfer487Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer487C0 d2Transfer487S0 d2Log122Q d2Log122Lo d2Log122Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log122Bounds
  have hn1 : x-((d2Transfer487S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487S1,d2Transfer487Lo,d2Transfer487Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer487C1 then |x-((d2Transfer487S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2Transfer487S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer487S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487S1,d2Transfer487Lo,d2Transfer487Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers060.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer487C1,d2Log50Q,d2Transfer487S1,d2Transfer487Lo,d2Transfer487Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer487C1 d2Transfer487S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2Transfer487C0 d2Log122Lo d2Log122Hi:ℚ):ℝ) + ((weightedUpper d2Transfer487C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2Transfer487Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer487Arithmetic
  linarith
#print axioms d2Transfer487Arithmetic
#print axioms d2Transfer487Bound
end CatalanMeasure.GenD.Signed.Data.Cells

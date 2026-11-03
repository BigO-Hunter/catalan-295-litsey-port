module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers059
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers059
open D72.LogTransfer
def d2Transfer472Lo : ℚ := (d2LitsNearTransfers059.q2 (6689897) 1 (-24))
def d2Transfer472Hi : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer472Cap : ℚ := (d2LitsNearTransfers059.q2 (1169469059) 1 (-40))
def d2Transfer472C0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer472S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
def d2Transfer472C1 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer472S1 : ℚ := (d2LitsNearTransfers059.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer472Arithmetic : weightedUpper d2Transfer472C0 d2Log117Lo d2Log117Hi + weightedUpper d2Transfer472C1 d2Log56Lo d2Log56Hi ≤ d2Transfer472Cap := by decide +kernel
theorem d2Transfer472Bound : ∀ x ∈ Set.Icc ((d2Transfer472Lo:ℚ):ℝ) ((d2Transfer472Hi:ℚ):ℝ), ((d2Transfer472C0:ℚ):ℝ)*Real.log |x-((d2Transfer472S0:ℚ):ℝ)| + ((d2Transfer472C1:ℚ):ℝ)*Real.log |x-((d2Transfer472S1:ℚ):ℝ)| ≤ ((d2Transfer472Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer472S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472S0,d2Transfer472Lo,d2Transfer472Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer472C0 then |x-((d2Transfer472S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2Transfer472S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer472S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472S0,d2Transfer472Lo,d2Transfer472Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472C0,d2Log117Q,d2Transfer472S0,d2Transfer472Lo,d2Transfer472Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer472C0 d2Transfer472S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2Transfer472S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472S1,d2Transfer472Lo,d2Transfer472Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer472C1 then |x-((d2Transfer472S1:ℚ):ℝ)| ≤ ((d2Log56Q:ℚ):ℝ) else ((d2Log56Q:ℚ):ℝ) ≤ |x-((d2Transfer472S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer472S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472S1,d2Transfer472Lo,d2Transfer472Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer472C1,d2Log56Q,d2Transfer472S1,d2Transfer472Lo,d2Transfer472Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer472C1 d2Transfer472S1 d2Log56Q d2Log56Lo d2Log56Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log56Bounds
  have har : (((weightedUpper d2Transfer472C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2Transfer472C1 d2Log56Lo d2Log56Hi:ℚ):ℝ)) ≤ ((d2Transfer472Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer472Arithmetic
  linarith
#print axioms d2Transfer472Arithmetic
#print axioms d2Transfer472Bound
def d2Transfer473Lo : ℚ := (d2LitsNearTransfers059.q2 (6689897) 1 (-24))
def d2Transfer473Hi : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer473Cap : ℚ := (d2LitsNearTransfers059.q2 (15113656175) 1 (-40))
def d2Transfer473C0 : ℚ := (d2LitsNearTransfers059.q2 (23) 25 (-5))
def d2Transfer473S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer473Arithmetic : weightedUpper d2Transfer473C0 d2Log118Lo d2Log118Hi ≤ d2Transfer473Cap := by decide +kernel
theorem d2Transfer473Bound : ∀ x ∈ Set.Icc ((d2Transfer473Lo:ℚ):ℝ) ((d2Transfer473Hi:ℚ):ℝ), ((d2Transfer473C0:ℚ):ℝ)*Real.log |x-((d2Transfer473S0:ℚ):ℝ)| ≤ ((d2Transfer473Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer473S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer473S0,d2Transfer473Lo,d2Transfer473Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer473C0 then |x-((d2Transfer473S0:ℚ):ℝ)| ≤ ((d2Log118Q:ℚ):ℝ) else ((d2Log118Q:ℚ):ℝ) ≤ |x-((d2Transfer473S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer473S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer473S0,d2Transfer473Lo,d2Transfer473Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer473C0,d2Log118Q,d2Transfer473S0,d2Transfer473Lo,d2Transfer473Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer473C0 d2Transfer473S0 d2Log118Q d2Log118Lo d2Log118Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log118Bounds
  have har : (((weightedUpper d2Transfer473C0 d2Log118Lo d2Log118Hi:ℚ):ℝ)) ≤ ((d2Transfer473Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer473Arithmetic
  linarith
#print axioms d2Transfer473Arithmetic
#print axioms d2Transfer473Bound
def d2Transfer474Lo : ℚ := (d2LitsNearTransfers059.q2 (6689897) 1 (-24))
def d2Transfer474Hi : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer474Cap : ℚ := (d2LitsNearTransfers059.q2 (30439539927) 1 (-40))
def d2Transfer474C0 : ℚ := (d2LitsNearTransfers059.q2 (3) 275 (-5))
def d2Transfer474S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
def d2Transfer474C1 : ℚ := (d2LitsNearTransfers059.q2 (-5) 11 (-4))
def d2Transfer474S1 : ℚ := (d2LitsNearTransfers059.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer474Arithmetic : weightedUpper d2Transfer474C0 d2Log118Lo d2Log118Hi + weightedUpper d2Transfer474C1 d2Log56Lo d2Log56Hi ≤ d2Transfer474Cap := by decide +kernel
theorem d2Transfer474Bound : ∀ x ∈ Set.Icc ((d2Transfer474Lo:ℚ):ℝ) ((d2Transfer474Hi:ℚ):ℝ), ((d2Transfer474C0:ℚ):ℝ)*Real.log |x-((d2Transfer474S0:ℚ):ℝ)| + ((d2Transfer474C1:ℚ):ℝ)*Real.log |x-((d2Transfer474S1:ℚ):ℝ)| ≤ ((d2Transfer474Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer474S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474S0,d2Transfer474Lo,d2Transfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer474C0 then |x-((d2Transfer474S0:ℚ):ℝ)| ≤ ((d2Log118Q:ℚ):ℝ) else ((d2Log118Q:ℚ):ℝ) ≤ |x-((d2Transfer474S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer474S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474S0,d2Transfer474Lo,d2Transfer474Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474C0,d2Log118Q,d2Transfer474S0,d2Transfer474Lo,d2Transfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer474C0 d2Transfer474S0 d2Log118Q d2Log118Lo d2Log118Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log118Bounds
  have hn1 : x-((d2Transfer474S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474S1,d2Transfer474Lo,d2Transfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer474C1 then |x-((d2Transfer474S1:ℚ):ℝ)| ≤ ((d2Log56Q:ℚ):ℝ) else ((d2Log56Q:ℚ):ℝ) ≤ |x-((d2Transfer474S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer474S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474S1,d2Transfer474Lo,d2Transfer474Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer474C1,d2Log56Q,d2Transfer474S1,d2Transfer474Lo,d2Transfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer474C1 d2Transfer474S1 d2Log56Q d2Log56Lo d2Log56Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log56Bounds
  have har : (((weightedUpper d2Transfer474C0 d2Log118Lo d2Log118Hi:ℚ):ℝ) + ((weightedUpper d2Transfer474C1 d2Log56Lo d2Log56Hi:ℚ):ℝ)) ≤ ((d2Transfer474Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer474Arithmetic
  linarith
#print axioms d2Transfer474Arithmetic
#print axioms d2Transfer474Bound
def d2Transfer475Lo : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer475Hi : ℚ := (d2LitsNearTransfers059.q2 (15057515) 1 (-25))
def d2Transfer475Cap : ℚ := (d2LitsNearTransfers059.q2 (1169469059) 1 (-40))
def d2Transfer475C0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer475S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
def d2Transfer475C1 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer475S1 : ℚ := (d2LitsNearTransfers059.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer475Arithmetic : weightedUpper d2Transfer475C0 d2Log118Lo d2Log118Hi + weightedUpper d2Transfer475C1 d2Log55Lo d2Log55Hi ≤ d2Transfer475Cap := by decide +kernel
theorem d2Transfer475Bound : ∀ x ∈ Set.Icc ((d2Transfer475Lo:ℚ):ℝ) ((d2Transfer475Hi:ℚ):ℝ), ((d2Transfer475C0:ℚ):ℝ)*Real.log |x-((d2Transfer475S0:ℚ):ℝ)| + ((d2Transfer475C1:ℚ):ℝ)*Real.log |x-((d2Transfer475S1:ℚ):ℝ)| ≤ ((d2Transfer475Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer475S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475S0,d2Transfer475Lo,d2Transfer475Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer475C0 then |x-((d2Transfer475S0:ℚ):ℝ)| ≤ ((d2Log118Q:ℚ):ℝ) else ((d2Log118Q:ℚ):ℝ) ≤ |x-((d2Transfer475S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer475S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475S0,d2Transfer475Lo,d2Transfer475Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475C0,d2Log118Q,d2Transfer475S0,d2Transfer475Lo,d2Transfer475Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer475C0 d2Transfer475S0 d2Log118Q d2Log118Lo d2Log118Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log118Bounds
  have hn1 : x-((d2Transfer475S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475S1,d2Transfer475Lo,d2Transfer475Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer475C1 then |x-((d2Transfer475S1:ℚ):ℝ)| ≤ ((d2Log55Q:ℚ):ℝ) else ((d2Log55Q:ℚ):ℝ) ≤ |x-((d2Transfer475S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer475S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475S1,d2Transfer475Lo,d2Transfer475Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer475C1,d2Log55Q,d2Transfer475S1,d2Transfer475Lo,d2Transfer475Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer475C1 d2Transfer475S1 d2Log55Q d2Log55Lo d2Log55Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log55Bounds
  have har : (((weightedUpper d2Transfer475C0 d2Log118Lo d2Log118Hi:ℚ):ℝ) + ((weightedUpper d2Transfer475C1 d2Log55Lo d2Log55Hi:ℚ):ℝ)) ≤ ((d2Transfer475Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer475Arithmetic
  linarith
#print axioms d2Transfer475Arithmetic
#print axioms d2Transfer475Bound
def d2Transfer476Lo : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer476Hi : ℚ := (d2LitsNearTransfers059.q2 (15057515) 1 (-25))
def d2Transfer476Cap : ℚ := (d2LitsNearTransfers059.q2 (15113656175) 1 (-40))
def d2Transfer476C0 : ℚ := (d2LitsNearTransfers059.q2 (23) 25 (-5))
def d2Transfer476S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer476Arithmetic : weightedUpper d2Transfer476C0 d2Log119Lo d2Log119Hi ≤ d2Transfer476Cap := by decide +kernel
theorem d2Transfer476Bound : ∀ x ∈ Set.Icc ((d2Transfer476Lo:ℚ):ℝ) ((d2Transfer476Hi:ℚ):ℝ), ((d2Transfer476C0:ℚ):ℝ)*Real.log |x-((d2Transfer476S0:ℚ):ℝ)| ≤ ((d2Transfer476Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer476S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer476S0,d2Transfer476Lo,d2Transfer476Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer476C0 then |x-((d2Transfer476S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer476S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer476S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer476S0,d2Transfer476Lo,d2Transfer476Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer476C0,d2Log119Q,d2Transfer476S0,d2Transfer476Lo,d2Transfer476Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer476C0 d2Transfer476S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have har : (((weightedUpper d2Transfer476C0 d2Log119Lo d2Log119Hi:ℚ):ℝ)) ≤ ((d2Transfer476Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer476Arithmetic
  linarith
#print axioms d2Transfer476Arithmetic
#print axioms d2Transfer476Bound
def d2Transfer477Lo : ℚ := (d2LitsNearTransfers059.q2 (28437309) 1 (-26))
def d2Transfer477Hi : ℚ := (d2LitsNearTransfers059.q2 (15057515) 1 (-25))
def d2Transfer477Cap : ℚ := (d2LitsNearTransfers059.q2 (30439539927) 1 (-40))
def d2Transfer477C0 : ℚ := (d2LitsNearTransfers059.q2 (3) 275 (-5))
def d2Transfer477S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
def d2Transfer477C1 : ℚ := (d2LitsNearTransfers059.q2 (-5) 11 (-4))
def d2Transfer477S1 : ℚ := (d2LitsNearTransfers059.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer477Arithmetic : weightedUpper d2Transfer477C0 d2Log119Lo d2Log119Hi + weightedUpper d2Transfer477C1 d2Log55Lo d2Log55Hi ≤ d2Transfer477Cap := by decide +kernel
theorem d2Transfer477Bound : ∀ x ∈ Set.Icc ((d2Transfer477Lo:ℚ):ℝ) ((d2Transfer477Hi:ℚ):ℝ), ((d2Transfer477C0:ℚ):ℝ)*Real.log |x-((d2Transfer477S0:ℚ):ℝ)| + ((d2Transfer477C1:ℚ):ℝ)*Real.log |x-((d2Transfer477S1:ℚ):ℝ)| ≤ ((d2Transfer477Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer477S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477S0,d2Transfer477Lo,d2Transfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer477C0 then |x-((d2Transfer477S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer477S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer477S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477S0,d2Transfer477Lo,d2Transfer477Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477C0,d2Log119Q,d2Transfer477S0,d2Transfer477Lo,d2Transfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer477C0 d2Transfer477S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have hn1 : x-((d2Transfer477S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477S1,d2Transfer477Lo,d2Transfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer477C1 then |x-((d2Transfer477S1:ℚ):ℝ)| ≤ ((d2Log55Q:ℚ):ℝ) else ((d2Log55Q:ℚ):ℝ) ≤ |x-((d2Transfer477S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer477S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477S1,d2Transfer477Lo,d2Transfer477Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer477C1,d2Log55Q,d2Transfer477S1,d2Transfer477Lo,d2Transfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer477C1 d2Transfer477S1 d2Log55Q d2Log55Lo d2Log55Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log55Bounds
  have har : (((weightedUpper d2Transfer477C0 d2Log119Lo d2Log119Hi:ℚ):ℝ) + ((weightedUpper d2Transfer477C1 d2Log55Lo d2Log55Hi:ℚ):ℝ)) ≤ ((d2Transfer477Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer477Arithmetic
  linarith
#print axioms d2Transfer477Arithmetic
#print axioms d2Transfer477Bound
def d2Transfer478Lo : ℚ := (d2LitsNearTransfers059.q2 (15057515) 1 (-25))
def d2Transfer478Hi : ℚ := (d2LitsNearTransfers059.q2 (4183809) 1 (-23))
def d2Transfer478Cap : ℚ := (d2LitsNearTransfers059.q2 (1169469059) 1 (-40))
def d2Transfer478C0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer478S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
def d2Transfer478C1 : ℚ := (d2LitsNearTransfers059.q2 (-1) 55 (-3))
def d2Transfer478S1 : ℚ := (d2LitsNearTransfers059.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer478Arithmetic : weightedUpper d2Transfer478C0 d2Log119Lo d2Log119Hi + weightedUpper d2Transfer478C1 d2Log54Lo d2Log54Hi ≤ d2Transfer478Cap := by decide +kernel
theorem d2Transfer478Bound : ∀ x ∈ Set.Icc ((d2Transfer478Lo:ℚ):ℝ) ((d2Transfer478Hi:ℚ):ℝ), ((d2Transfer478C0:ℚ):ℝ)*Real.log |x-((d2Transfer478S0:ℚ):ℝ)| + ((d2Transfer478C1:ℚ):ℝ)*Real.log |x-((d2Transfer478S1:ℚ):ℝ)| ≤ ((d2Transfer478Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer478S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478S0,d2Transfer478Lo,d2Transfer478Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer478C0 then |x-((d2Transfer478S0:ℚ):ℝ)| ≤ ((d2Log119Q:ℚ):ℝ) else ((d2Log119Q:ℚ):ℝ) ≤ |x-((d2Transfer478S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer478S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478S0,d2Transfer478Lo,d2Transfer478Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478C0,d2Log119Q,d2Transfer478S0,d2Transfer478Lo,d2Transfer478Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer478C0 d2Transfer478S0 d2Log119Q d2Log119Lo d2Log119Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log119Bounds
  have hn1 : x-((d2Transfer478S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478S1,d2Transfer478Lo,d2Transfer478Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer478C1 then |x-((d2Transfer478S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2Transfer478S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer478S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478S1,d2Transfer478Lo,d2Transfer478Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer478C1,d2Log54Q,d2Transfer478S1,d2Transfer478Lo,d2Transfer478Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer478C1 d2Transfer478S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2Transfer478C0 d2Log119Lo d2Log119Hi:ℚ):ℝ) + ((weightedUpper d2Transfer478C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2Transfer478Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer478Arithmetic
  linarith
#print axioms d2Transfer478Arithmetic
#print axioms d2Transfer478Bound
def d2Transfer479Lo : ℚ := (d2LitsNearTransfers059.q2 (15057515) 1 (-25))
def d2Transfer479Hi : ℚ := (d2LitsNearTransfers059.q2 (4183809) 1 (-23))
def d2Transfer479Cap : ℚ := (d2LitsNearTransfers059.q2 (15113656175) 1 (-40))
def d2Transfer479C0 : ℚ := (d2LitsNearTransfers059.q2 (23) 25 (-5))
def d2Transfer479S0 : ℚ := (d2LitsNearTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer479Arithmetic : weightedUpper d2Transfer479C0 d2Log120Lo d2Log120Hi ≤ d2Transfer479Cap := by decide +kernel
theorem d2Transfer479Bound : ∀ x ∈ Set.Icc ((d2Transfer479Lo:ℚ):ℝ) ((d2Transfer479Hi:ℚ):ℝ), ((d2Transfer479C0:ℚ):ℝ)*Real.log |x-((d2Transfer479S0:ℚ):ℝ)| ≤ ((d2Transfer479Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer479S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer479S0,d2Transfer479Lo,d2Transfer479Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer479C0 then |x-((d2Transfer479S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2Transfer479S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer479S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer479S0,d2Transfer479Lo,d2Transfer479Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers059.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer479C0,d2Log120Q,d2Transfer479S0,d2Transfer479Lo,d2Transfer479Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer479C0 d2Transfer479S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2Transfer479C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2Transfer479Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer479Arithmetic
  linarith
#print axioms d2Transfer479Arithmetic
#print axioms d2Transfer479Bound
end CatalanMeasure.GenD.Signed.Data.Cells

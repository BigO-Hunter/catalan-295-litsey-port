module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers050
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers050
open D72.LogTransfer
def d2Transfer400Lo : ℚ := (d2LitsNearTransfers050.q2 (61404093) 1 (-29))
def d2Transfer400Hi : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer400Cap : ℚ := (d2LitsNearTransfers050.q2 (1169469059) 1 (-40))
def d2Transfer400C0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer400S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
def d2Transfer400C1 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer400S1 : ℚ := (d2LitsNearTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer400Arithmetic : weightedUpper d2Transfer400C0 d2Log93Lo d2Log93Hi + weightedUpper d2Transfer400C1 d2Log80Lo d2Log80Hi ≤ d2Transfer400Cap := by decide +kernel
theorem d2Transfer400Bound : ∀ x ∈ Set.Icc ((d2Transfer400Lo:ℚ):ℝ) ((d2Transfer400Hi:ℚ):ℝ), ((d2Transfer400C0:ℚ):ℝ)*Real.log |x-((d2Transfer400S0:ℚ):ℝ)| + ((d2Transfer400C1:ℚ):ℝ)*Real.log |x-((d2Transfer400S1:ℚ):ℝ)| ≤ ((d2Transfer400Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer400S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400S0,d2Transfer400Lo,d2Transfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer400C0 then |x-((d2Transfer400S0:ℚ):ℝ)| ≤ ((d2Log93Q:ℚ):ℝ) else ((d2Log93Q:ℚ):ℝ) ≤ |x-((d2Transfer400S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer400S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400S0,d2Transfer400Lo,d2Transfer400Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400C0,d2Log93Q,d2Transfer400S0,d2Transfer400Lo,d2Transfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer400C0 d2Transfer400S0 d2Log93Q d2Log93Lo d2Log93Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log93Bounds
  have hn1 : x-((d2Transfer400S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400S1,d2Transfer400Lo,d2Transfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer400C1 then |x-((d2Transfer400S1:ℚ):ℝ)| ≤ ((d2Log80Q:ℚ):ℝ) else ((d2Log80Q:ℚ):ℝ) ≤ |x-((d2Transfer400S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer400S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400S1,d2Transfer400Lo,d2Transfer400Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer400C1,d2Log80Q,d2Transfer400S1,d2Transfer400Lo,d2Transfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer400C1 d2Transfer400S1 d2Log80Q d2Log80Lo d2Log80Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log80Bounds
  have har : (((weightedUpper d2Transfer400C0 d2Log93Lo d2Log93Hi:ℚ):ℝ) + ((weightedUpper d2Transfer400C1 d2Log80Lo d2Log80Hi:ℚ):ℝ)) ≤ ((d2Transfer400Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer400Arithmetic
  linarith
#print axioms d2Transfer400Arithmetic
#print axioms d2Transfer400Bound
def d2Transfer401Lo : ℚ := (d2LitsNearTransfers050.q2 (61404093) 1 (-29))
def d2Transfer401Hi : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer401Cap : ℚ := (d2LitsNearTransfers050.q2 (15113656175) 1 (-40))
def d2Transfer401C0 : ℚ := (d2LitsNearTransfers050.q2 (23) 25 (-5))
def d2Transfer401S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer401Arithmetic : weightedUpper d2Transfer401C0 d2Log94Lo d2Log94Hi ≤ d2Transfer401Cap := by decide +kernel
theorem d2Transfer401Bound : ∀ x ∈ Set.Icc ((d2Transfer401Lo:ℚ):ℝ) ((d2Transfer401Hi:ℚ):ℝ), ((d2Transfer401C0:ℚ):ℝ)*Real.log |x-((d2Transfer401S0:ℚ):ℝ)| ≤ ((d2Transfer401Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer401S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer401S0,d2Transfer401Lo,d2Transfer401Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer401C0 then |x-((d2Transfer401S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer401S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer401S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer401S0,d2Transfer401Lo,d2Transfer401Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer401C0,d2Log94Q,d2Transfer401S0,d2Transfer401Lo,d2Transfer401Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer401C0 d2Transfer401S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have har : (((weightedUpper d2Transfer401C0 d2Log94Lo d2Log94Hi:ℚ):ℝ)) ≤ ((d2Transfer401Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer401Arithmetic
  linarith
#print axioms d2Transfer401Arithmetic
#print axioms d2Transfer401Bound
def d2Transfer402Lo : ℚ := (d2LitsNearTransfers050.q2 (61404093) 1 (-29))
def d2Transfer402Hi : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer402Cap : ℚ := (d2LitsNearTransfers050.q2 (30439539927) 1 (-40))
def d2Transfer402C0 : ℚ := (d2LitsNearTransfers050.q2 (3) 275 (-5))
def d2Transfer402S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
def d2Transfer402C1 : ℚ := (d2LitsNearTransfers050.q2 (-5) 11 (-4))
def d2Transfer402S1 : ℚ := (d2LitsNearTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer402Arithmetic : weightedUpper d2Transfer402C0 d2Log94Lo d2Log94Hi + weightedUpper d2Transfer402C1 d2Log80Lo d2Log80Hi ≤ d2Transfer402Cap := by decide +kernel
theorem d2Transfer402Bound : ∀ x ∈ Set.Icc ((d2Transfer402Lo:ℚ):ℝ) ((d2Transfer402Hi:ℚ):ℝ), ((d2Transfer402C0:ℚ):ℝ)*Real.log |x-((d2Transfer402S0:ℚ):ℝ)| + ((d2Transfer402C1:ℚ):ℝ)*Real.log |x-((d2Transfer402S1:ℚ):ℝ)| ≤ ((d2Transfer402Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer402S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402S0,d2Transfer402Lo,d2Transfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer402C0 then |x-((d2Transfer402S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer402S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer402S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402S0,d2Transfer402Lo,d2Transfer402Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402C0,d2Log94Q,d2Transfer402S0,d2Transfer402Lo,d2Transfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer402C0 d2Transfer402S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have hn1 : x-((d2Transfer402S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402S1,d2Transfer402Lo,d2Transfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer402C1 then |x-((d2Transfer402S1:ℚ):ℝ)| ≤ ((d2Log80Q:ℚ):ℝ) else ((d2Log80Q:ℚ):ℝ) ≤ |x-((d2Transfer402S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer402S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402S1,d2Transfer402Lo,d2Transfer402Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer402C1,d2Log80Q,d2Transfer402S1,d2Transfer402Lo,d2Transfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer402C1 d2Transfer402S1 d2Log80Q d2Log80Lo d2Log80Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log80Bounds
  have har : (((weightedUpper d2Transfer402C0 d2Log94Lo d2Log94Hi:ℚ):ℝ) + ((weightedUpper d2Transfer402C1 d2Log80Lo d2Log80Hi:ℚ):ℝ)) ≤ ((d2Transfer402Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer402Arithmetic
  linarith
#print axioms d2Transfer402Arithmetic
#print axioms d2Transfer402Bound
def d2Transfer403Lo : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer403Hi : ℚ := (d2LitsNearTransfers050.q2 (8304657) 1 (-26))
def d2Transfer403Cap : ℚ := (d2LitsNearTransfers050.q2 (1169469059) 1 (-40))
def d2Transfer403C0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer403S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
def d2Transfer403C1 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer403S1 : ℚ := (d2LitsNearTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer403Arithmetic : weightedUpper d2Transfer403C0 d2Log94Lo d2Log94Hi + weightedUpper d2Transfer403C1 d2Log79Lo d2Log79Hi ≤ d2Transfer403Cap := by decide +kernel
theorem d2Transfer403Bound : ∀ x ∈ Set.Icc ((d2Transfer403Lo:ℚ):ℝ) ((d2Transfer403Hi:ℚ):ℝ), ((d2Transfer403C0:ℚ):ℝ)*Real.log |x-((d2Transfer403S0:ℚ):ℝ)| + ((d2Transfer403C1:ℚ):ℝ)*Real.log |x-((d2Transfer403S1:ℚ):ℝ)| ≤ ((d2Transfer403Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer403S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403S0,d2Transfer403Lo,d2Transfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer403C0 then |x-((d2Transfer403S0:ℚ):ℝ)| ≤ ((d2Log94Q:ℚ):ℝ) else ((d2Log94Q:ℚ):ℝ) ≤ |x-((d2Transfer403S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer403S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403S0,d2Transfer403Lo,d2Transfer403Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403C0,d2Log94Q,d2Transfer403S0,d2Transfer403Lo,d2Transfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer403C0 d2Transfer403S0 d2Log94Q d2Log94Lo d2Log94Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log94Bounds
  have hn1 : x-((d2Transfer403S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403S1,d2Transfer403Lo,d2Transfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer403C1 then |x-((d2Transfer403S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2Transfer403S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer403S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403S1,d2Transfer403Lo,d2Transfer403Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer403C1,d2Log79Q,d2Transfer403S1,d2Transfer403Lo,d2Transfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer403C1 d2Transfer403S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2Transfer403C0 d2Log94Lo d2Log94Hi:ℚ):ℝ) + ((weightedUpper d2Transfer403C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2Transfer403Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer403Arithmetic
  linarith
#print axioms d2Transfer403Arithmetic
#print axioms d2Transfer403Bound
def d2Transfer404Lo : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer404Hi : ℚ := (d2LitsNearTransfers050.q2 (8304657) 1 (-26))
def d2Transfer404Cap : ℚ := (d2LitsNearTransfers050.q2 (15113656175) 1 (-40))
def d2Transfer404C0 : ℚ := (d2LitsNearTransfers050.q2 (23) 25 (-5))
def d2Transfer404S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer404Arithmetic : weightedUpper d2Transfer404C0 d2Log95Lo d2Log95Hi ≤ d2Transfer404Cap := by decide +kernel
theorem d2Transfer404Bound : ∀ x ∈ Set.Icc ((d2Transfer404Lo:ℚ):ℝ) ((d2Transfer404Hi:ℚ):ℝ), ((d2Transfer404C0:ℚ):ℝ)*Real.log |x-((d2Transfer404S0:ℚ):ℝ)| ≤ ((d2Transfer404Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer404S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer404S0,d2Transfer404Lo,d2Transfer404Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer404C0 then |x-((d2Transfer404S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer404S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer404S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer404S0,d2Transfer404Lo,d2Transfer404Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer404C0,d2Log95Q,d2Transfer404S0,d2Transfer404Lo,d2Transfer404Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer404C0 d2Transfer404S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2Transfer404C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2Transfer404Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer404Arithmetic
  linarith
#print axioms d2Transfer404Arithmetic
#print axioms d2Transfer404Bound
def d2Transfer405Lo : ℚ := (d2LitsNearTransfers050.q2 (31540907) 1 (-28))
def d2Transfer405Hi : ℚ := (d2LitsNearTransfers050.q2 (8304657) 1 (-26))
def d2Transfer405Cap : ℚ := (d2LitsNearTransfers050.q2 (30439539927) 1 (-40))
def d2Transfer405C0 : ℚ := (d2LitsNearTransfers050.q2 (3) 275 (-5))
def d2Transfer405S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
def d2Transfer405C1 : ℚ := (d2LitsNearTransfers050.q2 (-5) 11 (-4))
def d2Transfer405S1 : ℚ := (d2LitsNearTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer405Arithmetic : weightedUpper d2Transfer405C0 d2Log95Lo d2Log95Hi + weightedUpper d2Transfer405C1 d2Log79Lo d2Log79Hi ≤ d2Transfer405Cap := by decide +kernel
theorem d2Transfer405Bound : ∀ x ∈ Set.Icc ((d2Transfer405Lo:ℚ):ℝ) ((d2Transfer405Hi:ℚ):ℝ), ((d2Transfer405C0:ℚ):ℝ)*Real.log |x-((d2Transfer405S0:ℚ):ℝ)| + ((d2Transfer405C1:ℚ):ℝ)*Real.log |x-((d2Transfer405S1:ℚ):ℝ)| ≤ ((d2Transfer405Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer405S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405S0,d2Transfer405Lo,d2Transfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer405C0 then |x-((d2Transfer405S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer405S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer405S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405S0,d2Transfer405Lo,d2Transfer405Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405C0,d2Log95Q,d2Transfer405S0,d2Transfer405Lo,d2Transfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer405C0 d2Transfer405S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2Transfer405S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405S1,d2Transfer405Lo,d2Transfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer405C1 then |x-((d2Transfer405S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2Transfer405S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer405S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405S1,d2Transfer405Lo,d2Transfer405Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer405C1,d2Log79Q,d2Transfer405S1,d2Transfer405Lo,d2Transfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer405C1 d2Transfer405S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2Transfer405C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2Transfer405C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2Transfer405Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer405Arithmetic
  linarith
#print axioms d2Transfer405Arithmetic
#print axioms d2Transfer405Bound
def d2Transfer406Lo : ℚ := (d2LitsNearTransfers050.q2 (8304657) 1 (-26))
def d2Transfer406Hi : ℚ := (d2LitsNearTransfers050.q2 (34896349) 1 (-28))
def d2Transfer406Cap : ℚ := (d2LitsNearTransfers050.q2 (1169469059) 1 (-40))
def d2Transfer406C0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer406S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
def d2Transfer406C1 : ℚ := (d2LitsNearTransfers050.q2 (-1) 55 (-3))
def d2Transfer406S1 : ℚ := (d2LitsNearTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer406Arithmetic : weightedUpper d2Transfer406C0 d2Log95Lo d2Log95Hi + weightedUpper d2Transfer406C1 d2Log78Lo d2Log78Hi ≤ d2Transfer406Cap := by decide +kernel
theorem d2Transfer406Bound : ∀ x ∈ Set.Icc ((d2Transfer406Lo:ℚ):ℝ) ((d2Transfer406Hi:ℚ):ℝ), ((d2Transfer406C0:ℚ):ℝ)*Real.log |x-((d2Transfer406S0:ℚ):ℝ)| + ((d2Transfer406C1:ℚ):ℝ)*Real.log |x-((d2Transfer406S1:ℚ):ℝ)| ≤ ((d2Transfer406Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer406S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406S0,d2Transfer406Lo,d2Transfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer406C0 then |x-((d2Transfer406S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2Transfer406S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer406S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406S0,d2Transfer406Lo,d2Transfer406Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406C0,d2Log95Q,d2Transfer406S0,d2Transfer406Lo,d2Transfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer406C0 d2Transfer406S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2Transfer406S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406S1,d2Transfer406Lo,d2Transfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer406C1 then |x-((d2Transfer406S1:ℚ):ℝ)| ≤ ((d2Log78Q:ℚ):ℝ) else ((d2Log78Q:ℚ):ℝ) ≤ |x-((d2Transfer406S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer406S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406S1,d2Transfer406Lo,d2Transfer406Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer406C1,d2Log78Q,d2Transfer406S1,d2Transfer406Lo,d2Transfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer406C1 d2Transfer406S1 d2Log78Q d2Log78Lo d2Log78Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log78Bounds
  have har : (((weightedUpper d2Transfer406C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2Transfer406C1 d2Log78Lo d2Log78Hi:ℚ):ℝ)) ≤ ((d2Transfer406Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer406Arithmetic
  linarith
#print axioms d2Transfer406Arithmetic
#print axioms d2Transfer406Bound
def d2Transfer407Lo : ℚ := (d2LitsNearTransfers050.q2 (8304657) 1 (-26))
def d2Transfer407Hi : ℚ := (d2LitsNearTransfers050.q2 (34896349) 1 (-28))
def d2Transfer407Cap : ℚ := (d2LitsNearTransfers050.q2 (15113656175) 1 (-40))
def d2Transfer407C0 : ℚ := (d2LitsNearTransfers050.q2 (23) 25 (-5))
def d2Transfer407S0 : ℚ := (d2LitsNearTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer407Arithmetic : weightedUpper d2Transfer407C0 d2Log96Lo d2Log96Hi ≤ d2Transfer407Cap := by decide +kernel
theorem d2Transfer407Bound : ∀ x ∈ Set.Icc ((d2Transfer407Lo:ℚ):ℝ) ((d2Transfer407Hi:ℚ):ℝ), ((d2Transfer407C0:ℚ):ℝ)*Real.log |x-((d2Transfer407S0:ℚ):ℝ)| ≤ ((d2Transfer407Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer407S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer407S0,d2Transfer407Lo,d2Transfer407Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer407C0 then |x-((d2Transfer407S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer407S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer407S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer407S0,d2Transfer407Lo,d2Transfer407Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers050.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2Transfer407C0,d2Log96Q,d2Transfer407S0,d2Transfer407Lo,d2Transfer407Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer407C0 d2Transfer407S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have har : (((weightedUpper d2Transfer407C0 d2Log96Lo d2Log96Hi:ℚ):ℝ)) ≤ ((d2Transfer407Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer407Arithmetic
  linarith
#print axioms d2Transfer407Arithmetic
#print axioms d2Transfer407Bound
end CatalanMeasure.GenD.Signed.Data.Cells

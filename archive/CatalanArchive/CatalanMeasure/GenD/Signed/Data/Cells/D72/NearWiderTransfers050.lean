module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
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
namespace d2LitsNearWiderTransfers050
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers050
open D72.LogTransfer
def d2WiderTransfer400Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (8380219) 1 (-23))
def d2WiderTransfer400Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (999) 125 (-3))
def d2WiderTransfer400Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (102672983640873595763659) 1 (-79))
def d2WiderTransfer400C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 55 (-3))
def d2WiderTransfer400S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
def d2WiderTransfer400C1 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 55 (-3))
def d2WiderTransfer400S1 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer400Arithmetic : weightedUpper d2WiderTransfer400C0 d2Log173Lo d2Log173Hi + weightedUpper d2WiderTransfer400C1 d2Log0Lo d2Log0Hi ≤ d2WiderTransfer400Cap := by decide +kernel
theorem d2WiderTransfer400Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer400Lo:ℚ):ℝ) ((d2WiderTransfer400Hi:ℚ):ℝ), ((d2WiderTransfer400C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer400S0:ℚ):ℝ)| + ((d2WiderTransfer400C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer400S1:ℚ):ℝ)| ≤ ((d2WiderTransfer400Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer400S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400S0,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer400C0 then |x-((d2WiderTransfer400S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer400S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer400S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400S0,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400C0,d2Log173Q,d2WiderTransfer400S0,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer400C0 d2WiderTransfer400S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2WiderTransfer400S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400S1,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer400C1 then |x-((d2WiderTransfer400S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer400S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer400S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400S1,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer400C1,d2Log0Q,d2WiderTransfer400S1,d2WiderTransfer400Lo,d2WiderTransfer400Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer400C1 d2WiderTransfer400S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2WiderTransfer400C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer400C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer400Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer400Arithmetic
  linarith
#print axioms d2WiderTransfer400Arithmetic
#print axioms d2WiderTransfer400Bound
def d2WiderTransfer401Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (8380219) 1 (-23))
def d2WiderTransfer401Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (999) 125 (-3))
def d2WiderTransfer401Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (110338881577836739230667) 1 (-79))
def d2WiderTransfer401C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (23) 25 (-5))
def d2WiderTransfer401S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer401Arithmetic : weightedUpper d2WiderTransfer401C0 d2Log174Lo d2Log174Hi ≤ d2WiderTransfer401Cap := by decide +kernel
theorem d2WiderTransfer401Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer401Lo:ℚ):ℝ) ((d2WiderTransfer401Hi:ℚ):ℝ), ((d2WiderTransfer401C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer401S0:ℚ):ℝ)| ≤ ((d2WiderTransfer401Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer401S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer401S0,d2WiderTransfer401Lo,d2WiderTransfer401Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer401C0 then |x-((d2WiderTransfer401S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer401S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer401S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer401S0,d2WiderTransfer401Lo,d2WiderTransfer401Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer401C0,d2Log174Q,d2WiderTransfer401S0,d2WiderTransfer401Lo,d2WiderTransfer401Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer401C0 d2WiderTransfer401S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2WiderTransfer401C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer401Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer401Arithmetic
  linarith
#print axioms d2WiderTransfer401Arithmetic
#print axioms d2WiderTransfer401Bound
def d2WiderTransfer402Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (8380219) 1 (-23))
def d2WiderTransfer402Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (999) 125 (-3))
def d2WiderTransfer402Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (118764375273470374378443) 1 (-79))
def d2WiderTransfer402C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (3) 275 (-5))
def d2WiderTransfer402S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
def d2WiderTransfer402C1 : ℚ := (d2LitsNearWiderTransfers050.q2 (-5) 11 (-4))
def d2WiderTransfer402S1 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer402Arithmetic : weightedUpper d2WiderTransfer402C0 d2Log174Lo d2Log174Hi + weightedUpper d2WiderTransfer402C1 d2Log0Lo d2Log0Hi ≤ d2WiderTransfer402Cap := by decide +kernel
theorem d2WiderTransfer402Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer402Lo:ℚ):ℝ) ((d2WiderTransfer402Hi:ℚ):ℝ), ((d2WiderTransfer402C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer402S0:ℚ):ℝ)| + ((d2WiderTransfer402C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer402S1:ℚ):ℝ)| ≤ ((d2WiderTransfer402Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer402S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402S0,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer402C0 then |x-((d2WiderTransfer402S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer402S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer402S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402S0,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402C0,d2Log174Q,d2WiderTransfer402S0,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer402C0 d2WiderTransfer402S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2WiderTransfer402S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402S1,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer402C1 then |x-((d2WiderTransfer402S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer402S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer402S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402S1,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer402C1,d2Log0Q,d2WiderTransfer402S1,d2WiderTransfer402Lo,d2WiderTransfer402Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer402C1 d2WiderTransfer402S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2WiderTransfer402C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer402C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer402Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer402Arithmetic
  linarith
#print axioms d2WiderTransfer402Arithmetic
#print axioms d2WiderTransfer402Bound
def d2WiderTransfer403Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (999) 125 (-3))
def d2WiderTransfer403Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (16760439) 1 (-24))
def d2WiderTransfer403Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (2093397711619402323551) 1 (-80))
def d2WiderTransfer403C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 25 (-4))
def d2WiderTransfer403S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer403Arithmetic : weightedUpper d2WiderTransfer403C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer403Cap := by decide +kernel
theorem d2WiderTransfer403Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer403Lo:ℚ):ℝ) ((d2WiderTransfer403Hi:ℚ):ℝ), ((d2WiderTransfer403C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer403S0:ℚ):ℝ)| ≤ ((d2WiderTransfer403Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer403S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer403S0,d2WiderTransfer403Lo,d2WiderTransfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer403C0 then |x-((d2WiderTransfer403S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer403S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer403S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer403S0,d2WiderTransfer403Lo,d2WiderTransfer403Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer403C0,d2Log175Q,d2WiderTransfer403S0,d2WiderTransfer403Lo,d2WiderTransfer403Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer403C0 d2WiderTransfer403S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer403C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer403Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer403Arithmetic
  linarith
#print axioms d2WiderTransfer403Arithmetic
#print axioms d2WiderTransfer403Bound
def d2WiderTransfer404Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (999) 125 (-3))
def d2WiderTransfer404Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (16760439) 1 (-24))
def d2WiderTransfer404Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (2093397292705472140895) 1 (-80))
def d2WiderTransfer404C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 25 (-4))
def d2WiderTransfer404S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer404Arithmetic : weightedUpper d2WiderTransfer404C0 d2Log175Lo d2Log175Hi ≤ d2WiderTransfer404Cap := by decide +kernel
theorem d2WiderTransfer404Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer404Lo:ℚ):ℝ) ((d2WiderTransfer404Hi:ℚ):ℝ), ((d2WiderTransfer404C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer404S0:ℚ):ℝ)| ≤ ((d2WiderTransfer404Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer404S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer404S0,d2WiderTransfer404Lo,d2WiderTransfer404Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer404C0 then |x-((d2WiderTransfer404S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer404S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer404S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer404S0,d2WiderTransfer404Lo,d2WiderTransfer404Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer404C0,d2Log175Q,d2WiderTransfer404S0,d2WiderTransfer404Lo,d2WiderTransfer404Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer404C0 d2WiderTransfer404S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2WiderTransfer404C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer404Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer404Arithmetic
  linarith
#print axioms d2WiderTransfer404Arithmetic
#print axioms d2WiderTransfer404Bound
def d2WiderTransfer405Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (16760439) 1 (-24))
def d2WiderTransfer405Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (1023) 1 (-10))
def d2WiderTransfer405Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (1046716563706371062717) 1 (-79))
def d2WiderTransfer405C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 25 (-4))
def d2WiderTransfer405S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer405Arithmetic : weightedUpper d2WiderTransfer405C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer405Cap := by decide +kernel
theorem d2WiderTransfer405Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer405Lo:ℚ):ℝ) ((d2WiderTransfer405Hi:ℚ):ℝ), ((d2WiderTransfer405C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer405S0:ℚ):ℝ)| ≤ ((d2WiderTransfer405Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer405S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer405S0,d2WiderTransfer405Lo,d2WiderTransfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer405C0 then |x-((d2WiderTransfer405S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer405S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer405S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer405S0,d2WiderTransfer405Lo,d2WiderTransfer405Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer405C0,d2Log176Q,d2WiderTransfer405S0,d2WiderTransfer405Lo,d2WiderTransfer405Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer405C0 d2WiderTransfer405S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer405C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer405Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer405Arithmetic
  linarith
#print axioms d2WiderTransfer405Arithmetic
#print axioms d2WiderTransfer405Bound
def d2WiderTransfer406Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (16760439) 1 (-24))
def d2WiderTransfer406Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (1023) 1 (-10))
def d2WiderTransfer406Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (1046716354249405971389) 1 (-79))
def d2WiderTransfer406C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 25 (-4))
def d2WiderTransfer406S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer406Arithmetic : weightedUpper d2WiderTransfer406C0 d2Log176Lo d2Log176Hi ≤ d2WiderTransfer406Cap := by decide +kernel
theorem d2WiderTransfer406Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer406Lo:ℚ):ℝ) ((d2WiderTransfer406Hi:ℚ):ℝ), ((d2WiderTransfer406C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer406S0:ℚ):ℝ)| ≤ ((d2WiderTransfer406Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer406S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer406S0,d2WiderTransfer406Lo,d2WiderTransfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer406C0 then |x-((d2WiderTransfer406S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer406S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer406S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer406S0,d2WiderTransfer406Lo,d2WiderTransfer406Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer406C0,d2Log176Q,d2WiderTransfer406S0,d2WiderTransfer406Lo,d2WiderTransfer406Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer406C0 d2WiderTransfer406S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2WiderTransfer406C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer406Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer406Arithmetic
  linarith
#print axioms d2WiderTransfer406Arithmetic
#print axioms d2WiderTransfer406Bound
def d2WiderTransfer407Lo : ℚ := (d2LitsNearWiderTransfers050.q2 (1023) 1 (-10))
def d2WiderTransfer407Hi : ℚ := (d2LitsNearWiderTransfers050.q2 (2047) 1 (-11))
def d2WiderTransfer407Cap : ℚ := (d2LitsNearWiderTransfers050.q2 (1047085633747164758283) 1 (-79))
def d2WiderTransfer407C0 : ℚ := (d2LitsNearWiderTransfers050.q2 (1) 25 (-4))
def d2WiderTransfer407S0 : ℚ := (d2LitsNearWiderTransfers050.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer407Arithmetic : weightedUpper d2WiderTransfer407C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer407Cap := by decide +kernel
theorem d2WiderTransfer407Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer407Lo:ℚ):ℝ) ((d2WiderTransfer407Hi:ℚ):ℝ), ((d2WiderTransfer407C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer407S0:ℚ):ℝ)| ≤ ((d2WiderTransfer407Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer407S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer407S0,d2WiderTransfer407Lo,d2WiderTransfer407Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer407C0 then |x-((d2WiderTransfer407S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer407S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer407S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer407S0,d2WiderTransfer407Lo,d2WiderTransfer407Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers050.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2WiderTransfer407C0,d2Log177Q,d2WiderTransfer407S0,d2WiderTransfer407Lo,d2WiderTransfer407Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer407C0 d2WiderTransfer407S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer407C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer407Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer407Arithmetic
  linarith
#print axioms d2WiderTransfer407Arithmetic
#print axioms d2WiderTransfer407Bound
end CatalanMeasure.GenD.Signed.Data.Cells

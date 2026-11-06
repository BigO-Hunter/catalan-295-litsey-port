module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers029
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers029
open D72.LogTransfer
def d2WiderTransfer232Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (7539251) 1 (-23))
def d2WiderTransfer232Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer232Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (43982280163239795757679) 1 (-79))
def d2WiderTransfer232C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (-5))
def d2WiderTransfer232S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer232Arithmetic : weightedUpper d2WiderTransfer232C0 d2Log170Lo d2Log170Hi ≤ d2WiderTransfer232Cap := by decide +kernel
theorem d2WiderTransfer232Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer232Lo:ℚ):ℝ) ((d2WiderTransfer232Hi:ℚ):ℝ), ((d2WiderTransfer232C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer232S0:ℚ):ℝ)| ≤ ((d2WiderTransfer232Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer232S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer232S0,d2WiderTransfer232Lo,d2WiderTransfer232Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer232C0 then |x-((d2WiderTransfer232S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer232S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer232S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer232S0,d2WiderTransfer232Lo,d2WiderTransfer232Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer232C0,d2Log170Q,d2WiderTransfer232S0,d2WiderTransfer232Lo,d2WiderTransfer232Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer232C0 d2WiderTransfer232S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have har : (((weightedUpper d2WiderTransfer232C0 d2Log170Lo d2Log170Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer232Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer232Arithmetic
  linarith
#print axioms d2WiderTransfer232Arithmetic
#print axioms d2WiderTransfer232Bound
def d2WiderTransfer233Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (7539251) 1 (-23))
def d2WiderTransfer233Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer233Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (52164698824385549439599) 1 (-79))
def d2WiderTransfer233C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 11 (-5))
def d2WiderTransfer233S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
def d2WiderTransfer233C1 : ℚ := (d2LitsNearWiderTransfers029.q2 (-5) 11 (-4))
def d2WiderTransfer233S1 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer233Arithmetic : weightedUpper d2WiderTransfer233C0 d2Log170Lo d2Log170Hi + weightedUpper d2WiderTransfer233C1 d2Log4Lo d2Log4Hi ≤ d2WiderTransfer233Cap := by decide +kernel
theorem d2WiderTransfer233Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer233Lo:ℚ):ℝ) ((d2WiderTransfer233Hi:ℚ):ℝ), ((d2WiderTransfer233C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer233S0:ℚ):ℝ)| + ((d2WiderTransfer233C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer233S1:ℚ):ℝ)| ≤ ((d2WiderTransfer233Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer233S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233S0,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer233C0 then |x-((d2WiderTransfer233S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer233S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer233S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233S0,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233C0,d2Log170Q,d2WiderTransfer233S0,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer233C0 d2WiderTransfer233S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2WiderTransfer233S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233S1,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer233C1 then |x-((d2WiderTransfer233S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer233S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer233S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233S1,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer233C1,d2Log4Q,d2WiderTransfer233S1,d2WiderTransfer233Lo,d2WiderTransfer233Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer233C1 d2WiderTransfer233S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2WiderTransfer233C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer233C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer233Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer233Arithmetic
  linarith
#print axioms d2WiderTransfer233Arithmetic
#print axioms d2WiderTransfer233Bound
def d2WiderTransfer234Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer234Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer234Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (47256162031528428522913) 1 (-79))
def d2WiderTransfer234C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 25 (-4))
def d2WiderTransfer234S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer234Arithmetic : weightedUpper d2WiderTransfer234C0 d2Log171Lo d2Log171Hi ≤ d2WiderTransfer234Cap := by decide +kernel
theorem d2WiderTransfer234Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer234Lo:ℚ):ℝ) ((d2WiderTransfer234Hi:ℚ):ℝ), ((d2WiderTransfer234C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer234S0:ℚ):ℝ)| ≤ ((d2WiderTransfer234Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer234S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer234S0,d2WiderTransfer234Lo,d2WiderTransfer234Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer234C0 then |x-((d2WiderTransfer234S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer234S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer234S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer234S0,d2WiderTransfer234Lo,d2WiderTransfer234Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer234C0,d2Log171Q,d2WiderTransfer234S0,d2WiderTransfer234Lo,d2WiderTransfer234Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer234C0 d2WiderTransfer234S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2WiderTransfer234C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer234Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer234Arithmetic
  linarith
#print axioms d2WiderTransfer234Arithmetic
#print axioms d2WiderTransfer234Bound
def d2WiderTransfer235Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer235Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer235Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (47881312115846296194465) 1 (-79))
def d2WiderTransfer235C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 275 (-4))
def d2WiderTransfer235S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
def d2WiderTransfer235C1 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 55 (-3))
def d2WiderTransfer235S1 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer235Arithmetic : weightedUpper d2WiderTransfer235C0 d2Log171Lo d2Log171Hi + weightedUpper d2WiderTransfer235C1 d2Log3Lo d2Log3Hi ≤ d2WiderTransfer235Cap := by decide +kernel
theorem d2WiderTransfer235Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer235Lo:ℚ):ℝ) ((d2WiderTransfer235Hi:ℚ):ℝ), ((d2WiderTransfer235C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer235S0:ℚ):ℝ)| + ((d2WiderTransfer235C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer235S1:ℚ):ℝ)| ≤ ((d2WiderTransfer235Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer235S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235S0,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer235C0 then |x-((d2WiderTransfer235S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer235S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer235S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235S0,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235C0,d2Log171Q,d2WiderTransfer235S0,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer235C0 d2WiderTransfer235S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2WiderTransfer235S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235S1,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer235C1 then |x-((d2WiderTransfer235S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer235S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer235S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235S1,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer235C1,d2Log3Q,d2WiderTransfer235S1,d2WiderTransfer235Lo,d2WiderTransfer235Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer235C1 d2WiderTransfer235S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2WiderTransfer235C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer235C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer235Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer235Arithmetic
  linarith
#print axioms d2WiderTransfer235Arithmetic
#print axioms d2WiderTransfer235Bound
def d2WiderTransfer236Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer236Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer236Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (55492843161057776455073) 1 (-79))
def d2WiderTransfer236C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (-5))
def d2WiderTransfer236S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer236Arithmetic : weightedUpper d2WiderTransfer236C0 d2Log171Lo d2Log171Hi ≤ d2WiderTransfer236Cap := by decide +kernel
theorem d2WiderTransfer236Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer236Lo:ℚ):ℝ) ((d2WiderTransfer236Hi:ℚ):ℝ), ((d2WiderTransfer236C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer236S0:ℚ):ℝ)| ≤ ((d2WiderTransfer236Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer236S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer236S0,d2WiderTransfer236Lo,d2WiderTransfer236Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer236C0 then |x-((d2WiderTransfer236S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer236S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer236S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer236S0,d2WiderTransfer236Lo,d2WiderTransfer236Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer236C0,d2Log171Q,d2WiderTransfer236S0,d2WiderTransfer236Lo,d2WiderTransfer236Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer236C0 d2WiderTransfer236S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2WiderTransfer236C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer236Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer236Arithmetic
  linarith
#print axioms d2WiderTransfer236Arithmetic
#print axioms d2WiderTransfer236Bound
def d2WiderTransfer237Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (31834725) 1 (-25))
def d2WiderTransfer237Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer237Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (63675261822203530136993) 1 (-79))
def d2WiderTransfer237C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 11 (-5))
def d2WiderTransfer237S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
def d2WiderTransfer237C1 : ℚ := (d2LitsNearWiderTransfers029.q2 (-5) 11 (-4))
def d2WiderTransfer237S1 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer237Arithmetic : weightedUpper d2WiderTransfer237C0 d2Log171Lo d2Log171Hi + weightedUpper d2WiderTransfer237C1 d2Log3Lo d2Log3Hi ≤ d2WiderTransfer237Cap := by decide +kernel
theorem d2WiderTransfer237Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer237Lo:ℚ):ℝ) ((d2WiderTransfer237Hi:ℚ):ℝ), ((d2WiderTransfer237C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer237S0:ℚ):ℝ)| + ((d2WiderTransfer237C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer237S1:ℚ):ℝ)| ≤ ((d2WiderTransfer237Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer237S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237S0,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer237C0 then |x-((d2WiderTransfer237S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer237S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer237S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237S0,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237C0,d2Log171Q,d2WiderTransfer237S0,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer237C0 d2WiderTransfer237S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2WiderTransfer237S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237S1,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer237C1 then |x-((d2WiderTransfer237S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer237S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer237S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237S1,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer237C1,d2Log3Q,d2WiderTransfer237S1,d2WiderTransfer237Lo,d2WiderTransfer237Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer237C1 d2WiderTransfer237S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2WiderTransfer237C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer237C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer237Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer237Arithmetic
  linarith
#print axioms d2WiderTransfer237Arithmetic
#print axioms d2WiderTransfer237Bound
def d2WiderTransfer238Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer238Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (16756223) 1 (-24))
def d2WiderTransfer238Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (49771151816960380668549) 1 (-78))
def d2WiderTransfer238C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 25 (-4))
def d2WiderTransfer238S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer238Arithmetic : weightedUpper d2WiderTransfer238C0 d2Log172Lo d2Log172Hi ≤ d2WiderTransfer238Cap := by decide +kernel
theorem d2WiderTransfer238Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer238Lo:ℚ):ℝ) ((d2WiderTransfer238Hi:ℚ):ℝ), ((d2WiderTransfer238C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer238S0:ℚ):ℝ)| ≤ ((d2WiderTransfer238Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer238S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer238S0,d2WiderTransfer238Lo,d2WiderTransfer238Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer238C0 then |x-((d2WiderTransfer238S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer238S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer238S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer238S0,d2WiderTransfer238Lo,d2WiderTransfer238Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer238C0,d2Log172Q,d2WiderTransfer238S0,d2WiderTransfer238Lo,d2WiderTransfer238Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer238C0 d2WiderTransfer238S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2WiderTransfer238C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer238Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer238Arithmetic
  linarith
#print axioms d2WiderTransfer238Arithmetic
#print axioms d2WiderTransfer238Bound
def d2WiderTransfer239Lo : ℚ := (d2LitsNearWiderTransfers029.q2 (65347171) 1 (-26))
def d2WiderTransfer239Hi : ℚ := (d2LitsNearWiderTransfers029.q2 (16756223) 1 (-24))
def d2WiderTransfer239Cap : ℚ := (d2LitsNearWiderTransfers029.q2 (50083726859119314504325) 1 (-78))
def d2WiderTransfer239C0 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 275 (-4))
def d2WiderTransfer239S0 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 1 (0))
def d2WiderTransfer239C1 : ℚ := (d2LitsNearWiderTransfers029.q2 (-1) 55 (-3))
def d2WiderTransfer239S1 : ℚ := (d2LitsNearWiderTransfers029.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer239Arithmetic : weightedUpper d2WiderTransfer239C0 d2Log172Lo d2Log172Hi + weightedUpper d2WiderTransfer239C1 d2Log2Lo d2Log2Hi ≤ d2WiderTransfer239Cap := by decide +kernel
theorem d2WiderTransfer239Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer239Lo:ℚ):ℝ) ((d2WiderTransfer239Hi:ℚ):ℝ), ((d2WiderTransfer239C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer239S0:ℚ):ℝ)| + ((d2WiderTransfer239C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer239S1:ℚ):ℝ)| ≤ ((d2WiderTransfer239Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer239S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239S0,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer239C0 then |x-((d2WiderTransfer239S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer239S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer239S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239S0,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239C0,d2Log172Q,d2WiderTransfer239S0,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer239C0 d2WiderTransfer239S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2WiderTransfer239S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239S1,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer239C1 then |x-((d2WiderTransfer239S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer239S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer239S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239S1,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers029.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer239C1,d2Log2Q,d2WiderTransfer239S1,d2WiderTransfer239Lo,d2WiderTransfer239Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer239C1 d2WiderTransfer239S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2WiderTransfer239C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer239C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer239Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer239Arithmetic
  linarith
#print axioms d2WiderTransfer239Arithmetic
#print axioms d2WiderTransfer239Bound
end CatalanMeasure.GenD.Signed.Data.Cells

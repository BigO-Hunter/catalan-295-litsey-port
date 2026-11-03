module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers062
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers062
open D72.LogTransfer
def d2Transfer496Lo : ℚ := (d2LitsNearTransfers062.q2 (82040433) 1 (-27))
def d2Transfer496Hi : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer496Cap : ℚ := (d2LitsNearTransfers062.q2 (328696967227444328115) 1 (-78))
def d2Transfer496C0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer496S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
def d2Transfer496C1 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer496S1 : ℚ := (d2LitsNearTransfers062.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer496Arithmetic : weightedUpper d2Transfer496C0 d2Log128Lo d2Log128Hi + weightedUpper d2Transfer496C1 d2Log45Lo d2Log45Hi ≤ d2Transfer496Cap := by decide +kernel
theorem d2Transfer496Bound : ∀ x ∈ Set.Icc ((d2Transfer496Lo:ℚ):ℝ) ((d2Transfer496Hi:ℚ):ℝ), ((d2Transfer496C0:ℚ):ℝ)*Real.log |x-((d2Transfer496S0:ℚ):ℝ)| + ((d2Transfer496C1:ℚ):ℝ)*Real.log |x-((d2Transfer496S1:ℚ):ℝ)| ≤ ((d2Transfer496Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer496S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496S0,d2Transfer496Lo,d2Transfer496Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer496C0 then |x-((d2Transfer496S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer496S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer496S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496S0,d2Transfer496Lo,d2Transfer496Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496C0,d2Log128Q,d2Transfer496S0,d2Transfer496Lo,d2Transfer496Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer496C0 d2Transfer496S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2Transfer496S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496S1,d2Transfer496Lo,d2Transfer496Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer496C1 then |x-((d2Transfer496S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2Transfer496S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer496S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496S1,d2Transfer496Lo,d2Transfer496Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer496C1,d2Log45Q,d2Transfer496S1,d2Transfer496Lo,d2Transfer496Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer496C1 d2Transfer496S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2Transfer496C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2Transfer496C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2Transfer496Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer496Arithmetic
  linarith
#print axioms d2Transfer496Arithmetic
#print axioms d2Transfer496Bound
def d2Transfer497Lo : ℚ := (d2LitsNearTransfers062.q2 (82040433) 1 (-27))
def d2Transfer497Hi : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer497Cap : ℚ := (d2LitsNearTransfers062.q2 (4161645935709016061619) 1 (-78))
def d2Transfer497C0 : ℚ := (d2LitsNearTransfers062.q2 (23) 25 (-5))
def d2Transfer497S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer497Arithmetic : weightedUpper d2Transfer497C0 d2Log129Lo d2Log129Hi ≤ d2Transfer497Cap := by decide +kernel
theorem d2Transfer497Bound : ∀ x ∈ Set.Icc ((d2Transfer497Lo:ℚ):ℝ) ((d2Transfer497Hi:ℚ):ℝ), ((d2Transfer497C0:ℚ):ℝ)*Real.log |x-((d2Transfer497S0:ℚ):ℝ)| ≤ ((d2Transfer497Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer497S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer497S0,d2Transfer497Lo,d2Transfer497Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer497C0 then |x-((d2Transfer497S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer497S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer497S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer497S0,d2Transfer497Lo,d2Transfer497Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer497C0,d2Log129Q,d2Transfer497S0,d2Transfer497Lo,d2Transfer497Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer497C0 d2Transfer497S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2Transfer497C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2Transfer497Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer497Arithmetic
  linarith
#print axioms d2Transfer497Arithmetic
#print axioms d2Transfer497Bound
def d2Transfer498Lo : ℚ := (d2LitsNearTransfers062.q2 (82040433) 1 (-27))
def d2Transfer498Hi : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer498Cap : ℚ := (d2LitsNearTransfers062.q2 (8374392783525833635507) 1 (-78))
def d2Transfer498C0 : ℚ := (d2LitsNearTransfers062.q2 (3) 275 (-5))
def d2Transfer498S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
def d2Transfer498C1 : ℚ := (d2LitsNearTransfers062.q2 (-5) 11 (-4))
def d2Transfer498S1 : ℚ := (d2LitsNearTransfers062.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer498Arithmetic : weightedUpper d2Transfer498C0 d2Log129Lo d2Log129Hi + weightedUpper d2Transfer498C1 d2Log45Lo d2Log45Hi ≤ d2Transfer498Cap := by decide +kernel
theorem d2Transfer498Bound : ∀ x ∈ Set.Icc ((d2Transfer498Lo:ℚ):ℝ) ((d2Transfer498Hi:ℚ):ℝ), ((d2Transfer498C0:ℚ):ℝ)*Real.log |x-((d2Transfer498S0:ℚ):ℝ)| + ((d2Transfer498C1:ℚ):ℝ)*Real.log |x-((d2Transfer498S1:ℚ):ℝ)| ≤ ((d2Transfer498Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer498S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498S0,d2Transfer498Lo,d2Transfer498Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer498C0 then |x-((d2Transfer498S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer498S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer498S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498S0,d2Transfer498Lo,d2Transfer498Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498C0,d2Log129Q,d2Transfer498S0,d2Transfer498Lo,d2Transfer498Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer498C0 d2Transfer498S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2Transfer498S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498S1,d2Transfer498Lo,d2Transfer498Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer498C1 then |x-((d2Transfer498S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2Transfer498S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer498S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498S1,d2Transfer498Lo,d2Transfer498Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer498C1,d2Log45Q,d2Transfer498S1,d2Transfer498Lo,d2Transfer498Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer498C1 d2Transfer498S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2Transfer498C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2Transfer498C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2Transfer498Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer498Arithmetic
  linarith
#print axioms d2Transfer498Arithmetic
#print axioms d2Transfer498Bound
def d2Transfer499Lo : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer499Hi : ℚ := (d2LitsNearTransfers062.q2 (165758587) 1 (-28))
def d2Transfer499Cap : ℚ := (d2LitsNearTransfers062.q2 (1382002412149045531867) 1 (-80))
def d2Transfer499C0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer499S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
def d2Transfer499C1 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer499S1 : ℚ := (d2LitsNearTransfers062.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer499Arithmetic : weightedUpper d2Transfer499C0 d2Log129Lo d2Log129Hi + weightedUpper d2Transfer499C1 d2Log43Lo d2Log43Hi ≤ d2Transfer499Cap := by decide +kernel
theorem d2Transfer499Bound : ∀ x ∈ Set.Icc ((d2Transfer499Lo:ℚ):ℝ) ((d2Transfer499Hi:ℚ):ℝ), ((d2Transfer499C0:ℚ):ℝ)*Real.log |x-((d2Transfer499S0:ℚ):ℝ)| + ((d2Transfer499C1:ℚ):ℝ)*Real.log |x-((d2Transfer499S1:ℚ):ℝ)| ≤ ((d2Transfer499Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer499S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499S0,d2Transfer499Lo,d2Transfer499Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer499C0 then |x-((d2Transfer499S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer499S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer499S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499S0,d2Transfer499Lo,d2Transfer499Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499C0,d2Log129Q,d2Transfer499S0,d2Transfer499Lo,d2Transfer499Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer499C0 d2Transfer499S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2Transfer499S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499S1,d2Transfer499Lo,d2Transfer499Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer499C1 then |x-((d2Transfer499S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2Transfer499S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer499S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499S1,d2Transfer499Lo,d2Transfer499Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer499C1,d2Log43Q,d2Transfer499S1,d2Transfer499Lo,d2Transfer499Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer499C1 d2Transfer499S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2Transfer499C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2Transfer499C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2Transfer499Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer499Arithmetic
  linarith
#print axioms d2Transfer499Arithmetic
#print axioms d2Transfer499Bound
def d2Transfer500Lo : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer500Hi : ℚ := (d2LitsNearTransfers062.q2 (165758587) 1 (-28))
def d2Transfer500Cap : ℚ := (d2LitsNearTransfers062.q2 (16713798286075332465883) 1 (-80))
def d2Transfer500C0 : ℚ := (d2LitsNearTransfers062.q2 (23) 25 (-5))
def d2Transfer500S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer500Arithmetic : weightedUpper d2Transfer500C0 d2Log131Lo d2Log131Hi ≤ d2Transfer500Cap := by decide +kernel
theorem d2Transfer500Bound : ∀ x ∈ Set.Icc ((d2Transfer500Lo:ℚ):ℝ) ((d2Transfer500Hi:ℚ):ℝ), ((d2Transfer500C0:ℚ):ℝ)*Real.log |x-((d2Transfer500S0:ℚ):ℝ)| ≤ ((d2Transfer500Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer500S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer500S0,d2Transfer500Lo,d2Transfer500Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer500C0 then |x-((d2Transfer500S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer500S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer500S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer500S0,d2Transfer500Lo,d2Transfer500Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer500C0,d2Log131Q,d2Transfer500S0,d2Transfer500Lo,d2Transfer500Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer500C0 d2Transfer500S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2Transfer500C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2Transfer500Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer500Arithmetic
  linarith
#print axioms d2Transfer500Arithmetic
#print axioms d2Transfer500Bound
def d2Transfer501Lo : ℚ := (d2LitsNearTransfers062.q2 (329839453) 1 (-29))
def d2Transfer501Hi : ℚ := (d2LitsNearTransfers062.q2 (165758587) 1 (-28))
def d2Transfer501Cap : ℚ := (d2LitsNearTransfers062.q2 (33564785677342602761435) 1 (-80))
def d2Transfer501C0 : ℚ := (d2LitsNearTransfers062.q2 (3) 275 (-5))
def d2Transfer501S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
def d2Transfer501C1 : ℚ := (d2LitsNearTransfers062.q2 (-5) 11 (-4))
def d2Transfer501S1 : ℚ := (d2LitsNearTransfers062.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer501Arithmetic : weightedUpper d2Transfer501C0 d2Log131Lo d2Log131Hi + weightedUpper d2Transfer501C1 d2Log43Lo d2Log43Hi ≤ d2Transfer501Cap := by decide +kernel
theorem d2Transfer501Bound : ∀ x ∈ Set.Icc ((d2Transfer501Lo:ℚ):ℝ) ((d2Transfer501Hi:ℚ):ℝ), ((d2Transfer501C0:ℚ):ℝ)*Real.log |x-((d2Transfer501S0:ℚ):ℝ)| + ((d2Transfer501C1:ℚ):ℝ)*Real.log |x-((d2Transfer501S1:ℚ):ℝ)| ≤ ((d2Transfer501Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer501S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501S0,d2Transfer501Lo,d2Transfer501Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer501C0 then |x-((d2Transfer501S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer501S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer501S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501S0,d2Transfer501Lo,d2Transfer501Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501C0,d2Log131Q,d2Transfer501S0,d2Transfer501Lo,d2Transfer501Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer501C0 d2Transfer501S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2Transfer501S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501S1,d2Transfer501Lo,d2Transfer501Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer501C1 then |x-((d2Transfer501S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2Transfer501S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer501S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501S1,d2Transfer501Lo,d2Transfer501Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer501C1,d2Log43Q,d2Transfer501S1,d2Transfer501Lo,d2Transfer501Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer501C1 d2Transfer501S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2Transfer501C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2Transfer501C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2Transfer501Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer501Arithmetic
  linarith
#print axioms d2Transfer501Arithmetic
#print axioms d2Transfer501Bound
def d2Transfer502Lo : ℚ := (d2LitsNearTransfers062.q2 (165758587) 1 (-28))
def d2Transfer502Hi : ℚ := (d2LitsNearTransfers062.q2 (333194895) 1 (-29))
def d2Transfer502Cap : ℚ := (d2LitsNearTransfers062.q2 (1449087222501825393449) 1 (-80))
def d2Transfer502C0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer502S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
def d2Transfer502C1 : ℚ := (d2LitsNearTransfers062.q2 (-1) 55 (-3))
def d2Transfer502S1 : ℚ := (d2LitsNearTransfers062.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer502Arithmetic : weightedUpper d2Transfer502C0 d2Log131Lo d2Log131Hi + weightedUpper d2Transfer502C1 d2Log39Lo d2Log39Hi ≤ d2Transfer502Cap := by decide +kernel
theorem d2Transfer502Bound : ∀ x ∈ Set.Icc ((d2Transfer502Lo:ℚ):ℝ) ((d2Transfer502Hi:ℚ):ℝ), ((d2Transfer502C0:ℚ):ℝ)*Real.log |x-((d2Transfer502S0:ℚ):ℝ)| + ((d2Transfer502C1:ℚ):ℝ)*Real.log |x-((d2Transfer502S1:ℚ):ℝ)| ≤ ((d2Transfer502Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer502S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502S0,d2Transfer502Lo,d2Transfer502Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer502C0 then |x-((d2Transfer502S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer502S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer502S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502S0,d2Transfer502Lo,d2Transfer502Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502C0,d2Log131Q,d2Transfer502S0,d2Transfer502Lo,d2Transfer502Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer502C0 d2Transfer502S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2Transfer502S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502S1,d2Transfer502Lo,d2Transfer502Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer502C1 then |x-((d2Transfer502S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2Transfer502S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer502S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502S1,d2Transfer502Lo,d2Transfer502Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer502C1,d2Log39Q,d2Transfer502S1,d2Transfer502Lo,d2Transfer502Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer502C1 d2Transfer502S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2Transfer502C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2Transfer502C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2Transfer502Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer502Arithmetic
  linarith
#print axioms d2Transfer502Arithmetic
#print axioms d2Transfer502Bound
def d2Transfer503Lo : ℚ := (d2LitsNearTransfers062.q2 (165758587) 1 (-28))
def d2Transfer503Hi : ℚ := (d2LitsNearTransfers062.q2 (333194895) 1 (-29))
def d2Transfer503Cap : ℚ := (d2LitsNearTransfers062.q2 (16780883096428112327465) 1 (-80))
def d2Transfer503C0 : ℚ := (d2LitsNearTransfers062.q2 (23) 25 (-5))
def d2Transfer503S0 : ℚ := (d2LitsNearTransfers062.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer503Arithmetic : weightedUpper d2Transfer503C0 d2Log135Lo d2Log135Hi ≤ d2Transfer503Cap := by decide +kernel
theorem d2Transfer503Bound : ∀ x ∈ Set.Icc ((d2Transfer503Lo:ℚ):ℝ) ((d2Transfer503Hi:ℚ):ℝ), ((d2Transfer503C0:ℚ):ℝ)*Real.log |x-((d2Transfer503S0:ℚ):ℝ)| ≤ ((d2Transfer503Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer503S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer503S0,d2Transfer503Lo,d2Transfer503Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer503C0 then |x-((d2Transfer503S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2Transfer503S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer503S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer503S0,d2Transfer503Lo,d2Transfer503Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers062.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer503C0,d2Log135Q,d2Transfer503S0,d2Transfer503Lo,d2Transfer503Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer503C0 d2Transfer503S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2Transfer503C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2Transfer503Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer503Arithmetic
  linarith
#print axioms d2Transfer503Arithmetic
#print axioms d2Transfer503Bound
end CatalanMeasure.GenD.Signed.Data.Cells

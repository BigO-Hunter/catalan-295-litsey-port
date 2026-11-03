module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers036
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers036
open D72.LogTransfer
def d2WiderTransfer288Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (82040433) 1 (-27))
def d2WiderTransfer288Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (329839453) 1 (-29))
def d2WiderTransfer288Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (8374392783525833635507) 1 (-78))
def d2WiderTransfer288C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (3) 275 (-5))
def d2WiderTransfer288S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer288C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-5) 11 (-4))
def d2WiderTransfer288S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer288Arithmetic : weightedUpper d2WiderTransfer288C0 d2Log129Lo d2Log129Hi + weightedUpper d2WiderTransfer288C1 d2Log45Lo d2Log45Hi ≤ d2WiderTransfer288Cap := by decide +kernel
theorem d2WiderTransfer288Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer288Lo:ℚ):ℝ) ((d2WiderTransfer288Hi:ℚ):ℝ), ((d2WiderTransfer288C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer288S0:ℚ):ℝ)| + ((d2WiderTransfer288C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer288S1:ℚ):ℝ)| ≤ ((d2WiderTransfer288Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer288S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288S0,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer288C0 then |x-((d2WiderTransfer288S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer288S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer288S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288S0,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288C0,d2Log129Q,d2WiderTransfer288S0,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer288C0 d2WiderTransfer288S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2WiderTransfer288S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288S1,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer288C1 then |x-((d2WiderTransfer288S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer288S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer288S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288S1,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer288C1,d2Log45Q,d2WiderTransfer288S1,d2WiderTransfer288Lo,d2WiderTransfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer288C1 d2WiderTransfer288S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2WiderTransfer288C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer288C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer288Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer288Arithmetic
  linarith
#print axioms d2WiderTransfer288Arithmetic
#print axioms d2WiderTransfer288Bound
def d2WiderTransfer289Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (329839453) 1 (-29))
def d2WiderTransfer289Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer289Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (1382002412149045531867) 1 (-80))
def d2WiderTransfer289C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer289S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer289C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer289S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer289Arithmetic : weightedUpper d2WiderTransfer289C0 d2Log129Lo d2Log129Hi + weightedUpper d2WiderTransfer289C1 d2Log43Lo d2Log43Hi ≤ d2WiderTransfer289Cap := by decide +kernel
theorem d2WiderTransfer289Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer289Lo:ℚ):ℝ) ((d2WiderTransfer289Hi:ℚ):ℝ), ((d2WiderTransfer289C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer289S0:ℚ):ℝ)| + ((d2WiderTransfer289C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer289S1:ℚ):ℝ)| ≤ ((d2WiderTransfer289Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer289S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289S0,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer289C0 then |x-((d2WiderTransfer289S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer289S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer289S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289S0,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289C0,d2Log129Q,d2WiderTransfer289S0,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer289C0 d2WiderTransfer289S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2WiderTransfer289S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289S1,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer289C1 then |x-((d2WiderTransfer289S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer289S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer289S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289S1,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer289C1,d2Log43Q,d2WiderTransfer289S1,d2WiderTransfer289Lo,d2WiderTransfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer289C1 d2WiderTransfer289S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2WiderTransfer289C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer289C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer289Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer289Arithmetic
  linarith
#print axioms d2WiderTransfer289Arithmetic
#print axioms d2WiderTransfer289Bound
def d2WiderTransfer290Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (329839453) 1 (-29))
def d2WiderTransfer290Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer290Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (16713798286075332465883) 1 (-80))
def d2WiderTransfer290C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (23) 25 (-5))
def d2WiderTransfer290S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer290Arithmetic : weightedUpper d2WiderTransfer290C0 d2Log131Lo d2Log131Hi ≤ d2WiderTransfer290Cap := by decide +kernel
theorem d2WiderTransfer290Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer290Lo:ℚ):ℝ) ((d2WiderTransfer290Hi:ℚ):ℝ), ((d2WiderTransfer290C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer290S0:ℚ):ℝ)| ≤ ((d2WiderTransfer290Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer290S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer290S0,d2WiderTransfer290Lo,d2WiderTransfer290Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer290C0 then |x-((d2WiderTransfer290S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer290S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer290S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer290S0,d2WiderTransfer290Lo,d2WiderTransfer290Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer290C0,d2Log131Q,d2WiderTransfer290S0,d2WiderTransfer290Lo,d2WiderTransfer290Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer290C0 d2WiderTransfer290S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2WiderTransfer290C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer290Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer290Arithmetic
  linarith
#print axioms d2WiderTransfer290Arithmetic
#print axioms d2WiderTransfer290Bound
def d2WiderTransfer291Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (329839453) 1 (-29))
def d2WiderTransfer291Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer291Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (33564785677342602761435) 1 (-80))
def d2WiderTransfer291C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (3) 275 (-5))
def d2WiderTransfer291S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer291C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-5) 11 (-4))
def d2WiderTransfer291S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer291Arithmetic : weightedUpper d2WiderTransfer291C0 d2Log131Lo d2Log131Hi + weightedUpper d2WiderTransfer291C1 d2Log43Lo d2Log43Hi ≤ d2WiderTransfer291Cap := by decide +kernel
theorem d2WiderTransfer291Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer291Lo:ℚ):ℝ) ((d2WiderTransfer291Hi:ℚ):ℝ), ((d2WiderTransfer291C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer291S0:ℚ):ℝ)| + ((d2WiderTransfer291C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer291S1:ℚ):ℝ)| ≤ ((d2WiderTransfer291Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer291S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291S0,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer291C0 then |x-((d2WiderTransfer291S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer291S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer291S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291S0,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291C0,d2Log131Q,d2WiderTransfer291S0,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer291C0 d2WiderTransfer291S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2WiderTransfer291S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291S1,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer291C1 then |x-((d2WiderTransfer291S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer291S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer291S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291S1,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer291C1,d2Log43Q,d2WiderTransfer291S1,d2WiderTransfer291Lo,d2WiderTransfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer291C1 d2WiderTransfer291S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2WiderTransfer291C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer291C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer291Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer291Arithmetic
  linarith
#print axioms d2WiderTransfer291Arithmetic
#print axioms d2WiderTransfer291Bound
def d2WiderTransfer292Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer292Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (333194895) 1 (-29))
def d2WiderTransfer292Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (1449087222501825393449) 1 (-80))
def d2WiderTransfer292C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer292S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer292C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer292S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer292Arithmetic : weightedUpper d2WiderTransfer292C0 d2Log131Lo d2Log131Hi + weightedUpper d2WiderTransfer292C1 d2Log39Lo d2Log39Hi ≤ d2WiderTransfer292Cap := by decide +kernel
theorem d2WiderTransfer292Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer292Lo:ℚ):ℝ) ((d2WiderTransfer292Hi:ℚ):ℝ), ((d2WiderTransfer292C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer292S0:ℚ):ℝ)| + ((d2WiderTransfer292C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer292S1:ℚ):ℝ)| ≤ ((d2WiderTransfer292Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer292S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292S0,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer292C0 then |x-((d2WiderTransfer292S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer292S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer292S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292S0,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292C0,d2Log131Q,d2WiderTransfer292S0,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer292C0 d2WiderTransfer292S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2WiderTransfer292S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292S1,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer292C1 then |x-((d2WiderTransfer292S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer292S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer292S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292S1,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer292C1,d2Log39Q,d2WiderTransfer292S1,d2WiderTransfer292Lo,d2WiderTransfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer292C1 d2WiderTransfer292S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2WiderTransfer292C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer292C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer292Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer292Arithmetic
  linarith
#print axioms d2WiderTransfer292Arithmetic
#print axioms d2WiderTransfer292Bound
def d2WiderTransfer293Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer293Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (333194895) 1 (-29))
def d2WiderTransfer293Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (16780883096428112327465) 1 (-80))
def d2WiderTransfer293C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (23) 25 (-5))
def d2WiderTransfer293S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer293Arithmetic : weightedUpper d2WiderTransfer293C0 d2Log135Lo d2Log135Hi ≤ d2WiderTransfer293Cap := by decide +kernel
theorem d2WiderTransfer293Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer293Lo:ℚ):ℝ) ((d2WiderTransfer293Hi:ℚ):ℝ), ((d2WiderTransfer293C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer293S0:ℚ):ℝ)| ≤ ((d2WiderTransfer293Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer293S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer293S0,d2WiderTransfer293Lo,d2WiderTransfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer293C0 then |x-((d2WiderTransfer293S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer293S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer293S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer293S0,d2WiderTransfer293Lo,d2WiderTransfer293Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer293C0,d2Log135Q,d2WiderTransfer293S0,d2WiderTransfer293Lo,d2WiderTransfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer293C0 d2WiderTransfer293S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have har : (((weightedUpper d2WiderTransfer293C0 d2Log135Lo d2Log135Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer293Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer293Arithmetic
  linarith
#print axioms d2WiderTransfer293Arithmetic
#print axioms d2WiderTransfer293Bound
def d2WiderTransfer294Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (165758587) 1 (-28))
def d2WiderTransfer294Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (333194895) 1 (-29))
def d2WiderTransfer294Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (33631870487695382623017) 1 (-80))
def d2WiderTransfer294C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (3) 275 (-5))
def d2WiderTransfer294S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer294C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-5) 11 (-4))
def d2WiderTransfer294S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer294Arithmetic : weightedUpper d2WiderTransfer294C0 d2Log135Lo d2Log135Hi + weightedUpper d2WiderTransfer294C1 d2Log39Lo d2Log39Hi ≤ d2WiderTransfer294Cap := by decide +kernel
theorem d2WiderTransfer294Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer294Lo:ℚ):ℝ) ((d2WiderTransfer294Hi:ℚ):ℝ), ((d2WiderTransfer294C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer294S0:ℚ):ℝ)| + ((d2WiderTransfer294C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer294S1:ℚ):ℝ)| ≤ ((d2WiderTransfer294Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer294S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294S0,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer294C0 then |x-((d2WiderTransfer294S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer294S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer294S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294S0,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294C0,d2Log135Q,d2WiderTransfer294S0,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer294C0 d2WiderTransfer294S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2WiderTransfer294S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294S1,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer294C1 then |x-((d2WiderTransfer294S1:ℚ):ℝ)| ≤ ((d2Log39Q:ℚ):ℝ) else ((d2Log39Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer294S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer294S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294S1,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer294C1,d2Log39Q,d2WiderTransfer294S1,d2WiderTransfer294Lo,d2WiderTransfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer294C1 d2WiderTransfer294S1 d2Log39Q d2Log39Lo d2Log39Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log39Bounds
  have har : (((weightedUpper d2WiderTransfer294C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer294C1 d2Log39Lo d2Log39Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer294Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer294Arithmetic
  linarith
#print axioms d2WiderTransfer294Arithmetic
#print axioms d2WiderTransfer294Bound
def d2WiderTransfer295Lo : ℚ := (d2LitsNearWiderTransfers036.q2 (333194895) 1 (-29))
def d2WiderTransfer295Hi : ℚ := (d2LitsNearWiderTransfers036.q2 (668067511) 1 (-30))
def d2WiderTransfer295Cap : ℚ := (d2LitsNearWiderTransfers036.q2 (1482581134158159655265) 1 (-80))
def d2WiderTransfer295C0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer295S0 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 1 (0))
def d2WiderTransfer295C1 : ℚ := (d2LitsNearWiderTransfers036.q2 (-1) 55 (-3))
def d2WiderTransfer295S1 : ℚ := (d2LitsNearWiderTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer295Arithmetic : weightedUpper d2WiderTransfer295C0 d2Log135Lo d2Log135Hi + weightedUpper d2WiderTransfer295C1 d2Log37Lo d2Log37Hi ≤ d2WiderTransfer295Cap := by decide +kernel
theorem d2WiderTransfer295Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer295Lo:ℚ):ℝ) ((d2WiderTransfer295Hi:ℚ):ℝ), ((d2WiderTransfer295C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer295S0:ℚ):ℝ)| + ((d2WiderTransfer295C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer295S1:ℚ):ℝ)| ≤ ((d2WiderTransfer295Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer295S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295S0,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer295C0 then |x-((d2WiderTransfer295S0:ℚ):ℝ)| ≤ ((d2Log135Q:ℚ):ℝ) else ((d2Log135Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer295S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer295S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295S0,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295C0,d2Log135Q,d2WiderTransfer295S0,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer295C0 d2WiderTransfer295S0 d2Log135Q d2Log135Lo d2Log135Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log135Bounds
  have hn1 : x-((d2WiderTransfer295S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295S1,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer295C1 then |x-((d2WiderTransfer295S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer295S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer295S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295S1,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers036.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer295C1,d2Log37Q,d2WiderTransfer295S1,d2WiderTransfer295Lo,d2WiderTransfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer295C1 d2WiderTransfer295S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2WiderTransfer295C0 d2Log135Lo d2Log135Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer295C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer295Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer295Arithmetic
  linarith
#print axioms d2WiderTransfer295Arithmetic
#print axioms d2WiderTransfer295Bound
end CatalanMeasure.GenD.Signed.Data.Cells

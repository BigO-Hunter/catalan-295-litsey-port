module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers046
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers046
open D72.LogTransfer
def d2Transfer368Lo : ℚ := (d2LitsNearTransfers046.q2 (31834725) 1 (-25))
def d2Transfer368Hi : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer368Cap : ℚ := (d2LitsNearTransfers046.q2 (55492843161057776455073) 1 (-79))
def d2Transfer368C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (-5))
def d2Transfer368S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer368Arithmetic : weightedUpper d2Transfer368C0 d2Log171Lo d2Log171Hi ≤ d2Transfer368Cap := by decide +kernel
theorem d2Transfer368Bound : ∀ x ∈ Set.Icc ((d2Transfer368Lo:ℚ):ℝ) ((d2Transfer368Hi:ℚ):ℝ), ((d2Transfer368C0:ℚ):ℝ)*Real.log |x-((d2Transfer368S0:ℚ):ℝ)| ≤ ((d2Transfer368Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer368S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer368S0,d2Transfer368Lo,d2Transfer368Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer368C0 then |x-((d2Transfer368S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer368S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer368S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer368S0,d2Transfer368Lo,d2Transfer368Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer368C0,d2Log171Q,d2Transfer368S0,d2Transfer368Lo,d2Transfer368Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer368C0 d2Transfer368S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2Transfer368C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2Transfer368Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer368Arithmetic
  linarith
#print axioms d2Transfer368Arithmetic
#print axioms d2Transfer368Bound
def d2Transfer369Lo : ℚ := (d2LitsNearTransfers046.q2 (31834725) 1 (-25))
def d2Transfer369Hi : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer369Cap : ℚ := (d2LitsNearTransfers046.q2 (63675261822203530136993) 1 (-79))
def d2Transfer369C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 11 (-5))
def d2Transfer369S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
def d2Transfer369C1 : ℚ := (d2LitsNearTransfers046.q2 (-5) 11 (-4))
def d2Transfer369S1 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer369Arithmetic : weightedUpper d2Transfer369C0 d2Log171Lo d2Log171Hi + weightedUpper d2Transfer369C1 d2Log3Lo d2Log3Hi ≤ d2Transfer369Cap := by decide +kernel
theorem d2Transfer369Bound : ∀ x ∈ Set.Icc ((d2Transfer369Lo:ℚ):ℝ) ((d2Transfer369Hi:ℚ):ℝ), ((d2Transfer369C0:ℚ):ℝ)*Real.log |x-((d2Transfer369S0:ℚ):ℝ)| + ((d2Transfer369C1:ℚ):ℝ)*Real.log |x-((d2Transfer369S1:ℚ):ℝ)| ≤ ((d2Transfer369Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer369S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369S0,d2Transfer369Lo,d2Transfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer369C0 then |x-((d2Transfer369S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer369S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer369S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369S0,d2Transfer369Lo,d2Transfer369Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369C0,d2Log171Q,d2Transfer369S0,d2Transfer369Lo,d2Transfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer369C0 d2Transfer369S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2Transfer369S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369S1,d2Transfer369Lo,d2Transfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer369C1 then |x-((d2Transfer369S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2Transfer369S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer369S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369S1,d2Transfer369Lo,d2Transfer369Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer369C1,d2Log3Q,d2Transfer369S1,d2Transfer369Lo,d2Transfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer369C1 d2Transfer369S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2Transfer369C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2Transfer369C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2Transfer369Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer369Arithmetic
  linarith
#print axioms d2Transfer369Arithmetic
#print axioms d2Transfer369Bound
def d2Transfer370Lo : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer370Hi : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer370Cap : ℚ := (d2LitsNearTransfers046.q2 (49771151816960380668549) 1 (-78))
def d2Transfer370C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 25 (-4))
def d2Transfer370S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer370Arithmetic : weightedUpper d2Transfer370C0 d2Log172Lo d2Log172Hi ≤ d2Transfer370Cap := by decide +kernel
theorem d2Transfer370Bound : ∀ x ∈ Set.Icc ((d2Transfer370Lo:ℚ):ℝ) ((d2Transfer370Hi:ℚ):ℝ), ((d2Transfer370C0:ℚ):ℝ)*Real.log |x-((d2Transfer370S0:ℚ):ℝ)| ≤ ((d2Transfer370Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer370S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer370S0,d2Transfer370Lo,d2Transfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer370C0 then |x-((d2Transfer370S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer370S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer370S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer370S0,d2Transfer370Lo,d2Transfer370Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer370C0,d2Log172Q,d2Transfer370S0,d2Transfer370Lo,d2Transfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer370C0 d2Transfer370S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2Transfer370C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2Transfer370Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer370Arithmetic
  linarith
#print axioms d2Transfer370Arithmetic
#print axioms d2Transfer370Bound
def d2Transfer371Lo : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer371Hi : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer371Cap : ℚ := (d2LitsNearTransfers046.q2 (50083726859119314504325) 1 (-78))
def d2Transfer371C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 275 (-4))
def d2Transfer371S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
def d2Transfer371C1 : ℚ := (d2LitsNearTransfers046.q2 (-1) 55 (-3))
def d2Transfer371S1 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer371Arithmetic : weightedUpper d2Transfer371C0 d2Log172Lo d2Log172Hi + weightedUpper d2Transfer371C1 d2Log2Lo d2Log2Hi ≤ d2Transfer371Cap := by decide +kernel
theorem d2Transfer371Bound : ∀ x ∈ Set.Icc ((d2Transfer371Lo:ℚ):ℝ) ((d2Transfer371Hi:ℚ):ℝ), ((d2Transfer371C0:ℚ):ℝ)*Real.log |x-((d2Transfer371S0:ℚ):ℝ)| + ((d2Transfer371C1:ℚ):ℝ)*Real.log |x-((d2Transfer371S1:ℚ):ℝ)| ≤ ((d2Transfer371Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer371S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371S0,d2Transfer371Lo,d2Transfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer371C0 then |x-((d2Transfer371S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer371S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer371S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371S0,d2Transfer371Lo,d2Transfer371Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371C0,d2Log172Q,d2Transfer371S0,d2Transfer371Lo,d2Transfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer371C0 d2Transfer371S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2Transfer371S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371S1,d2Transfer371Lo,d2Transfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer371C1 then |x-((d2Transfer371S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2Transfer371S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer371S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371S1,d2Transfer371Lo,d2Transfer371Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer371C1,d2Log2Q,d2Transfer371S1,d2Transfer371Lo,d2Transfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer371C1 d2Transfer371S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2Transfer371C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2Transfer371C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2Transfer371Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer371Arithmetic
  linarith
#print axioms d2Transfer371Arithmetic
#print axioms d2Transfer371Bound
def d2Transfer372Lo : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer372Hi : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer372Cap : ℚ := (d2LitsNearTransfers046.q2 (53889492381725054634629) 1 (-78))
def d2Transfer372C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (-5))
def d2Transfer372S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer372Arithmetic : weightedUpper d2Transfer372C0 d2Log172Lo d2Log172Hi ≤ d2Transfer372Cap := by decide +kernel
theorem d2Transfer372Bound : ∀ x ∈ Set.Icc ((d2Transfer372Lo:ℚ):ℝ) ((d2Transfer372Hi:ℚ):ℝ), ((d2Transfer372C0:ℚ):ℝ)*Real.log |x-((d2Transfer372S0:ℚ):ℝ)| ≤ ((d2Transfer372Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer372S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer372S0,d2Transfer372Lo,d2Transfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer372C0 then |x-((d2Transfer372S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer372S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer372S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer372S0,d2Transfer372Lo,d2Transfer372Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer372C0,d2Log172Q,d2Transfer372S0,d2Transfer372Lo,d2Transfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer372C0 d2Transfer372S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2Transfer372C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2Transfer372Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer372Arithmetic
  linarith
#print axioms d2Transfer372Arithmetic
#print axioms d2Transfer372Bound
def d2Transfer373Lo : ℚ := (d2LitsNearTransfers046.q2 (65347171) 1 (-26))
def d2Transfer373Hi : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer373Cap : ℚ := (d2LitsNearTransfers046.q2 (57980701712297931475589) 1 (-78))
def d2Transfer373C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 11 (-5))
def d2Transfer373S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
def d2Transfer373C1 : ℚ := (d2LitsNearTransfers046.q2 (-5) 11 (-4))
def d2Transfer373S1 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer373Arithmetic : weightedUpper d2Transfer373C0 d2Log172Lo d2Log172Hi + weightedUpper d2Transfer373C1 d2Log2Lo d2Log2Hi ≤ d2Transfer373Cap := by decide +kernel
theorem d2Transfer373Bound : ∀ x ∈ Set.Icc ((d2Transfer373Lo:ℚ):ℝ) ((d2Transfer373Hi:ℚ):ℝ), ((d2Transfer373C0:ℚ):ℝ)*Real.log |x-((d2Transfer373S0:ℚ):ℝ)| + ((d2Transfer373C1:ℚ):ℝ)*Real.log |x-((d2Transfer373S1:ℚ):ℝ)| ≤ ((d2Transfer373Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer373S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373S0,d2Transfer373Lo,d2Transfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer373C0 then |x-((d2Transfer373S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer373S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer373S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373S0,d2Transfer373Lo,d2Transfer373Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373C0,d2Log172Q,d2Transfer373S0,d2Transfer373Lo,d2Transfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer373C0 d2Transfer373S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2Transfer373S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373S1,d2Transfer373Lo,d2Transfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer373C1 then |x-((d2Transfer373S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2Transfer373S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer373S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373S1,d2Transfer373Lo,d2Transfer373Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer373C1,d2Log2Q,d2Transfer373S1,d2Transfer373Lo,d2Transfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer373C1 d2Transfer373S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2Transfer373C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2Transfer373C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2Transfer373Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer373Arithmetic
  linarith
#print axioms d2Transfer373Arithmetic
#print axioms d2Transfer373Bound
def d2Transfer374Lo : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer374Hi : ℚ := (d2LitsNearTransfers046.q2 (8380219) 1 (-23))
def d2Transfer374Cap : ℚ := (d2LitsNearTransfers046.q2 (206782343276902498879489) 1 (-80))
def d2Transfer374C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 25 (-4))
def d2Transfer374S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer374Arithmetic : weightedUpper d2Transfer374C0 d2Log173Lo d2Log173Hi ≤ d2Transfer374Cap := by decide +kernel
theorem d2Transfer374Bound : ∀ x ∈ Set.Icc ((d2Transfer374Lo:ℚ):ℝ) ((d2Transfer374Hi:ℚ):ℝ), ((d2Transfer374C0:ℚ):ℝ)*Real.log |x-((d2Transfer374S0:ℚ):ℝ)| ≤ ((d2Transfer374Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer374S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer374S0,d2Transfer374Lo,d2Transfer374Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer374C0 then |x-((d2Transfer374S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer374S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer374S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer374S0,d2Transfer374Lo,d2Transfer374Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer374C0,d2Log173Q,d2Transfer374S0,d2Transfer374Lo,d2Transfer374Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer374C0 d2Transfer374S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2Transfer374C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2Transfer374Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer374Arithmetic
  linarith
#print axioms d2Transfer374Arithmetic
#print axioms d2Transfer374Bound
def d2Transfer375Lo : ℚ := (d2LitsNearTransfers046.q2 (16756223) 1 (-24))
def d2Transfer375Hi : ℚ := (d2LitsNearTransfers046.q2 (8380219) 1 (-23))
def d2Transfer375Cap : ℚ := (d2LitsNearTransfers046.q2 (208032643445538234222593) 1 (-80))
def d2Transfer375C0 : ℚ := (d2LitsNearTransfers046.q2 (1) 275 (-4))
def d2Transfer375S0 : ℚ := (d2LitsNearTransfers046.q2 (-1) 1 (0))
def d2Transfer375C1 : ℚ := (d2LitsNearTransfers046.q2 (-1) 55 (-3))
def d2Transfer375S1 : ℚ := (d2LitsNearTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer375Arithmetic : weightedUpper d2Transfer375C0 d2Log173Lo d2Log173Hi + weightedUpper d2Transfer375C1 d2Log1Lo d2Log1Hi ≤ d2Transfer375Cap := by decide +kernel
theorem d2Transfer375Bound : ∀ x ∈ Set.Icc ((d2Transfer375Lo:ℚ):ℝ) ((d2Transfer375Hi:ℚ):ℝ), ((d2Transfer375C0:ℚ):ℝ)*Real.log |x-((d2Transfer375S0:ℚ):ℝ)| + ((d2Transfer375C1:ℚ):ℝ)*Real.log |x-((d2Transfer375S1:ℚ):ℝ)| ≤ ((d2Transfer375Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer375S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375S0,d2Transfer375Lo,d2Transfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer375C0 then |x-((d2Transfer375S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2Transfer375S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer375S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375S0,d2Transfer375Lo,d2Transfer375Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375C0,d2Log173Q,d2Transfer375S0,d2Transfer375Lo,d2Transfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer375C0 d2Transfer375S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2Transfer375S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375S1,d2Transfer375Lo,d2Transfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer375C1 then |x-((d2Transfer375S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2Transfer375S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer375S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375S1,d2Transfer375Lo,d2Transfer375Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer375C1,d2Log1Q,d2Transfer375S1,d2Transfer375Lo,d2Transfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer375C1 d2Transfer375S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2Transfer375C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2Transfer375C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2Transfer375Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer375Arithmetic
  linarith
#print axioms d2Transfer375Arithmetic
#print axioms d2Transfer375Bound
end CatalanMeasure.GenD.Signed.Data.Cells

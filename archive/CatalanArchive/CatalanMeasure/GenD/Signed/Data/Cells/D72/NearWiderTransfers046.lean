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
namespace d2LitsNearWiderTransfers046
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers046
open D72.LogTransfer
def d2WiderTransfer368Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (21768399) 1 (-25))
def d2WiderTransfer368Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (175824913) 1 (-28))
def d2WiderTransfer368Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (4976575732930488727807) 1 (-78))
def d2WiderTransfer368C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (23) 25 (-5))
def d2WiderTransfer368S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer368Arithmetic : weightedUpper d2WiderTransfer368C0 d2Log163Lo d2Log163Hi ≤ d2WiderTransfer368Cap := by decide +kernel
theorem d2WiderTransfer368Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer368Lo:ℚ):ℝ) ((d2WiderTransfer368Hi:ℚ):ℝ), ((d2WiderTransfer368C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer368S0:ℚ):ℝ)| ≤ ((d2WiderTransfer368Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer368S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer368S0,d2WiderTransfer368Lo,d2WiderTransfer368Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer368C0 then |x-((d2WiderTransfer368S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer368S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer368S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer368S0,d2WiderTransfer368Lo,d2WiderTransfer368Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer368C0,d2Log163Q,d2WiderTransfer368S0,d2WiderTransfer368Lo,d2WiderTransfer368Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer368C0 d2WiderTransfer368S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have har : (((weightedUpper d2WiderTransfer368C0 d2Log163Lo d2Log163Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer368Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer368Arithmetic
  linarith
#print axioms d2WiderTransfer368Arithmetic
#print axioms d2WiderTransfer368Bound
def d2WiderTransfer369Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (21768399) 1 (-25))
def d2WiderTransfer369Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (175824913) 1 (-28))
def d2WiderTransfer369Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (9189322580747306301695) 1 (-78))
def d2WiderTransfer369C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (3) 275 (-5))
def d2WiderTransfer369S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
def d2WiderTransfer369C1 : ℚ := (d2LitsNearWiderTransfers046.q2 (-5) 11 (-4))
def d2WiderTransfer369S1 : ℚ := (d2LitsNearWiderTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer369Arithmetic : weightedUpper d2WiderTransfer369C0 d2Log163Lo d2Log163Hi + weightedUpper d2WiderTransfer369C1 d2Log11Lo d2Log11Hi ≤ d2WiderTransfer369Cap := by decide +kernel
theorem d2WiderTransfer369Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer369Lo:ℚ):ℝ) ((d2WiderTransfer369Hi:ℚ):ℝ), ((d2WiderTransfer369C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer369S0:ℚ):ℝ)| + ((d2WiderTransfer369C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer369S1:ℚ):ℝ)| ≤ ((d2WiderTransfer369Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer369S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369S0,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer369C0 then |x-((d2WiderTransfer369S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer369S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer369S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369S0,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369C0,d2Log163Q,d2WiderTransfer369S0,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer369C0 d2WiderTransfer369S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have hn1 : x-((d2WiderTransfer369S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369S1,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer369C1 then |x-((d2WiderTransfer369S1:ℚ):ℝ)| ≤ ((d2Log11Q:ℚ):ℝ) else ((d2Log11Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer369S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer369S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369S1,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer369C1,d2Log11Q,d2WiderTransfer369S1,d2WiderTransfer369Lo,d2WiderTransfer369Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer369C1 d2WiderTransfer369S1 d2Log11Q d2Log11Lo d2Log11Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log11Bounds
  have har : (((weightedUpper d2WiderTransfer369C0 d2Log163Lo d2Log163Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer369C1 d2Log11Lo d2Log11Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer369Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer369Arithmetic
  linarith
#print axioms d2WiderTransfer369Arithmetic
#print axioms d2WiderTransfer369Bound
def d2WiderTransfer370Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (175824913) 1 (-28))
def d2WiderTransfer370Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer370Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (325246597409181460825) 1 (-76))
def d2WiderTransfer370C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 55 (-3))
def d2WiderTransfer370S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
def d2WiderTransfer370C1 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 55 (-3))
def d2WiderTransfer370S1 : ℚ := (d2LitsNearWiderTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer370Arithmetic : weightedUpper d2WiderTransfer370C0 d2Log163Lo d2Log163Hi + weightedUpper d2WiderTransfer370C1 d2Log10Lo d2Log10Hi ≤ d2WiderTransfer370Cap := by decide +kernel
theorem d2WiderTransfer370Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer370Lo:ℚ):ℝ) ((d2WiderTransfer370Hi:ℚ):ℝ), ((d2WiderTransfer370C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer370S0:ℚ):ℝ)| + ((d2WiderTransfer370C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer370S1:ℚ):ℝ)| ≤ ((d2WiderTransfer370Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer370S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370S0,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer370C0 then |x-((d2WiderTransfer370S0:ℚ):ℝ)| ≤ ((d2Log163Q:ℚ):ℝ) else ((d2Log163Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer370S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer370S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370S0,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370C0,d2Log163Q,d2WiderTransfer370S0,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer370C0 d2WiderTransfer370S0 d2Log163Q d2Log163Lo d2Log163Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log163Bounds
  have hn1 : x-((d2WiderTransfer370S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370S1,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer370C1 then |x-((d2WiderTransfer370S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer370S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer370S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370S1,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer370C1,d2Log10Q,d2WiderTransfer370S1,d2WiderTransfer370Lo,d2WiderTransfer370Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer370C1 d2WiderTransfer370S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2WiderTransfer370C0 d2Log163Lo d2Log163Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer370C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer370Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer370Arithmetic
  linarith
#print axioms d2WiderTransfer370Arithmetic
#print axioms d2WiderTransfer370Bound
def d2WiderTransfer371Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (175824913) 1 (-28))
def d2WiderTransfer371Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer371Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (1283483839529574394201) 1 (-76))
def d2WiderTransfer371C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (23) 25 (-5))
def d2WiderTransfer371S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer371Arithmetic : weightedUpper d2WiderTransfer371C0 d2Log164Lo d2Log164Hi ≤ d2WiderTransfer371Cap := by decide +kernel
theorem d2WiderTransfer371Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer371Lo:ℚ):ℝ) ((d2WiderTransfer371Hi:ℚ):ℝ), ((d2WiderTransfer371C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer371S0:ℚ):ℝ)| ≤ ((d2WiderTransfer371Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer371S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer371S0,d2WiderTransfer371Lo,d2WiderTransfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer371C0 then |x-((d2WiderTransfer371S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer371S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer371S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer371S0,d2WiderTransfer371Lo,d2WiderTransfer371Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer371C0,d2Log164Q,d2WiderTransfer371S0,d2WiderTransfer371Lo,d2WiderTransfer371Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer371C0 d2WiderTransfer371S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have har : (((weightedUpper d2WiderTransfer371C0 d2Log164Lo d2Log164Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer371Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer371Arithmetic
  linarith
#print axioms d2WiderTransfer371Arithmetic
#print axioms d2WiderTransfer371Bound
def d2WiderTransfer372Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (175824913) 1 (-28))
def d2WiderTransfer372Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer372Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (2336670551483778787673) 1 (-76))
def d2WiderTransfer372C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (3) 275 (-5))
def d2WiderTransfer372S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
def d2WiderTransfer372C1 : ℚ := (d2LitsNearWiderTransfers046.q2 (-5) 11 (-4))
def d2WiderTransfer372S1 : ℚ := (d2LitsNearWiderTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer372Arithmetic : weightedUpper d2WiderTransfer372C0 d2Log164Lo d2Log164Hi + weightedUpper d2WiderTransfer372C1 d2Log10Lo d2Log10Hi ≤ d2WiderTransfer372Cap := by decide +kernel
theorem d2WiderTransfer372Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer372Lo:ℚ):ℝ) ((d2WiderTransfer372Hi:ℚ):ℝ), ((d2WiderTransfer372C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer372S0:ℚ):ℝ)| + ((d2WiderTransfer372C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer372S1:ℚ):ℝ)| ≤ ((d2WiderTransfer372Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer372S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372S0,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer372C0 then |x-((d2WiderTransfer372S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer372S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer372S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372S0,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372C0,d2Log164Q,d2WiderTransfer372S0,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer372C0 d2WiderTransfer372S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2WiderTransfer372S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372S1,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer372C1 then |x-((d2WiderTransfer372S1:ℚ):ℝ)| ≤ ((d2Log10Q:ℚ):ℝ) else ((d2Log10Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer372S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer372S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372S1,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer372C1,d2Log10Q,d2WiderTransfer372S1,d2WiderTransfer372Lo,d2WiderTransfer372Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer372C1 d2WiderTransfer372S1 d2Log10Q d2Log10Lo d2Log10Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log10Bounds
  have har : (((weightedUpper d2WiderTransfer372C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer372C1 d2Log10Lo d2Log10Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer372Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer372Arithmetic
  linarith
#print axioms d2WiderTransfer372Arithmetic
#print axioms d2WiderTransfer372Bound
def d2WiderTransfer373Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer373Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (45214519) 1 (-26))
def d2WiderTransfer373Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (1624582038057085385233) 1 (-78))
def d2WiderTransfer373C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 55 (-3))
def d2WiderTransfer373S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
def d2WiderTransfer373C1 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 55 (-3))
def d2WiderTransfer373S1 : ℚ := (d2LitsNearWiderTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer373Arithmetic : weightedUpper d2WiderTransfer373C0 d2Log164Lo d2Log164Hi + weightedUpper d2WiderTransfer373C1 d2Log9Lo d2Log9Hi ≤ d2WiderTransfer373Cap := by decide +kernel
theorem d2WiderTransfer373Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer373Lo:ℚ):ℝ) ((d2WiderTransfer373Hi:ℚ):ℝ), ((d2WiderTransfer373C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer373S0:ℚ):ℝ)| + ((d2WiderTransfer373C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer373S1:ℚ):ℝ)| ≤ ((d2WiderTransfer373Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer373S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373S0,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer373C0 then |x-((d2WiderTransfer373S0:ℚ):ℝ)| ≤ ((d2Log164Q:ℚ):ℝ) else ((d2Log164Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer373S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer373S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373S0,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373C0,d2Log164Q,d2WiderTransfer373S0,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer373C0 d2WiderTransfer373S0 d2Log164Q d2Log164Lo d2Log164Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log164Bounds
  have hn1 : x-((d2WiderTransfer373S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373S1,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer373C1 then |x-((d2WiderTransfer373S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer373S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer373S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373S1,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer373C1,d2Log9Q,d2WiderTransfer373S1,d2WiderTransfer373Lo,d2WiderTransfer373Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer373C1 d2WiderTransfer373S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2WiderTransfer373C0 d2Log164Lo d2Log164Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer373C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer373Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer373Arithmetic
  linarith
#print axioms d2WiderTransfer373Arithmetic
#print axioms d2WiderTransfer373Bound
def d2WiderTransfer374Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer374Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (45214519) 1 (-26))
def d2WiderTransfer374Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (5457531006538657118737) 1 (-78))
def d2WiderTransfer374C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (23) 25 (-5))
def d2WiderTransfer374S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer374Arithmetic : weightedUpper d2WiderTransfer374C0 d2Log165Lo d2Log165Hi ≤ d2WiderTransfer374Cap := by decide +kernel
theorem d2WiderTransfer374Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer374Lo:ℚ):ℝ) ((d2WiderTransfer374Hi:ℚ):ℝ), ((d2WiderTransfer374C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer374S0:ℚ):ℝ)| ≤ ((d2WiderTransfer374Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer374S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer374S0,d2WiderTransfer374Lo,d2WiderTransfer374Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer374C0 then |x-((d2WiderTransfer374S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer374S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer374S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer374S0,d2WiderTransfer374Lo,d2WiderTransfer374Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer374C0,d2Log165Q,d2WiderTransfer374S0,d2WiderTransfer374Lo,d2WiderTransfer374Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer374C0 d2WiderTransfer374S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have har : (((weightedUpper d2WiderTransfer374C0 d2Log165Lo d2Log165Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer374Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer374Arithmetic
  linarith
#print axioms d2WiderTransfer374Arithmetic
#print axioms d2WiderTransfer374Bound
def d2WiderTransfer375Lo : ℚ := (d2LitsNearWiderTransfers046.q2 (88751317) 1 (-27))
def d2WiderTransfer375Hi : ℚ := (d2LitsNearWiderTransfers046.q2 (45214519) 1 (-26))
def d2WiderTransfer375Cap : ℚ := (d2LitsNearWiderTransfers046.q2 (9670277854355474692625) 1 (-78))
def d2WiderTransfer375C0 : ℚ := (d2LitsNearWiderTransfers046.q2 (3) 275 (-5))
def d2WiderTransfer375S0 : ℚ := (d2LitsNearWiderTransfers046.q2 (-1) 1 (0))
def d2WiderTransfer375C1 : ℚ := (d2LitsNearWiderTransfers046.q2 (-5) 11 (-4))
def d2WiderTransfer375S1 : ℚ := (d2LitsNearWiderTransfers046.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer375Arithmetic : weightedUpper d2WiderTransfer375C0 d2Log165Lo d2Log165Hi + weightedUpper d2WiderTransfer375C1 d2Log9Lo d2Log9Hi ≤ d2WiderTransfer375Cap := by decide +kernel
theorem d2WiderTransfer375Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer375Lo:ℚ):ℝ) ((d2WiderTransfer375Hi:ℚ):ℝ), ((d2WiderTransfer375C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer375S0:ℚ):ℝ)| + ((d2WiderTransfer375C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer375S1:ℚ):ℝ)| ≤ ((d2WiderTransfer375Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer375S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375S0,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer375C0 then |x-((d2WiderTransfer375S0:ℚ):ℝ)| ≤ ((d2Log165Q:ℚ):ℝ) else ((d2Log165Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer375S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer375S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375S0,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375C0,d2Log165Q,d2WiderTransfer375S0,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer375C0 d2WiderTransfer375S0 d2Log165Q d2Log165Lo d2Log165Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log165Bounds
  have hn1 : x-((d2WiderTransfer375S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375S1,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer375C1 then |x-((d2WiderTransfer375S1:ℚ):ℝ)| ≤ ((d2Log9Q:ℚ):ℝ) else ((d2Log9Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer375S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer375S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375S1,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers046.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer375C1,d2Log9Q,d2WiderTransfer375S1,d2WiderTransfer375Lo,d2WiderTransfer375Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer375C1 d2WiderTransfer375S1 d2Log9Q d2Log9Lo d2Log9Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log9Bounds
  have har : (((weightedUpper d2WiderTransfer375C0 d2Log165Lo d2Log165Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer375C1 d2Log9Lo d2Log9Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer375Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer375Arithmetic
  linarith
#print axioms d2WiderTransfer375Arithmetic
#print axioms d2WiderTransfer375Bound
end CatalanMeasure.GenD.Signed.Data.Cells

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
namespace d2LitsNearWiderTransfers049
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers049
open D72.LogTransfer
def d2WiderTransfer392Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (31834725) 1 (-25))
def d2WiderTransfer392Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (65347171) 1 (-26))
def d2WiderTransfer392Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (108444559890870197571225) 1 (-80))
def d2WiderTransfer392C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (23) 25 (-5))
def d2WiderTransfer392S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer392Arithmetic : weightedUpper d2WiderTransfer392C0 d2Log171Lo d2Log171Hi ≤ d2WiderTransfer392Cap := by decide +kernel
theorem d2WiderTransfer392Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer392Lo:ℚ):ℝ) ((d2WiderTransfer392Hi:ℚ):ℝ), ((d2WiderTransfer392C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer392S0:ℚ):ℝ)| ≤ ((d2WiderTransfer392Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer392S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer392S0,d2WiderTransfer392Lo,d2WiderTransfer392Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer392C0 then |x-((d2WiderTransfer392S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer392S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer392S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer392S0,d2WiderTransfer392Lo,d2WiderTransfer392Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer392C0,d2Log171Q,d2WiderTransfer392S0,d2WiderTransfer392Lo,d2WiderTransfer392Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer392C0 d2WiderTransfer392S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2WiderTransfer392C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer392Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer392Arithmetic
  linarith
#print axioms d2WiderTransfer392Arithmetic
#print axioms d2WiderTransfer392Bound
def d2WiderTransfer393Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (31834725) 1 (-25))
def d2WiderTransfer393Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (65347171) 1 (-26))
def d2WiderTransfer393Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (125295547282137467866777) 1 (-80))
def d2WiderTransfer393C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (3) 275 (-5))
def d2WiderTransfer393S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
def d2WiderTransfer393C1 : ℚ := (d2LitsNearWiderTransfers049.q2 (-5) 11 (-4))
def d2WiderTransfer393S1 : ℚ := (d2LitsNearWiderTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer393Arithmetic : weightedUpper d2WiderTransfer393C0 d2Log171Lo d2Log171Hi + weightedUpper d2WiderTransfer393C1 d2Log3Lo d2Log3Hi ≤ d2WiderTransfer393Cap := by decide +kernel
theorem d2WiderTransfer393Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer393Lo:ℚ):ℝ) ((d2WiderTransfer393Hi:ℚ):ℝ), ((d2WiderTransfer393C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer393S0:ℚ):ℝ)| + ((d2WiderTransfer393C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer393S1:ℚ):ℝ)| ≤ ((d2WiderTransfer393Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer393S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393S0,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer393C0 then |x-((d2WiderTransfer393S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer393S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer393S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393S0,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393C0,d2Log171Q,d2WiderTransfer393S0,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer393C0 d2WiderTransfer393S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2WiderTransfer393S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393S1,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer393C1 then |x-((d2WiderTransfer393S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer393S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer393S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393S1,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer393C1,d2Log3Q,d2WiderTransfer393S1,d2WiderTransfer393Lo,d2WiderTransfer393Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer393C1 d2WiderTransfer393S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2WiderTransfer393C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer393C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer393Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer393Arithmetic
  linarith
#print axioms d2WiderTransfer393Arithmetic
#print axioms d2WiderTransfer393Bound
def d2WiderTransfer394Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (65347171) 1 (-26))
def d2WiderTransfer394Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer394Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (197647006248660188417815) 1 (-80))
def d2WiderTransfer394C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 55 (-3))
def d2WiderTransfer394S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
def d2WiderTransfer394C1 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 55 (-3))
def d2WiderTransfer394S1 : ℚ := (d2LitsNearWiderTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer394Arithmetic : weightedUpper d2WiderTransfer394C0 d2Log171Lo d2Log171Hi + weightedUpper d2WiderTransfer394C1 d2Log2Lo d2Log2Hi ≤ d2WiderTransfer394Cap := by decide +kernel
theorem d2WiderTransfer394Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer394Lo:ℚ):ℝ) ((d2WiderTransfer394Hi:ℚ):ℝ), ((d2WiderTransfer394C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer394S0:ℚ):ℝ)| + ((d2WiderTransfer394C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer394S1:ℚ):ℝ)| ≤ ((d2WiderTransfer394Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer394S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394S0,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer394C0 then |x-((d2WiderTransfer394S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer394S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer394S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394S0,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394C0,d2Log171Q,d2WiderTransfer394S0,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer394C0 d2WiderTransfer394S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2WiderTransfer394S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394S1,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer394C1 then |x-((d2WiderTransfer394S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer394S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer394S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394S1,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer394C1,d2Log2Q,d2WiderTransfer394S1,d2WiderTransfer394Lo,d2WiderTransfer394Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer394C1 d2WiderTransfer394S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2WiderTransfer394C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer394C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer394Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer394Arithmetic
  linarith
#print axioms d2WiderTransfer394Arithmetic
#print axioms d2WiderTransfer394Bound
def d2WiderTransfer395Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (65347171) 1 (-26))
def d2WiderTransfer395Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer395Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (212978802122586475351831) 1 (-80))
def d2WiderTransfer395C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (23) 25 (-5))
def d2WiderTransfer395S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer395Arithmetic : weightedUpper d2WiderTransfer395C0 d2Log172Lo d2Log172Hi ≤ d2WiderTransfer395Cap := by decide +kernel
theorem d2WiderTransfer395Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer395Lo:ℚ):ℝ) ((d2WiderTransfer395Hi:ℚ):ℝ), ((d2WiderTransfer395C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer395S0:ℚ):ℝ)| ≤ ((d2WiderTransfer395Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer395S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer395S0,d2WiderTransfer395Lo,d2WiderTransfer395Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer395C0 then |x-((d2WiderTransfer395S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer395S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer395S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer395S0,d2WiderTransfer395Lo,d2WiderTransfer395Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer395C0,d2Log172Q,d2WiderTransfer395S0,d2WiderTransfer395Lo,d2WiderTransfer395Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer395C0 d2WiderTransfer395S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2WiderTransfer395C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer395Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer395Arithmetic
  linarith
#print axioms d2WiderTransfer395Arithmetic
#print axioms d2WiderTransfer395Bound
def d2WiderTransfer396Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (65347171) 1 (-26))
def d2WiderTransfer396Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer396Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (229829789513853745647383) 1 (-80))
def d2WiderTransfer396C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (3) 275 (-5))
def d2WiderTransfer396S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
def d2WiderTransfer396C1 : ℚ := (d2LitsNearWiderTransfers049.q2 (-5) 11 (-4))
def d2WiderTransfer396S1 : ℚ := (d2LitsNearWiderTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer396Arithmetic : weightedUpper d2WiderTransfer396C0 d2Log172Lo d2Log172Hi + weightedUpper d2WiderTransfer396C1 d2Log2Lo d2Log2Hi ≤ d2WiderTransfer396Cap := by decide +kernel
theorem d2WiderTransfer396Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer396Lo:ℚ):ℝ) ((d2WiderTransfer396Hi:ℚ):ℝ), ((d2WiderTransfer396C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer396S0:ℚ):ℝ)| + ((d2WiderTransfer396C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer396S1:ℚ):ℝ)| ≤ ((d2WiderTransfer396Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer396S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396S0,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer396C0 then |x-((d2WiderTransfer396S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer396S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer396S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396S0,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396C0,d2Log172Q,d2WiderTransfer396S0,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer396C0 d2WiderTransfer396S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2WiderTransfer396S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396S1,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer396C1 then |x-((d2WiderTransfer396S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer396S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer396S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396S1,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer396C1,d2Log2Q,d2WiderTransfer396S1,d2WiderTransfer396Lo,d2WiderTransfer396Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer396C1 d2WiderTransfer396S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2WiderTransfer396C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer396C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer396Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer396Arithmetic
  linarith
#print axioms d2WiderTransfer396Arithmetic
#print axioms d2WiderTransfer396Bound
def d2WiderTransfer397Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer397Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (8380219) 1 (-23))
def d2WiderTransfer397Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (51336090597617681143313) 1 (-78))
def d2WiderTransfer397C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 55 (-3))
def d2WiderTransfer397S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
def d2WiderTransfer397C1 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 55 (-3))
def d2WiderTransfer397S1 : ℚ := (d2LitsNearWiderTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer397Arithmetic : weightedUpper d2WiderTransfer397C0 d2Log172Lo d2Log172Hi + weightedUpper d2WiderTransfer397C1 d2Log1Lo d2Log1Hi ≤ d2WiderTransfer397Cap := by decide +kernel
theorem d2WiderTransfer397Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer397Lo:ℚ):ℝ) ((d2WiderTransfer397Hi:ℚ):ℝ), ((d2WiderTransfer397C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer397S0:ℚ):ℝ)| + ((d2WiderTransfer397C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer397S1:ℚ):ℝ)| ≤ ((d2WiderTransfer397Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer397S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397S0,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer397C0 then |x-((d2WiderTransfer397S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer397S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer397S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397S0,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397C0,d2Log172Q,d2WiderTransfer397S0,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer397C0 d2WiderTransfer397S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2WiderTransfer397S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397S1,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer397C1 then |x-((d2WiderTransfer397S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer397S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer397S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397S1,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer397C1,d2Log1Q,d2WiderTransfer397S1,d2WiderTransfer397Lo,d2WiderTransfer397Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer397C1 d2WiderTransfer397S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2WiderTransfer397C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer397C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer397Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer397Arithmetic
  linarith
#print axioms d2WiderTransfer397Arithmetic
#print axioms d2WiderTransfer397Bound
def d2WiderTransfer398Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer398Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (8380219) 1 (-23))
def d2WiderTransfer398Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (55169039566099252876817) 1 (-78))
def d2WiderTransfer398C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (23) 25 (-5))
def d2WiderTransfer398S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer398Arithmetic : weightedUpper d2WiderTransfer398C0 d2Log173Lo d2Log173Hi ≤ d2WiderTransfer398Cap := by decide +kernel
theorem d2WiderTransfer398Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer398Lo:ℚ):ℝ) ((d2WiderTransfer398Hi:ℚ):ℝ), ((d2WiderTransfer398C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer398S0:ℚ):ℝ)| ≤ ((d2WiderTransfer398Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer398S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer398S0,d2WiderTransfer398Lo,d2WiderTransfer398Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer398C0 then |x-((d2WiderTransfer398S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer398S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer398S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer398S0,d2WiderTransfer398Lo,d2WiderTransfer398Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer398C0,d2Log173Q,d2WiderTransfer398S0,d2WiderTransfer398Lo,d2WiderTransfer398Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer398C0 d2WiderTransfer398S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2WiderTransfer398C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer398Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer398Arithmetic
  linarith
#print axioms d2WiderTransfer398Arithmetic
#print axioms d2WiderTransfer398Bound
def d2WiderTransfer399Lo : ℚ := (d2LitsNearWiderTransfers049.q2 (16756223) 1 (-24))
def d2WiderTransfer399Hi : ℚ := (d2LitsNearWiderTransfers049.q2 (8380219) 1 (-23))
def d2WiderTransfer399Cap : ℚ := (d2LitsNearWiderTransfers049.q2 (59381786413916070450705) 1 (-78))
def d2WiderTransfer399C0 : ℚ := (d2LitsNearWiderTransfers049.q2 (3) 275 (-5))
def d2WiderTransfer399S0 : ℚ := (d2LitsNearWiderTransfers049.q2 (-1) 1 (0))
def d2WiderTransfer399C1 : ℚ := (d2LitsNearWiderTransfers049.q2 (-5) 11 (-4))
def d2WiderTransfer399S1 : ℚ := (d2LitsNearWiderTransfers049.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer399Arithmetic : weightedUpper d2WiderTransfer399C0 d2Log173Lo d2Log173Hi + weightedUpper d2WiderTransfer399C1 d2Log1Lo d2Log1Hi ≤ d2WiderTransfer399Cap := by decide +kernel
theorem d2WiderTransfer399Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer399Lo:ℚ):ℝ) ((d2WiderTransfer399Hi:ℚ):ℝ), ((d2WiderTransfer399C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer399S0:ℚ):ℝ)| + ((d2WiderTransfer399C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer399S1:ℚ):ℝ)| ≤ ((d2WiderTransfer399Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer399S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399S0,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer399C0 then |x-((d2WiderTransfer399S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer399S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer399S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399S0,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399C0,d2Log173Q,d2WiderTransfer399S0,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer399C0 d2WiderTransfer399S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2WiderTransfer399S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399S1,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer399C1 then |x-((d2WiderTransfer399S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer399S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer399S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399S1,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers049.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer399C1,d2Log1Q,d2WiderTransfer399S1,d2WiderTransfer399Lo,d2WiderTransfer399Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer399C1 d2WiderTransfer399S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2WiderTransfer399C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer399C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer399Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer399Arithmetic
  linarith
#print axioms d2WiderTransfer399Arithmetic
#print axioms d2WiderTransfer399Bound
end CatalanMeasure.GenD.Signed.Data.Cells

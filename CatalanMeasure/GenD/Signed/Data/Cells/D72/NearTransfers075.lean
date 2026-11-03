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
namespace d2LitsNearTransfers075
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers075
open D72.LogTransfer
def d2Transfer600Lo : ℚ := (d2LitsNearTransfers075.q2 (7539251) 1 (-23))
def d2Transfer600Hi : ℚ := (d2LitsNearTransfers075.q2 (31834725) 1 (-25))
def d2Transfer600Cap : ℚ := (d2LitsNearTransfers075.q2 (102312947180000405823863) 1 (-80))
def d2Transfer600C0 : ℚ := (d2LitsNearTransfers075.q2 (3) 275 (-5))
def d2Transfer600S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer600C1 : ℚ := (d2LitsNearTransfers075.q2 (-5) 11 (-4))
def d2Transfer600S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer600Arithmetic : weightedUpper d2Transfer600C0 d2Log170Lo d2Log170Hi + weightedUpper d2Transfer600C1 d2Log4Lo d2Log4Hi ≤ d2Transfer600Cap := by decide +kernel
theorem d2Transfer600Bound : ∀ x ∈ Set.Icc ((d2Transfer600Lo:ℚ):ℝ) ((d2Transfer600Hi:ℚ):ℝ), ((d2Transfer600C0:ℚ):ℝ)*Real.log |x-((d2Transfer600S0:ℚ):ℝ)| + ((d2Transfer600C1:ℚ):ℝ)*Real.log |x-((d2Transfer600S1:ℚ):ℝ)| ≤ ((d2Transfer600Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer600S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600S0,d2Transfer600Lo,d2Transfer600Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer600C0 then |x-((d2Transfer600S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer600S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer600S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600S0,d2Transfer600Lo,d2Transfer600Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600C0,d2Log170Q,d2Transfer600S0,d2Transfer600Lo,d2Transfer600Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer600C0 d2Transfer600S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2Transfer600S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600S1,d2Transfer600Lo,d2Transfer600Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer600C1 then |x-((d2Transfer600S1:ℚ):ℝ)| ≤ ((d2Log4Q:ℚ):ℝ) else ((d2Log4Q:ℚ):ℝ) ≤ |x-((d2Transfer600S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer600S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600S1,d2Transfer600Lo,d2Transfer600Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer600C1,d2Log4Q,d2Transfer600S1,d2Transfer600Lo,d2Transfer600Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer600C1 d2Transfer600S1 d2Log4Q d2Log4Lo d2Log4Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log4Bounds
  have har : (((weightedUpper d2Transfer600C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2Transfer600C1 d2Log4Lo d2Log4Hi:ℚ):ℝ)) ≤ ((d2Transfer600Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer600Arithmetic
  linarith
#print axioms d2Transfer600Arithmetic
#print axioms d2Transfer600Bound
def d2Transfer601Lo : ℚ := (d2LitsNearTransfers075.q2 (31834725) 1 (-25))
def d2Transfer601Hi : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer601Cap : ℚ := (d2LitsNearTransfers075.q2 (93112764016943910637209) 1 (-80))
def d2Transfer601C0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer601S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer601C1 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer601S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer601Arithmetic : weightedUpper d2Transfer601C0 d2Log170Lo d2Log170Hi + weightedUpper d2Transfer601C1 d2Log3Lo d2Log3Hi ≤ d2Transfer601Cap := by decide +kernel
theorem d2Transfer601Bound : ∀ x ∈ Set.Icc ((d2Transfer601Lo:ℚ):ℝ) ((d2Transfer601Hi:ℚ):ℝ), ((d2Transfer601C0:ℚ):ℝ)*Real.log |x-((d2Transfer601S0:ℚ):ℝ)| + ((d2Transfer601C1:ℚ):ℝ)*Real.log |x-((d2Transfer601S1:ℚ):ℝ)| ≤ ((d2Transfer601Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer601S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601S0,d2Transfer601Lo,d2Transfer601Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer601C0 then |x-((d2Transfer601S0:ℚ):ℝ)| ≤ ((d2Log170Q:ℚ):ℝ) else ((d2Log170Q:ℚ):ℝ) ≤ |x-((d2Transfer601S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer601S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601S0,d2Transfer601Lo,d2Transfer601Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601C0,d2Log170Q,d2Transfer601S0,d2Transfer601Lo,d2Transfer601Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer601C0 d2Transfer601S0 d2Log170Q d2Log170Lo d2Log170Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log170Bounds
  have hn1 : x-((d2Transfer601S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601S1,d2Transfer601Lo,d2Transfer601Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer601C1 then |x-((d2Transfer601S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2Transfer601S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer601S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601S1,d2Transfer601Lo,d2Transfer601Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer601C1,d2Log3Q,d2Transfer601S1,d2Transfer601Lo,d2Transfer601Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer601C1 d2Transfer601S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2Transfer601C0 d2Log170Lo d2Log170Hi:ℚ):ℝ) + ((weightedUpper d2Transfer601C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2Transfer601Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer601Arithmetic
  linarith
#print axioms d2Transfer601Arithmetic
#print axioms d2Transfer601Bound
def d2Transfer602Lo : ℚ := (d2LitsNearTransfers075.q2 (31834725) 1 (-25))
def d2Transfer602Hi : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer602Cap : ℚ := (d2LitsNearTransfers075.q2 (108444559890870197571225) 1 (-80))
def d2Transfer602C0 : ℚ := (d2LitsNearTransfers075.q2 (23) 25 (-5))
def d2Transfer602S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer602Arithmetic : weightedUpper d2Transfer602C0 d2Log171Lo d2Log171Hi ≤ d2Transfer602Cap := by decide +kernel
theorem d2Transfer602Bound : ∀ x ∈ Set.Icc ((d2Transfer602Lo:ℚ):ℝ) ((d2Transfer602Hi:ℚ):ℝ), ((d2Transfer602C0:ℚ):ℝ)*Real.log |x-((d2Transfer602S0:ℚ):ℝ)| ≤ ((d2Transfer602Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer602S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer602S0,d2Transfer602Lo,d2Transfer602Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer602C0 then |x-((d2Transfer602S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer602S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer602S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer602S0,d2Transfer602Lo,d2Transfer602Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer602C0,d2Log171Q,d2Transfer602S0,d2Transfer602Lo,d2Transfer602Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer602C0 d2Transfer602S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have har : (((weightedUpper d2Transfer602C0 d2Log171Lo d2Log171Hi:ℚ):ℝ)) ≤ ((d2Transfer602Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer602Arithmetic
  linarith
#print axioms d2Transfer602Arithmetic
#print axioms d2Transfer602Bound
def d2Transfer603Lo : ℚ := (d2LitsNearTransfers075.q2 (31834725) 1 (-25))
def d2Transfer603Hi : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer603Cap : ℚ := (d2LitsNearTransfers075.q2 (125295547282137467866777) 1 (-80))
def d2Transfer603C0 : ℚ := (d2LitsNearTransfers075.q2 (3) 275 (-5))
def d2Transfer603S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer603C1 : ℚ := (d2LitsNearTransfers075.q2 (-5) 11 (-4))
def d2Transfer603S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer603Arithmetic : weightedUpper d2Transfer603C0 d2Log171Lo d2Log171Hi + weightedUpper d2Transfer603C1 d2Log3Lo d2Log3Hi ≤ d2Transfer603Cap := by decide +kernel
theorem d2Transfer603Bound : ∀ x ∈ Set.Icc ((d2Transfer603Lo:ℚ):ℝ) ((d2Transfer603Hi:ℚ):ℝ), ((d2Transfer603C0:ℚ):ℝ)*Real.log |x-((d2Transfer603S0:ℚ):ℝ)| + ((d2Transfer603C1:ℚ):ℝ)*Real.log |x-((d2Transfer603S1:ℚ):ℝ)| ≤ ((d2Transfer603Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer603S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603S0,d2Transfer603Lo,d2Transfer603Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer603C0 then |x-((d2Transfer603S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer603S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer603S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603S0,d2Transfer603Lo,d2Transfer603Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603C0,d2Log171Q,d2Transfer603S0,d2Transfer603Lo,d2Transfer603Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer603C0 d2Transfer603S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2Transfer603S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603S1,d2Transfer603Lo,d2Transfer603Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer603C1 then |x-((d2Transfer603S1:ℚ):ℝ)| ≤ ((d2Log3Q:ℚ):ℝ) else ((d2Log3Q:ℚ):ℝ) ≤ |x-((d2Transfer603S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer603S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603S1,d2Transfer603Lo,d2Transfer603Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer603C1,d2Log3Q,d2Transfer603S1,d2Transfer603Lo,d2Transfer603Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer603C1 d2Transfer603S1 d2Log3Q d2Log3Lo d2Log3Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log3Bounds
  have har : (((weightedUpper d2Transfer603C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2Transfer603C1 d2Log3Lo d2Log3Hi:ℚ):ℝ)) ≤ ((d2Transfer603Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer603Arithmetic
  linarith
#print axioms d2Transfer603Arithmetic
#print axioms d2Transfer603Bound
def d2Transfer604Lo : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer604Hi : ℚ := (d2LitsNearTransfers075.q2 (16756223) 1 (-24))
def d2Transfer604Cap : ℚ := (d2LitsNearTransfers075.q2 (197647006248660188417815) 1 (-80))
def d2Transfer604C0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer604S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer604C1 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer604S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer604Arithmetic : weightedUpper d2Transfer604C0 d2Log171Lo d2Log171Hi + weightedUpper d2Transfer604C1 d2Log2Lo d2Log2Hi ≤ d2Transfer604Cap := by decide +kernel
theorem d2Transfer604Bound : ∀ x ∈ Set.Icc ((d2Transfer604Lo:ℚ):ℝ) ((d2Transfer604Hi:ℚ):ℝ), ((d2Transfer604C0:ℚ):ℝ)*Real.log |x-((d2Transfer604S0:ℚ):ℝ)| + ((d2Transfer604C1:ℚ):ℝ)*Real.log |x-((d2Transfer604S1:ℚ):ℝ)| ≤ ((d2Transfer604Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer604S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604S0,d2Transfer604Lo,d2Transfer604Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer604C0 then |x-((d2Transfer604S0:ℚ):ℝ)| ≤ ((d2Log171Q:ℚ):ℝ) else ((d2Log171Q:ℚ):ℝ) ≤ |x-((d2Transfer604S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer604S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604S0,d2Transfer604Lo,d2Transfer604Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604C0,d2Log171Q,d2Transfer604S0,d2Transfer604Lo,d2Transfer604Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer604C0 d2Transfer604S0 d2Log171Q d2Log171Lo d2Log171Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log171Bounds
  have hn1 : x-((d2Transfer604S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604S1,d2Transfer604Lo,d2Transfer604Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer604C1 then |x-((d2Transfer604S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2Transfer604S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer604S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604S1,d2Transfer604Lo,d2Transfer604Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer604C1,d2Log2Q,d2Transfer604S1,d2Transfer604Lo,d2Transfer604Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer604C1 d2Transfer604S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2Transfer604C0 d2Log171Lo d2Log171Hi:ℚ):ℝ) + ((weightedUpper d2Transfer604C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2Transfer604Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer604Arithmetic
  linarith
#print axioms d2Transfer604Arithmetic
#print axioms d2Transfer604Bound
def d2Transfer605Lo : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer605Hi : ℚ := (d2LitsNearTransfers075.q2 (16756223) 1 (-24))
def d2Transfer605Cap : ℚ := (d2LitsNearTransfers075.q2 (212978802122586475351831) 1 (-80))
def d2Transfer605C0 : ℚ := (d2LitsNearTransfers075.q2 (23) 25 (-5))
def d2Transfer605S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer605Arithmetic : weightedUpper d2Transfer605C0 d2Log172Lo d2Log172Hi ≤ d2Transfer605Cap := by decide +kernel
theorem d2Transfer605Bound : ∀ x ∈ Set.Icc ((d2Transfer605Lo:ℚ):ℝ) ((d2Transfer605Hi:ℚ):ℝ), ((d2Transfer605C0:ℚ):ℝ)*Real.log |x-((d2Transfer605S0:ℚ):ℝ)| ≤ ((d2Transfer605Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer605S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer605S0,d2Transfer605Lo,d2Transfer605Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer605C0 then |x-((d2Transfer605S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer605S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer605S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer605S0,d2Transfer605Lo,d2Transfer605Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer605C0,d2Log172Q,d2Transfer605S0,d2Transfer605Lo,d2Transfer605Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer605C0 d2Transfer605S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2Transfer605C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2Transfer605Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer605Arithmetic
  linarith
#print axioms d2Transfer605Arithmetic
#print axioms d2Transfer605Bound
def d2Transfer606Lo : ℚ := (d2LitsNearTransfers075.q2 (65347171) 1 (-26))
def d2Transfer606Hi : ℚ := (d2LitsNearTransfers075.q2 (16756223) 1 (-24))
def d2Transfer606Cap : ℚ := (d2LitsNearTransfers075.q2 (229829789513853745647383) 1 (-80))
def d2Transfer606C0 : ℚ := (d2LitsNearTransfers075.q2 (3) 275 (-5))
def d2Transfer606S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer606C1 : ℚ := (d2LitsNearTransfers075.q2 (-5) 11 (-4))
def d2Transfer606S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer606Arithmetic : weightedUpper d2Transfer606C0 d2Log172Lo d2Log172Hi + weightedUpper d2Transfer606C1 d2Log2Lo d2Log2Hi ≤ d2Transfer606Cap := by decide +kernel
theorem d2Transfer606Bound : ∀ x ∈ Set.Icc ((d2Transfer606Lo:ℚ):ℝ) ((d2Transfer606Hi:ℚ):ℝ), ((d2Transfer606C0:ℚ):ℝ)*Real.log |x-((d2Transfer606S0:ℚ):ℝ)| + ((d2Transfer606C1:ℚ):ℝ)*Real.log |x-((d2Transfer606S1:ℚ):ℝ)| ≤ ((d2Transfer606Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer606S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606S0,d2Transfer606Lo,d2Transfer606Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer606C0 then |x-((d2Transfer606S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer606S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer606S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606S0,d2Transfer606Lo,d2Transfer606Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606C0,d2Log172Q,d2Transfer606S0,d2Transfer606Lo,d2Transfer606Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer606C0 d2Transfer606S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2Transfer606S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606S1,d2Transfer606Lo,d2Transfer606Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer606C1 then |x-((d2Transfer606S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2Transfer606S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer606S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606S1,d2Transfer606Lo,d2Transfer606Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer606C1,d2Log2Q,d2Transfer606S1,d2Transfer606Lo,d2Transfer606Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer606C1 d2Transfer606S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2Transfer606C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2Transfer606C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2Transfer606Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer606Arithmetic
  linarith
#print axioms d2Transfer606Arithmetic
#print axioms d2Transfer606Bound
def d2Transfer607Lo : ℚ := (d2LitsNearTransfers075.q2 (16756223) 1 (-24))
def d2Transfer607Hi : ℚ := (d2LitsNearTransfers075.q2 (8380219) 1 (-23))
def d2Transfer607Cap : ℚ := (d2LitsNearTransfers075.q2 (51336090597617681143313) 1 (-78))
def d2Transfer607C0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer607S0 : ℚ := (d2LitsNearTransfers075.q2 (-1) 1 (0))
def d2Transfer607C1 : ℚ := (d2LitsNearTransfers075.q2 (-1) 55 (-3))
def d2Transfer607S1 : ℚ := (d2LitsNearTransfers075.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer607Arithmetic : weightedUpper d2Transfer607C0 d2Log172Lo d2Log172Hi + weightedUpper d2Transfer607C1 d2Log1Lo d2Log1Hi ≤ d2Transfer607Cap := by decide +kernel
theorem d2Transfer607Bound : ∀ x ∈ Set.Icc ((d2Transfer607Lo:ℚ):ℝ) ((d2Transfer607Hi:ℚ):ℝ), ((d2Transfer607C0:ℚ):ℝ)*Real.log |x-((d2Transfer607S0:ℚ):ℝ)| + ((d2Transfer607C1:ℚ):ℝ)*Real.log |x-((d2Transfer607S1:ℚ):ℝ)| ≤ ((d2Transfer607Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer607S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607S0,d2Transfer607Lo,d2Transfer607Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer607C0 then |x-((d2Transfer607S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2Transfer607S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer607S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607S0,d2Transfer607Lo,d2Transfer607Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607C0,d2Log172Q,d2Transfer607S0,d2Transfer607Lo,d2Transfer607Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer607C0 d2Transfer607S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2Transfer607S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607S1,d2Transfer607Lo,d2Transfer607Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer607C1 then |x-((d2Transfer607S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2Transfer607S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer607S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607S1,d2Transfer607Lo,d2Transfer607Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers075.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer607C1,d2Log1Q,d2Transfer607S1,d2Transfer607Lo,d2Transfer607Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer607C1 d2Transfer607S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2Transfer607C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2Transfer607C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2Transfer607Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer607Arithmetic
  linarith
#print axioms d2Transfer607Arithmetic
#print axioms d2Transfer607Bound
end CatalanMeasure.GenD.Signed.Data.Cells

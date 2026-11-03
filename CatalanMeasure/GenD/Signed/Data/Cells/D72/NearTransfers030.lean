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
namespace d2LitsNearTransfers030
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers030
open D72.LogTransfer
def d2Transfer240Lo : ℚ := (d2LitsNearTransfers030.q2 (82040433) 1 (-27))
def d2Transfer240Hi : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer240Cap : ℚ := (d2LitsNearTransfers030.q2 (18094112763952243746169) 1 (-80))
def d2Transfer240C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (-5))
def d2Transfer240S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer240Arithmetic : weightedUpper d2Transfer240C0 d2Log129Lo d2Log129Hi ≤ d2Transfer240Cap := by decide +kernel
theorem d2Transfer240Bound : ∀ x ∈ Set.Icc ((d2Transfer240Lo:ℚ):ℝ) ((d2Transfer240Hi:ℚ):ℝ), ((d2Transfer240C0:ℚ):ℝ)*Real.log |x-((d2Transfer240S0:ℚ):ℝ)| ≤ ((d2Transfer240Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer240S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer240S0,d2Transfer240Lo,d2Transfer240Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer240C0 then |x-((d2Transfer240S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer240S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer240S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer240S0,d2Transfer240Lo,d2Transfer240Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer240C0,d2Log129Q,d2Transfer240S0,d2Transfer240Lo,d2Transfer240Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer240C0 d2Transfer240S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2Transfer240C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2Transfer240Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer240Arithmetic
  linarith
#print axioms d2Transfer240Arithmetic
#print axioms d2Transfer240Bound
def d2Transfer241Lo : ℚ := (d2LitsNearTransfers030.q2 (82040433) 1 (-27))
def d2Transfer241Hi : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer241Cap : ℚ := (d2LitsNearTransfers030.q2 (34458950086243751110009) 1 (-80))
def d2Transfer241C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 11 (-5))
def d2Transfer241S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
def d2Transfer241C1 : ℚ := (d2LitsNearTransfers030.q2 (-5) 11 (-4))
def d2Transfer241S1 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer241Arithmetic : weightedUpper d2Transfer241C0 d2Log129Lo d2Log129Hi + weightedUpper d2Transfer241C1 d2Log45Lo d2Log45Hi ≤ d2Transfer241Cap := by decide +kernel
theorem d2Transfer241Bound : ∀ x ∈ Set.Icc ((d2Transfer241Lo:ℚ):ℝ) ((d2Transfer241Hi:ℚ):ℝ), ((d2Transfer241C0:ℚ):ℝ)*Real.log |x-((d2Transfer241S0:ℚ):ℝ)| + ((d2Transfer241C1:ℚ):ℝ)*Real.log |x-((d2Transfer241S1:ℚ):ℝ)| ≤ ((d2Transfer241Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer241S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241S0,d2Transfer241Lo,d2Transfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer241C0 then |x-((d2Transfer241S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2Transfer241S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer241S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241S0,d2Transfer241Lo,d2Transfer241Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241C0,d2Log129Q,d2Transfer241S0,d2Transfer241Lo,d2Transfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer241C0 d2Transfer241S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2Transfer241S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241S1,d2Transfer241Lo,d2Transfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer241C1 then |x-((d2Transfer241S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2Transfer241S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer241S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241S1,d2Transfer241Lo,d2Transfer241Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer241C1,d2Log45Q,d2Transfer241S1,d2Transfer241Lo,d2Transfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer241C1 d2Transfer241S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2Transfer241C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2Transfer241C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2Transfer241Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer241Arithmetic
  linarith
#print axioms d2Transfer241Arithmetic
#print axioms d2Transfer241Bound
def d2Transfer242Lo : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer242Hi : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer242Cap : ℚ := (d2LitsNearTransfers030.q2 (418973194549188197207) 1 (-78))
def d2Transfer242C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 25 (-4))
def d2Transfer242S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer242Arithmetic : weightedUpper d2Transfer242C0 d2Log130Lo d2Log130Hi ≤ d2Transfer242Cap := by decide +kernel
theorem d2Transfer242Bound : ∀ x ∈ Set.Icc ((d2Transfer242Lo:ℚ):ℝ) ((d2Transfer242Hi:ℚ):ℝ), ((d2Transfer242C0:ℚ):ℝ)*Real.log |x-((d2Transfer242S0:ℚ):ℝ)| ≤ ((d2Transfer242Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer242S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer242S0,d2Transfer242Lo,d2Transfer242Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer242C0 then |x-((d2Transfer242S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2Transfer242S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer242S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer242S0,d2Transfer242Lo,d2Transfer242Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer242C0,d2Log130Q,d2Transfer242S0,d2Transfer242Lo,d2Transfer242Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer242C0 d2Transfer242S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have har : (((weightedUpper d2Transfer242C0 d2Log130Lo d2Log130Hi:ℚ):ℝ)) ≤ ((d2Transfer242Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer242Arithmetic
  linarith
#print axioms d2Transfer242Arithmetic
#print axioms d2Transfer242Bound
def d2Transfer243Lo : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer243Hi : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer243Cap : ℚ := (d2LitsNearTransfers030.q2 (731548236708122032983) 1 (-78))
def d2Transfer243C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 275 (-4))
def d2Transfer243S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
def d2Transfer243C1 : ℚ := (d2LitsNearTransfers030.q2 (-1) 55 (-3))
def d2Transfer243S1 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer243Arithmetic : weightedUpper d2Transfer243C0 d2Log130Lo d2Log130Hi + weightedUpper d2Transfer243C1 d2Log44Lo d2Log44Hi ≤ d2Transfer243Cap := by decide +kernel
theorem d2Transfer243Bound : ∀ x ∈ Set.Icc ((d2Transfer243Lo:ℚ):ℝ) ((d2Transfer243Hi:ℚ):ℝ), ((d2Transfer243C0:ℚ):ℝ)*Real.log |x-((d2Transfer243S0:ℚ):ℝ)| + ((d2Transfer243C1:ℚ):ℝ)*Real.log |x-((d2Transfer243S1:ℚ):ℝ)| ≤ ((d2Transfer243Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer243S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243S0,d2Transfer243Lo,d2Transfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer243C0 then |x-((d2Transfer243S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2Transfer243S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer243S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243S0,d2Transfer243Lo,d2Transfer243Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243C0,d2Log130Q,d2Transfer243S0,d2Transfer243Lo,d2Transfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer243C0 d2Transfer243S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have hn1 : x-((d2Transfer243S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243S1,d2Transfer243Lo,d2Transfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer243C1 then |x-((d2Transfer243S1:ℚ):ℝ)| ≤ ((d2Log44Q:ℚ):ℝ) else ((d2Log44Q:ℚ):ℝ) ≤ |x-((d2Transfer243S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer243S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243S1,d2Transfer243Lo,d2Transfer243Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer243C1,d2Log44Q,d2Transfer243S1,d2Transfer243Lo,d2Transfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer243C1 d2Transfer243S1 d2Log44Q d2Log44Lo d2Log44Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log44Bounds
  have har : (((weightedUpper d2Transfer243C0 d2Log130Lo d2Log130Hi:ℚ):ℝ) + ((weightedUpper d2Transfer243C1 d2Log44Lo d2Log44Hi:ℚ):ℝ)) ≤ ((d2Transfer243Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer243Arithmetic
  linarith
#print axioms d2Transfer243Arithmetic
#print axioms d2Transfer243Bound
def d2Transfer244Lo : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer244Hi : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer244Cap : ℚ := (d2LitsNearTransfers030.q2 (4537313759313862163287) 1 (-78))
def d2Transfer244C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (-5))
def d2Transfer244S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer244Arithmetic : weightedUpper d2Transfer244C0 d2Log130Lo d2Log130Hi ≤ d2Transfer244Cap := by decide +kernel
theorem d2Transfer244Bound : ∀ x ∈ Set.Icc ((d2Transfer244Lo:ℚ):ℝ) ((d2Transfer244Hi:ℚ):ℝ), ((d2Transfer244C0:ℚ):ℝ)*Real.log |x-((d2Transfer244S0:ℚ):ℝ)| ≤ ((d2Transfer244Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer244S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer244S0,d2Transfer244Lo,d2Transfer244Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer244C0 then |x-((d2Transfer244S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2Transfer244S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer244S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer244S0,d2Transfer244Lo,d2Transfer244Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer244C0,d2Log130Q,d2Transfer244S0,d2Transfer244Lo,d2Transfer244Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer244C0 d2Transfer244S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have har : (((weightedUpper d2Transfer244C0 d2Log130Lo d2Log130Hi:ℚ):ℝ)) ≤ ((d2Transfer244Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer244Arithmetic
  linarith
#print axioms d2Transfer244Arithmetic
#print axioms d2Transfer244Bound
def d2Transfer245Lo : ℚ := (d2LitsNearTransfers030.q2 (329839453) 1 (-29))
def d2Transfer245Hi : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer245Cap : ℚ := (d2LitsNearTransfers030.q2 (8628523089886739004247) 1 (-78))
def d2Transfer245C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 11 (-5))
def d2Transfer245S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
def d2Transfer245C1 : ℚ := (d2LitsNearTransfers030.q2 (-5) 11 (-4))
def d2Transfer245S1 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer245Arithmetic : weightedUpper d2Transfer245C0 d2Log130Lo d2Log130Hi + weightedUpper d2Transfer245C1 d2Log44Lo d2Log44Hi ≤ d2Transfer245Cap := by decide +kernel
theorem d2Transfer245Bound : ∀ x ∈ Set.Icc ((d2Transfer245Lo:ℚ):ℝ) ((d2Transfer245Hi:ℚ):ℝ), ((d2Transfer245C0:ℚ):ℝ)*Real.log |x-((d2Transfer245S0:ℚ):ℝ)| + ((d2Transfer245C1:ℚ):ℝ)*Real.log |x-((d2Transfer245S1:ℚ):ℝ)| ≤ ((d2Transfer245Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer245S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245S0,d2Transfer245Lo,d2Transfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer245C0 then |x-((d2Transfer245S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2Transfer245S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer245S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245S0,d2Transfer245Lo,d2Transfer245Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245C0,d2Log130Q,d2Transfer245S0,d2Transfer245Lo,d2Transfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer245C0 d2Transfer245S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have hn1 : x-((d2Transfer245S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245S1,d2Transfer245Lo,d2Transfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer245C1 then |x-((d2Transfer245S1:ℚ):ℝ)| ≤ ((d2Log44Q:ℚ):ℝ) else ((d2Log44Q:ℚ):ℝ) ≤ |x-((d2Transfer245S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer245S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245S1,d2Transfer245Lo,d2Transfer245Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer245C1,d2Log44Q,d2Transfer245S1,d2Transfer245Lo,d2Transfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer245C1 d2Transfer245S1 d2Log44Q d2Log44Lo d2Log44Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log44Bounds
  have har : (((weightedUpper d2Transfer245C0 d2Log130Lo d2Log130Hi:ℚ):ℝ) + ((weightedUpper d2Transfer245C1 d2Log44Lo d2Log44Hi:ℚ):ℝ)) ≤ ((d2Transfer245Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer245Arithmetic
  linarith
#print axioms d2Transfer245Arithmetic
#print axioms d2Transfer245Bound
def d2Transfer246Lo : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer246Hi : ℚ := (d2LitsNearTransfers030.q2 (165758587) 1 (-28))
def d2Transfer246Cap : ℚ := (d2LitsNearTransfers030.q2 (1819221899745516347231) 1 (-80))
def d2Transfer246C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 25 (-4))
def d2Transfer246S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer246Arithmetic : weightedUpper d2Transfer246C0 d2Log131Lo d2Log131Hi ≤ d2Transfer246Cap := by decide +kernel
theorem d2Transfer246Bound : ∀ x ∈ Set.Icc ((d2Transfer246Lo:ℚ):ℝ) ((d2Transfer246Hi:ℚ):ℝ), ((d2Transfer246C0:ℚ):ℝ)*Real.log |x-((d2Transfer246S0:ℚ):ℝ)| ≤ ((d2Transfer246Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer246S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer246S0,d2Transfer246Lo,d2Transfer246Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer246C0 then |x-((d2Transfer246S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer246S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer246S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer246S0,d2Transfer246Lo,d2Transfer246Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer246C0,d2Log131Q,d2Transfer246S0,d2Transfer246Lo,d2Transfer246Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer246C0 d2Transfer246S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2Transfer246C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2Transfer246Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer246Arithmetic
  linarith
#print axioms d2Transfer246Arithmetic
#print axioms d2Transfer246Bound
def d2Transfer247Lo : ℚ := (d2LitsNearTransfers030.q2 (661356627) 1 (-30))
def d2Transfer247Hi : ℚ := (d2LitsNearTransfers030.q2 (165758587) 1 (-28))
def d2Transfer247Cap : ℚ := (d2LitsNearTransfers030.q2 (3069522068381251690335) 1 (-80))
def d2Transfer247C0 : ℚ := (d2LitsNearTransfers030.q2 (1) 275 (-4))
def d2Transfer247S0 : ℚ := (d2LitsNearTransfers030.q2 (-1) 1 (0))
def d2Transfer247C1 : ℚ := (d2LitsNearTransfers030.q2 (-1) 55 (-3))
def d2Transfer247S1 : ℚ := (d2LitsNearTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer247Arithmetic : weightedUpper d2Transfer247C0 d2Log131Lo d2Log131Hi + weightedUpper d2Transfer247C1 d2Log43Lo d2Log43Hi ≤ d2Transfer247Cap := by decide +kernel
theorem d2Transfer247Bound : ∀ x ∈ Set.Icc ((d2Transfer247Lo:ℚ):ℝ) ((d2Transfer247Hi:ℚ):ℝ), ((d2Transfer247C0:ℚ):ℝ)*Real.log |x-((d2Transfer247S0:ℚ):ℝ)| + ((d2Transfer247C1:ℚ):ℝ)*Real.log |x-((d2Transfer247S1:ℚ):ℝ)| ≤ ((d2Transfer247Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer247S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247S0,d2Transfer247Lo,d2Transfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer247C0 then |x-((d2Transfer247S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer247S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer247S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247S0,d2Transfer247Lo,d2Transfer247Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247C0,d2Log131Q,d2Transfer247S0,d2Transfer247Lo,d2Transfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer247C0 d2Transfer247S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2Transfer247S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247S1,d2Transfer247Lo,d2Transfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer247C1 then |x-((d2Transfer247S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2Transfer247S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer247S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247S1,d2Transfer247Lo,d2Transfer247Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers030.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer247C1,d2Log43Q,d2Transfer247S1,d2Transfer247Lo,d2Transfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer247C1 d2Transfer247S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2Transfer247C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2Transfer247C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2Transfer247Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer247Arithmetic
  linarith
#print axioms d2Transfer247Arithmetic
#print axioms d2Transfer247Bound
end CatalanMeasure.GenD.Signed.Data.Cells

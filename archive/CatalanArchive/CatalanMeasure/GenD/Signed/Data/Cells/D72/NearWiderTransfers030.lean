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
namespace d2LitsNearWiderTransfers030
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers030
open D72.LogTransfer
def d2WiderTransfer240Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (65347171) 1 (-26))
def d2WiderTransfer240Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer240Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (53889492381725054634629) 1 (-78))
def d2WiderTransfer240C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (-5))
def d2WiderTransfer240S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer240Arithmetic : weightedUpper d2WiderTransfer240C0 d2Log172Lo d2Log172Hi ≤ d2WiderTransfer240Cap := by decide +kernel
theorem d2WiderTransfer240Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer240Lo:ℚ):ℝ) ((d2WiderTransfer240Hi:ℚ):ℝ), ((d2WiderTransfer240C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer240S0:ℚ):ℝ)| ≤ ((d2WiderTransfer240Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer240S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer240S0,d2WiderTransfer240Lo,d2WiderTransfer240Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer240C0 then |x-((d2WiderTransfer240S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer240S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer240S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer240S0,d2WiderTransfer240Lo,d2WiderTransfer240Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer240C0,d2Log172Q,d2WiderTransfer240S0,d2WiderTransfer240Lo,d2WiderTransfer240Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer240C0 d2WiderTransfer240S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2WiderTransfer240C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer240Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer240Arithmetic
  linarith
#print axioms d2WiderTransfer240Arithmetic
#print axioms d2WiderTransfer240Bound
def d2WiderTransfer241Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (65347171) 1 (-26))
def d2WiderTransfer241Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer241Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (57980701712297931475589) 1 (-78))
def d2WiderTransfer241C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 11 (-5))
def d2WiderTransfer241S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
def d2WiderTransfer241C1 : ℚ := (d2LitsNearWiderTransfers030.q2 (-5) 11 (-4))
def d2WiderTransfer241S1 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer241Arithmetic : weightedUpper d2WiderTransfer241C0 d2Log172Lo d2Log172Hi + weightedUpper d2WiderTransfer241C1 d2Log2Lo d2Log2Hi ≤ d2WiderTransfer241Cap := by decide +kernel
theorem d2WiderTransfer241Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer241Lo:ℚ):ℝ) ((d2WiderTransfer241Hi:ℚ):ℝ), ((d2WiderTransfer241C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer241S0:ℚ):ℝ)| + ((d2WiderTransfer241C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer241S1:ℚ):ℝ)| ≤ ((d2WiderTransfer241Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer241S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241S0,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer241C0 then |x-((d2WiderTransfer241S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer241S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer241S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241S0,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241C0,d2Log172Q,d2WiderTransfer241S0,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer241C0 d2WiderTransfer241S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2WiderTransfer241S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241S1,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer241C1 then |x-((d2WiderTransfer241S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer241S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer241S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241S1,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer241C1,d2Log2Q,d2WiderTransfer241S1,d2WiderTransfer241Lo,d2WiderTransfer241Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer241C1 d2WiderTransfer241S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2WiderTransfer241C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer241C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer241Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer241Arithmetic
  linarith
#print axioms d2WiderTransfer241Arithmetic
#print axioms d2WiderTransfer241Bound
def d2WiderTransfer242Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer242Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer242Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (206782343276902498879489) 1 (-80))
def d2WiderTransfer242C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 25 (-4))
def d2WiderTransfer242S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer242Arithmetic : weightedUpper d2WiderTransfer242C0 d2Log173Lo d2Log173Hi ≤ d2WiderTransfer242Cap := by decide +kernel
theorem d2WiderTransfer242Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer242Lo:ℚ):ℝ) ((d2WiderTransfer242Hi:ℚ):ℝ), ((d2WiderTransfer242C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer242S0:ℚ):ℝ)| ≤ ((d2WiderTransfer242Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer242S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer242S0,d2WiderTransfer242Lo,d2WiderTransfer242Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer242C0 then |x-((d2WiderTransfer242S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer242S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer242S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer242S0,d2WiderTransfer242Lo,d2WiderTransfer242Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer242C0,d2Log173Q,d2WiderTransfer242S0,d2WiderTransfer242Lo,d2WiderTransfer242Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer242C0 d2WiderTransfer242S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2WiderTransfer242C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer242Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer242Arithmetic
  linarith
#print axioms d2WiderTransfer242Arithmetic
#print axioms d2WiderTransfer242Bound
def d2WiderTransfer243Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer243Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer243Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (208032643445538234222593) 1 (-80))
def d2WiderTransfer243C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 275 (-4))
def d2WiderTransfer243S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
def d2WiderTransfer243C1 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 55 (-3))
def d2WiderTransfer243S1 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer243Arithmetic : weightedUpper d2WiderTransfer243C0 d2Log173Lo d2Log173Hi + weightedUpper d2WiderTransfer243C1 d2Log1Lo d2Log1Hi ≤ d2WiderTransfer243Cap := by decide +kernel
theorem d2WiderTransfer243Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer243Lo:ℚ):ℝ) ((d2WiderTransfer243Hi:ℚ):ℝ), ((d2WiderTransfer243C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer243S0:ℚ):ℝ)| + ((d2WiderTransfer243C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer243S1:ℚ):ℝ)| ≤ ((d2WiderTransfer243Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer243S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243S0,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer243C0 then |x-((d2WiderTransfer243S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer243S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer243S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243S0,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243C0,d2Log173Q,d2WiderTransfer243S0,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer243C0 d2WiderTransfer243S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2WiderTransfer243S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243S1,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer243C1 then |x-((d2WiderTransfer243S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer243S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer243S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243S1,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer243C1,d2Log1Q,d2WiderTransfer243S1,d2WiderTransfer243Lo,d2WiderTransfer243Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer243C1 d2WiderTransfer243S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2WiderTransfer243C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer243C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer243Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer243Arithmetic
  linarith
#print axioms d2WiderTransfer243Arithmetic
#print axioms d2WiderTransfer243Bound
def d2WiderTransfer244Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer244Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer244Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (223255705535961194743809) 1 (-80))
def d2WiderTransfer244C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (-5))
def d2WiderTransfer244S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer244Arithmetic : weightedUpper d2WiderTransfer244C0 d2Log173Lo d2Log173Hi ≤ d2WiderTransfer244Cap := by decide +kernel
theorem d2WiderTransfer244Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer244Lo:ℚ):ℝ) ((d2WiderTransfer244Hi:ℚ):ℝ), ((d2WiderTransfer244C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer244S0:ℚ):ℝ)| ≤ ((d2WiderTransfer244Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer244S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer244S0,d2WiderTransfer244Lo,d2WiderTransfer244Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer244C0 then |x-((d2WiderTransfer244S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer244S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer244S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer244S0,d2WiderTransfer244Lo,d2WiderTransfer244Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer244C0,d2Log173Q,d2WiderTransfer244S0,d2WiderTransfer244Lo,d2WiderTransfer244Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer244C0 d2WiderTransfer244S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2WiderTransfer244C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer244Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer244Arithmetic
  linarith
#print axioms d2WiderTransfer244Arithmetic
#print axioms d2WiderTransfer244Bound
def d2WiderTransfer245Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (16756223) 1 (-24))
def d2WiderTransfer245Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer245Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (239620542858252702107649) 1 (-80))
def d2WiderTransfer245C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 11 (-5))
def d2WiderTransfer245S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
def d2WiderTransfer245C1 : ℚ := (d2LitsNearWiderTransfers030.q2 (-5) 11 (-4))
def d2WiderTransfer245S1 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer245Arithmetic : weightedUpper d2WiderTransfer245C0 d2Log173Lo d2Log173Hi + weightedUpper d2WiderTransfer245C1 d2Log1Lo d2Log1Hi ≤ d2WiderTransfer245Cap := by decide +kernel
theorem d2WiderTransfer245Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer245Lo:ℚ):ℝ) ((d2WiderTransfer245Hi:ℚ):ℝ), ((d2WiderTransfer245C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer245S0:ℚ):ℝ)| + ((d2WiderTransfer245C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer245S1:ℚ):ℝ)| ≤ ((d2WiderTransfer245Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer245S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245S0,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer245C0 then |x-((d2WiderTransfer245S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer245S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer245S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245S0,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245C0,d2Log173Q,d2WiderTransfer245S0,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer245C0 d2WiderTransfer245S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2WiderTransfer245S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245S1,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer245C1 then |x-((d2WiderTransfer245S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer245S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer245S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245S1,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer245C1,d2Log1Q,d2WiderTransfer245S1,d2WiderTransfer245Lo,d2WiderTransfer245Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer245C1 d2WiderTransfer245S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2WiderTransfer245C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer245C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer245Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer245Arithmetic
  linarith
#print axioms d2WiderTransfer245Arithmetic
#print axioms d2WiderTransfer245Bound
def d2WiderTransfer246Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer246Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (999) 125 (-3))
def d2WiderTransfer246Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (206783948238830734700547) 1 (-80))
def d2WiderTransfer246C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 25 (-4))
def d2WiderTransfer246S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer246Arithmetic : weightedUpper d2WiderTransfer246C0 d2Log174Lo d2Log174Hi ≤ d2WiderTransfer246Cap := by decide +kernel
theorem d2WiderTransfer246Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer246Lo:ℚ):ℝ) ((d2WiderTransfer246Hi:ℚ):ℝ), ((d2WiderTransfer246C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer246S0:ℚ):ℝ)| ≤ ((d2WiderTransfer246Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer246S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer246S0,d2WiderTransfer246Lo,d2WiderTransfer246Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer246C0 then |x-((d2WiderTransfer246S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer246S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer246S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer246S0,d2WiderTransfer246Lo,d2WiderTransfer246Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer246C0,d2Log174Q,d2WiderTransfer246S0,d2WiderTransfer246Lo,d2WiderTransfer246Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer246C0 d2WiderTransfer246S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2WiderTransfer246C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer246Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer246Arithmetic
  linarith
#print axioms d2WiderTransfer246Arithmetic
#print axioms d2WiderTransfer246Bound
def d2WiderTransfer247Lo : ℚ := (d2LitsNearWiderTransfers030.q2 (8380219) 1 (-23))
def d2WiderTransfer247Hi : ℚ := (d2LitsNearWiderTransfers030.q2 (999) 125 (-3))
def d2WiderTransfer247Cap : ℚ := (d2LitsNearWiderTransfers030.q2 (208034248407466470043651) 1 (-80))
def d2WiderTransfer247C0 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 275 (-4))
def d2WiderTransfer247S0 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 1 (0))
def d2WiderTransfer247C1 : ℚ := (d2LitsNearWiderTransfers030.q2 (-1) 55 (-3))
def d2WiderTransfer247S1 : ℚ := (d2LitsNearWiderTransfers030.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer247Arithmetic : weightedUpper d2WiderTransfer247C0 d2Log174Lo d2Log174Hi + weightedUpper d2WiderTransfer247C1 d2Log0Lo d2Log0Hi ≤ d2WiderTransfer247Cap := by decide +kernel
theorem d2WiderTransfer247Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer247Lo:ℚ):ℝ) ((d2WiderTransfer247Hi:ℚ):ℝ), ((d2WiderTransfer247C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer247S0:ℚ):ℝ)| + ((d2WiderTransfer247C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer247S1:ℚ):ℝ)| ≤ ((d2WiderTransfer247Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer247S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247S0,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer247C0 then |x-((d2WiderTransfer247S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer247S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer247S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247S0,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247C0,d2Log174Q,d2WiderTransfer247S0,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer247C0 d2WiderTransfer247S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2WiderTransfer247S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247S1,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer247C1 then |x-((d2WiderTransfer247S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer247S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer247S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247S1,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers030.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer247C1,d2Log0Q,d2WiderTransfer247S1,d2WiderTransfer247Lo,d2WiderTransfer247Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer247C1 d2WiderTransfer247S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2WiderTransfer247C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer247C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer247Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer247Arithmetic
  linarith
#print axioms d2WiderTransfer247Arithmetic
#print axioms d2WiderTransfer247Bound
end CatalanMeasure.GenD.Signed.Data.Cells

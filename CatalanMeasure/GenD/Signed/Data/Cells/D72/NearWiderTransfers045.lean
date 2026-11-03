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
namespace d2LitsNearWiderTransfers045
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers045
open D72.LogTransfer
def d2WiderTransfer360Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (688200163) 1 (-30))
def d2WiderTransfer360Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (172469471) 1 (-28))
def d2WiderTransfer360Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (8882954386193858129455) 1 (-78))
def d2WiderTransfer360C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (3) 275 (-5))
def d2WiderTransfer360S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer360C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-5) 11 (-4))
def d2WiderTransfer360S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer360Arithmetic : weightedUpper d2WiderTransfer360C0 d2Log160Lo d2Log160Hi + weightedUpper d2WiderTransfer360C1 d2Log14Lo d2Log14Hi ≤ d2WiderTransfer360Cap := by decide +kernel
theorem d2WiderTransfer360Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer360Lo:ℚ):ℝ) ((d2WiderTransfer360Hi:ℚ):ℝ), ((d2WiderTransfer360C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer360S0:ℚ):ℝ)| + ((d2WiderTransfer360C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer360S1:ℚ):ℝ)| ≤ ((d2WiderTransfer360Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer360S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360S0,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer360C0 then |x-((d2WiderTransfer360S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer360S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer360S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360S0,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360C0,d2Log160Q,d2WiderTransfer360S0,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer360C0 d2WiderTransfer360S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2WiderTransfer360S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360S1,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer360C1 then |x-((d2WiderTransfer360S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer360S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer360S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360S1,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer360C1,d2Log14Q,d2WiderTransfer360S1,d2WiderTransfer360Lo,d2WiderTransfer360Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer360C1 d2WiderTransfer360S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2WiderTransfer360C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer360C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer360Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer360Arithmetic
  linarith
#print axioms d2WiderTransfer360Arithmetic
#print axioms d2WiderTransfer360Bound
def d2WiderTransfer361Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (172469471) 1 (-28))
def d2WiderTransfer361Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer361Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (3651350408292595360187) 1 (-80))
def d2WiderTransfer361C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer361S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer361C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer361S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer361Arithmetic : weightedUpper d2WiderTransfer361C0 d2Log160Lo d2Log160Hi + weightedUpper d2WiderTransfer361C1 d2Log13Lo d2Log13Hi ≤ d2WiderTransfer361Cap := by decide +kernel
theorem d2WiderTransfer361Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer361Lo:ℚ):ℝ) ((d2WiderTransfer361Hi:ℚ):ℝ), ((d2WiderTransfer361C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer361S0:ℚ):ℝ)| + ((d2WiderTransfer361C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer361S1:ℚ):ℝ)| ≤ ((d2WiderTransfer361Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer361S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361S0,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer361C0 then |x-((d2WiderTransfer361S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer361S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer361S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361S0,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361C0,d2Log160Q,d2WiderTransfer361S0,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer361C0 d2WiderTransfer361S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2WiderTransfer361S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361S1,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer361C1 then |x-((d2WiderTransfer361S1:ℚ):ℝ)| ≤ ((d2Log13Q:ℚ):ℝ) else ((d2Log13Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer361S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer361S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361S1,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer361C1,d2Log13Q,d2WiderTransfer361S1,d2WiderTransfer361Lo,d2WiderTransfer361Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer361C1 d2WiderTransfer361S1 d2Log13Q d2Log13Lo d2Log13Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log13Bounds
  have har : (((weightedUpper d2WiderTransfer361C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer361C1 d2Log13Lo d2Log13Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer361Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer361Arithmetic
  linarith
#print axioms d2WiderTransfer361Arithmetic
#print axioms d2WiderTransfer361Bound
def d2WiderTransfer362Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (172469471) 1 (-28))
def d2WiderTransfer362Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer362Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (18983146282218882294203) 1 (-80))
def d2WiderTransfer362C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (23) 25 (-5))
def d2WiderTransfer362S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer362Arithmetic : weightedUpper d2WiderTransfer362C0 d2Log161Lo d2Log161Hi ≤ d2WiderTransfer362Cap := by decide +kernel
theorem d2WiderTransfer362Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer362Lo:ℚ):ℝ) ((d2WiderTransfer362Hi:ℚ):ℝ), ((d2WiderTransfer362C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer362S0:ℚ):ℝ)| ≤ ((d2WiderTransfer362Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer362S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer362S0,d2WiderTransfer362Lo,d2WiderTransfer362Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer362C0 then |x-((d2WiderTransfer362S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer362S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer362S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer362S0,d2WiderTransfer362Lo,d2WiderTransfer362Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer362C0,d2Log161Q,d2WiderTransfer362S0,d2WiderTransfer362Lo,d2WiderTransfer362Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer362C0 d2WiderTransfer362S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have har : (((weightedUpper d2WiderTransfer362C0 d2Log161Lo d2Log161Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer362Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer362Arithmetic
  linarith
#print axioms d2WiderTransfer362Arithmetic
#print axioms d2WiderTransfer362Bound
def d2WiderTransfer363Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (172469471) 1 (-28))
def d2WiderTransfer363Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer363Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (35834133673486152589755) 1 (-80))
def d2WiderTransfer363C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (3) 275 (-5))
def d2WiderTransfer363S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer363C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-5) 11 (-4))
def d2WiderTransfer363S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer363Arithmetic : weightedUpper d2WiderTransfer363C0 d2Log161Lo d2Log161Hi + weightedUpper d2WiderTransfer363C1 d2Log13Lo d2Log13Hi ≤ d2WiderTransfer363Cap := by decide +kernel
theorem d2WiderTransfer363Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer363Lo:ℚ):ℝ) ((d2WiderTransfer363Hi:ℚ):ℝ), ((d2WiderTransfer363C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer363S0:ℚ):ℝ)| + ((d2WiderTransfer363C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer363S1:ℚ):ℝ)| ≤ ((d2WiderTransfer363Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer363S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363S0,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer363C0 then |x-((d2WiderTransfer363S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer363S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer363S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363S0,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363C0,d2Log161Q,d2WiderTransfer363S0,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer363C0 d2WiderTransfer363S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have hn1 : x-((d2WiderTransfer363S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363S1,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer363C1 then |x-((d2WiderTransfer363S1:ℚ):ℝ)| ≤ ((d2Log13Q:ℚ):ℝ) else ((d2Log13Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer363S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer363S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363S1,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer363C1,d2Log13Q,d2WiderTransfer363S1,d2WiderTransfer363Lo,d2WiderTransfer363Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer363C1 d2WiderTransfer363S1 d2Log13Q d2Log13Lo d2Log13Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log13Bounds
  have har : (((weightedUpper d2WiderTransfer363C0 d2Log161Lo d2Log161Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer363C1 d2Log13Lo d2Log13Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer363Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer363Arithmetic
  linarith
#print axioms d2WiderTransfer363Arithmetic
#print axioms d2WiderTransfer363Bound
def d2WiderTransfer364Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer364Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (21768399) 1 (-25))
def d2WiderTransfer364Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (3956335870851972903335) 1 (-80))
def d2WiderTransfer364C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer364S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer364C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer364S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer364Arithmetic : weightedUpper d2WiderTransfer364C0 d2Log161Lo d2Log161Hi + weightedUpper d2WiderTransfer364C1 d2Log12Lo d2Log12Hi ≤ d2WiderTransfer364Cap := by decide +kernel
theorem d2WiderTransfer364Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer364Lo:ℚ):ℝ) ((d2WiderTransfer364Hi:ℚ):ℝ), ((d2WiderTransfer364C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer364S0:ℚ):ℝ)| + ((d2WiderTransfer364C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer364S1:ℚ):ℝ)| ≤ ((d2WiderTransfer364Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer364S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364S0,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer364C0 then |x-((d2WiderTransfer364S0:ℚ):ℝ)| ≤ ((d2Log161Q:ℚ):ℝ) else ((d2Log161Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer364S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer364S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364S0,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364C0,d2Log161Q,d2WiderTransfer364S0,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer364C0 d2WiderTransfer364S0 d2Log161Q d2Log161Lo d2Log161Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log161Bounds
  have hn1 : x-((d2WiderTransfer364S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364S1,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer364C1 then |x-((d2WiderTransfer364S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer364S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer364S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364S1,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer364C1,d2Log12Q,d2WiderTransfer364S1,d2WiderTransfer364Lo,d2WiderTransfer364Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer364C1 d2WiderTransfer364S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2WiderTransfer364C0 d2Log161Lo d2Log161Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer364C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer364Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer364Arithmetic
  linarith
#print axioms d2WiderTransfer364Arithmetic
#print axioms d2WiderTransfer364Bound
def d2WiderTransfer365Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer365Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (21768399) 1 (-25))
def d2WiderTransfer365Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (19288131744778259837351) 1 (-80))
def d2WiderTransfer365C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (23) 25 (-5))
def d2WiderTransfer365S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer365Arithmetic : weightedUpper d2WiderTransfer365C0 d2Log162Lo d2Log162Hi ≤ d2WiderTransfer365Cap := by decide +kernel
theorem d2WiderTransfer365Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer365Lo:ℚ):ℝ) ((d2WiderTransfer365Hi:ℚ):ℝ), ((d2WiderTransfer365C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer365S0:ℚ):ℝ)| ≤ ((d2WiderTransfer365Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer365S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer365S0,d2WiderTransfer365Lo,d2WiderTransfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer365C0 then |x-((d2WiderTransfer365S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer365S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer365S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer365S0,d2WiderTransfer365Lo,d2WiderTransfer365Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer365C0,d2Log162Q,d2WiderTransfer365S0,d2WiderTransfer365Lo,d2WiderTransfer365Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer365C0 d2WiderTransfer365S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2WiderTransfer365C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer365Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer365Arithmetic
  linarith
#print axioms d2WiderTransfer365Arithmetic
#print axioms d2WiderTransfer365Bound
def d2WiderTransfer366Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (346616663) 1 (-29))
def d2WiderTransfer366Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (21768399) 1 (-25))
def d2WiderTransfer366Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (36139119136045530132903) 1 (-80))
def d2WiderTransfer366C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (3) 275 (-5))
def d2WiderTransfer366S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer366C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-5) 11 (-4))
def d2WiderTransfer366S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer366Arithmetic : weightedUpper d2WiderTransfer366C0 d2Log162Lo d2Log162Hi + weightedUpper d2WiderTransfer366C1 d2Log12Lo d2Log12Hi ≤ d2WiderTransfer366Cap := by decide +kernel
theorem d2WiderTransfer366Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer366Lo:ℚ):ℝ) ((d2WiderTransfer366Hi:ℚ):ℝ), ((d2WiderTransfer366C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer366S0:ℚ):ℝ)| + ((d2WiderTransfer366C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer366S1:ℚ):ℝ)| ≤ ((d2WiderTransfer366Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer366S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366S0,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer366C0 then |x-((d2WiderTransfer366S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer366S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer366S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366S0,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366C0,d2Log162Q,d2WiderTransfer366S0,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer366C0 d2WiderTransfer366S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2WiderTransfer366S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366S1,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer366C1 then |x-((d2WiderTransfer366S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer366S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer366S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366S1,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer366C1,d2Log12Q,d2WiderTransfer366S1,d2WiderTransfer366Lo,d2WiderTransfer366Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer366C1 d2WiderTransfer366S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2WiderTransfer366C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer366C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer366Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer366Arithmetic
  linarith
#print axioms d2WiderTransfer366Arithmetic
#print axioms d2WiderTransfer366Bound
def d2WiderTransfer367Lo : ℚ := (d2LitsNearWiderTransfers045.q2 (21768399) 1 (-25))
def d2WiderTransfer367Hi : ℚ := (d2LitsNearWiderTransfers045.q2 (175824913) 1 (-28))
def d2WiderTransfer367Cap : ℚ := (d2LitsNearWiderTransfers045.q2 (1143626764448916994303) 1 (-78))
def d2WiderTransfer367C0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer367S0 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 1 (0))
def d2WiderTransfer367C1 : ℚ := (d2LitsNearWiderTransfers045.q2 (-1) 55 (-3))
def d2WiderTransfer367S1 : ℚ := (d2LitsNearWiderTransfers045.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer367Arithmetic : weightedUpper d2WiderTransfer367C0 d2Log162Lo d2Log162Hi + weightedUpper d2WiderTransfer367C1 d2Log11Lo d2Log11Hi ≤ d2WiderTransfer367Cap := by decide +kernel
theorem d2WiderTransfer367Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer367Lo:ℚ):ℝ) ((d2WiderTransfer367Hi:ℚ):ℝ), ((d2WiderTransfer367C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer367S0:ℚ):ℝ)| + ((d2WiderTransfer367C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer367S1:ℚ):ℝ)| ≤ ((d2WiderTransfer367Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer367S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367S0,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer367C0 then |x-((d2WiderTransfer367S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer367S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer367S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367S0,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367C0,d2Log162Q,d2WiderTransfer367S0,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer367C0 d2WiderTransfer367S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2WiderTransfer367S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367S1,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer367C1 then |x-((d2WiderTransfer367S1:ℚ):ℝ)| ≤ ((d2Log11Q:ℚ):ℝ) else ((d2Log11Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer367S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer367S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367S1,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers045.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2WiderTransfer367C1,d2Log11Q,d2WiderTransfer367S1,d2WiderTransfer367Lo,d2WiderTransfer367Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer367C1 d2WiderTransfer367S1 d2Log11Q d2Log11Lo d2Log11Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log11Bounds
  have har : (((weightedUpper d2WiderTransfer367C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer367C1 d2Log11Lo d2Log11Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer367Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer367Arithmetic
  linarith
#print axioms d2WiderTransfer367Arithmetic
#print axioms d2WiderTransfer367Bound
end CatalanMeasure.GenD.Signed.Data.Cells

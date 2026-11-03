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
namespace d2LitsNearWiderTransfers013
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers013
open D72.LogTransfer
def d2WiderTransfer104Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (654645743) 1 (-30))
def d2WiderTransfer104Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer104Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (9010455958677416298425) 1 (-79))
def d2WiderTransfer104C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (-5))
def d2WiderTransfer104S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer104Arithmetic : weightedUpper d2WiderTransfer104C0 d2Log128Lo d2Log128Hi ≤ d2WiderTransfer104Cap := by decide +kernel
theorem d2WiderTransfer104Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer104Lo:ℚ):ℝ) ((d2WiderTransfer104Hi:ℚ):ℝ), ((d2WiderTransfer104C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer104S0:ℚ):ℝ)| ≤ ((d2WiderTransfer104Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer104S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer104S0,d2WiderTransfer104Lo,d2WiderTransfer104Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer104C0 then |x-((d2WiderTransfer104S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer104S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer104S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer104S0,d2WiderTransfer104Lo,d2WiderTransfer104Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer104C0,d2Log128Q,d2WiderTransfer104S0,d2WiderTransfer104Lo,d2WiderTransfer104Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer104C0 d2WiderTransfer104S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2WiderTransfer104C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer104Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer104Arithmetic
  linarith
#print axioms d2WiderTransfer104Arithmetic
#print axioms d2WiderTransfer104Bound
def d2WiderTransfer105Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (654645743) 1 (-30))
def d2WiderTransfer105Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer105Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (17192874619823169980345) 1 (-79))
def d2WiderTransfer105C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 11 (-5))
def d2WiderTransfer105S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
def d2WiderTransfer105C1 : ℚ := (d2LitsNearWiderTransfers013.q2 (-5) 11 (-4))
def d2WiderTransfer105S1 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer105Arithmetic : weightedUpper d2WiderTransfer105C0 d2Log128Lo d2Log128Hi + weightedUpper d2WiderTransfer105C1 d2Log46Lo d2Log46Hi ≤ d2WiderTransfer105Cap := by decide +kernel
theorem d2WiderTransfer105Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer105Lo:ℚ):ℝ) ((d2WiderTransfer105Hi:ℚ):ℝ), ((d2WiderTransfer105C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer105S0:ℚ):ℝ)| + ((d2WiderTransfer105C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer105S1:ℚ):ℝ)| ≤ ((d2WiderTransfer105Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer105S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105S0,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer105C0 then |x-((d2WiderTransfer105S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer105S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer105S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105S0,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105C0,d2Log128Q,d2WiderTransfer105S0,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer105C0 d2WiderTransfer105S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2WiderTransfer105S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105S1,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer105C1 then |x-((d2WiderTransfer105S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer105S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer105S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105S1,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer105C1,d2Log46Q,d2WiderTransfer105S1,d2WiderTransfer105Lo,d2WiderTransfer105Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer105C1 d2WiderTransfer105S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2WiderTransfer105C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer105C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer105Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer105Arithmetic
  linarith
#print axioms d2WiderTransfer105Arithmetic
#print axioms d2WiderTransfer105Bound
def d2WiderTransfer106Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer106Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer106Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (1620750504893547881849) 1 (-80))
def d2WiderTransfer106C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 25 (-4))
def d2WiderTransfer106S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer106Arithmetic : weightedUpper d2WiderTransfer106C0 d2Log129Lo d2Log129Hi ≤ d2WiderTransfer106Cap := by decide +kernel
theorem d2WiderTransfer106Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer106Lo:ℚ):ℝ) ((d2WiderTransfer106Hi:ℚ):ℝ), ((d2WiderTransfer106C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer106S0:ℚ):ℝ)| ≤ ((d2WiderTransfer106Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer106S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer106S0,d2WiderTransfer106Lo,d2WiderTransfer106Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer106C0 then |x-((d2WiderTransfer106S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer106S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer106S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer106S0,d2WiderTransfer106Lo,d2WiderTransfer106Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer106C0,d2Log129Q,d2WiderTransfer106S0,d2WiderTransfer106Lo,d2WiderTransfer106Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer106C0 d2WiderTransfer106S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2WiderTransfer106C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer106Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer106Arithmetic
  linarith
#print axioms d2WiderTransfer106Arithmetic
#print axioms d2WiderTransfer106Bound
def d2WiderTransfer107Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer107Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer107Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (2871050673529283224953) 1 (-80))
def d2WiderTransfer107C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 275 (-4))
def d2WiderTransfer107S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
def d2WiderTransfer107C1 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 55 (-3))
def d2WiderTransfer107S1 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer107Arithmetic : weightedUpper d2WiderTransfer107C0 d2Log129Lo d2Log129Hi + weightedUpper d2WiderTransfer107C1 d2Log45Lo d2Log45Hi ≤ d2WiderTransfer107Cap := by decide +kernel
theorem d2WiderTransfer107Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer107Lo:ℚ):ℝ) ((d2WiderTransfer107Hi:ℚ):ℝ), ((d2WiderTransfer107C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer107S0:ℚ):ℝ)| + ((d2WiderTransfer107C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer107S1:ℚ):ℝ)| ≤ ((d2WiderTransfer107Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer107S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107S0,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer107C0 then |x-((d2WiderTransfer107S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer107S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer107S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107S0,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107C0,d2Log129Q,d2WiderTransfer107S0,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer107C0 d2WiderTransfer107S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2WiderTransfer107S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107S1,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer107C1 then |x-((d2WiderTransfer107S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer107S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer107S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107S1,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer107C1,d2Log45Q,d2WiderTransfer107S1,d2WiderTransfer107Lo,d2WiderTransfer107Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer107C1 d2WiderTransfer107S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2WiderTransfer107C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer107C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer107Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer107Arithmetic
  linarith
#print axioms d2WiderTransfer107Arithmetic
#print axioms d2WiderTransfer107Bound
def d2WiderTransfer108Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer108Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer108Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (18094112763952243746169) 1 (-80))
def d2WiderTransfer108C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (-5))
def d2WiderTransfer108S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer108Arithmetic : weightedUpper d2WiderTransfer108C0 d2Log129Lo d2Log129Hi ≤ d2WiderTransfer108Cap := by decide +kernel
theorem d2WiderTransfer108Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer108Lo:ℚ):ℝ) ((d2WiderTransfer108Hi:ℚ):ℝ), ((d2WiderTransfer108C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer108S0:ℚ):ℝ)| ≤ ((d2WiderTransfer108Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer108S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer108S0,d2WiderTransfer108Lo,d2WiderTransfer108Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer108C0 then |x-((d2WiderTransfer108S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer108S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer108S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer108S0,d2WiderTransfer108Lo,d2WiderTransfer108Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer108C0,d2Log129Q,d2WiderTransfer108S0,d2WiderTransfer108Lo,d2WiderTransfer108Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer108C0 d2WiderTransfer108S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have har : (((weightedUpper d2WiderTransfer108C0 d2Log129Lo d2Log129Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer108Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer108Arithmetic
  linarith
#print axioms d2WiderTransfer108Arithmetic
#print axioms d2WiderTransfer108Bound
def d2WiderTransfer109Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (82040433) 1 (-27))
def d2WiderTransfer109Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer109Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (34458950086243751110009) 1 (-80))
def d2WiderTransfer109C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 11 (-5))
def d2WiderTransfer109S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
def d2WiderTransfer109C1 : ℚ := (d2LitsNearWiderTransfers013.q2 (-5) 11 (-4))
def d2WiderTransfer109S1 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer109Arithmetic : weightedUpper d2WiderTransfer109C0 d2Log129Lo d2Log129Hi + weightedUpper d2WiderTransfer109C1 d2Log45Lo d2Log45Hi ≤ d2WiderTransfer109Cap := by decide +kernel
theorem d2WiderTransfer109Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer109Lo:ℚ):ℝ) ((d2WiderTransfer109Hi:ℚ):ℝ), ((d2WiderTransfer109C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer109S0:ℚ):ℝ)| + ((d2WiderTransfer109C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer109S1:ℚ):ℝ)| ≤ ((d2WiderTransfer109Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer109S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109S0,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer109C0 then |x-((d2WiderTransfer109S0:ℚ):ℝ)| ≤ ((d2Log129Q:ℚ):ℝ) else ((d2Log129Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer109S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer109S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109S0,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109C0,d2Log129Q,d2WiderTransfer109S0,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer109C0 d2WiderTransfer109S0 d2Log129Q d2Log129Lo d2Log129Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log129Bounds
  have hn1 : x-((d2WiderTransfer109S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109S1,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer109C1 then |x-((d2WiderTransfer109S1:ℚ):ℝ)| ≤ ((d2Log45Q:ℚ):ℝ) else ((d2Log45Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer109S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer109S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109S1,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer109C1,d2Log45Q,d2WiderTransfer109S1,d2WiderTransfer109Lo,d2WiderTransfer109Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer109C1 d2WiderTransfer109S1 d2Log45Q d2Log45Lo d2Log45Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log45Bounds
  have har : (((weightedUpper d2WiderTransfer109C0 d2Log129Lo d2Log129Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer109C1 d2Log45Lo d2Log45Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer109Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer109Arithmetic
  linarith
#print axioms d2WiderTransfer109Arithmetic
#print axioms d2WiderTransfer109Bound
def d2WiderTransfer110Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer110Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (661356627) 1 (-30))
def d2WiderTransfer110Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (418973194549188197207) 1 (-78))
def d2WiderTransfer110C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 25 (-4))
def d2WiderTransfer110S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer110Arithmetic : weightedUpper d2WiderTransfer110C0 d2Log130Lo d2Log130Hi ≤ d2WiderTransfer110Cap := by decide +kernel
theorem d2WiderTransfer110Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer110Lo:ℚ):ℝ) ((d2WiderTransfer110Hi:ℚ):ℝ), ((d2WiderTransfer110C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer110S0:ℚ):ℝ)| ≤ ((d2WiderTransfer110Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer110S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer110S0,d2WiderTransfer110Lo,d2WiderTransfer110Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer110C0 then |x-((d2WiderTransfer110S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer110S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer110S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer110S0,d2WiderTransfer110Lo,d2WiderTransfer110Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer110C0,d2Log130Q,d2WiderTransfer110S0,d2WiderTransfer110Lo,d2WiderTransfer110Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer110C0 d2WiderTransfer110S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have har : (((weightedUpper d2WiderTransfer110C0 d2Log130Lo d2Log130Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer110Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer110Arithmetic
  linarith
#print axioms d2WiderTransfer110Arithmetic
#print axioms d2WiderTransfer110Bound
def d2WiderTransfer111Lo : ℚ := (d2LitsNearWiderTransfers013.q2 (329839453) 1 (-29))
def d2WiderTransfer111Hi : ℚ := (d2LitsNearWiderTransfers013.q2 (661356627) 1 (-30))
def d2WiderTransfer111Cap : ℚ := (d2LitsNearWiderTransfers013.q2 (731548236708122032983) 1 (-78))
def d2WiderTransfer111C0 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 275 (-4))
def d2WiderTransfer111S0 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 1 (0))
def d2WiderTransfer111C1 : ℚ := (d2LitsNearWiderTransfers013.q2 (-1) 55 (-3))
def d2WiderTransfer111S1 : ℚ := (d2LitsNearWiderTransfers013.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer111Arithmetic : weightedUpper d2WiderTransfer111C0 d2Log130Lo d2Log130Hi + weightedUpper d2WiderTransfer111C1 d2Log44Lo d2Log44Hi ≤ d2WiderTransfer111Cap := by decide +kernel
theorem d2WiderTransfer111Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer111Lo:ℚ):ℝ) ((d2WiderTransfer111Hi:ℚ):ℝ), ((d2WiderTransfer111C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer111S0:ℚ):ℝ)| + ((d2WiderTransfer111C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer111S1:ℚ):ℝ)| ≤ ((d2WiderTransfer111Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer111S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111S0,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer111C0 then |x-((d2WiderTransfer111S0:ℚ):ℝ)| ≤ ((d2Log130Q:ℚ):ℝ) else ((d2Log130Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer111S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer111S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111S0,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111C0,d2Log130Q,d2WiderTransfer111S0,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer111C0 d2WiderTransfer111S0 d2Log130Q d2Log130Lo d2Log130Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log130Bounds
  have hn1 : x-((d2WiderTransfer111S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111S1,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer111C1 then |x-((d2WiderTransfer111S1:ℚ):ℝ)| ≤ ((d2Log44Q:ℚ):ℝ) else ((d2Log44Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer111S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer111S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111S1,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers013.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer111C1,d2Log44Q,d2WiderTransfer111S1,d2WiderTransfer111Lo,d2WiderTransfer111Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer111C1 d2WiderTransfer111S1 d2Log44Q d2Log44Lo d2Log44Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log44Bounds
  have har : (((weightedUpper d2WiderTransfer111C0 d2Log130Lo d2Log130Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer111C1 d2Log44Lo d2Log44Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer111Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer111Arithmetic
  linarith
#print axioms d2WiderTransfer111Arithmetic
#print axioms d2WiderTransfer111Bound
end CatalanMeasure.GenD.Signed.Data.Cells

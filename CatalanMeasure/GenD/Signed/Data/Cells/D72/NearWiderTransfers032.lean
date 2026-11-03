module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers032
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers032
open D72.LogTransfer
def d2WiderTransfer256Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (8304657) 1 (-26))
def d2WiderTransfer256Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer256Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (1169469059) 1 (-40))
def d2WiderTransfer256C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer256S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
def d2WiderTransfer256C1 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer256S1 : ℚ := (d2LitsNearWiderTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer256Arithmetic : weightedUpper d2WiderTransfer256C0 d2Log95Lo d2Log95Hi + weightedUpper d2WiderTransfer256C1 d2Log75Lo d2Log75Hi ≤ d2WiderTransfer256Cap := by decide +kernel
theorem d2WiderTransfer256Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer256Lo:ℚ):ℝ) ((d2WiderTransfer256Hi:ℚ):ℝ), ((d2WiderTransfer256C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer256S0:ℚ):ℝ)| + ((d2WiderTransfer256C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer256S1:ℚ):ℝ)| ≤ ((d2WiderTransfer256Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer256S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256S0,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer256C0 then |x-((d2WiderTransfer256S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer256S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer256S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256S0,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256C0,d2Log95Q,d2WiderTransfer256S0,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer256C0 d2WiderTransfer256S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2WiderTransfer256S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256S1,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer256C1 then |x-((d2WiderTransfer256S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer256S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer256S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256S1,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer256C1,d2Log75Q,d2WiderTransfer256S1,d2WiderTransfer256Lo,d2WiderTransfer256Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer256C1 d2WiderTransfer256S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2WiderTransfer256C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer256C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer256Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer256Arithmetic
  linarith
#print axioms d2WiderTransfer256Arithmetic
#print axioms d2WiderTransfer256Bound
def d2WiderTransfer257Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (8304657) 1 (-26))
def d2WiderTransfer257Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer257Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (15113656175) 1 (-40))
def d2WiderTransfer257C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (23) 25 (-5))
def d2WiderTransfer257S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer257Arithmetic : weightedUpper d2WiderTransfer257C0 d2Log99Lo d2Log99Hi ≤ d2WiderTransfer257Cap := by decide +kernel
theorem d2WiderTransfer257Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer257Lo:ℚ):ℝ) ((d2WiderTransfer257Hi:ℚ):ℝ), ((d2WiderTransfer257C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer257S0:ℚ):ℝ)| ≤ ((d2WiderTransfer257Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer257S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer257S0,d2WiderTransfer257Lo,d2WiderTransfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer257C0 then |x-((d2WiderTransfer257S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer257S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer257S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer257S0,d2WiderTransfer257Lo,d2WiderTransfer257Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer257C0,d2Log99Q,d2WiderTransfer257S0,d2WiderTransfer257Lo,d2WiderTransfer257Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer257C0 d2WiderTransfer257S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have har : (((weightedUpper d2WiderTransfer257C0 d2Log99Lo d2Log99Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer257Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer257Arithmetic
  linarith
#print axioms d2WiderTransfer257Arithmetic
#print axioms d2WiderTransfer257Bound
def d2WiderTransfer258Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (8304657) 1 (-26))
def d2WiderTransfer258Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer258Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (30439539927) 1 (-40))
def d2WiderTransfer258C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (3) 275 (-5))
def d2WiderTransfer258S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
def d2WiderTransfer258C1 : ℚ := (d2LitsNearWiderTransfers032.q2 (-5) 11 (-4))
def d2WiderTransfer258S1 : ℚ := (d2LitsNearWiderTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer258Arithmetic : weightedUpper d2WiderTransfer258C0 d2Log99Lo d2Log99Hi + weightedUpper d2WiderTransfer258C1 d2Log75Lo d2Log75Hi ≤ d2WiderTransfer258Cap := by decide +kernel
theorem d2WiderTransfer258Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer258Lo:ℚ):ℝ) ((d2WiderTransfer258Hi:ℚ):ℝ), ((d2WiderTransfer258C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer258S0:ℚ):ℝ)| + ((d2WiderTransfer258C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer258S1:ℚ):ℝ)| ≤ ((d2WiderTransfer258Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer258S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258S0,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer258C0 then |x-((d2WiderTransfer258S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer258S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer258S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258S0,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258C0,d2Log99Q,d2WiderTransfer258S0,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer258C0 d2WiderTransfer258S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2WiderTransfer258S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258S1,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer258C1 then |x-((d2WiderTransfer258S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer258S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer258S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258S1,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer258C1,d2Log75Q,d2WiderTransfer258S1,d2WiderTransfer258Lo,d2WiderTransfer258Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer258C1 d2WiderTransfer258S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2WiderTransfer258C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer258C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer258Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer258Arithmetic
  linarith
#print axioms d2WiderTransfer258Arithmetic
#print axioms d2WiderTransfer258Bound
def d2WiderTransfer259Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer259Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (3334455) 1 (-24))
def d2WiderTransfer259Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (1169469059) 1 (-40))
def d2WiderTransfer259C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer259S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
def d2WiderTransfer259C1 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer259S1 : ℚ := (d2LitsNearWiderTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer259Arithmetic : weightedUpper d2WiderTransfer259C0 d2Log99Lo d2Log99Hi + weightedUpper d2WiderTransfer259C1 d2Log68Lo d2Log68Hi ≤ d2WiderTransfer259Cap := by decide +kernel
theorem d2WiderTransfer259Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer259Lo:ℚ):ℝ) ((d2WiderTransfer259Hi:ℚ):ℝ), ((d2WiderTransfer259C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer259S0:ℚ):ℝ)| + ((d2WiderTransfer259C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer259S1:ℚ):ℝ)| ≤ ((d2WiderTransfer259Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer259S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259S0,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer259C0 then |x-((d2WiderTransfer259S0:ℚ):ℝ)| ≤ ((d2Log99Q:ℚ):ℝ) else ((d2Log99Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer259S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer259S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259S0,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259C0,d2Log99Q,d2WiderTransfer259S0,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer259C0 d2WiderTransfer259S0 d2Log99Q d2Log99Lo d2Log99Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log99Bounds
  have hn1 : x-((d2WiderTransfer259S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259S1,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer259C1 then |x-((d2WiderTransfer259S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer259S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer259S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259S1,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer259C1,d2Log68Q,d2WiderTransfer259S1,d2WiderTransfer259Lo,d2WiderTransfer259Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer259C1 d2WiderTransfer259S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2WiderTransfer259C0 d2Log99Lo d2Log99Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer259C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer259Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer259Arithmetic
  linarith
#print axioms d2WiderTransfer259Arithmetic
#print axioms d2WiderTransfer259Bound
def d2WiderTransfer260Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer260Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (3334455) 1 (-24))
def d2WiderTransfer260Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (15113656175) 1 (-40))
def d2WiderTransfer260C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (23) 25 (-5))
def d2WiderTransfer260S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer260Arithmetic : weightedUpper d2WiderTransfer260C0 d2Log106Lo d2Log106Hi ≤ d2WiderTransfer260Cap := by decide +kernel
theorem d2WiderTransfer260Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer260Lo:ℚ):ℝ) ((d2WiderTransfer260Hi:ℚ):ℝ), ((d2WiderTransfer260C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer260S0:ℚ):ℝ)| ≤ ((d2WiderTransfer260Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer260S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer260S0,d2WiderTransfer260Lo,d2WiderTransfer260Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer260C0 then |x-((d2WiderTransfer260S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer260S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer260S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer260S0,d2WiderTransfer260Lo,d2WiderTransfer260Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer260C0,d2Log106Q,d2WiderTransfer260S0,d2WiderTransfer260Lo,d2WiderTransfer260Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer260C0 d2WiderTransfer260S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2WiderTransfer260C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer260Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer260Arithmetic
  linarith
#print axioms d2WiderTransfer260Arithmetic
#print axioms d2WiderTransfer260Bound
def d2WiderTransfer261Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (4991189) 1 (-25))
def d2WiderTransfer261Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (3334455) 1 (-24))
def d2WiderTransfer261Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (30439539927) 1 (-40))
def d2WiderTransfer261C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (3) 275 (-5))
def d2WiderTransfer261S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
def d2WiderTransfer261C1 : ℚ := (d2LitsNearWiderTransfers032.q2 (-5) 11 (-4))
def d2WiderTransfer261S1 : ℚ := (d2LitsNearWiderTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer261Arithmetic : weightedUpper d2WiderTransfer261C0 d2Log106Lo d2Log106Hi + weightedUpper d2WiderTransfer261C1 d2Log68Lo d2Log68Hi ≤ d2WiderTransfer261Cap := by decide +kernel
theorem d2WiderTransfer261Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer261Lo:ℚ):ℝ) ((d2WiderTransfer261Hi:ℚ):ℝ), ((d2WiderTransfer261C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer261S0:ℚ):ℝ)| + ((d2WiderTransfer261C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer261S1:ℚ):ℝ)| ≤ ((d2WiderTransfer261Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer261S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261S0,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer261C0 then |x-((d2WiderTransfer261S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer261S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer261S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261S0,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261C0,d2Log106Q,d2WiderTransfer261S0,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer261C0 d2WiderTransfer261S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2WiderTransfer261S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261S1,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer261C1 then |x-((d2WiderTransfer261S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer261S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer261S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261S1,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer261C1,d2Log68Q,d2WiderTransfer261S1,d2WiderTransfer261Lo,d2WiderTransfer261Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer261C1 d2WiderTransfer261S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2WiderTransfer261C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer261C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer261Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer261Arithmetic
  linarith
#print axioms d2WiderTransfer261Arithmetic
#print axioms d2WiderTransfer261Bound
def d2WiderTransfer262Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (3334455) 1 (-24))
def d2WiderTransfer262Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (313261) 1 (-20))
def d2WiderTransfer262Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (1169469059) 1 (-40))
def d2WiderTransfer262C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer262S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
def d2WiderTransfer262C1 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 55 (-3))
def d2WiderTransfer262S1 : ℚ := (d2LitsNearWiderTransfers032.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer262Arithmetic : weightedUpper d2WiderTransfer262C0 d2Log106Lo d2Log106Hi + weightedUpper d2WiderTransfer262C1 d2Log61Lo d2Log61Hi ≤ d2WiderTransfer262Cap := by decide +kernel
theorem d2WiderTransfer262Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer262Lo:ℚ):ℝ) ((d2WiderTransfer262Hi:ℚ):ℝ), ((d2WiderTransfer262C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer262S0:ℚ):ℝ)| + ((d2WiderTransfer262C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer262S1:ℚ):ℝ)| ≤ ((d2WiderTransfer262Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer262S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262S0,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer262C0 then |x-((d2WiderTransfer262S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer262S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer262S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262S0,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262C0,d2Log106Q,d2WiderTransfer262S0,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer262C0 d2WiderTransfer262S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2WiderTransfer262S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262S1,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer262C1 then |x-((d2WiderTransfer262S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer262S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer262S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262S1,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer262C1,d2Log61Q,d2WiderTransfer262S1,d2WiderTransfer262Lo,d2WiderTransfer262Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer262C1 d2WiderTransfer262S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2WiderTransfer262C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer262C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer262Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer262Arithmetic
  linarith
#print axioms d2WiderTransfer262Arithmetic
#print axioms d2WiderTransfer262Bound
def d2WiderTransfer263Lo : ℚ := (d2LitsNearWiderTransfers032.q2 (3334455) 1 (-24))
def d2WiderTransfer263Hi : ℚ := (d2LitsNearWiderTransfers032.q2 (313261) 1 (-20))
def d2WiderTransfer263Cap : ℚ := (d2LitsNearWiderTransfers032.q2 (15113656175) 1 (-40))
def d2WiderTransfer263C0 : ℚ := (d2LitsNearWiderTransfers032.q2 (23) 25 (-5))
def d2WiderTransfer263S0 : ℚ := (d2LitsNearWiderTransfers032.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer263Arithmetic : weightedUpper d2WiderTransfer263C0 d2Log113Lo d2Log113Hi ≤ d2WiderTransfer263Cap := by decide +kernel
theorem d2WiderTransfer263Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer263Lo:ℚ):ℝ) ((d2WiderTransfer263Hi:ℚ):ℝ), ((d2WiderTransfer263C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer263S0:ℚ):ℝ)| ≤ ((d2WiderTransfer263Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer263S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer263S0,d2WiderTransfer263Lo,d2WiderTransfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer263C0 then |x-((d2WiderTransfer263S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer263S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer263S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer263S0,d2WiderTransfer263Lo,d2WiderTransfer263Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers032.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2WiderTransfer263C0,d2Log113Q,d2WiderTransfer263S0,d2WiderTransfer263Lo,d2WiderTransfer263Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer263C0 d2WiderTransfer263S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2WiderTransfer263C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer263Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer263Arithmetic
  linarith
#print axioms d2WiderTransfer263Arithmetic
#print axioms d2WiderTransfer263Bound
end CatalanMeasure.GenD.Signed.Data.Cells

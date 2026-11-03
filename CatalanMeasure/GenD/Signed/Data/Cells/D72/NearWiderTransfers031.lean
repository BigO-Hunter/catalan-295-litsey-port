module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers031
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers031
open D72.LogTransfer
def d2WiderTransfer248Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (8380219) 1 (-23))
def d2WiderTransfer248Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (999) 125 (-3))
def d2WiderTransfer248Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (223257310497889430564867) 1 (-80))
def d2WiderTransfer248C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (-5))
def d2WiderTransfer248S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer248Arithmetic : weightedUpper d2WiderTransfer248C0 d2Log174Lo d2Log174Hi ≤ d2WiderTransfer248Cap := by decide +kernel
theorem d2WiderTransfer248Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer248Lo:ℚ):ℝ) ((d2WiderTransfer248Hi:ℚ):ℝ), ((d2WiderTransfer248C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer248S0:ℚ):ℝ)| ≤ ((d2WiderTransfer248Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer248S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer248S0,d2WiderTransfer248Lo,d2WiderTransfer248Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer248C0 then |x-((d2WiderTransfer248S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer248S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer248S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer248S0,d2WiderTransfer248Lo,d2WiderTransfer248Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer248C0,d2Log174Q,d2WiderTransfer248S0,d2WiderTransfer248Lo,d2WiderTransfer248Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer248C0 d2WiderTransfer248S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2WiderTransfer248C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer248Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer248Arithmetic
  linarith
#print axioms d2WiderTransfer248Arithmetic
#print axioms d2WiderTransfer248Bound
def d2WiderTransfer249Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (8380219) 1 (-23))
def d2WiderTransfer249Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (999) 125 (-3))
def d2WiderTransfer249Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (239622147820180937928707) 1 (-80))
def d2WiderTransfer249C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 11 (-5))
def d2WiderTransfer249S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
def d2WiderTransfer249C1 : ℚ := (d2LitsNearWiderTransfers031.q2 (-5) 11 (-4))
def d2WiderTransfer249S1 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer249Arithmetic : weightedUpper d2WiderTransfer249C0 d2Log174Lo d2Log174Hi + weightedUpper d2WiderTransfer249C1 d2Log0Lo d2Log0Hi ≤ d2WiderTransfer249Cap := by decide +kernel
theorem d2WiderTransfer249Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer249Lo:ℚ):ℝ) ((d2WiderTransfer249Hi:ℚ):ℝ), ((d2WiderTransfer249C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer249S0:ℚ):ℝ)| + ((d2WiderTransfer249C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer249S1:ℚ):ℝ)| ≤ ((d2WiderTransfer249Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer249S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249S0,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer249C0 then |x-((d2WiderTransfer249S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer249S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer249S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249S0,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249C0,d2Log174Q,d2WiderTransfer249S0,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer249C0 d2WiderTransfer249S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2WiderTransfer249S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249S1,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer249C1 then |x-((d2WiderTransfer249S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer249S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer249S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249S1,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer249C1,d2Log0Q,d2WiderTransfer249S1,d2WiderTransfer249Lo,d2WiderTransfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer249C1 d2WiderTransfer249S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2WiderTransfer249C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer249C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer249Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer249Arithmetic
  linarith
#print axioms d2WiderTransfer249Arithmetic
#print axioms d2WiderTransfer249Bound
def d2WiderTransfer250Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (98749) 15625 (-6))
def d2WiderTransfer250Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer250Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (1169469059) 1 (-40))
def d2WiderTransfer250C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 55 (-3))
def d2WiderTransfer250S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
def d2WiderTransfer250C1 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 55 (-3))
def d2WiderTransfer250S1 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer250Arithmetic : weightedUpper d2WiderTransfer250C0 d2Log87Lo d2Log87Hi + weightedUpper d2WiderTransfer250C1 d2Log86Lo d2Log86Hi ≤ d2WiderTransfer250Cap := by decide +kernel
theorem d2WiderTransfer250Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer250Lo:ℚ):ℝ) ((d2WiderTransfer250Hi:ℚ):ℝ), ((d2WiderTransfer250C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer250S0:ℚ):ℝ)| + ((d2WiderTransfer250C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer250S1:ℚ):ℝ)| ≤ ((d2WiderTransfer250Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer250S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250S0,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer250C0 then |x-((d2WiderTransfer250S0:ℚ):ℝ)| ≤ ((d2Log87Q:ℚ):ℝ) else ((d2Log87Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer250S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer250S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250S0,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250C0,d2Log87Q,d2WiderTransfer250S0,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer250C0 d2WiderTransfer250S0 d2Log87Q d2Log87Lo d2Log87Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log87Bounds
  have hn1 : x-((d2WiderTransfer250S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250S1,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer250C1 then |x-((d2WiderTransfer250S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer250S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer250S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250S1,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer250C1,d2Log86Q,d2WiderTransfer250S1,d2WiderTransfer250Lo,d2WiderTransfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer250C1 d2WiderTransfer250S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2WiderTransfer250C0 d2Log87Lo d2Log87Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer250C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer250Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer250Arithmetic
  linarith
#print axioms d2WiderTransfer250Arithmetic
#print axioms d2WiderTransfer250Bound
def d2WiderTransfer251Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (98749) 15625 (-6))
def d2WiderTransfer251Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer251Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (15113656175) 1 (-40))
def d2WiderTransfer251C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (23) 25 (-5))
def d2WiderTransfer251S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer251Arithmetic : weightedUpper d2WiderTransfer251C0 d2Log88Lo d2Log88Hi ≤ d2WiderTransfer251Cap := by decide +kernel
theorem d2WiderTransfer251Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer251Lo:ℚ):ℝ) ((d2WiderTransfer251Hi:ℚ):ℝ), ((d2WiderTransfer251C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer251S0:ℚ):ℝ)| ≤ ((d2WiderTransfer251Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer251S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer251S0,d2WiderTransfer251Lo,d2WiderTransfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer251C0 then |x-((d2WiderTransfer251S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer251S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer251S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer251S0,d2WiderTransfer251Lo,d2WiderTransfer251Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer251C0,d2Log88Q,d2WiderTransfer251S0,d2WiderTransfer251Lo,d2WiderTransfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer251C0 d2WiderTransfer251S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2WiderTransfer251C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer251Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer251Arithmetic
  linarith
#print axioms d2WiderTransfer251Arithmetic
#print axioms d2WiderTransfer251Bound
def d2WiderTransfer252Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (98749) 15625 (-6))
def d2WiderTransfer252Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer252Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (30439539927) 1 (-40))
def d2WiderTransfer252C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (3) 275 (-5))
def d2WiderTransfer252S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
def d2WiderTransfer252C1 : ℚ := (d2LitsNearWiderTransfers031.q2 (-5) 11 (-4))
def d2WiderTransfer252S1 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer252Arithmetic : weightedUpper d2WiderTransfer252C0 d2Log88Lo d2Log88Hi + weightedUpper d2WiderTransfer252C1 d2Log86Lo d2Log86Hi ≤ d2WiderTransfer252Cap := by decide +kernel
theorem d2WiderTransfer252Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer252Lo:ℚ):ℝ) ((d2WiderTransfer252Hi:ℚ):ℝ), ((d2WiderTransfer252C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer252S0:ℚ):ℝ)| + ((d2WiderTransfer252C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer252S1:ℚ):ℝ)| ≤ ((d2WiderTransfer252Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer252S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252S0,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer252C0 then |x-((d2WiderTransfer252S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer252S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer252S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252S0,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252C0,d2Log88Q,d2WiderTransfer252S0,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer252C0 d2WiderTransfer252S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2WiderTransfer252S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252S1,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer252C1 then |x-((d2WiderTransfer252S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer252S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer252S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252S1,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer252C1,d2Log86Q,d2WiderTransfer252S1,d2WiderTransfer252Lo,d2WiderTransfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer252C1 d2WiderTransfer252S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2WiderTransfer252C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer252C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer252Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer252Arithmetic
  linarith
#print axioms d2WiderTransfer252Arithmetic
#print axioms d2WiderTransfer252Bound
def d2WiderTransfer253Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer253Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (8304657) 1 (-26))
def d2WiderTransfer253Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (1169469059) 1 (-40))
def d2WiderTransfer253C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 55 (-3))
def d2WiderTransfer253S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
def d2WiderTransfer253C1 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 55 (-3))
def d2WiderTransfer253S1 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer253Arithmetic : weightedUpper d2WiderTransfer253C0 d2Log88Lo d2Log88Hi + weightedUpper d2WiderTransfer253C1 d2Log79Lo d2Log79Hi ≤ d2WiderTransfer253Cap := by decide +kernel
theorem d2WiderTransfer253Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer253Lo:ℚ):ℝ) ((d2WiderTransfer253Hi:ℚ):ℝ), ((d2WiderTransfer253C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer253S0:ℚ):ℝ)| + ((d2WiderTransfer253C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer253S1:ℚ):ℝ)| ≤ ((d2WiderTransfer253Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer253S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253S0,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer253C0 then |x-((d2WiderTransfer253S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer253S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer253S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253S0,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253C0,d2Log88Q,d2WiderTransfer253S0,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer253C0 d2WiderTransfer253S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2WiderTransfer253S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253S1,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer253C1 then |x-((d2WiderTransfer253S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer253S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer253S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253S1,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer253C1,d2Log79Q,d2WiderTransfer253S1,d2WiderTransfer253Lo,d2WiderTransfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer253C1 d2WiderTransfer253S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2WiderTransfer253C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer253C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer253Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer253Arithmetic
  linarith
#print axioms d2WiderTransfer253Arithmetic
#print axioms d2WiderTransfer253Bound
def d2WiderTransfer254Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer254Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (8304657) 1 (-26))
def d2WiderTransfer254Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (15113656175) 1 (-40))
def d2WiderTransfer254C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (23) 25 (-5))
def d2WiderTransfer254S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer254Arithmetic : weightedUpper d2WiderTransfer254C0 d2Log95Lo d2Log95Hi ≤ d2WiderTransfer254Cap := by decide +kernel
theorem d2WiderTransfer254Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer254Lo:ℚ):ℝ) ((d2WiderTransfer254Hi:ℚ):ℝ), ((d2WiderTransfer254C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer254S0:ℚ):ℝ)| ≤ ((d2WiderTransfer254Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer254S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer254S0,d2WiderTransfer254Lo,d2WiderTransfer254Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer254C0 then |x-((d2WiderTransfer254S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer254S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer254S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer254S0,d2WiderTransfer254Lo,d2WiderTransfer254Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer254C0,d2Log95Q,d2WiderTransfer254S0,d2WiderTransfer254Lo,d2WiderTransfer254Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer254C0 d2WiderTransfer254S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have har : (((weightedUpper d2WiderTransfer254C0 d2Log95Lo d2Log95Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer254Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer254Arithmetic
  linarith
#print axioms d2WiderTransfer254Arithmetic
#print axioms d2WiderTransfer254Bound
def d2WiderTransfer255Lo : ℚ := (d2LitsNearWiderTransfers031.q2 (828367) 1 (-23))
def d2WiderTransfer255Hi : ℚ := (d2LitsNearWiderTransfers031.q2 (8304657) 1 (-26))
def d2WiderTransfer255Cap : ℚ := (d2LitsNearWiderTransfers031.q2 (30439539927) 1 (-40))
def d2WiderTransfer255C0 : ℚ := (d2LitsNearWiderTransfers031.q2 (3) 275 (-5))
def d2WiderTransfer255S0 : ℚ := (d2LitsNearWiderTransfers031.q2 (-1) 1 (0))
def d2WiderTransfer255C1 : ℚ := (d2LitsNearWiderTransfers031.q2 (-5) 11 (-4))
def d2WiderTransfer255S1 : ℚ := (d2LitsNearWiderTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer255Arithmetic : weightedUpper d2WiderTransfer255C0 d2Log95Lo d2Log95Hi + weightedUpper d2WiderTransfer255C1 d2Log79Lo d2Log79Hi ≤ d2WiderTransfer255Cap := by decide +kernel
theorem d2WiderTransfer255Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer255Lo:ℚ):ℝ) ((d2WiderTransfer255Hi:ℚ):ℝ), ((d2WiderTransfer255C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer255S0:ℚ):ℝ)| + ((d2WiderTransfer255C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer255S1:ℚ):ℝ)| ≤ ((d2WiderTransfer255Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer255S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255S0,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer255C0 then |x-((d2WiderTransfer255S0:ℚ):ℝ)| ≤ ((d2Log95Q:ℚ):ℝ) else ((d2Log95Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer255S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer255S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255S0,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255C0,d2Log95Q,d2WiderTransfer255S0,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer255C0 d2WiderTransfer255S0 d2Log95Q d2Log95Lo d2Log95Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log95Bounds
  have hn1 : x-((d2WiderTransfer255S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255S1,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer255C1 then |x-((d2WiderTransfer255S1:ℚ):ℝ)| ≤ ((d2Log79Q:ℚ):ℝ) else ((d2Log79Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer255S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer255S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255S1,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers031.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer255C1,d2Log79Q,d2WiderTransfer255S1,d2WiderTransfer255Lo,d2WiderTransfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer255C1 d2WiderTransfer255S1 d2Log79Q d2Log79Lo d2Log79Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log79Bounds
  have har : (((weightedUpper d2WiderTransfer255C0 d2Log95Lo d2Log95Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer255C1 d2Log79Lo d2Log79Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer255Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer255Arithmetic
  linarith
#print axioms d2WiderTransfer255Arithmetic
#print axioms d2WiderTransfer255Bound
end CatalanMeasure.GenD.Signed.Data.Cells

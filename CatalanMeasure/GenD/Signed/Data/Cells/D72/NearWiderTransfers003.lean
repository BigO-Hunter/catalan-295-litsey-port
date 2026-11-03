module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers003
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers003
open D72.LogTransfer
def d2WiderTransfer24Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (162403145) 1 (-28))
def d2WiderTransfer24Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (82040433) 1 (-27))
def d2WiderTransfer24Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (1479355201795402184375) 1 (-80))
def d2WiderTransfer24C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 25 (-4))
def d2WiderTransfer24S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer24Arithmetic : weightedUpper d2WiderTransfer24C0 d2Log128Lo d2Log128Hi ≤ d2WiderTransfer24Cap := by decide +kernel
theorem d2WiderTransfer24Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer24Lo:ℚ):ℝ) ((d2WiderTransfer24Hi:ℚ):ℝ), ((d2WiderTransfer24C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer24S0:ℚ):ℝ)| ≤ ((d2WiderTransfer24Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer24S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer24S0,d2WiderTransfer24Lo,d2WiderTransfer24Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer24C0 then |x-((d2WiderTransfer24S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer24S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer24S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer24S0,d2WiderTransfer24Lo,d2WiderTransfer24Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer24C0,d2Log128Q,d2WiderTransfer24S0,d2WiderTransfer24Lo,d2WiderTransfer24Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer24C0 d2WiderTransfer24S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2WiderTransfer24C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer24Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer24Arithmetic
  linarith
#print axioms d2WiderTransfer24Arithmetic
#print axioms d2WiderTransfer24Bound
def d2WiderTransfer25Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (162403145) 1 (-28))
def d2WiderTransfer25Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (82040433) 1 (-27))
def d2WiderTransfer25Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (2726998246650988934839) 1 (-80))
def d2WiderTransfer25C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 275 (-4))
def d2WiderTransfer25S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
def d2WiderTransfer25C1 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 55 (-3))
def d2WiderTransfer25S1 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer25Arithmetic : weightedUpper d2WiderTransfer25C0 d2Log128Lo d2Log128Hi + weightedUpper d2WiderTransfer25C1 d2Log46Lo d2Log46Hi ≤ d2WiderTransfer25Cap := by decide +kernel
theorem d2WiderTransfer25Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer25Lo:ℚ):ℝ) ((d2WiderTransfer25Hi:ℚ):ℝ), ((d2WiderTransfer25C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer25S0:ℚ):ℝ)| + ((d2WiderTransfer25C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer25S1:ℚ):ℝ)| ≤ ((d2WiderTransfer25Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer25S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25S0,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer25C0 then |x-((d2WiderTransfer25S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer25S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer25S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25S0,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25C0,d2Log128Q,d2WiderTransfer25S0,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer25C0 d2WiderTransfer25S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2WiderTransfer25S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25S1,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer25C1 then |x-((d2WiderTransfer25S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer25S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer25S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25S1,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer25C1,d2Log46Q,d2WiderTransfer25S1,d2WiderTransfer25Lo,d2WiderTransfer25Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer25C1 d2WiderTransfer25S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2WiderTransfer25C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer25C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer25Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer25Arithmetic
  linarith
#print axioms d2WiderTransfer25Arithmetic
#print axioms d2WiderTransfer25Bound
def d2WiderTransfer26Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (82040433) 1 (-27))
def d2WiderTransfer26Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (165758587) 1 (-28))
def d2WiderTransfer26Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (95309417102004425973) 1 (-76))
def d2WiderTransfer26C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 25 (-4))
def d2WiderTransfer26S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer26Arithmetic : weightedUpper d2WiderTransfer26C0 d2Log131Lo d2Log131Hi ≤ d2WiderTransfer26Cap := by decide +kernel
theorem d2WiderTransfer26Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer26Lo:ℚ):ℝ) ((d2WiderTransfer26Hi:ℚ):ℝ), ((d2WiderTransfer26C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer26S0:ℚ):ℝ)| ≤ ((d2WiderTransfer26Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer26S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer26S0,d2WiderTransfer26Lo,d2WiderTransfer26Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer26C0 then |x-((d2WiderTransfer26S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer26S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer26S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer26S0,d2WiderTransfer26Lo,d2WiderTransfer26Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer26C0,d2Log131Q,d2WiderTransfer26S0,d2WiderTransfer26Lo,d2WiderTransfer26Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer26C0 d2WiderTransfer26S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2WiderTransfer26C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer26Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer26Arithmetic
  linarith
#print axioms d2WiderTransfer26Arithmetic
#print axioms d2WiderTransfer26Bound
def d2WiderTransfer27Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (82040433) 1 (-27))
def d2WiderTransfer27Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (165758587) 1 (-28))
def d2WiderTransfer27Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (173287107405478597877) 1 (-76))
def d2WiderTransfer27C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 275 (-4))
def d2WiderTransfer27S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
def d2WiderTransfer27C1 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 55 (-3))
def d2WiderTransfer27S1 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer27Arithmetic : weightedUpper d2WiderTransfer27C0 d2Log131Lo d2Log131Hi + weightedUpper d2WiderTransfer27C1 d2Log43Lo d2Log43Hi ≤ d2WiderTransfer27Cap := by decide +kernel
theorem d2WiderTransfer27Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer27Lo:ℚ):ℝ) ((d2WiderTransfer27Hi:ℚ):ℝ), ((d2WiderTransfer27C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer27S0:ℚ):ℝ)| + ((d2WiderTransfer27C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer27S1:ℚ):ℝ)| ≤ ((d2WiderTransfer27Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer27S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27S0,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer27C0 then |x-((d2WiderTransfer27S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer27S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer27S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27S0,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27C0,d2Log131Q,d2WiderTransfer27S0,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer27C0 d2WiderTransfer27S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2WiderTransfer27S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27S1,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer27C1 then |x-((d2WiderTransfer27S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer27S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer27S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27S1,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer27C1,d2Log43Q,d2WiderTransfer27S1,d2WiderTransfer27Lo,d2WiderTransfer27Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer27C1 d2WiderTransfer27S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2WiderTransfer27C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer27C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer27Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer27Arithmetic
  linarith
#print axioms d2WiderTransfer27Arithmetic
#print axioms d2WiderTransfer27Bound
def d2WiderTransfer28Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (165758587) 1 (-28))
def d2WiderTransfer28Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (41859077) 1 (-26))
def d2WiderTransfer28Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (785637855296999195535) 1 (-79))
def d2WiderTransfer28C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 25 (-4))
def d2WiderTransfer28S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer28Arithmetic : weightedUpper d2WiderTransfer28C0 d2Log139Lo d2Log139Hi ≤ d2WiderTransfer28Cap := by decide +kernel
theorem d2WiderTransfer28Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer28Lo:ℚ):ℝ) ((d2WiderTransfer28Hi:ℚ):ℝ), ((d2WiderTransfer28C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer28S0:ℚ):ℝ)| ≤ ((d2WiderTransfer28Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer28S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer28S0,d2WiderTransfer28Lo,d2WiderTransfer28Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer28C0 then |x-((d2WiderTransfer28S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer28S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer28S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer28S0,d2WiderTransfer28Lo,d2WiderTransfer28Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer28C0,d2Log139Q,d2WiderTransfer28S0,d2WiderTransfer28Lo,d2WiderTransfer28Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer28C0 d2WiderTransfer28S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2WiderTransfer28C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer28Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer28Arithmetic
  linarith
#print axioms d2WiderTransfer28Arithmetic
#print axioms d2WiderTransfer28Bound
def d2WiderTransfer29Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (165758587) 1 (-28))
def d2WiderTransfer29Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (41859077) 1 (-26))
def d2WiderTransfer29Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (1409459377724792570767) 1 (-79))
def d2WiderTransfer29C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 275 (-4))
def d2WiderTransfer29S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
def d2WiderTransfer29C1 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 55 (-3))
def d2WiderTransfer29S1 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer29Arithmetic : weightedUpper d2WiderTransfer29C0 d2Log139Lo d2Log139Hi + weightedUpper d2WiderTransfer29C1 d2Log35Lo d2Log35Hi ≤ d2WiderTransfer29Cap := by decide +kernel
theorem d2WiderTransfer29Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer29Lo:ℚ):ℝ) ((d2WiderTransfer29Hi:ℚ):ℝ), ((d2WiderTransfer29C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer29S0:ℚ):ℝ)| + ((d2WiderTransfer29C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer29S1:ℚ):ℝ)| ≤ ((d2WiderTransfer29Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer29S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29S0,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer29C0 then |x-((d2WiderTransfer29S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer29S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer29S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29S0,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29C0,d2Log139Q,d2WiderTransfer29S0,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer29C0 d2WiderTransfer29S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2WiderTransfer29S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29S1,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer29C1 then |x-((d2WiderTransfer29S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer29S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer29S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29S1,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer29C1,d2Log35Q,d2WiderTransfer29S1,d2WiderTransfer29Lo,d2WiderTransfer29Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer29C1 d2WiderTransfer29S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2WiderTransfer29C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer29C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer29Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer29Arithmetic
  linarith
#print axioms d2WiderTransfer29Arithmetic
#print axioms d2WiderTransfer29Bound
def d2WiderTransfer30Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (41859077) 1 (-26))
def d2WiderTransfer30Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (21768399) 1 (-25))
def d2WiderTransfer30Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (1764383111709710676961) 1 (-80))
def d2WiderTransfer30C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 25 (-4))
def d2WiderTransfer30S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer30Arithmetic : weightedUpper d2WiderTransfer30C0 d2Log162Lo d2Log162Hi ≤ d2WiderTransfer30Cap := by decide +kernel
theorem d2WiderTransfer30Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer30Lo:ℚ):ℝ) ((d2WiderTransfer30Hi:ℚ):ℝ), ((d2WiderTransfer30C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer30S0:ℚ):ℝ)| ≤ ((d2WiderTransfer30Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer30S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer30S0,d2WiderTransfer30Lo,d2WiderTransfer30Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer30C0 then |x-((d2WiderTransfer30S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer30S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer30S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer30S0,d2WiderTransfer30Lo,d2WiderTransfer30Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer30C0,d2Log162Q,d2WiderTransfer30S0,d2WiderTransfer30Lo,d2WiderTransfer30Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer30C0 d2WiderTransfer30S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2WiderTransfer30C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer30Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer30Arithmetic
  linarith
#print axioms d2WiderTransfer30Arithmetic
#print axioms d2WiderTransfer30Bound
def d2WiderTransfer31Lo : ℚ := (d2LitsNearWiderTransfers003.q2 (41859077) 1 (-26))
def d2WiderTransfer31Hi : ℚ := (d2LitsNearWiderTransfers003.q2 (21768399) 1 (-25))
def d2WiderTransfer31Cap : ℚ := (d2LitsNearWiderTransfers003.q2 (3012026156565297427425) 1 (-80))
def d2WiderTransfer31C0 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 275 (-4))
def d2WiderTransfer31S0 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 1 (0))
def d2WiderTransfer31C1 : ℚ := (d2LitsNearWiderTransfers003.q2 (-1) 55 (-3))
def d2WiderTransfer31S1 : ℚ := (d2LitsNearWiderTransfers003.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer31Arithmetic : weightedUpper d2WiderTransfer31C0 d2Log162Lo d2Log162Hi + weightedUpper d2WiderTransfer31C1 d2Log12Lo d2Log12Hi ≤ d2WiderTransfer31Cap := by decide +kernel
theorem d2WiderTransfer31Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer31Lo:ℚ):ℝ) ((d2WiderTransfer31Hi:ℚ):ℝ), ((d2WiderTransfer31C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer31S0:ℚ):ℝ)| + ((d2WiderTransfer31C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer31S1:ℚ):ℝ)| ≤ ((d2WiderTransfer31Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer31S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31S0,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer31C0 then |x-((d2WiderTransfer31S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer31S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer31S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31S0,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31C0,d2Log162Q,d2WiderTransfer31S0,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer31C0 d2WiderTransfer31S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2WiderTransfer31S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31S1,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer31C1 then |x-((d2WiderTransfer31S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer31S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer31S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31S1,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers003.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2WiderTransfer31C1,d2Log12Q,d2WiderTransfer31S1,d2WiderTransfer31Lo,d2WiderTransfer31Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer31C1 d2WiderTransfer31S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2WiderTransfer31C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer31C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer31Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer31Arithmetic
  linarith
#print axioms d2WiderTransfer31Arithmetic
#print axioms d2WiderTransfer31Bound
end CatalanMeasure.GenD.Signed.Data.Cells

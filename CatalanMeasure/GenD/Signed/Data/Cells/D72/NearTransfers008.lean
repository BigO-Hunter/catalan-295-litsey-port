module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers008
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers008
open D72.LogTransfer
def d2Transfer64Lo : ℚ := (d2LitsNearTransfers008.q2 (162403145) 1 (-28))
def d2Transfer64Hi : ℚ := (d2LitsNearTransfers008.q2 (82040433) 1 (-27))
def d2Transfer64Cap : ℚ := (d2LitsNearTransfers008.q2 (1479355201795402184375) 1 (-80))
def d2Transfer64C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 25 (-4))
def d2Transfer64S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer64Arithmetic : weightedUpper d2Transfer64C0 d2Log128Lo d2Log128Hi ≤ d2Transfer64Cap := by decide +kernel
theorem d2Transfer64Bound : ∀ x ∈ Set.Icc ((d2Transfer64Lo:ℚ):ℝ) ((d2Transfer64Hi:ℚ):ℝ), ((d2Transfer64C0:ℚ):ℝ)*Real.log |x-((d2Transfer64S0:ℚ):ℝ)| ≤ ((d2Transfer64Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer64S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer64S0,d2Transfer64Lo,d2Transfer64Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer64C0 then |x-((d2Transfer64S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer64S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer64S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer64S0,d2Transfer64Lo,d2Transfer64Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer64C0,d2Log128Q,d2Transfer64S0,d2Transfer64Lo,d2Transfer64Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer64C0 d2Transfer64S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2Transfer64C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2Transfer64Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer64Arithmetic
  linarith
#print axioms d2Transfer64Arithmetic
#print axioms d2Transfer64Bound
def d2Transfer65Lo : ℚ := (d2LitsNearTransfers008.q2 (162403145) 1 (-28))
def d2Transfer65Hi : ℚ := (d2LitsNearTransfers008.q2 (82040433) 1 (-27))
def d2Transfer65Cap : ℚ := (d2LitsNearTransfers008.q2 (2726998246650988934839) 1 (-80))
def d2Transfer65C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 275 (-4))
def d2Transfer65S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
def d2Transfer65C1 : ℚ := (d2LitsNearTransfers008.q2 (-1) 55 (-3))
def d2Transfer65S1 : ℚ := (d2LitsNearTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer65Arithmetic : weightedUpper d2Transfer65C0 d2Log128Lo d2Log128Hi + weightedUpper d2Transfer65C1 d2Log46Lo d2Log46Hi ≤ d2Transfer65Cap := by decide +kernel
theorem d2Transfer65Bound : ∀ x ∈ Set.Icc ((d2Transfer65Lo:ℚ):ℝ) ((d2Transfer65Hi:ℚ):ℝ), ((d2Transfer65C0:ℚ):ℝ)*Real.log |x-((d2Transfer65S0:ℚ):ℝ)| + ((d2Transfer65C1:ℚ):ℝ)*Real.log |x-((d2Transfer65S1:ℚ):ℝ)| ≤ ((d2Transfer65Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer65S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65S0,d2Transfer65Lo,d2Transfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer65C0 then |x-((d2Transfer65S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer65S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer65S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65S0,d2Transfer65Lo,d2Transfer65Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65C0,d2Log128Q,d2Transfer65S0,d2Transfer65Lo,d2Transfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer65C0 d2Transfer65S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2Transfer65S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65S1,d2Transfer65Lo,d2Transfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer65C1 then |x-((d2Transfer65S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2Transfer65S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer65S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65S1,d2Transfer65Lo,d2Transfer65Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer65C1,d2Log46Q,d2Transfer65S1,d2Transfer65Lo,d2Transfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer65C1 d2Transfer65S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2Transfer65C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2Transfer65C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2Transfer65Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer65Arithmetic
  linarith
#print axioms d2Transfer65Arithmetic
#print axioms d2Transfer65Bound
def d2Transfer66Lo : ℚ := (d2LitsNearTransfers008.q2 (82040433) 1 (-27))
def d2Transfer66Hi : ℚ := (d2LitsNearTransfers008.q2 (165758587) 1 (-28))
def d2Transfer66Cap : ℚ := (d2LitsNearTransfers008.q2 (95309417102004425973) 1 (-76))
def d2Transfer66C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 25 (-4))
def d2Transfer66S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer66Arithmetic : weightedUpper d2Transfer66C0 d2Log131Lo d2Log131Hi ≤ d2Transfer66Cap := by decide +kernel
theorem d2Transfer66Bound : ∀ x ∈ Set.Icc ((d2Transfer66Lo:ℚ):ℝ) ((d2Transfer66Hi:ℚ):ℝ), ((d2Transfer66C0:ℚ):ℝ)*Real.log |x-((d2Transfer66S0:ℚ):ℝ)| ≤ ((d2Transfer66Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer66S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer66S0,d2Transfer66Lo,d2Transfer66Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer66C0 then |x-((d2Transfer66S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer66S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer66S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer66S0,d2Transfer66Lo,d2Transfer66Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer66C0,d2Log131Q,d2Transfer66S0,d2Transfer66Lo,d2Transfer66Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer66C0 d2Transfer66S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2Transfer66C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2Transfer66Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer66Arithmetic
  linarith
#print axioms d2Transfer66Arithmetic
#print axioms d2Transfer66Bound
def d2Transfer67Lo : ℚ := (d2LitsNearTransfers008.q2 (82040433) 1 (-27))
def d2Transfer67Hi : ℚ := (d2LitsNearTransfers008.q2 (165758587) 1 (-28))
def d2Transfer67Cap : ℚ := (d2LitsNearTransfers008.q2 (173287107405478597877) 1 (-76))
def d2Transfer67C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 275 (-4))
def d2Transfer67S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
def d2Transfer67C1 : ℚ := (d2LitsNearTransfers008.q2 (-1) 55 (-3))
def d2Transfer67S1 : ℚ := (d2LitsNearTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer67Arithmetic : weightedUpper d2Transfer67C0 d2Log131Lo d2Log131Hi + weightedUpper d2Transfer67C1 d2Log43Lo d2Log43Hi ≤ d2Transfer67Cap := by decide +kernel
theorem d2Transfer67Bound : ∀ x ∈ Set.Icc ((d2Transfer67Lo:ℚ):ℝ) ((d2Transfer67Hi:ℚ):ℝ), ((d2Transfer67C0:ℚ):ℝ)*Real.log |x-((d2Transfer67S0:ℚ):ℝ)| + ((d2Transfer67C1:ℚ):ℝ)*Real.log |x-((d2Transfer67S1:ℚ):ℝ)| ≤ ((d2Transfer67Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer67S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67S0,d2Transfer67Lo,d2Transfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer67C0 then |x-((d2Transfer67S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer67S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer67S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67S0,d2Transfer67Lo,d2Transfer67Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67C0,d2Log131Q,d2Transfer67S0,d2Transfer67Lo,d2Transfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer67C0 d2Transfer67S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2Transfer67S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67S1,d2Transfer67Lo,d2Transfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer67C1 then |x-((d2Transfer67S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2Transfer67S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer67S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67S1,d2Transfer67Lo,d2Transfer67Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer67C1,d2Log43Q,d2Transfer67S1,d2Transfer67Lo,d2Transfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer67C1 d2Transfer67S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2Transfer67C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2Transfer67C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2Transfer67Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer67Arithmetic
  linarith
#print axioms d2Transfer67Arithmetic
#print axioms d2Transfer67Bound
def d2Transfer68Lo : ℚ := (d2LitsNearTransfers008.q2 (165758587) 1 (-28))
def d2Transfer68Hi : ℚ := (d2LitsNearTransfers008.q2 (41859077) 1 (-26))
def d2Transfer68Cap : ℚ := (d2LitsNearTransfers008.q2 (785637855296999195535) 1 (-79))
def d2Transfer68C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 25 (-4))
def d2Transfer68S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer68Arithmetic : weightedUpper d2Transfer68C0 d2Log139Lo d2Log139Hi ≤ d2Transfer68Cap := by decide +kernel
theorem d2Transfer68Bound : ∀ x ∈ Set.Icc ((d2Transfer68Lo:ℚ):ℝ) ((d2Transfer68Hi:ℚ):ℝ), ((d2Transfer68C0:ℚ):ℝ)*Real.log |x-((d2Transfer68S0:ℚ):ℝ)| ≤ ((d2Transfer68Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer68S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer68S0,d2Transfer68Lo,d2Transfer68Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer68C0 then |x-((d2Transfer68S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer68S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer68S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer68S0,d2Transfer68Lo,d2Transfer68Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer68C0,d2Log139Q,d2Transfer68S0,d2Transfer68Lo,d2Transfer68Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer68C0 d2Transfer68S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2Transfer68C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2Transfer68Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer68Arithmetic
  linarith
#print axioms d2Transfer68Arithmetic
#print axioms d2Transfer68Bound
def d2Transfer69Lo : ℚ := (d2LitsNearTransfers008.q2 (165758587) 1 (-28))
def d2Transfer69Hi : ℚ := (d2LitsNearTransfers008.q2 (41859077) 1 (-26))
def d2Transfer69Cap : ℚ := (d2LitsNearTransfers008.q2 (1409459377724792570767) 1 (-79))
def d2Transfer69C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 275 (-4))
def d2Transfer69S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
def d2Transfer69C1 : ℚ := (d2LitsNearTransfers008.q2 (-1) 55 (-3))
def d2Transfer69S1 : ℚ := (d2LitsNearTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer69Arithmetic : weightedUpper d2Transfer69C0 d2Log139Lo d2Log139Hi + weightedUpper d2Transfer69C1 d2Log35Lo d2Log35Hi ≤ d2Transfer69Cap := by decide +kernel
theorem d2Transfer69Bound : ∀ x ∈ Set.Icc ((d2Transfer69Lo:ℚ):ℝ) ((d2Transfer69Hi:ℚ):ℝ), ((d2Transfer69C0:ℚ):ℝ)*Real.log |x-((d2Transfer69S0:ℚ):ℝ)| + ((d2Transfer69C1:ℚ):ℝ)*Real.log |x-((d2Transfer69S1:ℚ):ℝ)| ≤ ((d2Transfer69Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer69S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69S0,d2Transfer69Lo,d2Transfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer69C0 then |x-((d2Transfer69S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer69S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer69S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69S0,d2Transfer69Lo,d2Transfer69Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69C0,d2Log139Q,d2Transfer69S0,d2Transfer69Lo,d2Transfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer69C0 d2Transfer69S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2Transfer69S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69S1,d2Transfer69Lo,d2Transfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer69C1 then |x-((d2Transfer69S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2Transfer69S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer69S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69S1,d2Transfer69Lo,d2Transfer69Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer69C1,d2Log35Q,d2Transfer69S1,d2Transfer69Lo,d2Transfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer69C1 d2Transfer69S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2Transfer69C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2Transfer69C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2Transfer69Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer69Arithmetic
  linarith
#print axioms d2Transfer69Arithmetic
#print axioms d2Transfer69Bound
def d2Transfer70Lo : ℚ := (d2LitsNearTransfers008.q2 (41859077) 1 (-26))
def d2Transfer70Hi : ℚ := (d2LitsNearTransfers008.q2 (21768399) 1 (-25))
def d2Transfer70Cap : ℚ := (d2LitsNearTransfers008.q2 (1764383111709710676961) 1 (-80))
def d2Transfer70C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 25 (-4))
def d2Transfer70S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer70Arithmetic : weightedUpper d2Transfer70C0 d2Log162Lo d2Log162Hi ≤ d2Transfer70Cap := by decide +kernel
theorem d2Transfer70Bound : ∀ x ∈ Set.Icc ((d2Transfer70Lo:ℚ):ℝ) ((d2Transfer70Hi:ℚ):ℝ), ((d2Transfer70C0:ℚ):ℝ)*Real.log |x-((d2Transfer70S0:ℚ):ℝ)| ≤ ((d2Transfer70Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer70S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer70S0,d2Transfer70Lo,d2Transfer70Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer70C0 then |x-((d2Transfer70S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer70S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer70S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer70S0,d2Transfer70Lo,d2Transfer70Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer70C0,d2Log162Q,d2Transfer70S0,d2Transfer70Lo,d2Transfer70Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer70C0 d2Transfer70S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2Transfer70C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2Transfer70Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer70Arithmetic
  linarith
#print axioms d2Transfer70Arithmetic
#print axioms d2Transfer70Bound
def d2Transfer71Lo : ℚ := (d2LitsNearTransfers008.q2 (41859077) 1 (-26))
def d2Transfer71Hi : ℚ := (d2LitsNearTransfers008.q2 (21768399) 1 (-25))
def d2Transfer71Cap : ℚ := (d2LitsNearTransfers008.q2 (3012026156565297427425) 1 (-80))
def d2Transfer71C0 : ℚ := (d2LitsNearTransfers008.q2 (1) 275 (-4))
def d2Transfer71S0 : ℚ := (d2LitsNearTransfers008.q2 (-1) 1 (0))
def d2Transfer71C1 : ℚ := (d2LitsNearTransfers008.q2 (-1) 55 (-3))
def d2Transfer71S1 : ℚ := (d2LitsNearTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer71Arithmetic : weightedUpper d2Transfer71C0 d2Log162Lo d2Log162Hi + weightedUpper d2Transfer71C1 d2Log12Lo d2Log12Hi ≤ d2Transfer71Cap := by decide +kernel
theorem d2Transfer71Bound : ∀ x ∈ Set.Icc ((d2Transfer71Lo:ℚ):ℝ) ((d2Transfer71Hi:ℚ):ℝ), ((d2Transfer71C0:ℚ):ℝ)*Real.log |x-((d2Transfer71S0:ℚ):ℝ)| + ((d2Transfer71C1:ℚ):ℝ)*Real.log |x-((d2Transfer71S1:ℚ):ℝ)| ≤ ((d2Transfer71Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer71S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71S0,d2Transfer71Lo,d2Transfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer71C0 then |x-((d2Transfer71S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer71S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer71S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71S0,d2Transfer71Lo,d2Transfer71Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71C0,d2Log162Q,d2Transfer71S0,d2Transfer71Lo,d2Transfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer71C0 d2Transfer71S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2Transfer71S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71S1,d2Transfer71Lo,d2Transfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer71C1 then |x-((d2Transfer71S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2Transfer71S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer71S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71S1,d2Transfer71Lo,d2Transfer71Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers008.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache010.q2, d2Transfer71C1,d2Log12Q,d2Transfer71S1,d2Transfer71Lo,d2Transfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer71C1 d2Transfer71S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2Transfer71C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2Transfer71C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2Transfer71Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer71Arithmetic
  linarith
#print axioms d2Transfer71Arithmetic
#print axioms d2Transfer71Bound
end CatalanMeasure.GenD.Signed.Data.Cells

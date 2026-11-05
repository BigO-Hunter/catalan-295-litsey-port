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
namespace d2LitsNearTransfers031
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers031
open D72.LogTransfer
def d2Transfer248Lo : ℚ := (d2LitsNearTransfers031.q2 (661356627) 1 (-30))
def d2Transfer248Hi : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer248Cap : ℚ := (d2LitsNearTransfers031.q2 (18292584158804212211551) 1 (-80))
def d2Transfer248C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (-5))
def d2Transfer248S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer248Arithmetic : weightedUpper d2Transfer248C0 d2Log131Lo d2Log131Hi ≤ d2Transfer248Cap := by decide +kernel
theorem d2Transfer248Bound : ∀ x ∈ Set.Icc ((d2Transfer248Lo:ℚ):ℝ) ((d2Transfer248Hi:ℚ):ℝ), ((d2Transfer248C0:ℚ):ℝ)*Real.log |x-((d2Transfer248S0:ℚ):ℝ)| ≤ ((d2Transfer248Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer248S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer248S0,d2Transfer248Lo,d2Transfer248Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer248C0 then |x-((d2Transfer248S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer248S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer248S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer248S0,d2Transfer248Lo,d2Transfer248Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer248C0,d2Log131Q,d2Transfer248S0,d2Transfer248Lo,d2Transfer248Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer248C0 d2Transfer248S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have har : (((weightedUpper d2Transfer248C0 d2Log131Lo d2Log131Hi:ℚ):ℝ)) ≤ ((d2Transfer248Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer248Arithmetic
  linarith
#print axioms d2Transfer248Arithmetic
#print axioms d2Transfer248Bound
def d2Transfer249Lo : ℚ := (d2LitsNearTransfers031.q2 (661356627) 1 (-30))
def d2Transfer249Hi : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer249Cap : ℚ := (d2LitsNearTransfers031.q2 (34657421481095719575391) 1 (-80))
def d2Transfer249C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 11 (-5))
def d2Transfer249S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
def d2Transfer249C1 : ℚ := (d2LitsNearTransfers031.q2 (-5) 11 (-4))
def d2Transfer249S1 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer249Arithmetic : weightedUpper d2Transfer249C0 d2Log131Lo d2Log131Hi + weightedUpper d2Transfer249C1 d2Log43Lo d2Log43Hi ≤ d2Transfer249Cap := by decide +kernel
theorem d2Transfer249Bound : ∀ x ∈ Set.Icc ((d2Transfer249Lo:ℚ):ℝ) ((d2Transfer249Hi:ℚ):ℝ), ((d2Transfer249C0:ℚ):ℝ)*Real.log |x-((d2Transfer249S0:ℚ):ℝ)| + ((d2Transfer249C1:ℚ):ℝ)*Real.log |x-((d2Transfer249S1:ℚ):ℝ)| ≤ ((d2Transfer249Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer249S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249S0,d2Transfer249Lo,d2Transfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer249C0 then |x-((d2Transfer249S0:ℚ):ℝ)| ≤ ((d2Log131Q:ℚ):ℝ) else ((d2Log131Q:ℚ):ℝ) ≤ |x-((d2Transfer249S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer249S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249S0,d2Transfer249Lo,d2Transfer249Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249C0,d2Log131Q,d2Transfer249S0,d2Transfer249Lo,d2Transfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer249C0 d2Transfer249S0 d2Log131Q d2Log131Lo d2Log131Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log131Bounds
  have hn1 : x-((d2Transfer249S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249S1,d2Transfer249Lo,d2Transfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer249C1 then |x-((d2Transfer249S1:ℚ):ℝ)| ≤ ((d2Log43Q:ℚ):ℝ) else ((d2Log43Q:ℚ):ℝ) ≤ |x-((d2Transfer249S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer249S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249S1,d2Transfer249Lo,d2Transfer249Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer249C1,d2Log43Q,d2Transfer249S1,d2Transfer249Lo,d2Transfer249Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer249C1 d2Transfer249S1 d2Log43Q d2Log43Lo d2Log43Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log43Bounds
  have har : (((weightedUpper d2Transfer249C0 d2Log131Lo d2Log131Hi:ℚ):ℝ) + ((weightedUpper d2Transfer249C1 d2Log43Lo d2Log43Hi:ℚ):ℝ)) ≤ ((d2Transfer249Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer249Arithmetic
  linarith
#print axioms d2Transfer249Arithmetic
#print axioms d2Transfer249Bound
def d2Transfer250Lo : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer250Hi : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer250Cap : ℚ := (d2LitsNearTransfers031.q2 (472774969983535760355) 1 (-78))
def d2Transfer250C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 25 (-4))
def d2Transfer250S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer250Arithmetic : weightedUpper d2Transfer250C0 d2Log132Lo d2Log132Hi ≤ d2Transfer250Cap := by decide +kernel
theorem d2Transfer250Bound : ∀ x ∈ Set.Icc ((d2Transfer250Lo:ℚ):ℝ) ((d2Transfer250Hi:ℚ):ℝ), ((d2Transfer250C0:ℚ):ℝ)*Real.log |x-((d2Transfer250S0:ℚ):ℝ)| ≤ ((d2Transfer250Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer250S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer250S0,d2Transfer250Lo,d2Transfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer250C0 then |x-((d2Transfer250S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2Transfer250S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer250S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer250S0,d2Transfer250Lo,d2Transfer250Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer250C0,d2Log132Q,d2Transfer250S0,d2Transfer250Lo,d2Transfer250Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer250C0 d2Transfer250S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have har : (((weightedUpper d2Transfer250C0 d2Log132Lo d2Log132Hi:ℚ):ℝ)) ≤ ((d2Transfer250Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer250Arithmetic
  linarith
#print axioms d2Transfer250Arithmetic
#print axioms d2Transfer250Bound
def d2Transfer251Lo : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer251Hi : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer251Cap : ℚ := (d2LitsNearTransfers031.q2 (785350012142469596131) 1 (-78))
def d2Transfer251C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 275 (-4))
def d2Transfer251S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
def d2Transfer251C1 : ℚ := (d2LitsNearTransfers031.q2 (-1) 55 (-3))
def d2Transfer251S1 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer251Arithmetic : weightedUpper d2Transfer251C0 d2Log132Lo d2Log132Hi + weightedUpper d2Transfer251C1 d2Log42Lo d2Log42Hi ≤ d2Transfer251Cap := by decide +kernel
theorem d2Transfer251Bound : ∀ x ∈ Set.Icc ((d2Transfer251Lo:ℚ):ℝ) ((d2Transfer251Hi:ℚ):ℝ), ((d2Transfer251C0:ℚ):ℝ)*Real.log |x-((d2Transfer251S0:ℚ):ℝ)| + ((d2Transfer251C1:ℚ):ℝ)*Real.log |x-((d2Transfer251S1:ℚ):ℝ)| ≤ ((d2Transfer251Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer251S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251S0,d2Transfer251Lo,d2Transfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer251C0 then |x-((d2Transfer251S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2Transfer251S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer251S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251S0,d2Transfer251Lo,d2Transfer251Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251C0,d2Log132Q,d2Transfer251S0,d2Transfer251Lo,d2Transfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer251C0 d2Transfer251S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have hn1 : x-((d2Transfer251S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251S1,d2Transfer251Lo,d2Transfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer251C1 then |x-((d2Transfer251S1:ℚ):ℝ)| ≤ ((d2Log42Q:ℚ):ℝ) else ((d2Log42Q:ℚ):ℝ) ≤ |x-((d2Transfer251S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer251S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251S1,d2Transfer251Lo,d2Transfer251Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer251C1,d2Log42Q,d2Transfer251S1,d2Transfer251Lo,d2Transfer251Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer251C1 d2Transfer251S1 d2Log42Q d2Log42Lo d2Log42Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log42Bounds
  have har : (((weightedUpper d2Transfer251C0 d2Log132Lo d2Log132Hi:ℚ):ℝ) + ((weightedUpper d2Transfer251C1 d2Log42Lo d2Log42Hi:ℚ):ℝ)) ≤ ((d2Transfer251Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer251Arithmetic
  linarith
#print axioms d2Transfer251Arithmetic
#print axioms d2Transfer251Bound
def d2Transfer252Lo : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer252Hi : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer252Cap : ℚ := (d2LitsNearTransfers031.q2 (4591115534748209726435) 1 (-78))
def d2Transfer252C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (-5))
def d2Transfer252S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer252Arithmetic : weightedUpper d2Transfer252C0 d2Log132Lo d2Log132Hi ≤ d2Transfer252Cap := by decide +kernel
theorem d2Transfer252Bound : ∀ x ∈ Set.Icc ((d2Transfer252Lo:ℚ):ℝ) ((d2Transfer252Hi:ℚ):ℝ), ((d2Transfer252C0:ℚ):ℝ)*Real.log |x-((d2Transfer252S0:ℚ):ℝ)| ≤ ((d2Transfer252Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer252S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer252S0,d2Transfer252Lo,d2Transfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer252C0 then |x-((d2Transfer252S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2Transfer252S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer252S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer252S0,d2Transfer252Lo,d2Transfer252Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer252C0,d2Log132Q,d2Transfer252S0,d2Transfer252Lo,d2Transfer252Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer252C0 d2Transfer252S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have har : (((weightedUpper d2Transfer252C0 d2Log132Lo d2Log132Hi:ℚ):ℝ)) ≤ ((d2Transfer252Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer252Arithmetic
  linarith
#print axioms d2Transfer252Arithmetic
#print axioms d2Transfer252Bound
def d2Transfer253Lo : ℚ := (d2LitsNearTransfers031.q2 (165758587) 1 (-28))
def d2Transfer253Hi : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer253Cap : ℚ := (d2LitsNearTransfers031.q2 (8682324865321086567395) 1 (-78))
def d2Transfer253C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 11 (-5))
def d2Transfer253S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
def d2Transfer253C1 : ℚ := (d2LitsNearTransfers031.q2 (-5) 11 (-4))
def d2Transfer253S1 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer253Arithmetic : weightedUpper d2Transfer253C0 d2Log132Lo d2Log132Hi + weightedUpper d2Transfer253C1 d2Log42Lo d2Log42Hi ≤ d2Transfer253Cap := by decide +kernel
theorem d2Transfer253Bound : ∀ x ∈ Set.Icc ((d2Transfer253Lo:ℚ):ℝ) ((d2Transfer253Hi:ℚ):ℝ), ((d2Transfer253C0:ℚ):ℝ)*Real.log |x-((d2Transfer253S0:ℚ):ℝ)| + ((d2Transfer253C1:ℚ):ℝ)*Real.log |x-((d2Transfer253S1:ℚ):ℝ)| ≤ ((d2Transfer253Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer253S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253S0,d2Transfer253Lo,d2Transfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer253C0 then |x-((d2Transfer253S0:ℚ):ℝ)| ≤ ((d2Log132Q:ℚ):ℝ) else ((d2Log132Q:ℚ):ℝ) ≤ |x-((d2Transfer253S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer253S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253S0,d2Transfer253Lo,d2Transfer253Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253C0,d2Log132Q,d2Transfer253S0,d2Transfer253Lo,d2Transfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer253C0 d2Transfer253S0 d2Log132Q d2Log132Lo d2Log132Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log132Bounds
  have hn1 : x-((d2Transfer253S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253S1,d2Transfer253Lo,d2Transfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer253C1 then |x-((d2Transfer253S1:ℚ):ℝ)| ≤ ((d2Log42Q:ℚ):ℝ) else ((d2Log42Q:ℚ):ℝ) ≤ |x-((d2Transfer253S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer253S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253S1,d2Transfer253Lo,d2Transfer253Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer253C1,d2Log42Q,d2Transfer253S1,d2Transfer253Lo,d2Transfer253Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer253C1 d2Transfer253S1 d2Log42Q d2Log42Lo d2Log42Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log42Bounds
  have har : (((weightedUpper d2Transfer253C0 d2Log132Lo d2Log132Hi:ℚ):ℝ) + ((weightedUpper d2Transfer253C1 d2Log42Lo d2Log42Hi:ℚ):ℝ)) ≤ ((d2Transfer253Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer253Arithmetic
  linarith
#print axioms d2Transfer253Arithmetic
#print axioms d2Transfer253Bound
def d2Transfer254Lo : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer254Hi : ℚ := (d2LitsNearTransfers031.q2 (664712069) 1 (-30))
def d2Transfer254Cap : ℚ := (d2LitsNearTransfers031.q2 (61347528822902331459) 1 (-75))
def d2Transfer254C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 25 (-4))
def d2Transfer254S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer254Arithmetic : weightedUpper d2Transfer254C0 d2Log133Lo d2Log133Hi ≤ d2Transfer254Cap := by decide +kernel
theorem d2Transfer254Bound : ∀ x ∈ Set.Icc ((d2Transfer254Lo:ℚ):ℝ) ((d2Transfer254Hi:ℚ):ℝ), ((d2Transfer254C0:ℚ):ℝ)*Real.log |x-((d2Transfer254S0:ℚ):ℝ)| ≤ ((d2Transfer254Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer254S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer254S0,d2Transfer254Lo,d2Transfer254Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer254C0 then |x-((d2Transfer254S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2Transfer254S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer254S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer254S0,d2Transfer254Lo,d2Transfer254Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer254C0,d2Log133Q,d2Transfer254S0,d2Transfer254Lo,d2Transfer254Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer254C0 d2Transfer254S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have har : (((weightedUpper d2Transfer254C0 d2Log133Lo d2Log133Hi:ℚ):ℝ)) ≤ ((d2Transfer254Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer254Arithmetic
  linarith
#print axioms d2Transfer254Arithmetic
#print axioms d2Transfer254Bound
def d2Transfer255Lo : ℚ := (d2LitsNearTransfers031.q2 (1327746417) 1 (-31))
def d2Transfer255Hi : ℚ := (d2LitsNearTransfers031.q2 (664712069) 1 (-30))
def d2Transfer255Cap : ℚ := (d2LitsNearTransfers031.q2 (100419409092769060931) 1 (-75))
def d2Transfer255C0 : ℚ := (d2LitsNearTransfers031.q2 (1) 275 (-4))
def d2Transfer255S0 : ℚ := (d2LitsNearTransfers031.q2 (-1) 1 (0))
def d2Transfer255C1 : ℚ := (d2LitsNearTransfers031.q2 (-1) 55 (-3))
def d2Transfer255S1 : ℚ := (d2LitsNearTransfers031.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer255Arithmetic : weightedUpper d2Transfer255C0 d2Log133Lo d2Log133Hi + weightedUpper d2Transfer255C1 d2Log41Lo d2Log41Hi ≤ d2Transfer255Cap := by decide +kernel
theorem d2Transfer255Bound : ∀ x ∈ Set.Icc ((d2Transfer255Lo:ℚ):ℝ) ((d2Transfer255Hi:ℚ):ℝ), ((d2Transfer255C0:ℚ):ℝ)*Real.log |x-((d2Transfer255S0:ℚ):ℝ)| + ((d2Transfer255C1:ℚ):ℝ)*Real.log |x-((d2Transfer255S1:ℚ):ℝ)| ≤ ((d2Transfer255Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer255S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255S0,d2Transfer255Lo,d2Transfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer255C0 then |x-((d2Transfer255S0:ℚ):ℝ)| ≤ ((d2Log133Q:ℚ):ℝ) else ((d2Log133Q:ℚ):ℝ) ≤ |x-((d2Transfer255S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer255S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255S0,d2Transfer255Lo,d2Transfer255Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255C0,d2Log133Q,d2Transfer255S0,d2Transfer255Lo,d2Transfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer255C0 d2Transfer255S0 d2Log133Q d2Log133Lo d2Log133Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log133Bounds
  have hn1 : x-((d2Transfer255S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255S1,d2Transfer255Lo,d2Transfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer255C1 then |x-((d2Transfer255S1:ℚ):ℝ)| ≤ ((d2Log41Q:ℚ):ℝ) else ((d2Log41Q:ℚ):ℝ) ≤ |x-((d2Transfer255S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer255S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255S1,d2Transfer255Lo,d2Transfer255Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers031.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer255C1,d2Log41Q,d2Transfer255S1,d2Transfer255Lo,d2Transfer255Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer255C1 d2Transfer255S1 d2Log41Q d2Log41Lo d2Log41Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log41Bounds
  have har : (((weightedUpper d2Transfer255C0 d2Log133Lo d2Log133Hi:ℚ):ℝ) + ((weightedUpper d2Transfer255C1 d2Log41Lo d2Log41Hi:ℚ):ℝ)) ≤ ((d2Transfer255Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer255Arithmetic
  linarith
#print axioms d2Transfer255Arithmetic
#print axioms d2Transfer255Bound
end CatalanMeasure.GenD.Signed.Data.Cells

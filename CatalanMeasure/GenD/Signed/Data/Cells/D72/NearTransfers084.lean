module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers084
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers084
open D72.LogTransfer
def d2Transfer672Lo : ℚ := (d2LitsNearTransfers084.q2 (65535) 1 (-16))
def d2Transfer672Hi : ℚ := (d2LitsNearTransfers084.q2 (1) 1 (0))
def d2Transfer672Cap : ℚ := (d2LitsNearTransfers084.q2 (1636647531324951549413) 1 (-76))
def d2Transfer672C0 : ℚ := (d2LitsNearTransfers084.q2 (1) 1 (-5))
def d2Transfer672S0 : ℚ := (d2LitsNearTransfers084.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer672Arithmetic : weightedUpper d2Transfer672C0 d2Log186Lo d2Log186Hi ≤ d2Transfer672Cap := by decide +kernel
theorem d2Transfer672Bound : ∀ x ∈ Set.Icc ((d2Transfer672Lo:ℚ):ℝ) ((d2Transfer672Hi:ℚ):ℝ), ((d2Transfer672C0:ℚ):ℝ)*Real.log |x-((d2Transfer672S0:ℚ):ℝ)| ≤ ((d2Transfer672Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer672S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer672S0,d2Transfer672Lo,d2Transfer672Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer672C0 then |x-((d2Transfer672S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2Transfer672S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer672S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer672S0,d2Transfer672Lo,d2Transfer672Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer672C0,d2Log186Q,d2Transfer672S0,d2Transfer672Lo,d2Transfer672Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer672C0 d2Transfer672S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2Transfer672C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2Transfer672Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer672Arithmetic
  linarith
#print axioms d2Transfer672Arithmetic
#print axioms d2Transfer672Bound
def d2Transfer673Lo : ℚ := (d2LitsNearTransfers084.q2 (999) 125 (-3))
def d2Transfer673Hi : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer673Cap : ℚ := (d2LitsNearTransfers084.q2 (241850313660495) 1 (-78))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer673Arithmetic : (0 : ℚ) ≤ d2Transfer673Cap := by decide +kernel
theorem d2Transfer673Bound : ∀ x ∈ Set.Icc ((d2Transfer673Lo:ℚ):ℝ) ((d2Transfer673Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer673Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer673Arithmetic
#print axioms d2Transfer673Arithmetic
#print axioms d2Transfer673Bound
def d2Transfer674Lo : ℚ := (d2LitsNearTransfers084.q2 (999) 125 (-3))
def d2Transfer674Hi : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer674Cap : ℚ := (d2LitsNearTransfers084.q2 (6018517399047162615887) 1 (-78))
def d2Transfer674C0 : ℚ := (d2LitsNearTransfers084.q2 (23) 25 (-5))
def d2Transfer674S0 : ℚ := (d2LitsNearTransfers084.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer674Arithmetic : weightedUpper d2Transfer674C0 d2Log175Lo d2Log175Hi ≤ d2Transfer674Cap := by decide +kernel
theorem d2Transfer674Bound : ∀ x ∈ Set.Icc ((d2Transfer674Lo:ℚ):ℝ) ((d2Transfer674Hi:ℚ):ℝ), ((d2Transfer674C0:ℚ):ℝ)*Real.log |x-((d2Transfer674S0:ℚ):ℝ)| ≤ ((d2Transfer674Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer674S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer674S0,d2Transfer674Lo,d2Transfer674Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer674C0 then |x-((d2Transfer674S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer674S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer674S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer674S0,d2Transfer674Lo,d2Transfer674Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer674C0,d2Log175Q,d2Transfer674S0,d2Transfer674Lo,d2Transfer674Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer674C0 d2Transfer674S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer674C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer674Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer674Arithmetic
  linarith
#print axioms d2Transfer674Arithmetic
#print axioms d2Transfer674Bound
def d2Transfer675Lo : ℚ := (d2LitsNearTransfers084.q2 (999) 125 (-3))
def d2Transfer675Hi : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer675Cap : ℚ := (d2LitsNearTransfers084.q2 (6018517216528232405071) 1 (-78))
def d2Transfer675C0 : ℚ := (d2LitsNearTransfers084.q2 (23) 25 (-5))
def d2Transfer675S0 : ℚ := (d2LitsNearTransfers084.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer675Arithmetic : weightedUpper d2Transfer675C0 d2Log175Lo d2Log175Hi ≤ d2Transfer675Cap := by decide +kernel
theorem d2Transfer675Bound : ∀ x ∈ Set.Icc ((d2Transfer675Lo:ℚ):ℝ) ((d2Transfer675Hi:ℚ):ℝ), ((d2Transfer675C0:ℚ):ℝ)*Real.log |x-((d2Transfer675S0:ℚ):ℝ)| ≤ ((d2Transfer675Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer675S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer675S0,d2Transfer675Lo,d2Transfer675Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer675C0 then |x-((d2Transfer675S0:ℚ):ℝ)| ≤ ((d2Log175Q:ℚ):ℝ) else ((d2Log175Q:ℚ):ℝ) ≤ |x-((d2Transfer675S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer675S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer675S0,d2Transfer675Lo,d2Transfer675Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer675C0,d2Log175Q,d2Transfer675S0,d2Transfer675Lo,d2Transfer675Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer675C0 d2Transfer675S0 d2Log175Q d2Log175Lo d2Log175Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log175Bounds
  have har : (((weightedUpper d2Transfer675C0 d2Log175Lo d2Log175Hi:ℚ):ℝ)) ≤ ((d2Transfer675Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer675Arithmetic
  linarith
#print axioms d2Transfer675Arithmetic
#print axioms d2Transfer675Bound
def d2Transfer676Lo : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer676Hi : ℚ := (d2LitsNearTransfers084.q2 (1023) 1 (-10))
def d2Transfer676Cap : ℚ := (d2LitsNearTransfers084.q2 (51031128082795455) 1 (-77))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer676Arithmetic : (0 : ℚ) ≤ d2Transfer676Cap := by decide +kernel
theorem d2Transfer676Bound : ∀ x ∈ Set.Icc ((d2Transfer676Lo:ℚ):ℝ) ((d2Transfer676Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer676Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer676Arithmetic
#print axioms d2Transfer676Arithmetic
#print axioms d2Transfer676Bound
def d2Transfer677Lo : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer677Hi : ℚ := (d2LitsNearTransfers084.q2 (1023) 1 (-10))
def d2Transfer677Cap : ℚ := (d2LitsNearTransfers084.q2 (3009309609726507273151) 1 (-77))
def d2Transfer677C0 : ℚ := (d2LitsNearTransfers084.q2 (23) 25 (-5))
def d2Transfer677S0 : ℚ := (d2LitsNearTransfers084.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer677Arithmetic : weightedUpper d2Transfer677C0 d2Log176Lo d2Log176Hi ≤ d2Transfer677Cap := by decide +kernel
theorem d2Transfer677Bound : ∀ x ∈ Set.Icc ((d2Transfer677Lo:ℚ):ℝ) ((d2Transfer677Hi:ℚ):ℝ), ((d2Transfer677C0:ℚ):ℝ)*Real.log |x-((d2Transfer677S0:ℚ):ℝ)| ≤ ((d2Transfer677Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer677S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer677S0,d2Transfer677Lo,d2Transfer677Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer677C0 then |x-((d2Transfer677S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer677S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer677S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer677S0,d2Transfer677Lo,d2Transfer677Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer677C0,d2Log176Q,d2Transfer677S0,d2Transfer677Lo,d2Transfer677Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer677C0 d2Transfer677S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer677C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer677Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer677Arithmetic
  linarith
#print axioms d2Transfer677Arithmetic
#print axioms d2Transfer677Bound
def d2Transfer678Lo : ℚ := (d2LitsNearTransfers084.q2 (16760439) 1 (-24))
def d2Transfer678Hi : ℚ := (d2LitsNearTransfers084.q2 (1023) 1 (-10))
def d2Transfer678Cap : ℚ := (d2LitsNearTransfers084.q2 (3009309518467042167743) 1 (-77))
def d2Transfer678C0 : ℚ := (d2LitsNearTransfers084.q2 (23) 25 (-5))
def d2Transfer678S0 : ℚ := (d2LitsNearTransfers084.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer678Arithmetic : weightedUpper d2Transfer678C0 d2Log176Lo d2Log176Hi ≤ d2Transfer678Cap := by decide +kernel
theorem d2Transfer678Bound : ∀ x ∈ Set.Icc ((d2Transfer678Lo:ℚ):ℝ) ((d2Transfer678Hi:ℚ):ℝ), ((d2Transfer678C0:ℚ):ℝ)*Real.log |x-((d2Transfer678S0:ℚ):ℝ)| ≤ ((d2Transfer678Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer678S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer678S0,d2Transfer678Lo,d2Transfer678Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer678C0 then |x-((d2Transfer678S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer678S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer678S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer678S0,d2Transfer678Lo,d2Transfer678Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers084.q2, d2LitsNearLogCache010.q2, d2LitsNearLogCache011.q2, d2Transfer678C0,d2Log176Q,d2Transfer678S0,d2Transfer678Lo,d2Transfer678Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer678C0 d2Transfer678S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer678C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer678Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer678Arithmetic
  linarith
#print axioms d2Transfer678Arithmetic
#print axioms d2Transfer678Bound
def d2Transfer679Lo : ℚ := (d2LitsNearTransfers084.q2 (1023) 1 (-10))
def d2Transfer679Hi : ℚ := (d2LitsNearTransfers084.q2 (2047) 1 (-11))
def d2Transfer679Cap : ℚ := (d2LitsNearTransfers084.q2 (8896859962917361653) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer679Arithmetic : (0 : ℚ) ≤ d2Transfer679Cap := by decide +kernel
theorem d2Transfer679Bound : ∀ x ∈ Set.Icc ((d2Transfer679Lo:ℚ):ℝ) ((d2Transfer679Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer679Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer679Arithmetic
#print axioms d2Transfer679Arithmetic
#print axioms d2Transfer679Bound
end CatalanMeasure.GenD.Signed.Data.Cells

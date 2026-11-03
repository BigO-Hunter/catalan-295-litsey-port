module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
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
namespace d2LitsNearTransfers036
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers036
open D72.LogTransfer
def d2Transfer288Lo : ℚ := (d2LitsNearTransfers036.q2 (1341168185) 1 (-31))
def d2Transfer288Hi : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer288Cap : ℚ := (d2LitsNearTransfers036.q2 (2377234188557733987133) 1 (-77))
def d2Transfer288C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (-5))
def d2Transfer288S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer288Arithmetic : weightedUpper d2Transfer288C0 d2Log141Lo d2Log141Hi ≤ d2Transfer288Cap := by decide +kernel
theorem d2Transfer288Bound : ∀ x ∈ Set.Icc ((d2Transfer288Lo:ℚ):ℝ) ((d2Transfer288Hi:ℚ):ℝ), ((d2Transfer288C0:ℚ):ℝ)*Real.log |x-((d2Transfer288S0:ℚ):ℝ)| ≤ ((d2Transfer288Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer288S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer288S0,d2Transfer288Lo,d2Transfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer288C0 then |x-((d2Transfer288S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer288S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer288S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer288S0,d2Transfer288Lo,d2Transfer288Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer288C0,d2Log141Q,d2Transfer288S0,d2Transfer288Lo,d2Transfer288Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer288C0 d2Transfer288S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2Transfer288C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2Transfer288Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer288Arithmetic
  linarith
#print axioms d2Transfer288Arithmetic
#print axioms d2Transfer288Bound
def d2Transfer289Lo : ℚ := (d2LitsNearTransfers036.q2 (1341168185) 1 (-31))
def d2Transfer289Hi : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer289Cap : ℚ := (d2LitsNearTransfers036.q2 (4422838853844172407613) 1 (-77))
def d2Transfer289C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 11 (-5))
def d2Transfer289S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
def d2Transfer289C1 : ℚ := (d2LitsNearTransfers036.q2 (-5) 11 (-4))
def d2Transfer289S1 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer289Arithmetic : weightedUpper d2Transfer289C0 d2Log141Lo d2Log141Hi + weightedUpper d2Transfer289C1 d2Log33Lo d2Log33Hi ≤ d2Transfer289Cap := by decide +kernel
theorem d2Transfer289Bound : ∀ x ∈ Set.Icc ((d2Transfer289Lo:ℚ):ℝ) ((d2Transfer289Hi:ℚ):ℝ), ((d2Transfer289C0:ℚ):ℝ)*Real.log |x-((d2Transfer289S0:ℚ):ℝ)| + ((d2Transfer289C1:ℚ):ℝ)*Real.log |x-((d2Transfer289S1:ℚ):ℝ)| ≤ ((d2Transfer289Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer289S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289S0,d2Transfer289Lo,d2Transfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer289C0 then |x-((d2Transfer289S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2Transfer289S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer289S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289S0,d2Transfer289Lo,d2Transfer289Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289C0,d2Log141Q,d2Transfer289S0,d2Transfer289Lo,d2Transfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer289C0 d2Transfer289S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2Transfer289S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289S1,d2Transfer289Lo,d2Transfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer289C1 then |x-((d2Transfer289S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2Transfer289S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer289S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289S1,d2Transfer289Lo,d2Transfer289Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer289C1,d2Log33Q,d2Transfer289S1,d2Transfer289Lo,d2Transfer289Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer289C1 d2Transfer289S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2Transfer289C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2Transfer289C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2Transfer289Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer289Arithmetic
  linarith
#print axioms d2Transfer289Arithmetic
#print axioms d2Transfer289Bound
def d2Transfer290Lo : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer290Hi : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer290Cap : ℚ := (d2LitsNearTransfers036.q2 (2617846911167768580485) 1 (-80))
def d2Transfer290C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 25 (-4))
def d2Transfer290S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer290Arithmetic : weightedUpper d2Transfer290C0 d2Log142Lo d2Log142Hi ≤ d2Transfer290Cap := by decide +kernel
theorem d2Transfer290Bound : ∀ x ∈ Set.Icc ((d2Transfer290Lo:ℚ):ℝ) ((d2Transfer290Hi:ℚ):ℝ), ((d2Transfer290C0:ℚ):ℝ)*Real.log |x-((d2Transfer290S0:ℚ):ℝ)| ≤ ((d2Transfer290Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer290S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer290S0,d2Transfer290Lo,d2Transfer290Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer290C0 then |x-((d2Transfer290S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer290S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer290S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer290S0,d2Transfer290Lo,d2Transfer290Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer290C0,d2Log142Q,d2Transfer290S0,d2Transfer290Lo,d2Transfer290Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer290C0 d2Transfer290S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2Transfer290C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2Transfer290Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer290Arithmetic
  linarith
#print axioms d2Transfer290Arithmetic
#print axioms d2Transfer290Bound
def d2Transfer291Lo : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer291Hi : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer291Cap : ℚ := (d2LitsNearTransfers036.q2 (3868147079803503923589) 1 (-80))
def d2Transfer291C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 275 (-4))
def d2Transfer291S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
def d2Transfer291C1 : ℚ := (d2LitsNearTransfers036.q2 (-1) 55 (-3))
def d2Transfer291S1 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer291Arithmetic : weightedUpper d2Transfer291C0 d2Log142Lo d2Log142Hi + weightedUpper d2Transfer291C1 d2Log32Lo d2Log32Hi ≤ d2Transfer291Cap := by decide +kernel
theorem d2Transfer291Bound : ∀ x ∈ Set.Icc ((d2Transfer291Lo:ℚ):ℝ) ((d2Transfer291Hi:ℚ):ℝ), ((d2Transfer291C0:ℚ):ℝ)*Real.log |x-((d2Transfer291S0:ℚ):ℝ)| + ((d2Transfer291C1:ℚ):ℝ)*Real.log |x-((d2Transfer291S1:ℚ):ℝ)| ≤ ((d2Transfer291Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer291S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291S0,d2Transfer291Lo,d2Transfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer291C0 then |x-((d2Transfer291S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer291S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer291S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291S0,d2Transfer291Lo,d2Transfer291Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291C0,d2Log142Q,d2Transfer291S0,d2Transfer291Lo,d2Transfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer291C0 d2Transfer291S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2Transfer291S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291S1,d2Transfer291Lo,d2Transfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer291C1 then |x-((d2Transfer291S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2Transfer291S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer291S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291S1,d2Transfer291Lo,d2Transfer291Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer291C1,d2Log32Q,d2Transfer291S1,d2Transfer291Lo,d2Transfer291Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer291C1 d2Transfer291S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2Transfer291C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2Transfer291C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2Transfer291Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer291Arithmetic
  linarith
#print axioms d2Transfer291Arithmetic
#print axioms d2Transfer291Bound
def d2Transfer292Lo : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer292Hi : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer292Cap : ℚ := (d2LitsNearTransfers036.q2 (19091209170226464444805) 1 (-80))
def d2Transfer292C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (-5))
def d2Transfer292S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer292Arithmetic : weightedUpper d2Transfer292C0 d2Log142Lo d2Log142Hi ≤ d2Transfer292Cap := by decide +kernel
theorem d2Transfer292Bound : ∀ x ∈ Set.Icc ((d2Transfer292Lo:ℚ):ℝ) ((d2Transfer292Hi:ℚ):ℝ), ((d2Transfer292C0:ℚ):ℝ)*Real.log |x-((d2Transfer292S0:ℚ):ℝ)| ≤ ((d2Transfer292Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer292S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer292S0,d2Transfer292Lo,d2Transfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer292C0 then |x-((d2Transfer292S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer292S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer292S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer292S0,d2Transfer292Lo,d2Transfer292Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer292C0,d2Log142Q,d2Transfer292S0,d2Transfer292Lo,d2Transfer292Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer292C0 d2Transfer292S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2Transfer292C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2Transfer292Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer292Arithmetic
  linarith
#print axioms d2Transfer292Arithmetic
#print axioms d2Transfer292Bound
def d2Transfer293Lo : ℚ := (d2LitsNearTransfers036.q2 (671422953) 1 (-30))
def d2Transfer293Hi : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer293Cap : ℚ := (d2LitsNearTransfers036.q2 (35456046492517971808645) 1 (-80))
def d2Transfer293C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 11 (-5))
def d2Transfer293S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
def d2Transfer293C1 : ℚ := (d2LitsNearTransfers036.q2 (-5) 11 (-4))
def d2Transfer293S1 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer293Arithmetic : weightedUpper d2Transfer293C0 d2Log142Lo d2Log142Hi + weightedUpper d2Transfer293C1 d2Log32Lo d2Log32Hi ≤ d2Transfer293Cap := by decide +kernel
theorem d2Transfer293Bound : ∀ x ∈ Set.Icc ((d2Transfer293Lo:ℚ):ℝ) ((d2Transfer293Hi:ℚ):ℝ), ((d2Transfer293C0:ℚ):ℝ)*Real.log |x-((d2Transfer293S0:ℚ):ℝ)| + ((d2Transfer293C1:ℚ):ℝ)*Real.log |x-((d2Transfer293S1:ℚ):ℝ)| ≤ ((d2Transfer293Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer293S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293S0,d2Transfer293Lo,d2Transfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer293C0 then |x-((d2Transfer293S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2Transfer293S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer293S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293S0,d2Transfer293Lo,d2Transfer293Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293C0,d2Log142Q,d2Transfer293S0,d2Transfer293Lo,d2Transfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer293C0 d2Transfer293S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2Transfer293S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293S1,d2Transfer293Lo,d2Transfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer293C1 then |x-((d2Transfer293S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2Transfer293S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer293S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293S1,d2Transfer293Lo,d2Transfer293Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer293C1,d2Log32Q,d2Transfer293S1,d2Transfer293Lo,d2Transfer293Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer293C1 d2Transfer293S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2Transfer293C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2Transfer293C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2Transfer293Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer293Arithmetic
  linarith
#print axioms d2Transfer293Arithmetic
#print axioms d2Transfer293Bound
def d2Transfer294Lo : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer294Hi : ℚ := (d2LitsNearTransfers036.q2 (336550337) 1 (-29))
def d2Transfer294Cap : ℚ := (d2LitsNearTransfers036.q2 (2691331717425410526057) 1 (-80))
def d2Transfer294C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 25 (-4))
def d2Transfer294S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer294Arithmetic : weightedUpper d2Transfer294C0 d2Log143Lo d2Log143Hi ≤ d2Transfer294Cap := by decide +kernel
theorem d2Transfer294Bound : ∀ x ∈ Set.Icc ((d2Transfer294Lo:ℚ):ℝ) ((d2Transfer294Hi:ℚ):ℝ), ((d2Transfer294C0:ℚ):ℝ)*Real.log |x-((d2Transfer294S0:ℚ):ℝ)| ≤ ((d2Transfer294Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer294S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer294S0,d2Transfer294Lo,d2Transfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer294C0 then |x-((d2Transfer294S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer294S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer294S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer294S0,d2Transfer294Lo,d2Transfer294Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer294C0,d2Log143Q,d2Transfer294S0,d2Transfer294Lo,d2Transfer294Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer294C0 d2Transfer294S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2Transfer294C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2Transfer294Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer294Arithmetic
  linarith
#print axioms d2Transfer294Arithmetic
#print axioms d2Transfer294Bound
def d2Transfer295Lo : ℚ := (d2LitsNearTransfers036.q2 (1344523627) 1 (-31))
def d2Transfer295Hi : ℚ := (d2LitsNearTransfers036.q2 (336550337) 1 (-29))
def d2Transfer295Cap : ℚ := (d2LitsNearTransfers036.q2 (3941631886061145869161) 1 (-80))
def d2Transfer295C0 : ℚ := (d2LitsNearTransfers036.q2 (1) 275 (-4))
def d2Transfer295S0 : ℚ := (d2LitsNearTransfers036.q2 (-1) 1 (0))
def d2Transfer295C1 : ℚ := (d2LitsNearTransfers036.q2 (-1) 55 (-3))
def d2Transfer295S1 : ℚ := (d2LitsNearTransfers036.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer295Arithmetic : weightedUpper d2Transfer295C0 d2Log143Lo d2Log143Hi + weightedUpper d2Transfer295C1 d2Log31Lo d2Log31Hi ≤ d2Transfer295Cap := by decide +kernel
theorem d2Transfer295Bound : ∀ x ∈ Set.Icc ((d2Transfer295Lo:ℚ):ℝ) ((d2Transfer295Hi:ℚ):ℝ), ((d2Transfer295C0:ℚ):ℝ)*Real.log |x-((d2Transfer295S0:ℚ):ℝ)| + ((d2Transfer295C1:ℚ):ℝ)*Real.log |x-((d2Transfer295S1:ℚ):ℝ)| ≤ ((d2Transfer295Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer295S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295S0,d2Transfer295Lo,d2Transfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer295C0 then |x-((d2Transfer295S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer295S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer295S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295S0,d2Transfer295Lo,d2Transfer295Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295C0,d2Log143Q,d2Transfer295S0,d2Transfer295Lo,d2Transfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer295C0 d2Transfer295S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2Transfer295S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295S1,d2Transfer295Lo,d2Transfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer295C1 then |x-((d2Transfer295S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2Transfer295S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer295S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295S1,d2Transfer295Lo,d2Transfer295Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers036.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer295C1,d2Log31Q,d2Transfer295S1,d2Transfer295Lo,d2Transfer295Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer295C1 d2Transfer295S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2Transfer295C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2Transfer295C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2Transfer295Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer295Arithmetic
  linarith
#print axioms d2Transfer295Arithmetic
#print axioms d2Transfer295Bound
end CatalanMeasure.GenD.Signed.Data.Cells

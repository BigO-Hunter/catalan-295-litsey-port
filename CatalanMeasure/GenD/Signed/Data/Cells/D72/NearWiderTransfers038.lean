module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers038
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers038
open D72.LogTransfer
def d2WiderTransfer304Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (671422953) 1 (-30))
def d2WiderTransfer304Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer304Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (1803874458056511115589) 1 (-80))
def d2WiderTransfer304C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer304S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
def d2WiderTransfer304C1 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer304S1 : ℚ := (d2LitsNearWiderTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer304Arithmetic : weightedUpper d2WiderTransfer304C0 d2Log141Lo d2Log141Hi + weightedUpper d2WiderTransfer304C1 d2Log32Lo d2Log32Hi ≤ d2WiderTransfer304Cap := by decide +kernel
theorem d2WiderTransfer304Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer304Lo:ℚ):ℝ) ((d2WiderTransfer304Hi:ℚ):ℝ), ((d2WiderTransfer304C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer304S0:ℚ):ℝ)| + ((d2WiderTransfer304C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer304S1:ℚ):ℝ)| ≤ ((d2WiderTransfer304Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer304S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304S0,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer304C0 then |x-((d2WiderTransfer304S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer304S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer304S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304S0,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304C0,d2Log141Q,d2WiderTransfer304S0,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer304C0 d2WiderTransfer304S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2WiderTransfer304S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304S1,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer304C1 then |x-((d2WiderTransfer304S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer304S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer304S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304S1,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer304C1,d2Log32Q,d2WiderTransfer304S1,d2WiderTransfer304Lo,d2WiderTransfer304Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer304C1 d2WiderTransfer304S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2WiderTransfer304C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer304C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer304Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer304Arithmetic
  linarith
#print axioms d2WiderTransfer304Arithmetic
#print axioms d2WiderTransfer304Bound
def d2WiderTransfer305Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (671422953) 1 (-30))
def d2WiderTransfer305Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer305Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (17135670331982798049605) 1 (-80))
def d2WiderTransfer305C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (23) 25 (-5))
def d2WiderTransfer305S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer305Arithmetic : weightedUpper d2WiderTransfer305C0 d2Log142Lo d2Log142Hi ≤ d2WiderTransfer305Cap := by decide +kernel
theorem d2WiderTransfer305Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer305Lo:ℚ):ℝ) ((d2WiderTransfer305Hi:ℚ):ℝ), ((d2WiderTransfer305C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer305S0:ℚ):ℝ)| ≤ ((d2WiderTransfer305Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer305S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer305S0,d2WiderTransfer305Lo,d2WiderTransfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer305C0 then |x-((d2WiderTransfer305S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer305S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer305S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer305S0,d2WiderTransfer305Lo,d2WiderTransfer305Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer305C0,d2Log142Q,d2WiderTransfer305S0,d2WiderTransfer305Lo,d2WiderTransfer305Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer305C0 d2WiderTransfer305S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2WiderTransfer305C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer305Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer305Arithmetic
  linarith
#print axioms d2WiderTransfer305Arithmetic
#print axioms d2WiderTransfer305Bound
def d2WiderTransfer306Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (671422953) 1 (-30))
def d2WiderTransfer306Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer306Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (33986657723250068345157) 1 (-80))
def d2WiderTransfer306C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (3) 275 (-5))
def d2WiderTransfer306S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
def d2WiderTransfer306C1 : ℚ := (d2LitsNearWiderTransfers038.q2 (-5) 11 (-4))
def d2WiderTransfer306S1 : ℚ := (d2LitsNearWiderTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer306Arithmetic : weightedUpper d2WiderTransfer306C0 d2Log142Lo d2Log142Hi + weightedUpper d2WiderTransfer306C1 d2Log32Lo d2Log32Hi ≤ d2WiderTransfer306Cap := by decide +kernel
theorem d2WiderTransfer306Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer306Lo:ℚ):ℝ) ((d2WiderTransfer306Hi:ℚ):ℝ), ((d2WiderTransfer306C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer306S0:ℚ):ℝ)| + ((d2WiderTransfer306C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer306S1:ℚ):ℝ)| ≤ ((d2WiderTransfer306Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer306S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306S0,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer306C0 then |x-((d2WiderTransfer306S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer306S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer306S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306S0,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306C0,d2Log142Q,d2WiderTransfer306S0,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer306C0 d2WiderTransfer306S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2WiderTransfer306S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306S1,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer306C1 then |x-((d2WiderTransfer306S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer306S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer306S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306S1,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer306C1,d2Log32Q,d2WiderTransfer306S1,d2WiderTransfer306Lo,d2WiderTransfer306Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer306C1 d2WiderTransfer306S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2WiderTransfer306C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer306C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer306Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer306Arithmetic
  linarith
#print axioms d2WiderTransfer306Arithmetic
#print axioms d2WiderTransfer306Bound
def d2WiderTransfer307Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer307Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (336550337) 1 (-29))
def d2WiderTransfer307Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (937953777010828006371) 1 (-79))
def d2WiderTransfer307C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer307S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
def d2WiderTransfer307C1 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer307S1 : ℚ := (d2LitsNearWiderTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer307Arithmetic : weightedUpper d2WiderTransfer307C0 d2Log142Lo d2Log142Hi + weightedUpper d2WiderTransfer307C1 d2Log31Lo d2Log31Hi ≤ d2WiderTransfer307Cap := by decide +kernel
theorem d2WiderTransfer307Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer307Lo:ℚ):ℝ) ((d2WiderTransfer307Hi:ℚ):ℝ), ((d2WiderTransfer307C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer307S0:ℚ):ℝ)| + ((d2WiderTransfer307C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer307S1:ℚ):ℝ)| ≤ ((d2WiderTransfer307Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer307S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307S0,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer307C0 then |x-((d2WiderTransfer307S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer307S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer307S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307S0,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307C0,d2Log142Q,d2WiderTransfer307S0,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer307C0 d2WiderTransfer307S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2WiderTransfer307S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307S1,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer307C1 then |x-((d2WiderTransfer307S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer307S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer307S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307S1,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer307C1,d2Log31Q,d2WiderTransfer307S1,d2WiderTransfer307Lo,d2WiderTransfer307Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer307C1 d2WiderTransfer307S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2WiderTransfer307C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer307C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer307Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer307Arithmetic
  linarith
#print axioms d2WiderTransfer307Arithmetic
#print axioms d2WiderTransfer307Bound
def d2WiderTransfer308Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer308Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (336550337) 1 (-29))
def d2WiderTransfer308Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (8603851713973971473379) 1 (-79))
def d2WiderTransfer308C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (23) 25 (-5))
def d2WiderTransfer308S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer308Arithmetic : weightedUpper d2WiderTransfer308C0 d2Log143Lo d2Log143Hi ≤ d2WiderTransfer308Cap := by decide +kernel
theorem d2WiderTransfer308Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer308Lo:ℚ):ℝ) ((d2WiderTransfer308Hi:ℚ):ℝ), ((d2WiderTransfer308C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer308S0:ℚ):ℝ)| ≤ ((d2WiderTransfer308Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer308S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer308S0,d2WiderTransfer308Lo,d2WiderTransfer308Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer308C0 then |x-((d2WiderTransfer308S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer308S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer308S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer308S0,d2WiderTransfer308Lo,d2WiderTransfer308Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer308C0,d2Log143Q,d2WiderTransfer308S0,d2WiderTransfer308Lo,d2WiderTransfer308Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer308C0 d2WiderTransfer308S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2WiderTransfer308C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer308Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer308Arithmetic
  linarith
#print axioms d2WiderTransfer308Arithmetic
#print axioms d2WiderTransfer308Bound
def d2WiderTransfer309Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (1344523627) 1 (-31))
def d2WiderTransfer309Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (336550337) 1 (-29))
def d2WiderTransfer309Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (17029345409607606621155) 1 (-79))
def d2WiderTransfer309C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (3) 275 (-5))
def d2WiderTransfer309S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
def d2WiderTransfer309C1 : ℚ := (d2LitsNearWiderTransfers038.q2 (-5) 11 (-4))
def d2WiderTransfer309S1 : ℚ := (d2LitsNearWiderTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer309Arithmetic : weightedUpper d2WiderTransfer309C0 d2Log143Lo d2Log143Hi + weightedUpper d2WiderTransfer309C1 d2Log31Lo d2Log31Hi ≤ d2WiderTransfer309Cap := by decide +kernel
theorem d2WiderTransfer309Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer309Lo:ℚ):ℝ) ((d2WiderTransfer309Hi:ℚ):ℝ), ((d2WiderTransfer309C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer309S0:ℚ):ℝ)| + ((d2WiderTransfer309C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer309S1:ℚ):ℝ)| ≤ ((d2WiderTransfer309Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer309S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309S0,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer309C0 then |x-((d2WiderTransfer309S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer309S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer309S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309S0,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309C0,d2Log143Q,d2WiderTransfer309S0,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer309C0 d2WiderTransfer309S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2WiderTransfer309S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309S1,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer309C1 then |x-((d2WiderTransfer309S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer309S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer309S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309S1,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer309C1,d2Log31Q,d2WiderTransfer309S1,d2WiderTransfer309Lo,d2WiderTransfer309Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer309C1 d2WiderTransfer309S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2WiderTransfer309C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer309C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer309Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer309Arithmetic
  linarith
#print axioms d2WiderTransfer309Arithmetic
#print axioms d2WiderTransfer309Bound
def d2WiderTransfer310Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (336550337) 1 (-29))
def d2WiderTransfer310Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (1347879069) 1 (-31))
def d2WiderTransfer310Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (1948091120741767569807) 1 (-80))
def d2WiderTransfer310C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer310S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
def d2WiderTransfer310C1 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 55 (-3))
def d2WiderTransfer310S1 : ℚ := (d2LitsNearWiderTransfers038.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer310Arithmetic : weightedUpper d2WiderTransfer310C0 d2Log143Lo d2Log143Hi + weightedUpper d2WiderTransfer310C1 d2Log30Lo d2Log30Hi ≤ d2WiderTransfer310Cap := by decide +kernel
theorem d2WiderTransfer310Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer310Lo:ℚ):ℝ) ((d2WiderTransfer310Hi:ℚ):ℝ), ((d2WiderTransfer310C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer310S0:ℚ):ℝ)| + ((d2WiderTransfer310C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer310S1:ℚ):ℝ)| ≤ ((d2WiderTransfer310Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer310S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310S0,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer310C0 then |x-((d2WiderTransfer310S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer310S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer310S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310S0,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310C0,d2Log143Q,d2WiderTransfer310S0,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer310C0 d2WiderTransfer310S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2WiderTransfer310S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310S1,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer310C1 then |x-((d2WiderTransfer310S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer310S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer310S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310S1,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer310C1,d2Log30Q,d2WiderTransfer310S1,d2WiderTransfer310Lo,d2WiderTransfer310Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer310C1 d2WiderTransfer310S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2WiderTransfer310C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer310C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer310Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer310Arithmetic
  linarith
#print axioms d2WiderTransfer310Arithmetic
#print axioms d2WiderTransfer310Bound
def d2WiderTransfer311Lo : ℚ := (d2LitsNearWiderTransfers038.q2 (336550337) 1 (-29))
def d2WiderTransfer311Hi : ℚ := (d2LitsNearWiderTransfers038.q2 (1347879069) 1 (-31))
def d2WiderTransfer311Cap : ℚ := (d2LitsNearWiderTransfers038.q2 (17279886994668054503823) 1 (-80))
def d2WiderTransfer311C0 : ℚ := (d2LitsNearWiderTransfers038.q2 (23) 25 (-5))
def d2WiderTransfer311S0 : ℚ := (d2LitsNearWiderTransfers038.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer311Arithmetic : weightedUpper d2WiderTransfer311C0 d2Log144Lo d2Log144Hi ≤ d2WiderTransfer311Cap := by decide +kernel
theorem d2WiderTransfer311Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer311Lo:ℚ):ℝ) ((d2WiderTransfer311Hi:ℚ):ℝ), ((d2WiderTransfer311C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer311S0:ℚ):ℝ)| ≤ ((d2WiderTransfer311Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer311S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer311S0,d2WiderTransfer311Lo,d2WiderTransfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer311C0 then |x-((d2WiderTransfer311S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer311S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer311S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer311S0,d2WiderTransfer311Lo,d2WiderTransfer311Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers038.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer311C0,d2Log144Q,d2WiderTransfer311S0,d2WiderTransfer311Lo,d2WiderTransfer311Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer311C0 d2WiderTransfer311S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2WiderTransfer311C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer311Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer311Arithmetic
  linarith
#print axioms d2WiderTransfer311Arithmetic
#print axioms d2WiderTransfer311Bound
end CatalanMeasure.GenD.Signed.Data.Cells

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
namespace d2LitsNearWiderTransfers020
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers020
open D72.LogTransfer
def d2WiderTransfer160Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (671422953) 1 (-30))
def d2WiderTransfer160Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer160Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (19091209170226464444805) 1 (-80))
def d2WiderTransfer160C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (-5))
def d2WiderTransfer160S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer160Arithmetic : weightedUpper d2WiderTransfer160C0 d2Log142Lo d2Log142Hi ≤ d2WiderTransfer160Cap := by decide +kernel
theorem d2WiderTransfer160Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer160Lo:ℚ):ℝ) ((d2WiderTransfer160Hi:ℚ):ℝ), ((d2WiderTransfer160C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer160S0:ℚ):ℝ)| ≤ ((d2WiderTransfer160Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer160S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer160S0,d2WiderTransfer160Lo,d2WiderTransfer160Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer160C0 then |x-((d2WiderTransfer160S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer160S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer160S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer160S0,d2WiderTransfer160Lo,d2WiderTransfer160Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer160C0,d2Log142Q,d2WiderTransfer160S0,d2WiderTransfer160Lo,d2WiderTransfer160Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer160C0 d2WiderTransfer160S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have har : (((weightedUpper d2WiderTransfer160C0 d2Log142Lo d2Log142Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer160Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer160Arithmetic
  linarith
#print axioms d2WiderTransfer160Arithmetic
#print axioms d2WiderTransfer160Bound
def d2WiderTransfer161Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (671422953) 1 (-30))
def d2WiderTransfer161Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer161Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (35456046492517971808645) 1 (-80))
def d2WiderTransfer161C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 11 (-5))
def d2WiderTransfer161S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
def d2WiderTransfer161C1 : ℚ := (d2LitsNearWiderTransfers020.q2 (-5) 11 (-4))
def d2WiderTransfer161S1 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer161Arithmetic : weightedUpper d2WiderTransfer161C0 d2Log142Lo d2Log142Hi + weightedUpper d2WiderTransfer161C1 d2Log32Lo d2Log32Hi ≤ d2WiderTransfer161Cap := by decide +kernel
theorem d2WiderTransfer161Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer161Lo:ℚ):ℝ) ((d2WiderTransfer161Hi:ℚ):ℝ), ((d2WiderTransfer161C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer161S0:ℚ):ℝ)| + ((d2WiderTransfer161C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer161S1:ℚ):ℝ)| ≤ ((d2WiderTransfer161Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer161S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161S0,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer161C0 then |x-((d2WiderTransfer161S0:ℚ):ℝ)| ≤ ((d2Log142Q:ℚ):ℝ) else ((d2Log142Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer161S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer161S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161S0,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161C0,d2Log142Q,d2WiderTransfer161S0,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer161C0 d2WiderTransfer161S0 d2Log142Q d2Log142Lo d2Log142Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log142Bounds
  have hn1 : x-((d2WiderTransfer161S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161S1,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer161C1 then |x-((d2WiderTransfer161S1:ℚ):ℝ)| ≤ ((d2Log32Q:ℚ):ℝ) else ((d2Log32Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer161S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer161S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161S1,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer161C1,d2Log32Q,d2WiderTransfer161S1,d2WiderTransfer161Lo,d2WiderTransfer161Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer161C1 d2WiderTransfer161S1 d2Log32Q d2Log32Lo d2Log32Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log32Bounds
  have har : (((weightedUpper d2WiderTransfer161C0 d2Log142Lo d2Log142Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer161C1 d2Log32Lo d2Log32Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer161Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer161Arithmetic
  linarith
#print axioms d2WiderTransfer161Arithmetic
#print axioms d2WiderTransfer161Bound
def d2WiderTransfer162Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer162Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer162Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (2691331717425410526057) 1 (-80))
def d2WiderTransfer162C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 25 (-4))
def d2WiderTransfer162S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer162Arithmetic : weightedUpper d2WiderTransfer162C0 d2Log143Lo d2Log143Hi ≤ d2WiderTransfer162Cap := by decide +kernel
theorem d2WiderTransfer162Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer162Lo:ℚ):ℝ) ((d2WiderTransfer162Hi:ℚ):ℝ), ((d2WiderTransfer162C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer162S0:ℚ):ℝ)| ≤ ((d2WiderTransfer162Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer162S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer162S0,d2WiderTransfer162Lo,d2WiderTransfer162Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer162C0 then |x-((d2WiderTransfer162S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer162S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer162S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer162S0,d2WiderTransfer162Lo,d2WiderTransfer162Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer162C0,d2Log143Q,d2WiderTransfer162S0,d2WiderTransfer162Lo,d2WiderTransfer162Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer162C0 d2WiderTransfer162S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2WiderTransfer162C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer162Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer162Arithmetic
  linarith
#print axioms d2WiderTransfer162Arithmetic
#print axioms d2WiderTransfer162Bound
def d2WiderTransfer163Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer163Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer163Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (3941631886061145869161) 1 (-80))
def d2WiderTransfer163C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 275 (-4))
def d2WiderTransfer163S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
def d2WiderTransfer163C1 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 55 (-3))
def d2WiderTransfer163S1 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer163Arithmetic : weightedUpper d2WiderTransfer163C0 d2Log143Lo d2Log143Hi + weightedUpper d2WiderTransfer163C1 d2Log31Lo d2Log31Hi ≤ d2WiderTransfer163Cap := by decide +kernel
theorem d2WiderTransfer163Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer163Lo:ℚ):ℝ) ((d2WiderTransfer163Hi:ℚ):ℝ), ((d2WiderTransfer163C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer163S0:ℚ):ℝ)| + ((d2WiderTransfer163C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer163S1:ℚ):ℝ)| ≤ ((d2WiderTransfer163Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer163S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163S0,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer163C0 then |x-((d2WiderTransfer163S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer163S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer163S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163S0,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163C0,d2Log143Q,d2WiderTransfer163S0,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer163C0 d2WiderTransfer163S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2WiderTransfer163S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163S1,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer163C1 then |x-((d2WiderTransfer163S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer163S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer163S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163S1,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer163C1,d2Log31Q,d2WiderTransfer163S1,d2WiderTransfer163Lo,d2WiderTransfer163Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer163C1 d2WiderTransfer163S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2WiderTransfer163C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer163C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer163Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer163Arithmetic
  linarith
#print axioms d2WiderTransfer163Arithmetic
#print axioms d2WiderTransfer163Bound
def d2WiderTransfer164Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer164Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer164Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (19164693976484106390377) 1 (-80))
def d2WiderTransfer164C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (-5))
def d2WiderTransfer164S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer164Arithmetic : weightedUpper d2WiderTransfer164C0 d2Log143Lo d2Log143Hi ≤ d2WiderTransfer164Cap := by decide +kernel
theorem d2WiderTransfer164Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer164Lo:ℚ):ℝ) ((d2WiderTransfer164Hi:ℚ):ℝ), ((d2WiderTransfer164C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer164S0:ℚ):ℝ)| ≤ ((d2WiderTransfer164Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer164S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer164S0,d2WiderTransfer164Lo,d2WiderTransfer164Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer164C0 then |x-((d2WiderTransfer164S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer164S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer164S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer164S0,d2WiderTransfer164Lo,d2WiderTransfer164Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer164C0,d2Log143Q,d2WiderTransfer164S0,d2WiderTransfer164Lo,d2WiderTransfer164Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer164C0 d2WiderTransfer164S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2WiderTransfer164C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer164Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer164Arithmetic
  linarith
#print axioms d2WiderTransfer164Arithmetic
#print axioms d2WiderTransfer164Bound
def d2WiderTransfer165Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (1344523627) 1 (-31))
def d2WiderTransfer165Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer165Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (35529531298775613754217) 1 (-80))
def d2WiderTransfer165C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 11 (-5))
def d2WiderTransfer165S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
def d2WiderTransfer165C1 : ℚ := (d2LitsNearWiderTransfers020.q2 (-5) 11 (-4))
def d2WiderTransfer165S1 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer165Arithmetic : weightedUpper d2WiderTransfer165C0 d2Log143Lo d2Log143Hi + weightedUpper d2WiderTransfer165C1 d2Log31Lo d2Log31Hi ≤ d2WiderTransfer165Cap := by decide +kernel
theorem d2WiderTransfer165Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer165Lo:ℚ):ℝ) ((d2WiderTransfer165Hi:ℚ):ℝ), ((d2WiderTransfer165C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer165S0:ℚ):ℝ)| + ((d2WiderTransfer165C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer165S1:ℚ):ℝ)| ≤ ((d2WiderTransfer165Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer165S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165S0,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer165C0 then |x-((d2WiderTransfer165S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer165S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer165S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165S0,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165C0,d2Log143Q,d2WiderTransfer165S0,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer165C0 d2WiderTransfer165S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2WiderTransfer165S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165S1,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer165C1 then |x-((d2WiderTransfer165S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer165S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer165S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165S1,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer165C1,d2Log31Q,d2WiderTransfer165S1,d2WiderTransfer165Lo,d2WiderTransfer165Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer165C1 d2WiderTransfer165S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2WiderTransfer165C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer165C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer165Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer165Arithmetic
  linarith
#print axioms d2WiderTransfer165Arithmetic
#print axioms d2WiderTransfer165Bound
def d2WiderTransfer166Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer166Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (1347879069) 1 (-31))
def d2WiderTransfer166Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (2764966297471840836517) 1 (-80))
def d2WiderTransfer166C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 25 (-4))
def d2WiderTransfer166S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer166Arithmetic : weightedUpper d2WiderTransfer166C0 d2Log144Lo d2Log144Hi ≤ d2WiderTransfer166Cap := by decide +kernel
theorem d2WiderTransfer166Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer166Lo:ℚ):ℝ) ((d2WiderTransfer166Hi:ℚ):ℝ), ((d2WiderTransfer166C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer166S0:ℚ):ℝ)| ≤ ((d2WiderTransfer166Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer166S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer166S0,d2WiderTransfer166Lo,d2WiderTransfer166Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer166C0 then |x-((d2WiderTransfer166S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer166S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer166S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer166S0,d2WiderTransfer166Lo,d2WiderTransfer166Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer166C0,d2Log144Q,d2WiderTransfer166S0,d2WiderTransfer166Lo,d2WiderTransfer166Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer166C0 d2WiderTransfer166S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2WiderTransfer166C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer166Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer166Arithmetic
  linarith
#print axioms d2WiderTransfer166Arithmetic
#print axioms d2WiderTransfer166Bound
def d2WiderTransfer167Lo : ℚ := (d2LitsNearWiderTransfers020.q2 (336550337) 1 (-29))
def d2WiderTransfer167Hi : ℚ := (d2LitsNearWiderTransfers020.q2 (1347879069) 1 (-31))
def d2WiderTransfer167Cap : ℚ := (d2LitsNearWiderTransfers020.q2 (4015266466107576179621) 1 (-80))
def d2WiderTransfer167C0 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 275 (-4))
def d2WiderTransfer167S0 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 1 (0))
def d2WiderTransfer167C1 : ℚ := (d2LitsNearWiderTransfers020.q2 (-1) 55 (-3))
def d2WiderTransfer167S1 : ℚ := (d2LitsNearWiderTransfers020.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer167Arithmetic : weightedUpper d2WiderTransfer167C0 d2Log144Lo d2Log144Hi + weightedUpper d2WiderTransfer167C1 d2Log30Lo d2Log30Hi ≤ d2WiderTransfer167Cap := by decide +kernel
theorem d2WiderTransfer167Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer167Lo:ℚ):ℝ) ((d2WiderTransfer167Hi:ℚ):ℝ), ((d2WiderTransfer167C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer167S0:ℚ):ℝ)| + ((d2WiderTransfer167C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer167S1:ℚ):ℝ)| ≤ ((d2WiderTransfer167Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer167S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167S0,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer167C0 then |x-((d2WiderTransfer167S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer167S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer167S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167S0,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167C0,d2Log144Q,d2WiderTransfer167S0,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer167C0 d2WiderTransfer167S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2WiderTransfer167S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167S1,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer167C1 then |x-((d2WiderTransfer167S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer167S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer167S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167S1,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers020.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2WiderTransfer167C1,d2Log30Q,d2WiderTransfer167S1,d2WiderTransfer167Lo,d2WiderTransfer167Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer167C1 d2WiderTransfer167S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2WiderTransfer167C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer167C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer167Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer167Arithmetic
  linarith
#print axioms d2WiderTransfer167Arithmetic
#print axioms d2WiderTransfer167Bound
end CatalanMeasure.GenD.Signed.Data.Cells

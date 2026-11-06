module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers059
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers059
open D72.LogTransfer
def d2WiderTransfer472Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (2047) 1 (-11))
def d2WiderTransfer472Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer472Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (13140388118353036535) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer472Arithmetic : (0 : ℚ) ≤ d2WiderTransfer472Cap := by decide +kernel
theorem d2WiderTransfer472Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer472Lo:ℚ):ℝ) ((d2WiderTransfer472Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer472Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer472Arithmetic
#print axioms d2WiderTransfer472Arithmetic
#print axioms d2WiderTransfer472Bound
def d2WiderTransfer473Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (2047) 1 (-11))
def d2WiderTransfer473Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer473Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (24087209016905748858103) 1 (-80))
def d2WiderTransfer473C0 : ℚ := (d2LitsNearWiderTransfers059.q2 (23) 25 (-5))
def d2WiderTransfer473S0 : ℚ := (d2LitsNearWiderTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer473Arithmetic : weightedUpper d2WiderTransfer473C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer473Cap := by decide +kernel
theorem d2WiderTransfer473Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer473Lo:ℚ):ℝ) ((d2WiderTransfer473Hi:ℚ):ℝ), ((d2WiderTransfer473C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer473S0:ℚ):ℝ)| ≤ ((d2WiderTransfer473Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer473S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer473S0,d2WiderTransfer473Lo,d2WiderTransfer473Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer473C0 then |x-((d2WiderTransfer473S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer473S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer473S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer473S0,d2WiderTransfer473Lo,d2WiderTransfer473Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer473C0,d2Log178Q,d2WiderTransfer473S0,d2WiderTransfer473Lo,d2WiderTransfer473Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer473C0 d2WiderTransfer473S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer473C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer473Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer473Arithmetic
  linarith
#print axioms d2WiderTransfer473Arithmetic
#print axioms d2WiderTransfer473Bound
def d2WiderTransfer474Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (2047) 1 (-11))
def d2WiderTransfer474Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer474Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (24087208286830028014839) 1 (-80))
def d2WiderTransfer474C0 : ℚ := (d2LitsNearWiderTransfers059.q2 (23) 25 (-5))
def d2WiderTransfer474S0 : ℚ := (d2LitsNearWiderTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer474Arithmetic : weightedUpper d2WiderTransfer474C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer474Cap := by decide +kernel
theorem d2WiderTransfer474Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer474Lo:ℚ):ℝ) ((d2WiderTransfer474Hi:ℚ):ℝ), ((d2WiderTransfer474C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer474S0:ℚ):ℝ)| ≤ ((d2WiderTransfer474Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer474S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer474S0,d2WiderTransfer474Lo,d2WiderTransfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer474C0 then |x-((d2WiderTransfer474S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer474S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer474S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer474S0,d2WiderTransfer474Lo,d2WiderTransfer474Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer474C0,d2Log178Q,d2WiderTransfer474S0,d2WiderTransfer474Lo,d2WiderTransfer474Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer474C0 d2WiderTransfer474S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer474C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer474Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer474Arithmetic
  linarith
#print axioms d2WiderTransfer474Arithmetic
#print axioms d2WiderTransfer474Bound
def d2WiderTransfer475Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer475Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (8191) 1 (-13))
def d2WiderTransfer475Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (15261957923005100557) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer475Arithmetic : (0 : ℚ) ≤ d2WiderTransfer475Cap := by decide +kernel
theorem d2WiderTransfer475Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer475Lo:ℚ):ℝ) ((d2WiderTransfer475Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer475Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer475Arithmetic
#print axioms d2WiderTransfer475Arithmetic
#print axioms d2WiderTransfer475Bound
def d2WiderTransfer476Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer476Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (8191) 1 (-13))
def d2WiderTransfer476Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (24089330586710400922125) 1 (-80))
def d2WiderTransfer476C0 : ℚ := (d2LitsNearWiderTransfers059.q2 (23) 25 (-5))
def d2WiderTransfer476S0 : ℚ := (d2LitsNearWiderTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer476Arithmetic : weightedUpper d2WiderTransfer476C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer476Cap := by decide +kernel
theorem d2WiderTransfer476Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer476Lo:ℚ):ℝ) ((d2WiderTransfer476Hi:ℚ):ℝ), ((d2WiderTransfer476C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer476S0:ℚ):ℝ)| ≤ ((d2WiderTransfer476Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer476S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer476S0,d2WiderTransfer476Lo,d2WiderTransfer476Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer476C0 then |x-((d2WiderTransfer476S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer476S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer476S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer476S0,d2WiderTransfer476Lo,d2WiderTransfer476Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer476C0,d2Log179Q,d2WiderTransfer476S0,d2WiderTransfer476Lo,d2WiderTransfer476Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer476C0 d2WiderTransfer476S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer476C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer476Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer476Arithmetic
  linarith
#print axioms d2WiderTransfer476Arithmetic
#print axioms d2WiderTransfer476Bound
def d2WiderTransfer477Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (4095) 1 (-12))
def d2WiderTransfer477Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (8191) 1 (-13))
def d2WiderTransfer477Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (24089329856634680078861) 1 (-80))
def d2WiderTransfer477C0 : ℚ := (d2LitsNearWiderTransfers059.q2 (23) 25 (-5))
def d2WiderTransfer477S0 : ℚ := (d2LitsNearWiderTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer477Arithmetic : weightedUpper d2WiderTransfer477C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer477Cap := by decide +kernel
theorem d2WiderTransfer477Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer477Lo:ℚ):ℝ) ((d2WiderTransfer477Hi:ℚ):ℝ), ((d2WiderTransfer477C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer477S0:ℚ):ℝ)| ≤ ((d2WiderTransfer477Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer477S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer477S0,d2WiderTransfer477Lo,d2WiderTransfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer477C0 then |x-((d2WiderTransfer477S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer477S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer477S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer477S0,d2WiderTransfer477Lo,d2WiderTransfer477Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer477C0,d2Log179Q,d2WiderTransfer477S0,d2WiderTransfer477Lo,d2WiderTransfer477Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer477C0 d2WiderTransfer477S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer477C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer477Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer477Arithmetic
  linarith
#print axioms d2WiderTransfer477Arithmetic
#print axioms d2WiderTransfer477Bound
def d2WiderTransfer478Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (8191) 1 (-13))
def d2WiderTransfer478Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (16383) 1 (-14))
def d2WiderTransfer478Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (1020168391498872575) 1 (-76))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer478Arithmetic : (0 : ℚ) ≤ d2WiderTransfer478Cap := by decide +kernel
theorem d2WiderTransfer478Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer478Lo:ℚ):ℝ) ((d2WiderTransfer478Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer478Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer478Arithmetic
#print axioms d2WiderTransfer478Arithmetic
#print axioms d2WiderTransfer478Bound
def d2WiderTransfer479Lo : ℚ := (d2LitsNearWiderTransfers059.q2 (8191) 1 (-13))
def d2WiderTransfer479Hi : ℚ := (d2LitsNearWiderTransfers059.q2 (16383) 1 (-14))
def d2WiderTransfer479Cap : ℚ := (d2LitsNearWiderTransfers059.q2 (1505649457690711111423) 1 (-76))
def d2WiderTransfer479C0 : ℚ := (d2LitsNearWiderTransfers059.q2 (23) 25 (-5))
def d2WiderTransfer479S0 : ℚ := (d2LitsNearWiderTransfers059.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer479Arithmetic : weightedUpper d2WiderTransfer479C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer479Cap := by decide +kernel
theorem d2WiderTransfer479Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer479Lo:ℚ):ℝ) ((d2WiderTransfer479Hi:ℚ):ℝ), ((d2WiderTransfer479C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer479S0:ℚ):ℝ)| ≤ ((d2WiderTransfer479Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer479S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer479S0,d2WiderTransfer479Lo,d2WiderTransfer479Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer479C0 then |x-((d2WiderTransfer479S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer479S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer479S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer479S0,d2WiderTransfer479Lo,d2WiderTransfer479Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers059.q2, d2LitsNearLogCache011.q2, d2WiderTransfer479C0,d2Log180Q,d2WiderTransfer479S0,d2WiderTransfer479Lo,d2WiderTransfer479Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer479C0 d2WiderTransfer479S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer479C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer479Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer479Arithmetic
  linarith
#print axioms d2WiderTransfer479Arithmetic
#print axioms d2WiderTransfer479Bound
end CatalanMeasure.GenD.Signed.Data.Cells

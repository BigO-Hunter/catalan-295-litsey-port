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
namespace d2LitsNearWiderTransfers051
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers051
open D72.LogTransfer
def d2WiderTransfer408Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (1023) 1 (-10))
def d2WiderTransfer408Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (2047) 1 (-11))
def d2WiderTransfer408Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (1047085424290199666955) 1 (-79))
def d2WiderTransfer408C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer408S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer408Arithmetic : weightedUpper d2WiderTransfer408C0 d2Log177Lo d2Log177Hi ≤ d2WiderTransfer408Cap := by decide +kernel
theorem d2WiderTransfer408Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer408Lo:ℚ):ℝ) ((d2WiderTransfer408Hi:ℚ):ℝ), ((d2WiderTransfer408C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer408S0:ℚ):ℝ)| ≤ ((d2WiderTransfer408Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer408S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer408S0,d2WiderTransfer408Lo,d2WiderTransfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer408C0 then |x-((d2WiderTransfer408S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer408S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer408S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer408S0,d2WiderTransfer408Lo,d2WiderTransfer408Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer408C0,d2Log177Q,d2WiderTransfer408S0,d2WiderTransfer408Lo,d2WiderTransfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer408C0 d2WiderTransfer408S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2WiderTransfer408C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer408Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer408Arithmetic
  linarith
#print axioms d2WiderTransfer408Arithmetic
#print axioms d2WiderTransfer408Bound
def d2WiderTransfer409Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (2047) 1 (-11))
def d2WiderTransfer409Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (4095) 1 (-12))
def d2WiderTransfer409Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (2094540269942628270903) 1 (-80))
def d2WiderTransfer409C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer409S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer409Arithmetic : weightedUpper d2WiderTransfer409C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer409Cap := by decide +kernel
theorem d2WiderTransfer409Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer409Lo:ℚ):ℝ) ((d2WiderTransfer409Hi:ℚ):ℝ), ((d2WiderTransfer409C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer409S0:ℚ):ℝ)| ≤ ((d2WiderTransfer409Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer409S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer409S0,d2WiderTransfer409Lo,d2WiderTransfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer409C0 then |x-((d2WiderTransfer409S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer409S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer409S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer409S0,d2WiderTransfer409Lo,d2WiderTransfer409Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer409C0,d2Log178Q,d2WiderTransfer409S0,d2WiderTransfer409Lo,d2WiderTransfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer409C0 d2WiderTransfer409S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer409C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer409Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer409Arithmetic
  linarith
#print axioms d2WiderTransfer409Arithmetic
#print axioms d2WiderTransfer409Bound
def d2WiderTransfer410Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (2047) 1 (-11))
def d2WiderTransfer410Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (4095) 1 (-12))
def d2WiderTransfer410Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (2094539851028698088247) 1 (-80))
def d2WiderTransfer410C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer410S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer410Arithmetic : weightedUpper d2WiderTransfer410C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer410Cap := by decide +kernel
theorem d2WiderTransfer410Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer410Lo:ℚ):ℝ) ((d2WiderTransfer410Hi:ℚ):ℝ), ((d2WiderTransfer410C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer410S0:ℚ):ℝ)| ≤ ((d2WiderTransfer410Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer410S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer410S0,d2WiderTransfer410Lo,d2WiderTransfer410Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer410C0 then |x-((d2WiderTransfer410S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer410S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer410S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer410S0,d2WiderTransfer410Lo,d2WiderTransfer410Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer410C0,d2Log178Q,d2WiderTransfer410S0,d2WiderTransfer410Lo,d2WiderTransfer410Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer410C0 d2WiderTransfer410S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer410C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer410Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer410Arithmetic
  linarith
#print axioms d2WiderTransfer410Arithmetic
#print axioms d2WiderTransfer410Bound
def d2WiderTransfer411Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (4095) 1 (-12))
def d2WiderTransfer411Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (8191) 1 (-13))
def d2WiderTransfer411Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (1047362377136733790409) 1 (-79))
def d2WiderTransfer411C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer411S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer411Arithmetic : weightedUpper d2WiderTransfer411C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer411Cap := by decide +kernel
theorem d2WiderTransfer411Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer411Lo:ℚ):ℝ) ((d2WiderTransfer411Hi:ℚ):ℝ), ((d2WiderTransfer411C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer411S0:ℚ):ℝ)| ≤ ((d2WiderTransfer411Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer411S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer411S0,d2WiderTransfer411Lo,d2WiderTransfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer411C0 then |x-((d2WiderTransfer411S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer411S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer411S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer411S0,d2WiderTransfer411Lo,d2WiderTransfer411Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer411C0,d2Log179Q,d2WiderTransfer411S0,d2WiderTransfer411Lo,d2WiderTransfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer411C0 d2WiderTransfer411S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer411C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer411Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer411Arithmetic
  linarith
#print axioms d2WiderTransfer411Arithmetic
#print axioms d2WiderTransfer411Bound
def d2WiderTransfer412Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (4095) 1 (-12))
def d2WiderTransfer412Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (8191) 1 (-13))
def d2WiderTransfer412Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (1047362167679768699081) 1 (-79))
def d2WiderTransfer412C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer412S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer412Arithmetic : weightedUpper d2WiderTransfer412C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer412Cap := by decide +kernel
theorem d2WiderTransfer412Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer412Lo:ℚ):ℝ) ((d2WiderTransfer412Hi:ℚ):ℝ), ((d2WiderTransfer412C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer412S0:ℚ):ℝ)| ≤ ((d2WiderTransfer412Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer412S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer412S0,d2WiderTransfer412Lo,d2WiderTransfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer412C0 then |x-((d2WiderTransfer412S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer412S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer412S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer412S0,d2WiderTransfer412Lo,d2WiderTransfer412Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer412C0,d2Log179Q,d2WiderTransfer412S0,d2WiderTransfer412Lo,d2WiderTransfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer412C0 d2WiderTransfer412S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer412C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer412Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer412Arithmetic
  linarith
#print axioms d2WiderTransfer412Arithmetic
#print axioms d2WiderTransfer412Bound
def d2WiderTransfer413Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (8191) 1 (-13))
def d2WiderTransfer413Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (16383) 1 (-14))
def d2WiderTransfer413Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (1047408496108080610437) 1 (-79))
def d2WiderTransfer413C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer413S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer413Arithmetic : weightedUpper d2WiderTransfer413C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer413Cap := by decide +kernel
theorem d2WiderTransfer413Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer413Lo:ℚ):ℝ) ((d2WiderTransfer413Hi:ℚ):ℝ), ((d2WiderTransfer413C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer413S0:ℚ):ℝ)| ≤ ((d2WiderTransfer413Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer413S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer413S0,d2WiderTransfer413Lo,d2WiderTransfer413Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer413C0 then |x-((d2WiderTransfer413S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer413S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer413S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer413S0,d2WiderTransfer413Lo,d2WiderTransfer413Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer413C0,d2Log180Q,d2WiderTransfer413S0,d2WiderTransfer413Lo,d2WiderTransfer413Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer413C0 d2WiderTransfer413S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer413C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer413Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer413Arithmetic
  linarith
#print axioms d2WiderTransfer413Arithmetic
#print axioms d2WiderTransfer413Bound
def d2WiderTransfer414Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (8191) 1 (-13))
def d2WiderTransfer414Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (16383) 1 (-14))
def d2WiderTransfer414Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (1047408286651115519109) 1 (-79))
def d2WiderTransfer414C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer414S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer414Arithmetic : weightedUpper d2WiderTransfer414C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer414Cap := by decide +kernel
theorem d2WiderTransfer414Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer414Lo:ℚ):ℝ) ((d2WiderTransfer414Hi:ℚ):ℝ), ((d2WiderTransfer414C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer414S0:ℚ):ℝ)| ≤ ((d2WiderTransfer414Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer414S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer414S0,d2WiderTransfer414Lo,d2WiderTransfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer414C0 then |x-((d2WiderTransfer414S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer414S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer414S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer414S0,d2WiderTransfer414Lo,d2WiderTransfer414Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer414C0,d2Log180Q,d2WiderTransfer414S0,d2WiderTransfer414Lo,d2WiderTransfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer414C0 d2WiderTransfer414S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer414C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer414Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer414Arithmetic
  linarith
#print axioms d2WiderTransfer414Arithmetic
#print axioms d2WiderTransfer414Bound
def d2WiderTransfer415Lo : ℚ := (d2LitsNearWiderTransfers051.q2 (16383) 1 (-14))
def d2WiderTransfer415Hi : ℚ := (d2LitsNearWiderTransfers051.q2 (32767) 1 (-15))
def d2WiderTransfer415Cap : ℚ := (d2LitsNearWiderTransfers051.q2 (2094863110131901712009) 1 (-80))
def d2WiderTransfer415C0 : ℚ := (d2LitsNearWiderTransfers051.q2 (1) 25 (-4))
def d2WiderTransfer415S0 : ℚ := (d2LitsNearWiderTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer415Arithmetic : weightedUpper d2WiderTransfer415C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer415Cap := by decide +kernel
theorem d2WiderTransfer415Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer415Lo:ℚ):ℝ) ((d2WiderTransfer415Hi:ℚ):ℝ), ((d2WiderTransfer415C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer415S0:ℚ):ℝ)| ≤ ((d2WiderTransfer415Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer415S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer415S0,d2WiderTransfer415Lo,d2WiderTransfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer415C0 then |x-((d2WiderTransfer415S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer415S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer415S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer415S0,d2WiderTransfer415Lo,d2WiderTransfer415Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers051.q2, d2LitsNearLogCache011.q2, d2WiderTransfer415C0,d2Log181Q,d2WiderTransfer415S0,d2WiderTransfer415Lo,d2WiderTransfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer415C0 d2WiderTransfer415S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer415C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer415Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer415Arithmetic
  linarith
#print axioms d2WiderTransfer415Arithmetic
#print axioms d2WiderTransfer415Bound
end CatalanMeasure.GenD.Signed.Data.Cells

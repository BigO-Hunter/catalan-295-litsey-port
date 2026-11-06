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
namespace d2LitsNearWiderTransfers061
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers061
open D72.LogTransfer
def d2WiderTransfer488Lo : ℚ := (d2LitsNearWiderTransfers061.q2 (65535) 1 (-16))
def d2WiderTransfer488Hi : ℚ := (d2LitsNearWiderTransfers061.q2 (131071) 1 (-17))
def d2WiderTransfer488Cap : ℚ := (d2LitsNearWiderTransfers061.q2 (24091319440794838426293) 1 (-80))
def d2WiderTransfer488C0 : ℚ := (d2LitsNearWiderTransfers061.q2 (23) 25 (-5))
def d2WiderTransfer488S0 : ℚ := (d2LitsNearWiderTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer488Arithmetic : weightedUpper d2WiderTransfer488C0 d2Log183Lo d2Log183Hi ≤ d2WiderTransfer488Cap := by decide +kernel
theorem d2WiderTransfer488Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer488Lo:ℚ):ℝ) ((d2WiderTransfer488Hi:ℚ):ℝ), ((d2WiderTransfer488C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer488S0:ℚ):ℝ)| ≤ ((d2WiderTransfer488Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer488S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer488S0,d2WiderTransfer488Lo,d2WiderTransfer488Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer488C0 then |x-((d2WiderTransfer488S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer488S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer488S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer488S0,d2WiderTransfer488Lo,d2WiderTransfer488Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer488C0,d2Log183Q,d2WiderTransfer488S0,d2WiderTransfer488Lo,d2WiderTransfer488Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer488C0 d2WiderTransfer488S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2WiderTransfer488C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer488Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer488Arithmetic
  linarith
#print axioms d2WiderTransfer488Arithmetic
#print axioms d2WiderTransfer488Bound
def d2WiderTransfer489Lo : ℚ := (d2LitsNearWiderTransfers061.q2 (65535) 1 (-16))
def d2WiderTransfer489Hi : ℚ := (d2LitsNearWiderTransfers061.q2 (131071) 1 (-17))
def d2WiderTransfer489Cap : ℚ := (d2LitsNearWiderTransfers061.q2 (24091318710719117583029) 1 (-80))
def d2WiderTransfer489C0 : ℚ := (d2LitsNearWiderTransfers061.q2 (23) 25 (-5))
def d2WiderTransfer489S0 : ℚ := (d2LitsNearWiderTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer489Arithmetic : weightedUpper d2WiderTransfer489C0 d2Log183Lo d2Log183Hi ≤ d2WiderTransfer489Cap := by decide +kernel
theorem d2WiderTransfer489Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer489Lo:ℚ):ℝ) ((d2WiderTransfer489Hi:ℚ):ℝ), ((d2WiderTransfer489C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer489S0:ℚ):ℝ)| ≤ ((d2WiderTransfer489Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer489S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer489S0,d2WiderTransfer489Lo,d2WiderTransfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer489C0 then |x-((d2WiderTransfer489S0:ℚ):ℝ)| ≤ ((d2Log183Q:ℚ):ℝ) else ((d2Log183Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer489S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer489S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer489S0,d2WiderTransfer489Lo,d2WiderTransfer489Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer489C0,d2Log183Q,d2WiderTransfer489S0,d2WiderTransfer489Lo,d2WiderTransfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer489C0 d2WiderTransfer489S0 d2Log183Q d2Log183Lo d2Log183Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log183Bounds
  have har : (((weightedUpper d2WiderTransfer489C0 d2Log183Lo d2Log183Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer489Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer489Arithmetic
  linarith
#print axioms d2WiderTransfer489Arithmetic
#print axioms d2WiderTransfer489Bound
def d2WiderTransfer490Lo : ℚ := (d2LitsNearWiderTransfers061.q2 (131071) 1 (-17))
def d2WiderTransfer490Hi : ℚ := (d2LitsNearWiderTransfers061.q2 (1) 1 (0))
def d2WiderTransfer490Cap : ℚ := (d2LitsNearWiderTransfers061.q2 (4345849558340177411) 1 (-78))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer490Arithmetic : (0 : ℚ) ≤ d2WiderTransfer490Cap := by decide +kernel
theorem d2WiderTransfer490Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer490Lo:ℚ):ℝ) ((d2WiderTransfer490Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2WiderTransfer490Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2WiderTransfer490Arithmetic
#print axioms d2WiderTransfer490Arithmetic
#print axioms d2WiderTransfer490Bound
def d2WiderTransfer491Lo : ℚ := (d2LitsNearWiderTransfers061.q2 (131071) 1 (-17))
def d2WiderTransfer491Hi : ℚ := (d2LitsNearWiderTransfers061.q2 (1) 1 (0))
def d2WiderTransfer491Cap : ℚ := (d2LitsNearWiderTransfers061.q2 (6022863006755189132803) 1 (-78))
def d2WiderTransfer491C0 : ℚ := (d2LitsNearWiderTransfers061.q2 (23) 25 (-5))
def d2WiderTransfer491S0 : ℚ := (d2LitsNearWiderTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer491Arithmetic : weightedUpper d2WiderTransfer491C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer491Cap := by decide +kernel
theorem d2WiderTransfer491Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer491Lo:ℚ):ℝ) ((d2WiderTransfer491Hi:ℚ):ℝ), ((d2WiderTransfer491C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer491S0:ℚ):ℝ)| ≤ ((d2WiderTransfer491Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer491S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer491S0,d2WiderTransfer491Lo,d2WiderTransfer491Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer491C0 then |x-((d2WiderTransfer491S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer491S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer491S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer491S0,d2WiderTransfer491Lo,d2WiderTransfer491Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer491C0,d2Log186Q,d2WiderTransfer491S0,d2WiderTransfer491Lo,d2WiderTransfer491Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer491C0 d2WiderTransfer491S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer491C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer491Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer491Arithmetic
  linarith
#print axioms d2WiderTransfer491Arithmetic
#print axioms d2WiderTransfer491Bound
def d2WiderTransfer492Lo : ℚ := (d2LitsNearWiderTransfers061.q2 (131071) 1 (-17))
def d2WiderTransfer492Hi : ℚ := (d2LitsNearWiderTransfers061.q2 (1) 1 (0))
def d2WiderTransfer492Cap : ℚ := (d2LitsNearWiderTransfers061.q2 (6022862824236258921987) 1 (-78))
def d2WiderTransfer492C0 : ℚ := (d2LitsNearWiderTransfers061.q2 (23) 25 (-5))
def d2WiderTransfer492S0 : ℚ := (d2LitsNearWiderTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer492Arithmetic : weightedUpper d2WiderTransfer492C0 d2Log186Lo d2Log186Hi ≤ d2WiderTransfer492Cap := by decide +kernel
theorem d2WiderTransfer492Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer492Lo:ℚ):ℝ) ((d2WiderTransfer492Hi:ℚ):ℝ), ((d2WiderTransfer492C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer492S0:ℚ):ℝ)| ≤ ((d2WiderTransfer492Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer492S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer492S0,d2WiderTransfer492Lo,d2WiderTransfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer492C0 then |x-((d2WiderTransfer492S0:ℚ):ℝ)| ≤ ((d2Log186Q:ℚ):ℝ) else ((d2Log186Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer492S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer492S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer492S0,d2WiderTransfer492Lo,d2WiderTransfer492Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers061.q2, d2LitsNearLogCache011.q2, d2WiderTransfer492C0,d2Log186Q,d2WiderTransfer492S0,d2WiderTransfer492Lo,d2WiderTransfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer492C0 d2WiderTransfer492S0 d2Log186Q d2Log186Lo d2Log186Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log186Bounds
  have har : (((weightedUpper d2WiderTransfer492C0 d2Log186Lo d2Log186Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer492Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer492Arithmetic
  linarith
#print axioms d2WiderTransfer492Arithmetic
#print axioms d2WiderTransfer492Bound
end CatalanMeasure.GenD.Signed.Data.Cells

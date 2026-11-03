module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers033
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers033
open D72.LogTransfer
def d2WiderTransfer264Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (3334455) 1 (-24))
def d2WiderTransfer264Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (313261) 1 (-20))
def d2WiderTransfer264Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (30439539927) 1 (-40))
def d2WiderTransfer264C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (3) 275 (-5))
def d2WiderTransfer264S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer264C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-5) 11 (-4))
def d2WiderTransfer264S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer264Arithmetic : weightedUpper d2WiderTransfer264C0 d2Log113Lo d2Log113Hi + weightedUpper d2WiderTransfer264C1 d2Log61Lo d2Log61Hi ≤ d2WiderTransfer264Cap := by decide +kernel
theorem d2WiderTransfer264Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer264Lo:ℚ):ℝ) ((d2WiderTransfer264Hi:ℚ):ℝ), ((d2WiderTransfer264C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer264S0:ℚ):ℝ)| + ((d2WiderTransfer264C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer264S1:ℚ):ℝ)| ≤ ((d2WiderTransfer264Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer264S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264S0,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer264C0 then |x-((d2WiderTransfer264S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer264S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer264S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264S0,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264C0,d2Log113Q,d2WiderTransfer264S0,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer264C0 d2WiderTransfer264S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2WiderTransfer264S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264S1,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer264C1 then |x-((d2WiderTransfer264S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer264S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer264S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264S1,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer264C1,d2Log61Q,d2WiderTransfer264S1,d2WiderTransfer264Lo,d2WiderTransfer264Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer264C1 d2WiderTransfer264S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2WiderTransfer264C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer264C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer264Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer264Arithmetic
  linarith
#print axioms d2WiderTransfer264Arithmetic
#print axioms d2WiderTransfer264Bound
def d2WiderTransfer265Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (313261) 1 (-20))
def d2WiderTransfer265Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer265Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (1169469059) 1 (-40))
def d2WiderTransfer265C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer265S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer265C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer265S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer265Arithmetic : weightedUpper d2WiderTransfer265C0 d2Log113Lo d2Log113Hi + weightedUpper d2WiderTransfer265C1 d2Log57Lo d2Log57Hi ≤ d2WiderTransfer265Cap := by decide +kernel
theorem d2WiderTransfer265Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer265Lo:ℚ):ℝ) ((d2WiderTransfer265Hi:ℚ):ℝ), ((d2WiderTransfer265C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer265S0:ℚ):ℝ)| + ((d2WiderTransfer265C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer265S1:ℚ):ℝ)| ≤ ((d2WiderTransfer265Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer265S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265S0,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer265C0 then |x-((d2WiderTransfer265S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer265S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer265S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265S0,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265C0,d2Log113Q,d2WiderTransfer265S0,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer265C0 d2WiderTransfer265S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2WiderTransfer265S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265S1,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer265C1 then |x-((d2WiderTransfer265S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer265S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer265S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265S1,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer265C1,d2Log57Q,d2WiderTransfer265S1,d2WiderTransfer265Lo,d2WiderTransfer265Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer265C1 d2WiderTransfer265S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2WiderTransfer265C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer265C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer265Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer265Arithmetic
  linarith
#print axioms d2WiderTransfer265Arithmetic
#print axioms d2WiderTransfer265Bound
def d2WiderTransfer266Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (313261) 1 (-20))
def d2WiderTransfer266Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer266Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (15113656175) 1 (-40))
def d2WiderTransfer266C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (23) 25 (-5))
def d2WiderTransfer266S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer266Arithmetic : weightedUpper d2WiderTransfer266C0 d2Log117Lo d2Log117Hi ≤ d2WiderTransfer266Cap := by decide +kernel
theorem d2WiderTransfer266Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer266Lo:ℚ):ℝ) ((d2WiderTransfer266Hi:ℚ):ℝ), ((d2WiderTransfer266C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer266S0:ℚ):ℝ)| ≤ ((d2WiderTransfer266Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer266S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer266S0,d2WiderTransfer266Lo,d2WiderTransfer266Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer266C0 then |x-((d2WiderTransfer266S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer266S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer266S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer266S0,d2WiderTransfer266Lo,d2WiderTransfer266Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer266C0,d2Log117Q,d2WiderTransfer266S0,d2WiderTransfer266Lo,d2WiderTransfer266Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer266C0 d2WiderTransfer266S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2WiderTransfer266C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer266Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer266Arithmetic
  linarith
#print axioms d2WiderTransfer266Arithmetic
#print axioms d2WiderTransfer266Bound
def d2WiderTransfer267Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (313261) 1 (-20))
def d2WiderTransfer267Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer267Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (30439539927) 1 (-40))
def d2WiderTransfer267C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (3) 275 (-5))
def d2WiderTransfer267S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer267C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-5) 11 (-4))
def d2WiderTransfer267S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer267Arithmetic : weightedUpper d2WiderTransfer267C0 d2Log117Lo d2Log117Hi + weightedUpper d2WiderTransfer267C1 d2Log57Lo d2Log57Hi ≤ d2WiderTransfer267Cap := by decide +kernel
theorem d2WiderTransfer267Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer267Lo:ℚ):ℝ) ((d2WiderTransfer267Hi:ℚ):ℝ), ((d2WiderTransfer267C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer267S0:ℚ):ℝ)| + ((d2WiderTransfer267C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer267S1:ℚ):ℝ)| ≤ ((d2WiderTransfer267Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer267S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267S0,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer267C0 then |x-((d2WiderTransfer267S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer267S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer267S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267S0,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267C0,d2Log117Q,d2WiderTransfer267S0,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer267C0 d2WiderTransfer267S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2WiderTransfer267S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267S1,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer267C1 then |x-((d2WiderTransfer267S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer267S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer267S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267S1,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer267C1,d2Log57Q,d2WiderTransfer267S1,d2WiderTransfer267Lo,d2WiderTransfer267Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer267C1 d2WiderTransfer267S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2WiderTransfer267C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer267C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer267Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer267Arithmetic
  linarith
#print axioms d2WiderTransfer267Arithmetic
#print axioms d2WiderTransfer267Bound
def d2WiderTransfer268Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer268Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (4183809) 1 (-23))
def d2WiderTransfer268Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (1169469059) 1 (-40))
def d2WiderTransfer268C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer268S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer268C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer268S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer268Arithmetic : weightedUpper d2WiderTransfer268C0 d2Log117Lo d2Log117Hi + weightedUpper d2WiderTransfer268C1 d2Log54Lo d2Log54Hi ≤ d2WiderTransfer268Cap := by decide +kernel
theorem d2WiderTransfer268Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer268Lo:ℚ):ℝ) ((d2WiderTransfer268Hi:ℚ):ℝ), ((d2WiderTransfer268C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer268S0:ℚ):ℝ)| + ((d2WiderTransfer268C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer268S1:ℚ):ℝ)| ≤ ((d2WiderTransfer268Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer268S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268S0,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer268C0 then |x-((d2WiderTransfer268S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer268S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer268S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268S0,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268C0,d2Log117Q,d2WiderTransfer268S0,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer268C0 d2WiderTransfer268S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2WiderTransfer268S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268S1,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer268C1 then |x-((d2WiderTransfer268S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer268S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer268S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268S1,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer268C1,d2Log54Q,d2WiderTransfer268S1,d2WiderTransfer268Lo,d2WiderTransfer268Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer268C1 d2WiderTransfer268S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2WiderTransfer268C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer268C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer268Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer268Arithmetic
  linarith
#print axioms d2WiderTransfer268Arithmetic
#print axioms d2WiderTransfer268Bound
def d2WiderTransfer269Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer269Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (4183809) 1 (-23))
def d2WiderTransfer269Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (15113656175) 1 (-40))
def d2WiderTransfer269C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (23) 25 (-5))
def d2WiderTransfer269S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer269Arithmetic : weightedUpper d2WiderTransfer269C0 d2Log120Lo d2Log120Hi ≤ d2WiderTransfer269Cap := by decide +kernel
theorem d2WiderTransfer269Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer269Lo:ℚ):ℝ) ((d2WiderTransfer269Hi:ℚ):ℝ), ((d2WiderTransfer269C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer269S0:ℚ):ℝ)| ≤ ((d2WiderTransfer269Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer269S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer269S0,d2WiderTransfer269Lo,d2WiderTransfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer269C0 then |x-((d2WiderTransfer269S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer269S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer269S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer269S0,d2WiderTransfer269Lo,d2WiderTransfer269Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer269C0,d2Log120Q,d2WiderTransfer269S0,d2WiderTransfer269Lo,d2WiderTransfer269Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer269C0 d2WiderTransfer269S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2WiderTransfer269C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer269Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer269Arithmetic
  linarith
#print axioms d2WiderTransfer269Arithmetic
#print axioms d2WiderTransfer269Bound
def d2WiderTransfer270Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (6689897) 1 (-24))
def d2WiderTransfer270Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (4183809) 1 (-23))
def d2WiderTransfer270Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (30439539927) 1 (-40))
def d2WiderTransfer270C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (3) 275 (-5))
def d2WiderTransfer270S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer270C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-5) 11 (-4))
def d2WiderTransfer270S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer270Arithmetic : weightedUpper d2WiderTransfer270C0 d2Log120Lo d2Log120Hi + weightedUpper d2WiderTransfer270C1 d2Log54Lo d2Log54Hi ≤ d2WiderTransfer270Cap := by decide +kernel
theorem d2WiderTransfer270Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer270Lo:ℚ):ℝ) ((d2WiderTransfer270Hi:ℚ):ℝ), ((d2WiderTransfer270C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer270S0:ℚ):ℝ)| + ((d2WiderTransfer270C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer270S1:ℚ):ℝ)| ≤ ((d2WiderTransfer270Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer270S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270S0,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer270C0 then |x-((d2WiderTransfer270S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer270S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer270S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270S0,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270C0,d2Log120Q,d2WiderTransfer270S0,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer270C0 d2WiderTransfer270S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2WiderTransfer270S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270S1,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer270C1 then |x-((d2WiderTransfer270S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer270S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer270S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270S1,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer270C1,d2Log54Q,d2WiderTransfer270S1,d2WiderTransfer270Lo,d2WiderTransfer270Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer270C1 d2WiderTransfer270S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2WiderTransfer270C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer270C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer270Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer270Arithmetic
  linarith
#print axioms d2WiderTransfer270Arithmetic
#print axioms d2WiderTransfer270Bound
def d2WiderTransfer271Lo : ℚ := (d2LitsNearWiderTransfers033.q2 (4183809) 1 (-23))
def d2WiderTransfer271Hi : ℚ := (d2LitsNearWiderTransfers033.q2 (18412957) 1 (-25))
def d2WiderTransfer271Cap : ℚ := (d2LitsNearWiderTransfers033.q2 (1169469059) 1 (-40))
def d2WiderTransfer271C0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer271S0 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 1 (0))
def d2WiderTransfer271C1 : ℚ := (d2LitsNearWiderTransfers033.q2 (-1) 55 (-3))
def d2WiderTransfer271S1 : ℚ := (d2LitsNearWiderTransfers033.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer271Arithmetic : weightedUpper d2WiderTransfer271C0 d2Log120Lo d2Log120Hi + weightedUpper d2WiderTransfer271C1 d2Log53Lo d2Log53Hi ≤ d2WiderTransfer271Cap := by decide +kernel
theorem d2WiderTransfer271Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer271Lo:ℚ):ℝ) ((d2WiderTransfer271Hi:ℚ):ℝ), ((d2WiderTransfer271C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer271S0:ℚ):ℝ)| + ((d2WiderTransfer271C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer271S1:ℚ):ℝ)| ≤ ((d2WiderTransfer271Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer271S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271S0,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer271C0 then |x-((d2WiderTransfer271S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer271S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer271S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271S0,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271C0,d2Log120Q,d2WiderTransfer271S0,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer271C0 d2WiderTransfer271S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2WiderTransfer271S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271S1,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer271C1 then |x-((d2WiderTransfer271S1:ℚ):ℝ)| ≤ ((d2Log53Q:ℚ):ℝ) else ((d2Log53Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer271S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer271S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271S1,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers033.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer271C1,d2Log53Q,d2WiderTransfer271S1,d2WiderTransfer271Lo,d2WiderTransfer271Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer271C1 d2WiderTransfer271S1 d2Log53Q d2Log53Lo d2Log53Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log53Bounds
  have har : (((weightedUpper d2WiderTransfer271C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer271C1 d2Log53Lo d2Log53Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer271Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer271Arithmetic
  linarith
#print axioms d2WiderTransfer271Arithmetic
#print axioms d2WiderTransfer271Bound
end CatalanMeasure.GenD.Signed.Data.Cells

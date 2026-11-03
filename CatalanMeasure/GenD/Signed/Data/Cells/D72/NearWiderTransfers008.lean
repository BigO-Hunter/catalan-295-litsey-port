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
namespace d2LitsNearWiderTransfers008
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers008
open D72.LogTransfer
def d2WiderTransfer64Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (3334455) 1 (-24))
def d2WiderTransfer64Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer64Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (16281318465) 1 (-40))
def d2WiderTransfer64C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (-5))
def d2WiderTransfer64S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer64Arithmetic : weightedUpper d2WiderTransfer64C0 d2Log113Lo d2Log113Hi ≤ d2WiderTransfer64Cap := by decide +kernel
theorem d2WiderTransfer64Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer64Lo:ℚ):ℝ) ((d2WiderTransfer64Hi:ℚ):ℝ), ((d2WiderTransfer64C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer64S0:ℚ):ℝ)| ≤ ((d2WiderTransfer64Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer64S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer64S0,d2WiderTransfer64Lo,d2WiderTransfer64Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer64C0 then |x-((d2WiderTransfer64S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer64S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer64S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer64S0,d2WiderTransfer64Lo,d2WiderTransfer64Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer64C0,d2Log113Q,d2WiderTransfer64S0,d2WiderTransfer64Lo,d2WiderTransfer64Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer64C0 d2WiderTransfer64S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2WiderTransfer64C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer64Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer64Arithmetic
  linarith
#print axioms d2WiderTransfer64Arithmetic
#print axioms d2WiderTransfer64Bound
def d2WiderTransfer65Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (3334455) 1 (-24))
def d2WiderTransfer65Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer65Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (31165051305) 1 (-40))
def d2WiderTransfer65C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 11 (-5))
def d2WiderTransfer65S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
def d2WiderTransfer65C1 : ℚ := (d2LitsNearWiderTransfers008.q2 (-5) 11 (-4))
def d2WiderTransfer65S1 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer65Arithmetic : weightedUpper d2WiderTransfer65C0 d2Log113Lo d2Log113Hi + weightedUpper d2WiderTransfer65C1 d2Log61Lo d2Log61Hi ≤ d2WiderTransfer65Cap := by decide +kernel
theorem d2WiderTransfer65Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer65Lo:ℚ):ℝ) ((d2WiderTransfer65Hi:ℚ):ℝ), ((d2WiderTransfer65C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer65S0:ℚ):ℝ)| + ((d2WiderTransfer65C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer65S1:ℚ):ℝ)| ≤ ((d2WiderTransfer65Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer65S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65S0,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer65C0 then |x-((d2WiderTransfer65S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer65S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer65S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65S0,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65C0,d2Log113Q,d2WiderTransfer65S0,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer65C0 d2WiderTransfer65S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2WiderTransfer65S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65S1,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer65C1 then |x-((d2WiderTransfer65S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer65S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer65S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65S1,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer65C1,d2Log61Q,d2WiderTransfer65S1,d2WiderTransfer65Lo,d2WiderTransfer65Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer65C1 d2WiderTransfer65S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2WiderTransfer65C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer65C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer65Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer65Arithmetic
  linarith
#print axioms d2WiderTransfer65Arithmetic
#print axioms d2WiderTransfer65Bound
def d2WiderTransfer66Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer66Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer66Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (649441385) 1 (-39))
def d2WiderTransfer66C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 25 (-4))
def d2WiderTransfer66S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer66Arithmetic : weightedUpper d2WiderTransfer66C0 d2Log117Lo d2Log117Hi ≤ d2WiderTransfer66Cap := by decide +kernel
theorem d2WiderTransfer66Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer66Lo:ℚ):ℝ) ((d2WiderTransfer66Hi:ℚ):ℝ), ((d2WiderTransfer66C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer66S0:ℚ):ℝ)| ≤ ((d2WiderTransfer66Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer66S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer66S0,d2WiderTransfer66Lo,d2WiderTransfer66Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer66C0 then |x-((d2WiderTransfer66S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer66S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer66S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer66S0,d2WiderTransfer66Lo,d2WiderTransfer66Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer66C0,d2Log117Q,d2WiderTransfer66S0,d2WiderTransfer66Lo,d2WiderTransfer66Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer66C0 d2WiderTransfer66S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2WiderTransfer66C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer66Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer66Arithmetic
  linarith
#print axioms d2WiderTransfer66Arithmetic
#print axioms d2WiderTransfer66Bound
def d2WiderTransfer67Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer67Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer67Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (2436024149) 1 (-40))
def d2WiderTransfer67C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 275 (-4))
def d2WiderTransfer67S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
def d2WiderTransfer67C1 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 55 (-3))
def d2WiderTransfer67S1 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer67Arithmetic : weightedUpper d2WiderTransfer67C0 d2Log117Lo d2Log117Hi + weightedUpper d2WiderTransfer67C1 d2Log57Lo d2Log57Hi ≤ d2WiderTransfer67Cap := by decide +kernel
theorem d2WiderTransfer67Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer67Lo:ℚ):ℝ) ((d2WiderTransfer67Hi:ℚ):ℝ), ((d2WiderTransfer67C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer67S0:ℚ):ℝ)| + ((d2WiderTransfer67C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer67S1:ℚ):ℝ)| ≤ ((d2WiderTransfer67Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer67S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67S0,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer67C0 then |x-((d2WiderTransfer67S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer67S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer67S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67S0,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67C0,d2Log117Q,d2WiderTransfer67S0,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer67C0 d2WiderTransfer67S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2WiderTransfer67S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67S1,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer67C1 then |x-((d2WiderTransfer67S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer67S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer67S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67S1,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer67C1,d2Log57Q,d2WiderTransfer67S1,d2WiderTransfer67Lo,d2WiderTransfer67Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer67C1 d2WiderTransfer67S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2WiderTransfer67C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer67C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer67Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer67Arithmetic
  linarith
#print axioms d2WiderTransfer67Arithmetic
#print axioms d2WiderTransfer67Bound
def d2WiderTransfer68Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer68Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer68Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (16281318465) 1 (-40))
def d2WiderTransfer68C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (-5))
def d2WiderTransfer68S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer68Arithmetic : weightedUpper d2WiderTransfer68C0 d2Log117Lo d2Log117Hi ≤ d2WiderTransfer68Cap := by decide +kernel
theorem d2WiderTransfer68Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer68Lo:ℚ):ℝ) ((d2WiderTransfer68Hi:ℚ):ℝ), ((d2WiderTransfer68C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer68S0:ℚ):ℝ)| ≤ ((d2WiderTransfer68Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer68S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer68S0,d2WiderTransfer68Lo,d2WiderTransfer68Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer68C0 then |x-((d2WiderTransfer68S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer68S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer68S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer68S0,d2WiderTransfer68Lo,d2WiderTransfer68Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer68C0,d2Log117Q,d2WiderTransfer68S0,d2WiderTransfer68Lo,d2WiderTransfer68Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer68C0 d2WiderTransfer68S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have har : (((weightedUpper d2WiderTransfer68C0 d2Log117Lo d2Log117Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer68Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer68Arithmetic
  linarith
#print axioms d2WiderTransfer68Arithmetic
#print axioms d2WiderTransfer68Bound
def d2WiderTransfer69Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (313261) 1 (-20))
def d2WiderTransfer69Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer69Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (31165051305) 1 (-40))
def d2WiderTransfer69C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 11 (-5))
def d2WiderTransfer69S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
def d2WiderTransfer69C1 : ℚ := (d2LitsNearWiderTransfers008.q2 (-5) 11 (-4))
def d2WiderTransfer69S1 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer69Arithmetic : weightedUpper d2WiderTransfer69C0 d2Log117Lo d2Log117Hi + weightedUpper d2WiderTransfer69C1 d2Log57Lo d2Log57Hi ≤ d2WiderTransfer69Cap := by decide +kernel
theorem d2WiderTransfer69Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer69Lo:ℚ):ℝ) ((d2WiderTransfer69Hi:ℚ):ℝ), ((d2WiderTransfer69C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer69S0:ℚ):ℝ)| + ((d2WiderTransfer69C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer69S1:ℚ):ℝ)| ≤ ((d2WiderTransfer69Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer69S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69S0,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer69C0 then |x-((d2WiderTransfer69S0:ℚ):ℝ)| ≤ ((d2Log117Q:ℚ):ℝ) else ((d2Log117Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer69S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer69S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69S0,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69C0,d2Log117Q,d2WiderTransfer69S0,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer69C0 d2WiderTransfer69S0 d2Log117Q d2Log117Lo d2Log117Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log117Bounds
  have hn1 : x-((d2WiderTransfer69S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69S1,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer69C1 then |x-((d2WiderTransfer69S1:ℚ):ℝ)| ≤ ((d2Log57Q:ℚ):ℝ) else ((d2Log57Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer69S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer69S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69S1,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer69C1,d2Log57Q,d2WiderTransfer69S1,d2WiderTransfer69Lo,d2WiderTransfer69Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer69C1 d2WiderTransfer69S1 d2Log57Q d2Log57Lo d2Log57Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log57Bounds
  have har : (((weightedUpper d2WiderTransfer69C0 d2Log117Lo d2Log117Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer69C1 d2Log57Lo d2Log57Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer69Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer69Arithmetic
  linarith
#print axioms d2WiderTransfer69Arithmetic
#print axioms d2WiderTransfer69Bound
def d2WiderTransfer70Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer70Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (4183809) 1 (-23))
def d2WiderTransfer70Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (649441385) 1 (-39))
def d2WiderTransfer70C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 25 (-4))
def d2WiderTransfer70S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer70Arithmetic : weightedUpper d2WiderTransfer70C0 d2Log120Lo d2Log120Hi ≤ d2WiderTransfer70Cap := by decide +kernel
theorem d2WiderTransfer70Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer70Lo:ℚ):ℝ) ((d2WiderTransfer70Hi:ℚ):ℝ), ((d2WiderTransfer70C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer70S0:ℚ):ℝ)| ≤ ((d2WiderTransfer70Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer70S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer70S0,d2WiderTransfer70Lo,d2WiderTransfer70Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer70C0 then |x-((d2WiderTransfer70S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer70S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer70S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer70S0,d2WiderTransfer70Lo,d2WiderTransfer70Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer70C0,d2Log120Q,d2WiderTransfer70S0,d2WiderTransfer70Lo,d2WiderTransfer70Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer70C0 d2WiderTransfer70S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have har : (((weightedUpper d2WiderTransfer70C0 d2Log120Lo d2Log120Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer70Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer70Arithmetic
  linarith
#print axioms d2WiderTransfer70Arithmetic
#print axioms d2WiderTransfer70Bound
def d2WiderTransfer71Lo : ℚ := (d2LitsNearWiderTransfers008.q2 (6689897) 1 (-24))
def d2WiderTransfer71Hi : ℚ := (d2LitsNearWiderTransfers008.q2 (4183809) 1 (-23))
def d2WiderTransfer71Cap : ℚ := (d2LitsNearWiderTransfers008.q2 (2436024149) 1 (-40))
def d2WiderTransfer71C0 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 275 (-4))
def d2WiderTransfer71S0 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 1 (0))
def d2WiderTransfer71C1 : ℚ := (d2LitsNearWiderTransfers008.q2 (-1) 55 (-3))
def d2WiderTransfer71S1 : ℚ := (d2LitsNearWiderTransfers008.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer71Arithmetic : weightedUpper d2WiderTransfer71C0 d2Log120Lo d2Log120Hi + weightedUpper d2WiderTransfer71C1 d2Log54Lo d2Log54Hi ≤ d2WiderTransfer71Cap := by decide +kernel
theorem d2WiderTransfer71Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer71Lo:ℚ):ℝ) ((d2WiderTransfer71Hi:ℚ):ℝ), ((d2WiderTransfer71C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer71S0:ℚ):ℝ)| + ((d2WiderTransfer71C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer71S1:ℚ):ℝ)| ≤ ((d2WiderTransfer71Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer71S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71S0,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer71C0 then |x-((d2WiderTransfer71S0:ℚ):ℝ)| ≤ ((d2Log120Q:ℚ):ℝ) else ((d2Log120Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer71S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer71S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71S0,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71C0,d2Log120Q,d2WiderTransfer71S0,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer71C0 d2WiderTransfer71S0 d2Log120Q d2Log120Lo d2Log120Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log120Bounds
  have hn1 : x-((d2WiderTransfer71S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71S1,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer71C1 then |x-((d2WiderTransfer71S1:ℚ):ℝ)| ≤ ((d2Log54Q:ℚ):ℝ) else ((d2Log54Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer71S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer71S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71S1,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers008.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2WiderTransfer71C1,d2Log54Q,d2WiderTransfer71S1,d2WiderTransfer71Lo,d2WiderTransfer71Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer71C1 d2WiderTransfer71S1 d2Log54Q d2Log54Lo d2Log54Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log54Bounds
  have har : (((weightedUpper d2WiderTransfer71C0 d2Log120Lo d2Log120Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer71C1 d2Log54Lo d2Log54Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer71Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer71Arithmetic
  linarith
#print axioms d2WiderTransfer71Arithmetic
#print axioms d2WiderTransfer71Bound
end CatalanMeasure.GenD.Signed.Data.Cells

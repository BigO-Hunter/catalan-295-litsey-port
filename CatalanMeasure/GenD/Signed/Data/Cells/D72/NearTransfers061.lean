module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers061
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers061
open D72.LogTransfer
def d2Transfer488Lo : ℚ := (d2LitsNearTransfers061.q2 (38503635) 1 (-26))
def d2Transfer488Hi : ℚ := (d2LitsNearTransfers061.q2 (10045339) 1 (-24))
def d2Transfer488Cap : ℚ := (d2LitsNearTransfers061.q2 (15113656175) 1 (-40))
def d2Transfer488C0 : ℚ := (d2LitsNearTransfers061.q2 (23) 25 (-5))
def d2Transfer488S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer488Arithmetic : weightedUpper d2Transfer488C0 d2Log124Lo d2Log124Hi ≤ d2Transfer488Cap := by decide +kernel
theorem d2Transfer488Bound : ∀ x ∈ Set.Icc ((d2Transfer488Lo:ℚ):ℝ) ((d2Transfer488Hi:ℚ):ℝ), ((d2Transfer488C0:ℚ):ℝ)*Real.log |x-((d2Transfer488S0:ℚ):ℝ)| ≤ ((d2Transfer488Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer488S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer488S0,d2Transfer488Lo,d2Transfer488Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer488C0 then |x-((d2Transfer488S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer488S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer488S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer488S0,d2Transfer488Lo,d2Transfer488Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer488C0,d2Log124Q,d2Transfer488S0,d2Transfer488Lo,d2Transfer488Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer488C0 d2Transfer488S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have har : (((weightedUpper d2Transfer488C0 d2Log124Lo d2Log124Hi:ℚ):ℝ)) ≤ ((d2Transfer488Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer488Arithmetic
  linarith
#print axioms d2Transfer488Arithmetic
#print axioms d2Transfer488Bound
def d2Transfer489Lo : ℚ := (d2LitsNearTransfers061.q2 (38503635) 1 (-26))
def d2Transfer489Hi : ℚ := (d2LitsNearTransfers061.q2 (10045339) 1 (-24))
def d2Transfer489Cap : ℚ := (d2LitsNearTransfers061.q2 (30439539927) 1 (-40))
def d2Transfer489C0 : ℚ := (d2LitsNearTransfers061.q2 (3) 275 (-5))
def d2Transfer489S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
def d2Transfer489C1 : ℚ := (d2LitsNearTransfers061.q2 (-5) 11 (-4))
def d2Transfer489S1 : ℚ := (d2LitsNearTransfers061.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer489Arithmetic : weightedUpper d2Transfer489C0 d2Log124Lo d2Log124Hi + weightedUpper d2Transfer489C1 d2Log50Lo d2Log50Hi ≤ d2Transfer489Cap := by decide +kernel
theorem d2Transfer489Bound : ∀ x ∈ Set.Icc ((d2Transfer489Lo:ℚ):ℝ) ((d2Transfer489Hi:ℚ):ℝ), ((d2Transfer489C0:ℚ):ℝ)*Real.log |x-((d2Transfer489S0:ℚ):ℝ)| + ((d2Transfer489C1:ℚ):ℝ)*Real.log |x-((d2Transfer489S1:ℚ):ℝ)| ≤ ((d2Transfer489Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer489S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489S0,d2Transfer489Lo,d2Transfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer489C0 then |x-((d2Transfer489S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer489S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer489S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489S0,d2Transfer489Lo,d2Transfer489Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489C0,d2Log124Q,d2Transfer489S0,d2Transfer489Lo,d2Transfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer489C0 d2Transfer489S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2Transfer489S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489S1,d2Transfer489Lo,d2Transfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer489C1 then |x-((d2Transfer489S1:ℚ):ℝ)| ≤ ((d2Log50Q:ℚ):ℝ) else ((d2Log50Q:ℚ):ℝ) ≤ |x-((d2Transfer489S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer489S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489S1,d2Transfer489Lo,d2Transfer489Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer489C1,d2Log50Q,d2Transfer489S1,d2Transfer489Lo,d2Transfer489Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer489C1 d2Transfer489S1 d2Log50Q d2Log50Lo d2Log50Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log50Bounds
  have har : (((weightedUpper d2Transfer489C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2Transfer489C1 d2Log50Lo d2Log50Hi:ℚ):ℝ)) ≤ ((d2Transfer489Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer489Arithmetic
  linarith
#print axioms d2Transfer489Arithmetic
#print axioms d2Transfer489Bound
def d2Transfer490Lo : ℚ := (d2LitsNearTransfers061.q2 (10045339) 1 (-24))
def d2Transfer490Hi : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer490Cap : ℚ := (d2LitsNearTransfers061.q2 (1169469059) 1 (-40))
def d2Transfer490C0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 55 (-3))
def d2Transfer490S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
def d2Transfer490C1 : ℚ := (d2LitsNearTransfers061.q2 (-1) 55 (-3))
def d2Transfer490S1 : ℚ := (d2LitsNearTransfers061.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer490Arithmetic : weightedUpper d2Transfer490C0 d2Log124Lo d2Log124Hi + weightedUpper d2Transfer490C1 d2Log49Lo d2Log49Hi ≤ d2Transfer490Cap := by decide +kernel
theorem d2Transfer490Bound : ∀ x ∈ Set.Icc ((d2Transfer490Lo:ℚ):ℝ) ((d2Transfer490Hi:ℚ):ℝ), ((d2Transfer490C0:ℚ):ℝ)*Real.log |x-((d2Transfer490S0:ℚ):ℝ)| + ((d2Transfer490C1:ℚ):ℝ)*Real.log |x-((d2Transfer490S1:ℚ):ℝ)| ≤ ((d2Transfer490Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer490S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490S0,d2Transfer490Lo,d2Transfer490Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer490C0 then |x-((d2Transfer490S0:ℚ):ℝ)| ≤ ((d2Log124Q:ℚ):ℝ) else ((d2Log124Q:ℚ):ℝ) ≤ |x-((d2Transfer490S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer490S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490S0,d2Transfer490Lo,d2Transfer490Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490C0,d2Log124Q,d2Transfer490S0,d2Transfer490Lo,d2Transfer490Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer490C0 d2Transfer490S0 d2Log124Q d2Log124Lo d2Log124Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log124Bounds
  have hn1 : x-((d2Transfer490S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490S1,d2Transfer490Lo,d2Transfer490Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer490C1 then |x-((d2Transfer490S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2Transfer490S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer490S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490S1,d2Transfer490Lo,d2Transfer490Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer490C1,d2Log49Q,d2Transfer490S1,d2Transfer490Lo,d2Transfer490Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer490C1 d2Transfer490S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2Transfer490C0 d2Log124Lo d2Log124Hi:ℚ):ℝ) + ((weightedUpper d2Transfer490C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2Transfer490Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer490Arithmetic
  linarith
#print axioms d2Transfer490Arithmetic
#print axioms d2Transfer490Bound
def d2Transfer491Lo : ℚ := (d2LitsNearTransfers061.q2 (10045339) 1 (-24))
def d2Transfer491Hi : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer491Cap : ℚ := (d2LitsNearTransfers061.q2 (15113656175) 1 (-40))
def d2Transfer491C0 : ℚ := (d2LitsNearTransfers061.q2 (23) 25 (-5))
def d2Transfer491S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer491Arithmetic : weightedUpper d2Transfer491C0 d2Log125Lo d2Log125Hi ≤ d2Transfer491Cap := by decide +kernel
theorem d2Transfer491Bound : ∀ x ∈ Set.Icc ((d2Transfer491Lo:ℚ):ℝ) ((d2Transfer491Hi:ℚ):ℝ), ((d2Transfer491C0:ℚ):ℝ)*Real.log |x-((d2Transfer491S0:ℚ):ℝ)| ≤ ((d2Transfer491Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer491S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer491S0,d2Transfer491Lo,d2Transfer491Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer491C0 then |x-((d2Transfer491S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer491S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer491S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer491S0,d2Transfer491Lo,d2Transfer491Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer491C0,d2Log125Q,d2Transfer491S0,d2Transfer491Lo,d2Transfer491Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer491C0 d2Transfer491S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have har : (((weightedUpper d2Transfer491C0 d2Log125Lo d2Log125Hi:ℚ):ℝ)) ≤ ((d2Transfer491Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer491Arithmetic
  linarith
#print axioms d2Transfer491Arithmetic
#print axioms d2Transfer491Bound
def d2Transfer492Lo : ℚ := (d2LitsNearTransfers061.q2 (10045339) 1 (-24))
def d2Transfer492Hi : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer492Cap : ℚ := (d2LitsNearTransfers061.q2 (30439539927) 1 (-40))
def d2Transfer492C0 : ℚ := (d2LitsNearTransfers061.q2 (3) 275 (-5))
def d2Transfer492S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
def d2Transfer492C1 : ℚ := (d2LitsNearTransfers061.q2 (-5) 11 (-4))
def d2Transfer492S1 : ℚ := (d2LitsNearTransfers061.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer492Arithmetic : weightedUpper d2Transfer492C0 d2Log125Lo d2Log125Hi + weightedUpper d2Transfer492C1 d2Log49Lo d2Log49Hi ≤ d2Transfer492Cap := by decide +kernel
theorem d2Transfer492Bound : ∀ x ∈ Set.Icc ((d2Transfer492Lo:ℚ):ℝ) ((d2Transfer492Hi:ℚ):ℝ), ((d2Transfer492C0:ℚ):ℝ)*Real.log |x-((d2Transfer492S0:ℚ):ℝ)| + ((d2Transfer492C1:ℚ):ℝ)*Real.log |x-((d2Transfer492S1:ℚ):ℝ)| ≤ ((d2Transfer492Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer492S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492S0,d2Transfer492Lo,d2Transfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer492C0 then |x-((d2Transfer492S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer492S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer492S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492S0,d2Transfer492Lo,d2Transfer492Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492C0,d2Log125Q,d2Transfer492S0,d2Transfer492Lo,d2Transfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer492C0 d2Transfer492S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2Transfer492S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492S1,d2Transfer492Lo,d2Transfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer492C1 then |x-((d2Transfer492S1:ℚ):ℝ)| ≤ ((d2Log49Q:ℚ):ℝ) else ((d2Log49Q:ℚ):ℝ) ≤ |x-((d2Transfer492S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer492S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492S1,d2Transfer492Lo,d2Transfer492Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer492C1,d2Log49Q,d2Transfer492S1,d2Transfer492Lo,d2Transfer492Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer492C1 d2Transfer492S1 d2Log49Q d2Log49Lo d2Log49Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log49Bounds
  have har : (((weightedUpper d2Transfer492C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2Transfer492C1 d2Log49Lo d2Log49Hi:ℚ):ℝ)) ≤ ((d2Transfer492Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer492Arithmetic
  linarith
#print axioms d2Transfer492Arithmetic
#print axioms d2Transfer492Bound
def d2Transfer493Lo : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer493Hi : ℚ := (d2LitsNearTransfers061.q2 (82040433) 1 (-27))
def d2Transfer493Cap : ℚ := (d2LitsNearTransfers061.q2 (324000933795269575833) 1 (-78))
def d2Transfer493C0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 55 (-3))
def d2Transfer493S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
def d2Transfer493C1 : ℚ := (d2LitsNearTransfers061.q2 (-1) 55 (-3))
def d2Transfer493S1 : ℚ := (d2LitsNearTransfers061.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer493Arithmetic : weightedUpper d2Transfer493C0 d2Log125Lo d2Log125Hi + weightedUpper d2Transfer493C1 d2Log46Lo d2Log46Hi ≤ d2Transfer493Cap := by decide +kernel
theorem d2Transfer493Bound : ∀ x ∈ Set.Icc ((d2Transfer493Lo:ℚ):ℝ) ((d2Transfer493Hi:ℚ):ℝ), ((d2Transfer493C0:ℚ):ℝ)*Real.log |x-((d2Transfer493S0:ℚ):ℝ)| + ((d2Transfer493C1:ℚ):ℝ)*Real.log |x-((d2Transfer493S1:ℚ):ℝ)| ≤ ((d2Transfer493Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer493S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493S0,d2Transfer493Lo,d2Transfer493Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer493C0 then |x-((d2Transfer493S0:ℚ):ℝ)| ≤ ((d2Log125Q:ℚ):ℝ) else ((d2Log125Q:ℚ):ℝ) ≤ |x-((d2Transfer493S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer493S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493S0,d2Transfer493Lo,d2Transfer493Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493C0,d2Log125Q,d2Transfer493S0,d2Transfer493Lo,d2Transfer493Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer493C0 d2Transfer493S0 d2Log125Q d2Log125Lo d2Log125Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log125Bounds
  have hn1 : x-((d2Transfer493S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493S1,d2Transfer493Lo,d2Transfer493Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer493C1 then |x-((d2Transfer493S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2Transfer493S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer493S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493S1,d2Transfer493Lo,d2Transfer493Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer493C1,d2Log46Q,d2Transfer493S1,d2Transfer493Lo,d2Transfer493Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer493C1 d2Transfer493S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2Transfer493C0 d2Log125Lo d2Log125Hi:ℚ):ℝ) + ((weightedUpper d2Transfer493C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2Transfer493Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer493Arithmetic
  linarith
#print axioms d2Transfer493Arithmetic
#print axioms d2Transfer493Bound
def d2Transfer494Lo : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer494Hi : ℚ := (d2LitsNearTransfers061.q2 (82040433) 1 (-27))
def d2Transfer494Cap : ℚ := (d2LitsNearTransfers061.q2 (4156949902276841309337) 1 (-78))
def d2Transfer494C0 : ℚ := (d2LitsNearTransfers061.q2 (23) 25 (-5))
def d2Transfer494S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer494Arithmetic : weightedUpper d2Transfer494C0 d2Log128Lo d2Log128Hi ≤ d2Transfer494Cap := by decide +kernel
theorem d2Transfer494Bound : ∀ x ∈ Set.Icc ((d2Transfer494Lo:ℚ):ℝ) ((d2Transfer494Hi:ℚ):ℝ), ((d2Transfer494C0:ℚ):ℝ)*Real.log |x-((d2Transfer494S0:ℚ):ℝ)| ≤ ((d2Transfer494Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer494S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer494S0,d2Transfer494Lo,d2Transfer494Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer494C0 then |x-((d2Transfer494S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer494S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer494S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer494S0,d2Transfer494Lo,d2Transfer494Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer494C0,d2Log128Q,d2Transfer494S0,d2Transfer494Lo,d2Transfer494Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer494C0 d2Transfer494S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2Transfer494C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2Transfer494Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer494Arithmetic
  linarith
#print axioms d2Transfer494Arithmetic
#print axioms d2Transfer494Bound
def d2Transfer495Lo : ℚ := (d2LitsNearTransfers061.q2 (162403145) 1 (-28))
def d2Transfer495Hi : ℚ := (d2LitsNearTransfers061.q2 (82040433) 1 (-27))
def d2Transfer495Cap : ℚ := (d2LitsNearTransfers061.q2 (8369696750093658883225) 1 (-78))
def d2Transfer495C0 : ℚ := (d2LitsNearTransfers061.q2 (3) 275 (-5))
def d2Transfer495S0 : ℚ := (d2LitsNearTransfers061.q2 (-1) 1 (0))
def d2Transfer495C1 : ℚ := (d2LitsNearTransfers061.q2 (-5) 11 (-4))
def d2Transfer495S1 : ℚ := (d2LitsNearTransfers061.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer495Arithmetic : weightedUpper d2Transfer495C0 d2Log128Lo d2Log128Hi + weightedUpper d2Transfer495C1 d2Log46Lo d2Log46Hi ≤ d2Transfer495Cap := by decide +kernel
theorem d2Transfer495Bound : ∀ x ∈ Set.Icc ((d2Transfer495Lo:ℚ):ℝ) ((d2Transfer495Hi:ℚ):ℝ), ((d2Transfer495C0:ℚ):ℝ)*Real.log |x-((d2Transfer495S0:ℚ):ℝ)| + ((d2Transfer495C1:ℚ):ℝ)*Real.log |x-((d2Transfer495S1:ℚ):ℝ)| ≤ ((d2Transfer495Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer495S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495S0,d2Transfer495Lo,d2Transfer495Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer495C0 then |x-((d2Transfer495S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2Transfer495S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer495S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495S0,d2Transfer495Lo,d2Transfer495Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495C0,d2Log128Q,d2Transfer495S0,d2Transfer495Lo,d2Transfer495Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer495C0 d2Transfer495S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2Transfer495S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495S1,d2Transfer495Lo,d2Transfer495Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer495C1 then |x-((d2Transfer495S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2Transfer495S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer495S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495S1,d2Transfer495Lo,d2Transfer495Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers061.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2Transfer495C1,d2Log46Q,d2Transfer495S1,d2Transfer495Lo,d2Transfer495Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer495C1 d2Transfer495S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2Transfer495C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2Transfer495C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2Transfer495Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer495Arithmetic
  linarith
#print axioms d2Transfer495Arithmetic
#print axioms d2Transfer495Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers019
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers019
open D72.LogTransfer
def d2Transfer152Lo : ℚ := (d2LitsNearTransfers019.q2 (24997919) 1 (-27))
def d2Transfer152Hi : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer152Cap : ℚ := (d2LitsNearTransfers019.q2 (16281318465) 1 (-40))
def d2Transfer152C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (-5))
def d2Transfer152S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer152Arithmetic : weightedUpper d2Transfer152C0 d2Log106Lo d2Log106Hi ≤ d2Transfer152Cap := by decide +kernel
theorem d2Transfer152Bound : ∀ x ∈ Set.Icc ((d2Transfer152Lo:ℚ):ℝ) ((d2Transfer152Hi:ℚ):ℝ), ((d2Transfer152C0:ℚ):ℝ)*Real.log |x-((d2Transfer152S0:ℚ):ℝ)| ≤ ((d2Transfer152Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer152S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer152S0,d2Transfer152Lo,d2Transfer152Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer152C0 then |x-((d2Transfer152S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer152S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer152S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer152S0,d2Transfer152Lo,d2Transfer152Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer152C0,d2Log106Q,d2Transfer152S0,d2Transfer152Lo,d2Transfer152Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer152C0 d2Transfer152S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have har : (((weightedUpper d2Transfer152C0 d2Log106Lo d2Log106Hi:ℚ):ℝ)) ≤ ((d2Transfer152Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer152Arithmetic
  linarith
#print axioms d2Transfer152Arithmetic
#print axioms d2Transfer152Bound
def d2Transfer153Lo : ℚ := (d2LitsNearTransfers019.q2 (24997919) 1 (-27))
def d2Transfer153Hi : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer153Cap : ℚ := (d2LitsNearTransfers019.q2 (31165051305) 1 (-40))
def d2Transfer153C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 11 (-5))
def d2Transfer153S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
def d2Transfer153C1 : ℚ := (d2LitsNearTransfers019.q2 (-5) 11 (-4))
def d2Transfer153S1 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer153Arithmetic : weightedUpper d2Transfer153C0 d2Log106Lo d2Log106Hi + weightedUpper d2Transfer153C1 d2Log68Lo d2Log68Hi ≤ d2Transfer153Cap := by decide +kernel
theorem d2Transfer153Bound : ∀ x ∈ Set.Icc ((d2Transfer153Lo:ℚ):ℝ) ((d2Transfer153Hi:ℚ):ℝ), ((d2Transfer153C0:ℚ):ℝ)*Real.log |x-((d2Transfer153S0:ℚ):ℝ)| + ((d2Transfer153C1:ℚ):ℝ)*Real.log |x-((d2Transfer153S1:ℚ):ℝ)| ≤ ((d2Transfer153Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer153S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153S0,d2Transfer153Lo,d2Transfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer153C0 then |x-((d2Transfer153S0:ℚ):ℝ)| ≤ ((d2Log106Q:ℚ):ℝ) else ((d2Log106Q:ℚ):ℝ) ≤ |x-((d2Transfer153S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer153S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153S0,d2Transfer153Lo,d2Transfer153Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153C0,d2Log106Q,d2Transfer153S0,d2Transfer153Lo,d2Transfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer153C0 d2Transfer153S0 d2Log106Q d2Log106Lo d2Log106Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log106Bounds
  have hn1 : x-((d2Transfer153S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153S1,d2Transfer153Lo,d2Transfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer153C1 then |x-((d2Transfer153S1:ℚ):ℝ)| ≤ ((d2Log68Q:ℚ):ℝ) else ((d2Log68Q:ℚ):ℝ) ≤ |x-((d2Transfer153S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer153S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153S1,d2Transfer153Lo,d2Transfer153Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer153C1,d2Log68Q,d2Transfer153S1,d2Transfer153Lo,d2Transfer153Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer153C1 d2Transfer153S1 d2Log68Q d2Log68Lo d2Log68Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log68Bounds
  have har : (((weightedUpper d2Transfer153C0 d2Log106Lo d2Log106Hi:ℚ):ℝ) + ((weightedUpper d2Transfer153C1 d2Log68Lo d2Log68Hi:ℚ):ℝ)) ≤ ((d2Transfer153Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer153Arithmetic
  linarith
#print axioms d2Transfer153Arithmetic
#print axioms d2Transfer153Bound
def d2Transfer154Lo : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer154Hi : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer154Cap : ℚ := (d2LitsNearTransfers019.q2 (649441385) 1 (-39))
def d2Transfer154C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 25 (-4))
def d2Transfer154S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer154Arithmetic : weightedUpper d2Transfer154C0 d2Log107Lo d2Log107Hi ≤ d2Transfer154Cap := by decide +kernel
theorem d2Transfer154Bound : ∀ x ∈ Set.Icc ((d2Transfer154Lo:ℚ):ℝ) ((d2Transfer154Hi:ℚ):ℝ), ((d2Transfer154C0:ℚ):ℝ)*Real.log |x-((d2Transfer154S0:ℚ):ℝ)| ≤ ((d2Transfer154Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer154S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer154S0,d2Transfer154Lo,d2Transfer154Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer154C0 then |x-((d2Transfer154S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer154S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer154S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer154S0,d2Transfer154Lo,d2Transfer154Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer154C0,d2Log107Q,d2Transfer154S0,d2Transfer154Lo,d2Transfer154Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer154C0 d2Transfer154S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have har : (((weightedUpper d2Transfer154C0 d2Log107Lo d2Log107Hi:ℚ):ℝ)) ≤ ((d2Transfer154Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer154Arithmetic
  linarith
#print axioms d2Transfer154Arithmetic
#print axioms d2Transfer154Bound
def d2Transfer155Lo : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer155Hi : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer155Cap : ℚ := (d2LitsNearTransfers019.q2 (2436024149) 1 (-40))
def d2Transfer155C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 275 (-4))
def d2Transfer155S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
def d2Transfer155C1 : ℚ := (d2LitsNearTransfers019.q2 (-1) 55 (-3))
def d2Transfer155S1 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer155Arithmetic : weightedUpper d2Transfer155C0 d2Log107Lo d2Log107Hi + weightedUpper d2Transfer155C1 d2Log67Lo d2Log67Hi ≤ d2Transfer155Cap := by decide +kernel
theorem d2Transfer155Bound : ∀ x ∈ Set.Icc ((d2Transfer155Lo:ℚ):ℝ) ((d2Transfer155Hi:ℚ):ℝ), ((d2Transfer155C0:ℚ):ℝ)*Real.log |x-((d2Transfer155S0:ℚ):ℝ)| + ((d2Transfer155C1:ℚ):ℝ)*Real.log |x-((d2Transfer155S1:ℚ):ℝ)| ≤ ((d2Transfer155Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer155S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155S0,d2Transfer155Lo,d2Transfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer155C0 then |x-((d2Transfer155S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer155S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer155S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155S0,d2Transfer155Lo,d2Transfer155Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155C0,d2Log107Q,d2Transfer155S0,d2Transfer155Lo,d2Transfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer155C0 d2Transfer155S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have hn1 : x-((d2Transfer155S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155S1,d2Transfer155Lo,d2Transfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer155C1 then |x-((d2Transfer155S1:ℚ):ℝ)| ≤ ((d2Log67Q:ℚ):ℝ) else ((d2Log67Q:ℚ):ℝ) ≤ |x-((d2Transfer155S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer155S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155S1,d2Transfer155Lo,d2Transfer155Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer155C1,d2Log67Q,d2Transfer155S1,d2Transfer155Lo,d2Transfer155Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer155C1 d2Transfer155S1 d2Log67Q d2Log67Lo d2Log67Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log67Bounds
  have har : (((weightedUpper d2Transfer155C0 d2Log107Lo d2Log107Hi:ℚ):ℝ) + ((weightedUpper d2Transfer155C1 d2Log67Lo d2Log67Hi:ℚ):ℝ)) ≤ ((d2Transfer155Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer155Arithmetic
  linarith
#print axioms d2Transfer155Arithmetic
#print axioms d2Transfer155Bound
def d2Transfer156Lo : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer156Hi : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer156Cap : ℚ := (d2LitsNearTransfers019.q2 (16281318465) 1 (-40))
def d2Transfer156C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (-5))
def d2Transfer156S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer156Arithmetic : weightedUpper d2Transfer156C0 d2Log107Lo d2Log107Hi ≤ d2Transfer156Cap := by decide +kernel
theorem d2Transfer156Bound : ∀ x ∈ Set.Icc ((d2Transfer156Lo:ℚ):ℝ) ((d2Transfer156Hi:ℚ):ℝ), ((d2Transfer156C0:ℚ):ℝ)*Real.log |x-((d2Transfer156S0:ℚ):ℝ)| ≤ ((d2Transfer156Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer156S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer156S0,d2Transfer156Lo,d2Transfer156Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer156C0 then |x-((d2Transfer156S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer156S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer156S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer156S0,d2Transfer156Lo,d2Transfer156Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer156C0,d2Log107Q,d2Transfer156S0,d2Transfer156Lo,d2Transfer156Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer156C0 d2Transfer156S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have har : (((weightedUpper d2Transfer156C0 d2Log107Lo d2Log107Hi:ℚ):ℝ)) ≤ ((d2Transfer156Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer156Arithmetic
  linarith
#print axioms d2Transfer156Arithmetic
#print axioms d2Transfer156Bound
def d2Transfer157Lo : ℚ := (d2LitsNearTransfers019.q2 (3334455) 1 (-24))
def d2Transfer157Hi : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer157Cap : ℚ := (d2LitsNearTransfers019.q2 (31165051305) 1 (-40))
def d2Transfer157C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 11 (-5))
def d2Transfer157S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
def d2Transfer157C1 : ℚ := (d2LitsNearTransfers019.q2 (-5) 11 (-4))
def d2Transfer157S1 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer157Arithmetic : weightedUpper d2Transfer157C0 d2Log107Lo d2Log107Hi + weightedUpper d2Transfer157C1 d2Log67Lo d2Log67Hi ≤ d2Transfer157Cap := by decide +kernel
theorem d2Transfer157Bound : ∀ x ∈ Set.Icc ((d2Transfer157Lo:ℚ):ℝ) ((d2Transfer157Hi:ℚ):ℝ), ((d2Transfer157C0:ℚ):ℝ)*Real.log |x-((d2Transfer157S0:ℚ):ℝ)| + ((d2Transfer157C1:ℚ):ℝ)*Real.log |x-((d2Transfer157S1:ℚ):ℝ)| ≤ ((d2Transfer157Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer157S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157S0,d2Transfer157Lo,d2Transfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer157C0 then |x-((d2Transfer157S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer157S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer157S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157S0,d2Transfer157Lo,d2Transfer157Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157C0,d2Log107Q,d2Transfer157S0,d2Transfer157Lo,d2Transfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer157C0 d2Transfer157S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have hn1 : x-((d2Transfer157S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157S1,d2Transfer157Lo,d2Transfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer157C1 then |x-((d2Transfer157S1:ℚ):ℝ)| ≤ ((d2Log67Q:ℚ):ℝ) else ((d2Log67Q:ℚ):ℝ) ≤ |x-((d2Transfer157S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer157S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157S1,d2Transfer157Lo,d2Transfer157Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer157C1,d2Log67Q,d2Transfer157S1,d2Transfer157Lo,d2Transfer157Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer157C1 d2Transfer157S1 d2Log67Q d2Log67Lo d2Log67Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log67Bounds
  have har : (((weightedUpper d2Transfer157C0 d2Log107Lo d2Log107Hi:ℚ):ℝ) + ((weightedUpper d2Transfer157C1 d2Log67Lo d2Log67Hi:ℚ):ℝ)) ≤ ((d2Transfer157Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer157Arithmetic
  linarith
#print axioms d2Transfer157Arithmetic
#print axioms d2Transfer157Bound
def d2Transfer158Lo : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer158Hi : ℚ := (d2LitsNearTransfers019.q2 (15015541) 1 (-26))
def d2Transfer158Cap : ℚ := (d2LitsNearTransfers019.q2 (649441385) 1 (-39))
def d2Transfer158C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 25 (-4))
def d2Transfer158S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer158Arithmetic : weightedUpper d2Transfer158C0 d2Log108Lo d2Log108Hi ≤ d2Transfer158Cap := by decide +kernel
theorem d2Transfer158Bound : ∀ x ∈ Set.Icc ((d2Transfer158Lo:ℚ):ℝ) ((d2Transfer158Hi:ℚ):ℝ), ((d2Transfer158C0:ℚ):ℝ)*Real.log |x-((d2Transfer158S0:ℚ):ℝ)| ≤ ((d2Transfer158Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer158S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer158S0,d2Transfer158Lo,d2Transfer158Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer158C0 then |x-((d2Transfer158S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer158S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer158S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer158S0,d2Transfer158Lo,d2Transfer158Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer158C0,d2Log108Q,d2Transfer158S0,d2Transfer158Lo,d2Transfer158Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer158C0 d2Transfer158S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have har : (((weightedUpper d2Transfer158C0 d2Log108Lo d2Log108Hi:ℚ):ℝ)) ≤ ((d2Transfer158Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer158Arithmetic
  linarith
#print axioms d2Transfer158Arithmetic
#print axioms d2Transfer158Bound
def d2Transfer159Lo : ℚ := (d2LitsNearTransfers019.q2 (28353361) 1 (-27))
def d2Transfer159Hi : ℚ := (d2LitsNearTransfers019.q2 (15015541) 1 (-26))
def d2Transfer159Cap : ℚ := (d2LitsNearTransfers019.q2 (2436024149) 1 (-40))
def d2Transfer159C0 : ℚ := (d2LitsNearTransfers019.q2 (1) 275 (-4))
def d2Transfer159S0 : ℚ := (d2LitsNearTransfers019.q2 (-1) 1 (0))
def d2Transfer159C1 : ℚ := (d2LitsNearTransfers019.q2 (-1) 55 (-3))
def d2Transfer159S1 : ℚ := (d2LitsNearTransfers019.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer159Arithmetic : weightedUpper d2Transfer159C0 d2Log108Lo d2Log108Hi + weightedUpper d2Transfer159C1 d2Log66Lo d2Log66Hi ≤ d2Transfer159Cap := by decide +kernel
theorem d2Transfer159Bound : ∀ x ∈ Set.Icc ((d2Transfer159Lo:ℚ):ℝ) ((d2Transfer159Hi:ℚ):ℝ), ((d2Transfer159C0:ℚ):ℝ)*Real.log |x-((d2Transfer159S0:ℚ):ℝ)| + ((d2Transfer159C1:ℚ):ℝ)*Real.log |x-((d2Transfer159S1:ℚ):ℝ)| ≤ ((d2Transfer159Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer159S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159S0,d2Transfer159Lo,d2Transfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer159C0 then |x-((d2Transfer159S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer159S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer159S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159S0,d2Transfer159Lo,d2Transfer159Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159C0,d2Log108Q,d2Transfer159S0,d2Transfer159Lo,d2Transfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer159C0 d2Transfer159S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have hn1 : x-((d2Transfer159S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159S1,d2Transfer159Lo,d2Transfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer159C1 then |x-((d2Transfer159S1:ℚ):ℝ)| ≤ ((d2Log66Q:ℚ):ℝ) else ((d2Log66Q:ℚ):ℝ) ≤ |x-((d2Transfer159S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer159S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159S1,d2Transfer159Lo,d2Transfer159Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers019.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer159C1,d2Log66Q,d2Transfer159S1,d2Transfer159Lo,d2Transfer159Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer159C1 d2Transfer159S1 d2Log66Q d2Log66Lo d2Log66Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log66Bounds
  have har : (((weightedUpper d2Transfer159C0 d2Log108Lo d2Log108Hi:ℚ):ℝ) + ((weightedUpper d2Transfer159C1 d2Log66Lo d2Log66Hi:ℚ):ℝ)) ≤ ((d2Transfer159Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer159Arithmetic
  linarith
#print axioms d2Transfer159Arithmetic
#print axioms d2Transfer159Bound
end CatalanMeasure.GenD.Signed.Data.Cells

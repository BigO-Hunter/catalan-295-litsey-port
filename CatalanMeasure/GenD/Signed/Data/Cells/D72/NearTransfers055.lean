module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers055
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers055
open D72.LogTransfer
def d2Transfer440Lo : ℚ := (d2LitsNearTransfers055.q2 (3334455) 1 (-24))
def d2Transfer440Hi : ℚ := (d2LitsNearTransfers055.q2 (28353361) 1 (-27))
def d2Transfer440Cap : ℚ := (d2LitsNearTransfers055.q2 (15113656175) 1 (-40))
def d2Transfer440C0 : ℚ := (d2LitsNearTransfers055.q2 (23) 25 (-5))
def d2Transfer440S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer440Arithmetic : weightedUpper d2Transfer440C0 d2Log107Lo d2Log107Hi ≤ d2Transfer440Cap := by decide +kernel
theorem d2Transfer440Bound : ∀ x ∈ Set.Icc ((d2Transfer440Lo:ℚ):ℝ) ((d2Transfer440Hi:ℚ):ℝ), ((d2Transfer440C0:ℚ):ℝ)*Real.log |x-((d2Transfer440S0:ℚ):ℝ)| ≤ ((d2Transfer440Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer440S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer440S0,d2Transfer440Lo,d2Transfer440Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer440C0 then |x-((d2Transfer440S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer440S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer440S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer440S0,d2Transfer440Lo,d2Transfer440Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer440C0,d2Log107Q,d2Transfer440S0,d2Transfer440Lo,d2Transfer440Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer440C0 d2Transfer440S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have har : (((weightedUpper d2Transfer440C0 d2Log107Lo d2Log107Hi:ℚ):ℝ)) ≤ ((d2Transfer440Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer440Arithmetic
  linarith
#print axioms d2Transfer440Arithmetic
#print axioms d2Transfer440Bound
def d2Transfer441Lo : ℚ := (d2LitsNearTransfers055.q2 (3334455) 1 (-24))
def d2Transfer441Hi : ℚ := (d2LitsNearTransfers055.q2 (28353361) 1 (-27))
def d2Transfer441Cap : ℚ := (d2LitsNearTransfers055.q2 (30439539927) 1 (-40))
def d2Transfer441C0 : ℚ := (d2LitsNearTransfers055.q2 (3) 275 (-5))
def d2Transfer441S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
def d2Transfer441C1 : ℚ := (d2LitsNearTransfers055.q2 (-5) 11 (-4))
def d2Transfer441S1 : ℚ := (d2LitsNearTransfers055.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer441Arithmetic : weightedUpper d2Transfer441C0 d2Log107Lo d2Log107Hi + weightedUpper d2Transfer441C1 d2Log67Lo d2Log67Hi ≤ d2Transfer441Cap := by decide +kernel
theorem d2Transfer441Bound : ∀ x ∈ Set.Icc ((d2Transfer441Lo:ℚ):ℝ) ((d2Transfer441Hi:ℚ):ℝ), ((d2Transfer441C0:ℚ):ℝ)*Real.log |x-((d2Transfer441S0:ℚ):ℝ)| + ((d2Transfer441C1:ℚ):ℝ)*Real.log |x-((d2Transfer441S1:ℚ):ℝ)| ≤ ((d2Transfer441Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer441S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441S0,d2Transfer441Lo,d2Transfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer441C0 then |x-((d2Transfer441S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer441S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer441S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441S0,d2Transfer441Lo,d2Transfer441Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441C0,d2Log107Q,d2Transfer441S0,d2Transfer441Lo,d2Transfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer441C0 d2Transfer441S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have hn1 : x-((d2Transfer441S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441S1,d2Transfer441Lo,d2Transfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer441C1 then |x-((d2Transfer441S1:ℚ):ℝ)| ≤ ((d2Log67Q:ℚ):ℝ) else ((d2Log67Q:ℚ):ℝ) ≤ |x-((d2Transfer441S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer441S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441S1,d2Transfer441Lo,d2Transfer441Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer441C1,d2Log67Q,d2Transfer441S1,d2Transfer441Lo,d2Transfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer441C1 d2Transfer441S1 d2Log67Q d2Log67Lo d2Log67Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log67Bounds
  have har : (((weightedUpper d2Transfer441C0 d2Log107Lo d2Log107Hi:ℚ):ℝ) + ((weightedUpper d2Transfer441C1 d2Log67Lo d2Log67Hi:ℚ):ℝ)) ≤ ((d2Transfer441Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer441Arithmetic
  linarith
#print axioms d2Transfer441Arithmetic
#print axioms d2Transfer441Bound
def d2Transfer442Lo : ℚ := (d2LitsNearTransfers055.q2 (28353361) 1 (-27))
def d2Transfer442Hi : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer442Cap : ℚ := (d2LitsNearTransfers055.q2 (1169469059) 1 (-40))
def d2Transfer442C0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 55 (-3))
def d2Transfer442S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
def d2Transfer442C1 : ℚ := (d2LitsNearTransfers055.q2 (-1) 55 (-3))
def d2Transfer442S1 : ℚ := (d2LitsNearTransfers055.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer442Arithmetic : weightedUpper d2Transfer442C0 d2Log107Lo d2Log107Hi + weightedUpper d2Transfer442C1 d2Log66Lo d2Log66Hi ≤ d2Transfer442Cap := by decide +kernel
theorem d2Transfer442Bound : ∀ x ∈ Set.Icc ((d2Transfer442Lo:ℚ):ℝ) ((d2Transfer442Hi:ℚ):ℝ), ((d2Transfer442C0:ℚ):ℝ)*Real.log |x-((d2Transfer442S0:ℚ):ℝ)| + ((d2Transfer442C1:ℚ):ℝ)*Real.log |x-((d2Transfer442S1:ℚ):ℝ)| ≤ ((d2Transfer442Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer442S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442S0,d2Transfer442Lo,d2Transfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer442C0 then |x-((d2Transfer442S0:ℚ):ℝ)| ≤ ((d2Log107Q:ℚ):ℝ) else ((d2Log107Q:ℚ):ℝ) ≤ |x-((d2Transfer442S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer442S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442S0,d2Transfer442Lo,d2Transfer442Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442C0,d2Log107Q,d2Transfer442S0,d2Transfer442Lo,d2Transfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer442C0 d2Transfer442S0 d2Log107Q d2Log107Lo d2Log107Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log107Bounds
  have hn1 : x-((d2Transfer442S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442S1,d2Transfer442Lo,d2Transfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer442C1 then |x-((d2Transfer442S1:ℚ):ℝ)| ≤ ((d2Log66Q:ℚ):ℝ) else ((d2Log66Q:ℚ):ℝ) ≤ |x-((d2Transfer442S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer442S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442S1,d2Transfer442Lo,d2Transfer442Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer442C1,d2Log66Q,d2Transfer442S1,d2Transfer442Lo,d2Transfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer442C1 d2Transfer442S1 d2Log66Q d2Log66Lo d2Log66Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log66Bounds
  have har : (((weightedUpper d2Transfer442C0 d2Log107Lo d2Log107Hi:ℚ):ℝ) + ((weightedUpper d2Transfer442C1 d2Log66Lo d2Log66Hi:ℚ):ℝ)) ≤ ((d2Transfer442Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer442Arithmetic
  linarith
#print axioms d2Transfer442Arithmetic
#print axioms d2Transfer442Bound
def d2Transfer443Lo : ℚ := (d2LitsNearTransfers055.q2 (28353361) 1 (-27))
def d2Transfer443Hi : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer443Cap : ℚ := (d2LitsNearTransfers055.q2 (15113656175) 1 (-40))
def d2Transfer443C0 : ℚ := (d2LitsNearTransfers055.q2 (23) 25 (-5))
def d2Transfer443S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer443Arithmetic : weightedUpper d2Transfer443C0 d2Log108Lo d2Log108Hi ≤ d2Transfer443Cap := by decide +kernel
theorem d2Transfer443Bound : ∀ x ∈ Set.Icc ((d2Transfer443Lo:ℚ):ℝ) ((d2Transfer443Hi:ℚ):ℝ), ((d2Transfer443C0:ℚ):ℝ)*Real.log |x-((d2Transfer443S0:ℚ):ℝ)| ≤ ((d2Transfer443Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer443S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer443S0,d2Transfer443Lo,d2Transfer443Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer443C0 then |x-((d2Transfer443S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer443S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer443S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer443S0,d2Transfer443Lo,d2Transfer443Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer443C0,d2Log108Q,d2Transfer443S0,d2Transfer443Lo,d2Transfer443Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer443C0 d2Transfer443S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have har : (((weightedUpper d2Transfer443C0 d2Log108Lo d2Log108Hi:ℚ):ℝ)) ≤ ((d2Transfer443Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer443Arithmetic
  linarith
#print axioms d2Transfer443Arithmetic
#print axioms d2Transfer443Bound
def d2Transfer444Lo : ℚ := (d2LitsNearTransfers055.q2 (28353361) 1 (-27))
def d2Transfer444Hi : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer444Cap : ℚ := (d2LitsNearTransfers055.q2 (30439539927) 1 (-40))
def d2Transfer444C0 : ℚ := (d2LitsNearTransfers055.q2 (3) 275 (-5))
def d2Transfer444S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
def d2Transfer444C1 : ℚ := (d2LitsNearTransfers055.q2 (-5) 11 (-4))
def d2Transfer444S1 : ℚ := (d2LitsNearTransfers055.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer444Arithmetic : weightedUpper d2Transfer444C0 d2Log108Lo d2Log108Hi + weightedUpper d2Transfer444C1 d2Log66Lo d2Log66Hi ≤ d2Transfer444Cap := by decide +kernel
theorem d2Transfer444Bound : ∀ x ∈ Set.Icc ((d2Transfer444Lo:ℚ):ℝ) ((d2Transfer444Hi:ℚ):ℝ), ((d2Transfer444C0:ℚ):ℝ)*Real.log |x-((d2Transfer444S0:ℚ):ℝ)| + ((d2Transfer444C1:ℚ):ℝ)*Real.log |x-((d2Transfer444S1:ℚ):ℝ)| ≤ ((d2Transfer444Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer444S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444S0,d2Transfer444Lo,d2Transfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer444C0 then |x-((d2Transfer444S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer444S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer444S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444S0,d2Transfer444Lo,d2Transfer444Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444C0,d2Log108Q,d2Transfer444S0,d2Transfer444Lo,d2Transfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer444C0 d2Transfer444S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have hn1 : x-((d2Transfer444S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444S1,d2Transfer444Lo,d2Transfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer444C1 then |x-((d2Transfer444S1:ℚ):ℝ)| ≤ ((d2Log66Q:ℚ):ℝ) else ((d2Log66Q:ℚ):ℝ) ≤ |x-((d2Transfer444S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer444S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444S1,d2Transfer444Lo,d2Transfer444Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer444C1,d2Log66Q,d2Transfer444S1,d2Transfer444Lo,d2Transfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer444C1 d2Transfer444S1 d2Log66Q d2Log66Lo d2Log66Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log66Bounds
  have har : (((weightedUpper d2Transfer444C0 d2Log108Lo d2Log108Hi:ℚ):ℝ) + ((weightedUpper d2Transfer444C1 d2Log66Lo d2Log66Hi:ℚ):ℝ)) ≤ ((d2Transfer444Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer444Arithmetic
  linarith
#print axioms d2Transfer444Arithmetic
#print axioms d2Transfer444Bound
def d2Transfer445Lo : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer445Hi : ℚ := (d2LitsNearTransfers055.q2 (31708803) 1 (-27))
def d2Transfer445Cap : ℚ := (d2LitsNearTransfers055.q2 (1169469059) 1 (-40))
def d2Transfer445C0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 55 (-3))
def d2Transfer445S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
def d2Transfer445C1 : ℚ := (d2LitsNearTransfers055.q2 (-1) 55 (-3))
def d2Transfer445S1 : ℚ := (d2LitsNearTransfers055.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer445Arithmetic : weightedUpper d2Transfer445C0 d2Log108Lo d2Log108Hi + weightedUpper d2Transfer445C1 d2Log65Lo d2Log65Hi ≤ d2Transfer445Cap := by decide +kernel
theorem d2Transfer445Bound : ∀ x ∈ Set.Icc ((d2Transfer445Lo:ℚ):ℝ) ((d2Transfer445Hi:ℚ):ℝ), ((d2Transfer445C0:ℚ):ℝ)*Real.log |x-((d2Transfer445S0:ℚ):ℝ)| + ((d2Transfer445C1:ℚ):ℝ)*Real.log |x-((d2Transfer445S1:ℚ):ℝ)| ≤ ((d2Transfer445Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer445S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445S0,d2Transfer445Lo,d2Transfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer445C0 then |x-((d2Transfer445S0:ℚ):ℝ)| ≤ ((d2Log108Q:ℚ):ℝ) else ((d2Log108Q:ℚ):ℝ) ≤ |x-((d2Transfer445S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer445S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445S0,d2Transfer445Lo,d2Transfer445Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445C0,d2Log108Q,d2Transfer445S0,d2Transfer445Lo,d2Transfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer445C0 d2Transfer445S0 d2Log108Q d2Log108Lo d2Log108Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log108Bounds
  have hn1 : x-((d2Transfer445S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445S1,d2Transfer445Lo,d2Transfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer445C1 then |x-((d2Transfer445S1:ℚ):ℝ)| ≤ ((d2Log65Q:ℚ):ℝ) else ((d2Log65Q:ℚ):ℝ) ≤ |x-((d2Transfer445S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer445S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445S1,d2Transfer445Lo,d2Transfer445Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer445C1,d2Log65Q,d2Transfer445S1,d2Transfer445Lo,d2Transfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer445C1 d2Transfer445S1 d2Log65Q d2Log65Lo d2Log65Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log65Bounds
  have har : (((weightedUpper d2Transfer445C0 d2Log108Lo d2Log108Hi:ℚ):ℝ) + ((weightedUpper d2Transfer445C1 d2Log65Lo d2Log65Hi:ℚ):ℝ)) ≤ ((d2Transfer445Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer445Arithmetic
  linarith
#print axioms d2Transfer445Arithmetic
#print axioms d2Transfer445Bound
def d2Transfer446Lo : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer446Hi : ℚ := (d2LitsNearTransfers055.q2 (31708803) 1 (-27))
def d2Transfer446Cap : ℚ := (d2LitsNearTransfers055.q2 (15113656175) 1 (-40))
def d2Transfer446C0 : ℚ := (d2LitsNearTransfers055.q2 (23) 25 (-5))
def d2Transfer446S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer446Arithmetic : weightedUpper d2Transfer446C0 d2Log109Lo d2Log109Hi ≤ d2Transfer446Cap := by decide +kernel
theorem d2Transfer446Bound : ∀ x ∈ Set.Icc ((d2Transfer446Lo:ℚ):ℝ) ((d2Transfer446Hi:ℚ):ℝ), ((d2Transfer446C0:ℚ):ℝ)*Real.log |x-((d2Transfer446S0:ℚ):ℝ)| ≤ ((d2Transfer446Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer446S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer446S0,d2Transfer446Lo,d2Transfer446Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer446C0 then |x-((d2Transfer446S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer446S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer446S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer446S0,d2Transfer446Lo,d2Transfer446Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer446C0,d2Log109Q,d2Transfer446S0,d2Transfer446Lo,d2Transfer446Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer446C0 d2Transfer446S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have har : (((weightedUpper d2Transfer446C0 d2Log109Lo d2Log109Hi:ℚ):ℝ)) ≤ ((d2Transfer446Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer446Arithmetic
  linarith
#print axioms d2Transfer446Arithmetic
#print axioms d2Transfer446Bound
def d2Transfer447Lo : ℚ := (d2LitsNearTransfers055.q2 (15015541) 1 (-26))
def d2Transfer447Hi : ℚ := (d2LitsNearTransfers055.q2 (31708803) 1 (-27))
def d2Transfer447Cap : ℚ := (d2LitsNearTransfers055.q2 (30439539927) 1 (-40))
def d2Transfer447C0 : ℚ := (d2LitsNearTransfers055.q2 (3) 275 (-5))
def d2Transfer447S0 : ℚ := (d2LitsNearTransfers055.q2 (-1) 1 (0))
def d2Transfer447C1 : ℚ := (d2LitsNearTransfers055.q2 (-5) 11 (-4))
def d2Transfer447S1 : ℚ := (d2LitsNearTransfers055.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer447Arithmetic : weightedUpper d2Transfer447C0 d2Log109Lo d2Log109Hi + weightedUpper d2Transfer447C1 d2Log65Lo d2Log65Hi ≤ d2Transfer447Cap := by decide +kernel
theorem d2Transfer447Bound : ∀ x ∈ Set.Icc ((d2Transfer447Lo:ℚ):ℝ) ((d2Transfer447Hi:ℚ):ℝ), ((d2Transfer447C0:ℚ):ℝ)*Real.log |x-((d2Transfer447S0:ℚ):ℝ)| + ((d2Transfer447C1:ℚ):ℝ)*Real.log |x-((d2Transfer447S1:ℚ):ℝ)| ≤ ((d2Transfer447Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer447S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447S0,d2Transfer447Lo,d2Transfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer447C0 then |x-((d2Transfer447S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer447S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer447S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447S0,d2Transfer447Lo,d2Transfer447Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447C0,d2Log109Q,d2Transfer447S0,d2Transfer447Lo,d2Transfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer447C0 d2Transfer447S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have hn1 : x-((d2Transfer447S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447S1,d2Transfer447Lo,d2Transfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer447C1 then |x-((d2Transfer447S1:ℚ):ℝ)| ≤ ((d2Log65Q:ℚ):ℝ) else ((d2Log65Q:ℚ):ℝ) ≤ |x-((d2Transfer447S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer447S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447S1,d2Transfer447Lo,d2Transfer447Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers055.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer447C1,d2Log65Q,d2Transfer447S1,d2Transfer447Lo,d2Transfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer447C1 d2Transfer447S1 d2Log65Q d2Log65Lo d2Log65Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log65Bounds
  have har : (((weightedUpper d2Transfer447C0 d2Log109Lo d2Log109Hi:ℚ):ℝ) + ((weightedUpper d2Transfer447C1 d2Log65Lo d2Log65Hi:ℚ):ℝ)) ≤ ((d2Transfer447Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer447Arithmetic
  linarith
#print axioms d2Transfer447Arithmetic
#print axioms d2Transfer447Bound
end CatalanMeasure.GenD.Signed.Data.Cells

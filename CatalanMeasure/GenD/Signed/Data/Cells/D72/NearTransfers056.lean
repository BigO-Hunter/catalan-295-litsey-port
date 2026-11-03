module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers056
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers056
open D72.LogTransfer
def d2Transfer448Lo : ℚ := (d2LitsNearTransfers056.q2 (31708803) 1 (-27))
def d2Transfer448Hi : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer448Cap : ℚ := (d2LitsNearTransfers056.q2 (1169469059) 1 (-40))
def d2Transfer448C0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer448S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
def d2Transfer448C1 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer448S1 : ℚ := (d2LitsNearTransfers056.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer448Arithmetic : weightedUpper d2Transfer448C0 d2Log109Lo d2Log109Hi + weightedUpper d2Transfer448C1 d2Log64Lo d2Log64Hi ≤ d2Transfer448Cap := by decide +kernel
theorem d2Transfer448Bound : ∀ x ∈ Set.Icc ((d2Transfer448Lo:ℚ):ℝ) ((d2Transfer448Hi:ℚ):ℝ), ((d2Transfer448C0:ℚ):ℝ)*Real.log |x-((d2Transfer448S0:ℚ):ℝ)| + ((d2Transfer448C1:ℚ):ℝ)*Real.log |x-((d2Transfer448S1:ℚ):ℝ)| ≤ ((d2Transfer448Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer448S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448S0,d2Transfer448Lo,d2Transfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer448C0 then |x-((d2Transfer448S0:ℚ):ℝ)| ≤ ((d2Log109Q:ℚ):ℝ) else ((d2Log109Q:ℚ):ℝ) ≤ |x-((d2Transfer448S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer448S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448S0,d2Transfer448Lo,d2Transfer448Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448C0,d2Log109Q,d2Transfer448S0,d2Transfer448Lo,d2Transfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer448C0 d2Transfer448S0 d2Log109Q d2Log109Lo d2Log109Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log109Bounds
  have hn1 : x-((d2Transfer448S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448S1,d2Transfer448Lo,d2Transfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer448C1 then |x-((d2Transfer448S1:ℚ):ℝ)| ≤ ((d2Log64Q:ℚ):ℝ) else ((d2Log64Q:ℚ):ℝ) ≤ |x-((d2Transfer448S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer448S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448S1,d2Transfer448Lo,d2Transfer448Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer448C1,d2Log64Q,d2Transfer448S1,d2Transfer448Lo,d2Transfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer448C1 d2Transfer448S1 d2Log64Q d2Log64Lo d2Log64Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log64Bounds
  have har : (((weightedUpper d2Transfer448C0 d2Log109Lo d2Log109Hi:ℚ):ℝ) + ((weightedUpper d2Transfer448C1 d2Log64Lo d2Log64Hi:ℚ):ℝ)) ≤ ((d2Transfer448Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer448Arithmetic
  linarith
#print axioms d2Transfer448Arithmetic
#print axioms d2Transfer448Bound
def d2Transfer449Lo : ℚ := (d2LitsNearTransfers056.q2 (31708803) 1 (-27))
def d2Transfer449Hi : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer449Cap : ℚ := (d2LitsNearTransfers056.q2 (15113656175) 1 (-40))
def d2Transfer449C0 : ℚ := (d2LitsNearTransfers056.q2 (23) 25 (-5))
def d2Transfer449S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer449Arithmetic : weightedUpper d2Transfer449C0 d2Log110Lo d2Log110Hi ≤ d2Transfer449Cap := by decide +kernel
theorem d2Transfer449Bound : ∀ x ∈ Set.Icc ((d2Transfer449Lo:ℚ):ℝ) ((d2Transfer449Hi:ℚ):ℝ), ((d2Transfer449C0:ℚ):ℝ)*Real.log |x-((d2Transfer449S0:ℚ):ℝ)| ≤ ((d2Transfer449Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer449S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer449S0,d2Transfer449Lo,d2Transfer449Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer449C0 then |x-((d2Transfer449S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer449S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer449S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer449S0,d2Transfer449Lo,d2Transfer449Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer449C0,d2Log110Q,d2Transfer449S0,d2Transfer449Lo,d2Transfer449Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer449C0 d2Transfer449S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have har : (((weightedUpper d2Transfer449C0 d2Log110Lo d2Log110Hi:ℚ):ℝ)) ≤ ((d2Transfer449Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer449Arithmetic
  linarith
#print axioms d2Transfer449Arithmetic
#print axioms d2Transfer449Bound
def d2Transfer450Lo : ℚ := (d2LitsNearTransfers056.q2 (31708803) 1 (-27))
def d2Transfer450Hi : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer450Cap : ℚ := (d2LitsNearTransfers056.q2 (30439539927) 1 (-40))
def d2Transfer450C0 : ℚ := (d2LitsNearTransfers056.q2 (3) 275 (-5))
def d2Transfer450S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
def d2Transfer450C1 : ℚ := (d2LitsNearTransfers056.q2 (-5) 11 (-4))
def d2Transfer450S1 : ℚ := (d2LitsNearTransfers056.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer450Arithmetic : weightedUpper d2Transfer450C0 d2Log110Lo d2Log110Hi + weightedUpper d2Transfer450C1 d2Log64Lo d2Log64Hi ≤ d2Transfer450Cap := by decide +kernel
theorem d2Transfer450Bound : ∀ x ∈ Set.Icc ((d2Transfer450Lo:ℚ):ℝ) ((d2Transfer450Hi:ℚ):ℝ), ((d2Transfer450C0:ℚ):ℝ)*Real.log |x-((d2Transfer450S0:ℚ):ℝ)| + ((d2Transfer450C1:ℚ):ℝ)*Real.log |x-((d2Transfer450S1:ℚ):ℝ)| ≤ ((d2Transfer450Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer450S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450S0,d2Transfer450Lo,d2Transfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer450C0 then |x-((d2Transfer450S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer450S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer450S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450S0,d2Transfer450Lo,d2Transfer450Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450C0,d2Log110Q,d2Transfer450S0,d2Transfer450Lo,d2Transfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer450C0 d2Transfer450S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have hn1 : x-((d2Transfer450S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450S1,d2Transfer450Lo,d2Transfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer450C1 then |x-((d2Transfer450S1:ℚ):ℝ)| ≤ ((d2Log64Q:ℚ):ℝ) else ((d2Log64Q:ℚ):ℝ) ≤ |x-((d2Transfer450S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer450S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450S1,d2Transfer450Lo,d2Transfer450Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer450C1,d2Log64Q,d2Transfer450S1,d2Transfer450Lo,d2Transfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer450C1 d2Transfer450S1 d2Log64Q d2Log64Lo d2Log64Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log64Bounds
  have har : (((weightedUpper d2Transfer450C0 d2Log110Lo d2Log110Hi:ℚ):ℝ) + ((weightedUpper d2Transfer450C1 d2Log64Lo d2Log64Hi:ℚ):ℝ)) ≤ ((d2Transfer450Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer450Arithmetic
  linarith
#print axioms d2Transfer450Arithmetic
#print axioms d2Transfer450Bound
def d2Transfer451Lo : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer451Hi : ℚ := (d2LitsNearTransfers056.q2 (35064245) 1 (-27))
def d2Transfer451Cap : ℚ := (d2LitsNearTransfers056.q2 (1169469059) 1 (-40))
def d2Transfer451C0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer451S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
def d2Transfer451C1 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer451S1 : ℚ := (d2LitsNearTransfers056.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer451Arithmetic : weightedUpper d2Transfer451C0 d2Log110Lo d2Log110Hi + weightedUpper d2Transfer451C1 d2Log63Lo d2Log63Hi ≤ d2Transfer451Cap := by decide +kernel
theorem d2Transfer451Bound : ∀ x ∈ Set.Icc ((d2Transfer451Lo:ℚ):ℝ) ((d2Transfer451Hi:ℚ):ℝ), ((d2Transfer451C0:ℚ):ℝ)*Real.log |x-((d2Transfer451S0:ℚ):ℝ)| + ((d2Transfer451C1:ℚ):ℝ)*Real.log |x-((d2Transfer451S1:ℚ):ℝ)| ≤ ((d2Transfer451Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer451S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451S0,d2Transfer451Lo,d2Transfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer451C0 then |x-((d2Transfer451S0:ℚ):ℝ)| ≤ ((d2Log110Q:ℚ):ℝ) else ((d2Log110Q:ℚ):ℝ) ≤ |x-((d2Transfer451S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer451S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451S0,d2Transfer451Lo,d2Transfer451Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451C0,d2Log110Q,d2Transfer451S0,d2Transfer451Lo,d2Transfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer451C0 d2Transfer451S0 d2Log110Q d2Log110Lo d2Log110Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log110Bounds
  have hn1 : x-((d2Transfer451S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451S1,d2Transfer451Lo,d2Transfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer451C1 then |x-((d2Transfer451S1:ℚ):ℝ)| ≤ ((d2Log63Q:ℚ):ℝ) else ((d2Log63Q:ℚ):ℝ) ≤ |x-((d2Transfer451S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer451S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451S1,d2Transfer451Lo,d2Transfer451Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer451C1,d2Log63Q,d2Transfer451S1,d2Transfer451Lo,d2Transfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer451C1 d2Transfer451S1 d2Log63Q d2Log63Lo d2Log63Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log63Bounds
  have har : (((weightedUpper d2Transfer451C0 d2Log110Lo d2Log110Hi:ℚ):ℝ) + ((weightedUpper d2Transfer451C1 d2Log63Lo d2Log63Hi:ℚ):ℝ)) ≤ ((d2Transfer451Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer451Arithmetic
  linarith
#print axioms d2Transfer451Arithmetic
#print axioms d2Transfer451Bound
def d2Transfer452Lo : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer452Hi : ℚ := (d2LitsNearTransfers056.q2 (35064245) 1 (-27))
def d2Transfer452Cap : ℚ := (d2LitsNearTransfers056.q2 (15113656175) 1 (-40))
def d2Transfer452C0 : ℚ := (d2LitsNearTransfers056.q2 (23) 25 (-5))
def d2Transfer452S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer452Arithmetic : weightedUpper d2Transfer452C0 d2Log111Lo d2Log111Hi ≤ d2Transfer452Cap := by decide +kernel
theorem d2Transfer452Bound : ∀ x ∈ Set.Icc ((d2Transfer452Lo:ℚ):ℝ) ((d2Transfer452Hi:ℚ):ℝ), ((d2Transfer452C0:ℚ):ℝ)*Real.log |x-((d2Transfer452S0:ℚ):ℝ)| ≤ ((d2Transfer452Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer452S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer452S0,d2Transfer452Lo,d2Transfer452Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer452C0 then |x-((d2Transfer452S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer452S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer452S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer452S0,d2Transfer452Lo,d2Transfer452Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer452C0,d2Log111Q,d2Transfer452S0,d2Transfer452Lo,d2Transfer452Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer452C0 d2Transfer452S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have har : (((weightedUpper d2Transfer452C0 d2Log111Lo d2Log111Hi:ℚ):ℝ)) ≤ ((d2Transfer452Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer452Arithmetic
  linarith
#print axioms d2Transfer452Arithmetic
#print axioms d2Transfer452Bound
def d2Transfer453Lo : ℚ := (d2LitsNearTransfers056.q2 (8346631) 1 (-25))
def d2Transfer453Hi : ℚ := (d2LitsNearTransfers056.q2 (35064245) 1 (-27))
def d2Transfer453Cap : ℚ := (d2LitsNearTransfers056.q2 (30439539927) 1 (-40))
def d2Transfer453C0 : ℚ := (d2LitsNearTransfers056.q2 (3) 275 (-5))
def d2Transfer453S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
def d2Transfer453C1 : ℚ := (d2LitsNearTransfers056.q2 (-5) 11 (-4))
def d2Transfer453S1 : ℚ := (d2LitsNearTransfers056.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer453Arithmetic : weightedUpper d2Transfer453C0 d2Log111Lo d2Log111Hi + weightedUpper d2Transfer453C1 d2Log63Lo d2Log63Hi ≤ d2Transfer453Cap := by decide +kernel
theorem d2Transfer453Bound : ∀ x ∈ Set.Icc ((d2Transfer453Lo:ℚ):ℝ) ((d2Transfer453Hi:ℚ):ℝ), ((d2Transfer453C0:ℚ):ℝ)*Real.log |x-((d2Transfer453S0:ℚ):ℝ)| + ((d2Transfer453C1:ℚ):ℝ)*Real.log |x-((d2Transfer453S1:ℚ):ℝ)| ≤ ((d2Transfer453Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer453S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453S0,d2Transfer453Lo,d2Transfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer453C0 then |x-((d2Transfer453S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer453S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer453S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453S0,d2Transfer453Lo,d2Transfer453Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453C0,d2Log111Q,d2Transfer453S0,d2Transfer453Lo,d2Transfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer453C0 d2Transfer453S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have hn1 : x-((d2Transfer453S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453S1,d2Transfer453Lo,d2Transfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer453C1 then |x-((d2Transfer453S1:ℚ):ℝ)| ≤ ((d2Log63Q:ℚ):ℝ) else ((d2Log63Q:ℚ):ℝ) ≤ |x-((d2Transfer453S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer453S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453S1,d2Transfer453Lo,d2Transfer453Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer453C1,d2Log63Q,d2Transfer453S1,d2Transfer453Lo,d2Transfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer453C1 d2Transfer453S1 d2Log63Q d2Log63Lo d2Log63Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log63Bounds
  have har : (((weightedUpper d2Transfer453C0 d2Log111Lo d2Log111Hi:ℚ):ℝ) + ((weightedUpper d2Transfer453C1 d2Log63Lo d2Log63Hi:ℚ):ℝ)) ≤ ((d2Transfer453Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer453Arithmetic
  linarith
#print axioms d2Transfer453Arithmetic
#print axioms d2Transfer453Bound
def d2Transfer454Lo : ℚ := (d2LitsNearTransfers056.q2 (35064245) 1 (-27))
def d2Transfer454Hi : ℚ := (d2LitsNearTransfers056.q2 (18370983) 1 (-26))
def d2Transfer454Cap : ℚ := (d2LitsNearTransfers056.q2 (1169469059) 1 (-40))
def d2Transfer454C0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer454S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
def d2Transfer454C1 : ℚ := (d2LitsNearTransfers056.q2 (-1) 55 (-3))
def d2Transfer454S1 : ℚ := (d2LitsNearTransfers056.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer454Arithmetic : weightedUpper d2Transfer454C0 d2Log111Lo d2Log111Hi + weightedUpper d2Transfer454C1 d2Log62Lo d2Log62Hi ≤ d2Transfer454Cap := by decide +kernel
theorem d2Transfer454Bound : ∀ x ∈ Set.Icc ((d2Transfer454Lo:ℚ):ℝ) ((d2Transfer454Hi:ℚ):ℝ), ((d2Transfer454C0:ℚ):ℝ)*Real.log |x-((d2Transfer454S0:ℚ):ℝ)| + ((d2Transfer454C1:ℚ):ℝ)*Real.log |x-((d2Transfer454S1:ℚ):ℝ)| ≤ ((d2Transfer454Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer454S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454S0,d2Transfer454Lo,d2Transfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer454C0 then |x-((d2Transfer454S0:ℚ):ℝ)| ≤ ((d2Log111Q:ℚ):ℝ) else ((d2Log111Q:ℚ):ℝ) ≤ |x-((d2Transfer454S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer454S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454S0,d2Transfer454Lo,d2Transfer454Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454C0,d2Log111Q,d2Transfer454S0,d2Transfer454Lo,d2Transfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer454C0 d2Transfer454S0 d2Log111Q d2Log111Lo d2Log111Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log111Bounds
  have hn1 : x-((d2Transfer454S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454S1,d2Transfer454Lo,d2Transfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer454C1 then |x-((d2Transfer454S1:ℚ):ℝ)| ≤ ((d2Log62Q:ℚ):ℝ) else ((d2Log62Q:ℚ):ℝ) ≤ |x-((d2Transfer454S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer454S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454S1,d2Transfer454Lo,d2Transfer454Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer454C1,d2Log62Q,d2Transfer454S1,d2Transfer454Lo,d2Transfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer454C1 d2Transfer454S1 d2Log62Q d2Log62Lo d2Log62Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log62Bounds
  have har : (((weightedUpper d2Transfer454C0 d2Log111Lo d2Log111Hi:ℚ):ℝ) + ((weightedUpper d2Transfer454C1 d2Log62Lo d2Log62Hi:ℚ):ℝ)) ≤ ((d2Transfer454Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer454Arithmetic
  linarith
#print axioms d2Transfer454Arithmetic
#print axioms d2Transfer454Bound
def d2Transfer455Lo : ℚ := (d2LitsNearTransfers056.q2 (35064245) 1 (-27))
def d2Transfer455Hi : ℚ := (d2LitsNearTransfers056.q2 (18370983) 1 (-26))
def d2Transfer455Cap : ℚ := (d2LitsNearTransfers056.q2 (15113656175) 1 (-40))
def d2Transfer455C0 : ℚ := (d2LitsNearTransfers056.q2 (23) 25 (-5))
def d2Transfer455S0 : ℚ := (d2LitsNearTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer455Arithmetic : weightedUpper d2Transfer455C0 d2Log112Lo d2Log112Hi ≤ d2Transfer455Cap := by decide +kernel
theorem d2Transfer455Bound : ∀ x ∈ Set.Icc ((d2Transfer455Lo:ℚ):ℝ) ((d2Transfer455Hi:ℚ):ℝ), ((d2Transfer455C0:ℚ):ℝ)*Real.log |x-((d2Transfer455S0:ℚ):ℝ)| ≤ ((d2Transfer455Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer455S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer455S0,d2Transfer455Lo,d2Transfer455Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer455C0 then |x-((d2Transfer455S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer455S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer455S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer455S0,d2Transfer455Lo,d2Transfer455Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers056.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2LitsNearLogCache007.q2, d2Transfer455C0,d2Log112Q,d2Transfer455S0,d2Transfer455Lo,d2Transfer455Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer455C0 d2Transfer455S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have har : (((weightedUpper d2Transfer455C0 d2Log112Lo d2Log112Hi:ℚ):ℝ)) ≤ ((d2Transfer455Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer455Arithmetic
  linarith
#print axioms d2Transfer455Arithmetic
#print axioms d2Transfer455Bound
end CatalanMeasure.GenD.Signed.Data.Cells

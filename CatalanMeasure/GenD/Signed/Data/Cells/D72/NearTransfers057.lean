module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
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
namespace d2LitsNearTransfers057
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers057
open D72.LogTransfer
def d2Transfer456Lo : ℚ := (d2LitsNearTransfers057.q2 (35064245) 1 (-27))
def d2Transfer456Hi : ℚ := (d2LitsNearTransfers057.q2 (18370983) 1 (-26))
def d2Transfer456Cap : ℚ := (d2LitsNearTransfers057.q2 (30439539927) 1 (-40))
def d2Transfer456C0 : ℚ := (d2LitsNearTransfers057.q2 (3) 275 (-5))
def d2Transfer456S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer456C1 : ℚ := (d2LitsNearTransfers057.q2 (-5) 11 (-4))
def d2Transfer456S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer456Arithmetic : weightedUpper d2Transfer456C0 d2Log112Lo d2Log112Hi + weightedUpper d2Transfer456C1 d2Log62Lo d2Log62Hi ≤ d2Transfer456Cap := by decide +kernel
theorem d2Transfer456Bound : ∀ x ∈ Set.Icc ((d2Transfer456Lo:ℚ):ℝ) ((d2Transfer456Hi:ℚ):ℝ), ((d2Transfer456C0:ℚ):ℝ)*Real.log |x-((d2Transfer456S0:ℚ):ℝ)| + ((d2Transfer456C1:ℚ):ℝ)*Real.log |x-((d2Transfer456S1:ℚ):ℝ)| ≤ ((d2Transfer456Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer456S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456S0,d2Transfer456Lo,d2Transfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer456C0 then |x-((d2Transfer456S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer456S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer456S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456S0,d2Transfer456Lo,d2Transfer456Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456C0,d2Log112Q,d2Transfer456S0,d2Transfer456Lo,d2Transfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer456C0 d2Transfer456S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have hn1 : x-((d2Transfer456S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456S1,d2Transfer456Lo,d2Transfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer456C1 then |x-((d2Transfer456S1:ℚ):ℝ)| ≤ ((d2Log62Q:ℚ):ℝ) else ((d2Log62Q:ℚ):ℝ) ≤ |x-((d2Transfer456S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer456S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456S1,d2Transfer456Lo,d2Transfer456Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer456C1,d2Log62Q,d2Transfer456S1,d2Transfer456Lo,d2Transfer456Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer456C1 d2Transfer456S1 d2Log62Q d2Log62Lo d2Log62Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log62Bounds
  have har : (((weightedUpper d2Transfer456C0 d2Log112Lo d2Log112Hi:ℚ):ℝ) + ((weightedUpper d2Transfer456C1 d2Log62Lo d2Log62Hi:ℚ):ℝ)) ≤ ((d2Transfer456Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer456Arithmetic
  linarith
#print axioms d2Transfer456Arithmetic
#print axioms d2Transfer456Bound
def d2Transfer457Lo : ℚ := (d2LitsNearTransfers057.q2 (18370983) 1 (-26))
def d2Transfer457Hi : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer457Cap : ℚ := (d2LitsNearTransfers057.q2 (1169469059) 1 (-40))
def d2Transfer457C0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer457S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer457C1 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer457S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer457Arithmetic : weightedUpper d2Transfer457C0 d2Log112Lo d2Log112Hi + weightedUpper d2Transfer457C1 d2Log61Lo d2Log61Hi ≤ d2Transfer457Cap := by decide +kernel
theorem d2Transfer457Bound : ∀ x ∈ Set.Icc ((d2Transfer457Lo:ℚ):ℝ) ((d2Transfer457Hi:ℚ):ℝ), ((d2Transfer457C0:ℚ):ℝ)*Real.log |x-((d2Transfer457S0:ℚ):ℝ)| + ((d2Transfer457C1:ℚ):ℝ)*Real.log |x-((d2Transfer457S1:ℚ):ℝ)| ≤ ((d2Transfer457Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer457S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457S0,d2Transfer457Lo,d2Transfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer457C0 then |x-((d2Transfer457S0:ℚ):ℝ)| ≤ ((d2Log112Q:ℚ):ℝ) else ((d2Log112Q:ℚ):ℝ) ≤ |x-((d2Transfer457S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer457S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457S0,d2Transfer457Lo,d2Transfer457Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457C0,d2Log112Q,d2Transfer457S0,d2Transfer457Lo,d2Transfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer457C0 d2Transfer457S0 d2Log112Q d2Log112Lo d2Log112Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log112Bounds
  have hn1 : x-((d2Transfer457S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457S1,d2Transfer457Lo,d2Transfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer457C1 then |x-((d2Transfer457S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2Transfer457S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer457S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457S1,d2Transfer457Lo,d2Transfer457Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer457C1,d2Log61Q,d2Transfer457S1,d2Transfer457Lo,d2Transfer457Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer457C1 d2Transfer457S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2Transfer457C0 d2Log112Lo d2Log112Hi:ℚ):ℝ) + ((weightedUpper d2Transfer457C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2Transfer457Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer457Arithmetic
  linarith
#print axioms d2Transfer457Arithmetic
#print axioms d2Transfer457Bound
def d2Transfer458Lo : ℚ := (d2LitsNearTransfers057.q2 (18370983) 1 (-26))
def d2Transfer458Hi : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer458Cap : ℚ := (d2LitsNearTransfers057.q2 (15113656175) 1 (-40))
def d2Transfer458C0 : ℚ := (d2LitsNearTransfers057.q2 (23) 25 (-5))
def d2Transfer458S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer458Arithmetic : weightedUpper d2Transfer458C0 d2Log113Lo d2Log113Hi ≤ d2Transfer458Cap := by decide +kernel
theorem d2Transfer458Bound : ∀ x ∈ Set.Icc ((d2Transfer458Lo:ℚ):ℝ) ((d2Transfer458Hi:ℚ):ℝ), ((d2Transfer458C0:ℚ):ℝ)*Real.log |x-((d2Transfer458S0:ℚ):ℝ)| ≤ ((d2Transfer458Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer458S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer458S0,d2Transfer458Lo,d2Transfer458Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer458C0 then |x-((d2Transfer458S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer458S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer458S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer458S0,d2Transfer458Lo,d2Transfer458Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer458C0,d2Log113Q,d2Transfer458S0,d2Transfer458Lo,d2Transfer458Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer458C0 d2Transfer458S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2Transfer458C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2Transfer458Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer458Arithmetic
  linarith
#print axioms d2Transfer458Arithmetic
#print axioms d2Transfer458Bound
def d2Transfer459Lo : ℚ := (d2LitsNearTransfers057.q2 (18370983) 1 (-26))
def d2Transfer459Hi : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer459Cap : ℚ := (d2LitsNearTransfers057.q2 (30439539927) 1 (-40))
def d2Transfer459C0 : ℚ := (d2LitsNearTransfers057.q2 (3) 275 (-5))
def d2Transfer459S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer459C1 : ℚ := (d2LitsNearTransfers057.q2 (-5) 11 (-4))
def d2Transfer459S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer459Arithmetic : weightedUpper d2Transfer459C0 d2Log113Lo d2Log113Hi + weightedUpper d2Transfer459C1 d2Log61Lo d2Log61Hi ≤ d2Transfer459Cap := by decide +kernel
theorem d2Transfer459Bound : ∀ x ∈ Set.Icc ((d2Transfer459Lo:ℚ):ℝ) ((d2Transfer459Hi:ℚ):ℝ), ((d2Transfer459C0:ℚ):ℝ)*Real.log |x-((d2Transfer459S0:ℚ):ℝ)| + ((d2Transfer459C1:ℚ):ℝ)*Real.log |x-((d2Transfer459S1:ℚ):ℝ)| ≤ ((d2Transfer459Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer459S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459S0,d2Transfer459Lo,d2Transfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer459C0 then |x-((d2Transfer459S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer459S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer459S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459S0,d2Transfer459Lo,d2Transfer459Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459C0,d2Log113Q,d2Transfer459S0,d2Transfer459Lo,d2Transfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer459C0 d2Transfer459S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2Transfer459S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459S1,d2Transfer459Lo,d2Transfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer459C1 then |x-((d2Transfer459S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2Transfer459S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer459S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459S1,d2Transfer459Lo,d2Transfer459Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer459C1,d2Log61Q,d2Transfer459S1,d2Transfer459Lo,d2Transfer459Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer459C1 d2Transfer459S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2Transfer459C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2Transfer459C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2Transfer459Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer459Arithmetic
  linarith
#print axioms d2Transfer459Arithmetic
#print axioms d2Transfer459Bound
def d2Transfer460Lo : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer460Hi : ℚ := (d2LitsNearTransfers057.q2 (21726425) 1 (-26))
def d2Transfer460Cap : ℚ := (d2LitsNearTransfers057.q2 (1169469059) 1 (-40))
def d2Transfer460C0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer460S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer460C1 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer460S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer460Arithmetic : weightedUpper d2Transfer460C0 d2Log113Lo d2Log113Hi + weightedUpper d2Transfer460C1 d2Log60Lo d2Log60Hi ≤ d2Transfer460Cap := by decide +kernel
theorem d2Transfer460Bound : ∀ x ∈ Set.Icc ((d2Transfer460Lo:ℚ):ℝ) ((d2Transfer460Hi:ℚ):ℝ), ((d2Transfer460C0:ℚ):ℝ)*Real.log |x-((d2Transfer460S0:ℚ):ℝ)| + ((d2Transfer460C1:ℚ):ℝ)*Real.log |x-((d2Transfer460S1:ℚ):ℝ)| ≤ ((d2Transfer460Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer460S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460S0,d2Transfer460Lo,d2Transfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer460C0 then |x-((d2Transfer460S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer460S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer460S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460S0,d2Transfer460Lo,d2Transfer460Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460C0,d2Log113Q,d2Transfer460S0,d2Transfer460Lo,d2Transfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer460C0 d2Transfer460S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2Transfer460S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460S1,d2Transfer460Lo,d2Transfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer460C1 then |x-((d2Transfer460S1:ℚ):ℝ)| ≤ ((d2Log60Q:ℚ):ℝ) else ((d2Log60Q:ℚ):ℝ) ≤ |x-((d2Transfer460S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer460S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460S1,d2Transfer460Lo,d2Transfer460Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer460C1,d2Log60Q,d2Transfer460S1,d2Transfer460Lo,d2Transfer460Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer460C1 d2Transfer460S1 d2Log60Q d2Log60Lo d2Log60Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log60Bounds
  have har : (((weightedUpper d2Transfer460C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2Transfer460C1 d2Log60Lo d2Log60Hi:ℚ):ℝ)) ≤ ((d2Transfer460Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer460Arithmetic
  linarith
#print axioms d2Transfer460Arithmetic
#print axioms d2Transfer460Bound
def d2Transfer461Lo : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer461Hi : ℚ := (d2LitsNearTransfers057.q2 (21726425) 1 (-26))
def d2Transfer461Cap : ℚ := (d2LitsNearTransfers057.q2 (15113656175) 1 (-40))
def d2Transfer461C0 : ℚ := (d2LitsNearTransfers057.q2 (23) 25 (-5))
def d2Transfer461S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer461Arithmetic : weightedUpper d2Transfer461C0 d2Log114Lo d2Log114Hi ≤ d2Transfer461Cap := by decide +kernel
theorem d2Transfer461Bound : ∀ x ∈ Set.Icc ((d2Transfer461Lo:ℚ):ℝ) ((d2Transfer461Hi:ℚ):ℝ), ((d2Transfer461C0:ℚ):ℝ)*Real.log |x-((d2Transfer461S0:ℚ):ℝ)| ≤ ((d2Transfer461Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer461S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer461S0,d2Transfer461Lo,d2Transfer461Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer461C0 then |x-((d2Transfer461S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer461S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer461S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer461S0,d2Transfer461Lo,d2Transfer461Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer461C0,d2Log114Q,d2Transfer461S0,d2Transfer461Lo,d2Transfer461Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer461C0 d2Transfer461S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have har : (((weightedUpper d2Transfer461C0 d2Log114Lo d2Log114Hi:ℚ):ℝ)) ≤ ((d2Transfer461Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer461Arithmetic
  linarith
#print axioms d2Transfer461Arithmetic
#print axioms d2Transfer461Bound
def d2Transfer462Lo : ℚ := (d2LitsNearTransfers057.q2 (313261) 1 (-20))
def d2Transfer462Hi : ℚ := (d2LitsNearTransfers057.q2 (21726425) 1 (-26))
def d2Transfer462Cap : ℚ := (d2LitsNearTransfers057.q2 (30439539927) 1 (-40))
def d2Transfer462C0 : ℚ := (d2LitsNearTransfers057.q2 (3) 275 (-5))
def d2Transfer462S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer462C1 : ℚ := (d2LitsNearTransfers057.q2 (-5) 11 (-4))
def d2Transfer462S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer462Arithmetic : weightedUpper d2Transfer462C0 d2Log114Lo d2Log114Hi + weightedUpper d2Transfer462C1 d2Log60Lo d2Log60Hi ≤ d2Transfer462Cap := by decide +kernel
theorem d2Transfer462Bound : ∀ x ∈ Set.Icc ((d2Transfer462Lo:ℚ):ℝ) ((d2Transfer462Hi:ℚ):ℝ), ((d2Transfer462C0:ℚ):ℝ)*Real.log |x-((d2Transfer462S0:ℚ):ℝ)| + ((d2Transfer462C1:ℚ):ℝ)*Real.log |x-((d2Transfer462S1:ℚ):ℝ)| ≤ ((d2Transfer462Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer462S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462S0,d2Transfer462Lo,d2Transfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer462C0 then |x-((d2Transfer462S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer462S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer462S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462S0,d2Transfer462Lo,d2Transfer462Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462C0,d2Log114Q,d2Transfer462S0,d2Transfer462Lo,d2Transfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer462C0 d2Transfer462S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have hn1 : x-((d2Transfer462S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462S1,d2Transfer462Lo,d2Transfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer462C1 then |x-((d2Transfer462S1:ℚ):ℝ)| ≤ ((d2Log60Q:ℚ):ℝ) else ((d2Log60Q:ℚ):ℝ) ≤ |x-((d2Transfer462S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer462S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462S1,d2Transfer462Lo,d2Transfer462Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer462C1,d2Log60Q,d2Transfer462S1,d2Transfer462Lo,d2Transfer462Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer462C1 d2Transfer462S1 d2Log60Q d2Log60Lo d2Log60Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log60Bounds
  have har : (((weightedUpper d2Transfer462C0 d2Log114Lo d2Log114Hi:ℚ):ℝ) + ((weightedUpper d2Transfer462C1 d2Log60Lo d2Log60Hi:ℚ):ℝ)) ≤ ((d2Transfer462Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer462Arithmetic
  linarith
#print axioms d2Transfer462Arithmetic
#print axioms d2Transfer462Bound
def d2Transfer463Lo : ℚ := (d2LitsNearTransfers057.q2 (21726425) 1 (-26))
def d2Transfer463Hi : ℚ := (d2LitsNearTransfers057.q2 (11702073) 1 (-25))
def d2Transfer463Cap : ℚ := (d2LitsNearTransfers057.q2 (1169469059) 1 (-40))
def d2Transfer463C0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer463S0 : ℚ := (d2LitsNearTransfers057.q2 (-1) 1 (0))
def d2Transfer463C1 : ℚ := (d2LitsNearTransfers057.q2 (-1) 55 (-3))
def d2Transfer463S1 : ℚ := (d2LitsNearTransfers057.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer463Arithmetic : weightedUpper d2Transfer463C0 d2Log114Lo d2Log114Hi + weightedUpper d2Transfer463C1 d2Log59Lo d2Log59Hi ≤ d2Transfer463Cap := by decide +kernel
theorem d2Transfer463Bound : ∀ x ∈ Set.Icc ((d2Transfer463Lo:ℚ):ℝ) ((d2Transfer463Hi:ℚ):ℝ), ((d2Transfer463C0:ℚ):ℝ)*Real.log |x-((d2Transfer463S0:ℚ):ℝ)| + ((d2Transfer463C1:ℚ):ℝ)*Real.log |x-((d2Transfer463S1:ℚ):ℝ)| ≤ ((d2Transfer463Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer463S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463S0,d2Transfer463Lo,d2Transfer463Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer463C0 then |x-((d2Transfer463S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer463S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer463S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463S0,d2Transfer463Lo,d2Transfer463Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463C0,d2Log114Q,d2Transfer463S0,d2Transfer463Lo,d2Transfer463Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer463C0 d2Transfer463S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have hn1 : x-((d2Transfer463S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463S1,d2Transfer463Lo,d2Transfer463Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer463C1 then |x-((d2Transfer463S1:ℚ):ℝ)| ≤ ((d2Log59Q:ℚ):ℝ) else ((d2Log59Q:ℚ):ℝ) ≤ |x-((d2Transfer463S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer463S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463S1,d2Transfer463Lo,d2Transfer463Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers057.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer463C1,d2Log59Q,d2Transfer463S1,d2Transfer463Lo,d2Transfer463Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer463C1 d2Transfer463S1 d2Log59Q d2Log59Lo d2Log59Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log59Bounds
  have har : (((weightedUpper d2Transfer463C0 d2Log114Lo d2Log114Hi:ℚ):ℝ) + ((weightedUpper d2Transfer463C1 d2Log59Lo d2Log59Hi:ℚ):ℝ)) ≤ ((d2Transfer463Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer463Arithmetic
  linarith
#print axioms d2Transfer463Arithmetic
#print axioms d2Transfer463Bound
end CatalanMeasure.GenD.Signed.Data.Cells

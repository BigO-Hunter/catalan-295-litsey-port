module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers034
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers034
open D72.LogTransfer
def d2Transfer272Lo : ℚ := (d2LitsNearTransfers034.q2 (1334457301) 1 (-31))
def d2Transfer272Hi : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer272Cap : ℚ := (d2LitsNearTransfers034.q2 (18726009857160385983239) 1 (-80))
def d2Transfer272C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (-5))
def d2Transfer272S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer272Arithmetic : weightedUpper d2Transfer272C0 d2Log137Lo d2Log137Hi ≤ d2Transfer272Cap := by decide +kernel
theorem d2Transfer272Bound : ∀ x ∈ Set.Icc ((d2Transfer272Lo:ℚ):ℝ) ((d2Transfer272Hi:ℚ):ℝ), ((d2Transfer272C0:ℚ):ℝ)*Real.log |x-((d2Transfer272S0:ℚ):ℝ)| ≤ ((d2Transfer272Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer272S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer272S0,d2Transfer272Lo,d2Transfer272Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer272C0 then |x-((d2Transfer272S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer272S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer272S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer272S0,d2Transfer272Lo,d2Transfer272Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer272C0,d2Log137Q,d2Transfer272S0,d2Transfer272Lo,d2Transfer272Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer272C0 d2Transfer272S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2Transfer272C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2Transfer272Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer272Arithmetic
  linarith
#print axioms d2Transfer272Arithmetic
#print axioms d2Transfer272Bound
def d2Transfer273Lo : ℚ := (d2LitsNearTransfers034.q2 (1334457301) 1 (-31))
def d2Transfer273Hi : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer273Cap : ℚ := (d2LitsNearTransfers034.q2 (35090847179451893347079) 1 (-80))
def d2Transfer273C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 11 (-5))
def d2Transfer273S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
def d2Transfer273C1 : ℚ := (d2LitsNearTransfers034.q2 (-5) 11 (-4))
def d2Transfer273S1 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer273Arithmetic : weightedUpper d2Transfer273C0 d2Log137Lo d2Log137Hi + weightedUpper d2Transfer273C1 d2Log37Lo d2Log37Hi ≤ d2Transfer273Cap := by decide +kernel
theorem d2Transfer273Bound : ∀ x ∈ Set.Icc ((d2Transfer273Lo:ℚ):ℝ) ((d2Transfer273Hi:ℚ):ℝ), ((d2Transfer273C0:ℚ):ℝ)*Real.log |x-((d2Transfer273S0:ℚ):ℝ)| + ((d2Transfer273C1:ℚ):ℝ)*Real.log |x-((d2Transfer273S1:ℚ):ℝ)| ≤ ((d2Transfer273Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer273S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273S0,d2Transfer273Lo,d2Transfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer273C0 then |x-((d2Transfer273S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2Transfer273S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer273S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273S0,d2Transfer273Lo,d2Transfer273Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273C0,d2Log137Q,d2Transfer273S0,d2Transfer273Lo,d2Transfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer273C0 d2Transfer273S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2Transfer273S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273S1,d2Transfer273Lo,d2Transfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer273C1 then |x-((d2Transfer273S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2Transfer273S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer273S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273S1,d2Transfer273Lo,d2Transfer273Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer273C1,d2Log37Q,d2Transfer273S1,d2Transfer273Lo,d2Transfer273Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer273C1 d2Transfer273S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2Transfer273C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2Transfer273C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2Transfer273Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer273Arithmetic
  linarith
#print axioms d2Transfer273Arithmetic
#print axioms d2Transfer273Bound
def d2Transfer274Lo : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer274Hi : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer274Cap : ℚ := (d2LitsNearTransfers034.q2 (1162696448405478776057) 1 (-79))
def d2Transfer274C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 25 (-4))
def d2Transfer274S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer274Arithmetic : weightedUpper d2Transfer274C0 d2Log138Lo d2Log138Hi ≤ d2Transfer274Cap := by decide +kernel
theorem d2Transfer274Bound : ∀ x ∈ Set.Icc ((d2Transfer274Lo:ℚ):ℝ) ((d2Transfer274Hi:ℚ):ℝ), ((d2Transfer274C0:ℚ):ℝ)*Real.log |x-((d2Transfer274S0:ℚ):ℝ)| ≤ ((d2Transfer274Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer274S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer274S0,d2Transfer274Lo,d2Transfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer274C0 then |x-((d2Transfer274S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2Transfer274S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer274S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer274S0,d2Transfer274Lo,d2Transfer274Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer274C0,d2Log138Q,d2Transfer274S0,d2Transfer274Lo,d2Transfer274Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer274C0 d2Transfer274S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have har : (((weightedUpper d2Transfer274C0 d2Log138Lo d2Log138Hi:ℚ):ℝ)) ≤ ((d2Transfer274Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer274Arithmetic
  linarith
#print axioms d2Transfer274Arithmetic
#print axioms d2Transfer274Bound
def d2Transfer275Lo : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer275Hi : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer275Cap : ℚ := (d2LitsNearTransfers034.q2 (1787846532723346447609) 1 (-79))
def d2Transfer275C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 275 (-4))
def d2Transfer275S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
def d2Transfer275C1 : ℚ := (d2LitsNearTransfers034.q2 (-1) 55 (-3))
def d2Transfer275S1 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer275Arithmetic : weightedUpper d2Transfer275C0 d2Log138Lo d2Log138Hi + weightedUpper d2Transfer275C1 d2Log36Lo d2Log36Hi ≤ d2Transfer275Cap := by decide +kernel
theorem d2Transfer275Bound : ∀ x ∈ Set.Icc ((d2Transfer275Lo:ℚ):ℝ) ((d2Transfer275Hi:ℚ):ℝ), ((d2Transfer275C0:ℚ):ℝ)*Real.log |x-((d2Transfer275S0:ℚ):ℝ)| + ((d2Transfer275C1:ℚ):ℝ)*Real.log |x-((d2Transfer275S1:ℚ):ℝ)| ≤ ((d2Transfer275Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer275S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275S0,d2Transfer275Lo,d2Transfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer275C0 then |x-((d2Transfer275S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2Transfer275S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer275S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275S0,d2Transfer275Lo,d2Transfer275Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275C0,d2Log138Q,d2Transfer275S0,d2Transfer275Lo,d2Transfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer275C0 d2Transfer275S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have hn1 : x-((d2Transfer275S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275S1,d2Transfer275Lo,d2Transfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer275C1 then |x-((d2Transfer275S1:ℚ):ℝ)| ≤ ((d2Log36Q:ℚ):ℝ) else ((d2Log36Q:ℚ):ℝ) ≤ |x-((d2Transfer275S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer275S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275S1,d2Transfer275Lo,d2Transfer275Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer275C1,d2Log36Q,d2Transfer275S1,d2Transfer275Lo,d2Transfer275Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer275C1 d2Transfer275S1 d2Log36Q d2Log36Lo d2Log36Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log36Bounds
  have har : (((weightedUpper d2Transfer275C0 d2Log138Lo d2Log138Hi:ℚ):ℝ) + ((weightedUpper d2Transfer275C1 d2Log36Lo d2Log36Hi:ℚ):ℝ)) ≤ ((d2Transfer275Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer275Arithmetic
  linarith
#print axioms d2Transfer275Arithmetic
#print axioms d2Transfer275Bound
def d2Transfer276Lo : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer276Hi : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer276Cap : ℚ := (d2LitsNearTransfers034.q2 (9399377577934826708217) 1 (-79))
def d2Transfer276C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (-5))
def d2Transfer276S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer276Arithmetic : weightedUpper d2Transfer276C0 d2Log138Lo d2Log138Hi ≤ d2Transfer276Cap := by decide +kernel
theorem d2Transfer276Bound : ∀ x ∈ Set.Icc ((d2Transfer276Lo:ℚ):ℝ) ((d2Transfer276Hi:ℚ):ℝ), ((d2Transfer276C0:ℚ):ℝ)*Real.log |x-((d2Transfer276S0:ℚ):ℝ)| ≤ ((d2Transfer276Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer276S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer276S0,d2Transfer276Lo,d2Transfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer276C0 then |x-((d2Transfer276S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2Transfer276S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer276S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer276S0,d2Transfer276Lo,d2Transfer276Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer276C0,d2Log138Q,d2Transfer276S0,d2Transfer276Lo,d2Transfer276Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer276C0 d2Transfer276S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have har : (((weightedUpper d2Transfer276C0 d2Log138Lo d2Log138Hi:ℚ):ℝ)) ≤ ((d2Transfer276Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer276Arithmetic
  linarith
#print axioms d2Transfer276Arithmetic
#print axioms d2Transfer276Bound
def d2Transfer277Lo : ℚ := (d2LitsNearTransfers034.q2 (668067511) 1 (-30))
def d2Transfer277Hi : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer277Cap : ℚ := (d2LitsNearTransfers034.q2 (17581796239080580390137) 1 (-79))
def d2Transfer277C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 11 (-5))
def d2Transfer277S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
def d2Transfer277C1 : ℚ := (d2LitsNearTransfers034.q2 (-5) 11 (-4))
def d2Transfer277S1 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer277Arithmetic : weightedUpper d2Transfer277C0 d2Log138Lo d2Log138Hi + weightedUpper d2Transfer277C1 d2Log36Lo d2Log36Hi ≤ d2Transfer277Cap := by decide +kernel
theorem d2Transfer277Bound : ∀ x ∈ Set.Icc ((d2Transfer277Lo:ℚ):ℝ) ((d2Transfer277Hi:ℚ):ℝ), ((d2Transfer277C0:ℚ):ℝ)*Real.log |x-((d2Transfer277S0:ℚ):ℝ)| + ((d2Transfer277C1:ℚ):ℝ)*Real.log |x-((d2Transfer277S1:ℚ):ℝ)| ≤ ((d2Transfer277Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer277S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277S0,d2Transfer277Lo,d2Transfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer277C0 then |x-((d2Transfer277S0:ℚ):ℝ)| ≤ ((d2Log138Q:ℚ):ℝ) else ((d2Log138Q:ℚ):ℝ) ≤ |x-((d2Transfer277S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer277S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277S0,d2Transfer277Lo,d2Transfer277Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277C0,d2Log138Q,d2Transfer277S0,d2Transfer277Lo,d2Transfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer277C0 d2Transfer277S0 d2Log138Q d2Log138Lo d2Log138Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log138Bounds
  have hn1 : x-((d2Transfer277S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277S1,d2Transfer277Lo,d2Transfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer277C1 then |x-((d2Transfer277S1:ℚ):ℝ)| ≤ ((d2Log36Q:ℚ):ℝ) else ((d2Log36Q:ℚ):ℝ) ≤ |x-((d2Transfer277S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer277S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277S1,d2Transfer277Lo,d2Transfer277Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer277C1,d2Log36Q,d2Transfer277S1,d2Transfer277Lo,d2Transfer277Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer277C1 d2Transfer277S1 d2Log36Q d2Log36Lo d2Log36Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log36Bounds
  have har : (((weightedUpper d2Transfer277C0 d2Log138Lo d2Log138Hi:ℚ):ℝ) + ((weightedUpper d2Transfer277C1 d2Log36Lo d2Log36Hi:ℚ):ℝ)) ≤ ((d2Transfer277Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer277Arithmetic
  linarith
#print axioms d2Transfer277Arithmetic
#print axioms d2Transfer277Bound
def d2Transfer278Lo : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer278Hi : ℚ := (d2LitsNearTransfers034.q2 (41859077) 1 (-26))
def d2Transfer278Cap : ℚ := (d2LitsNearTransfers034.q2 (149892803860600690063) 1 (-76))
def d2Transfer278C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 25 (-4))
def d2Transfer278S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer278Arithmetic : weightedUpper d2Transfer278C0 d2Log139Lo d2Log139Hi ≤ d2Transfer278Cap := by decide +kernel
theorem d2Transfer278Bound : ∀ x ∈ Set.Icc ((d2Transfer278Lo:ℚ):ℝ) ((d2Transfer278Hi:ℚ):ℝ), ((d2Transfer278C0:ℚ):ℝ)*Real.log |x-((d2Transfer278S0:ℚ):ℝ)| ≤ ((d2Transfer278Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer278S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer278S0,d2Transfer278Lo,d2Transfer278Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer278C0 then |x-((d2Transfer278S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer278S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer278S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer278S0,d2Transfer278Lo,d2Transfer278Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer278C0,d2Log139Q,d2Transfer278S0,d2Transfer278Lo,d2Transfer278Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer278C0 d2Transfer278S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2Transfer278C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2Transfer278Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer278Arithmetic
  linarith
#print axioms d2Transfer278Arithmetic
#print axioms d2Transfer278Bound
def d2Transfer279Lo : ℚ := (d2LitsNearTransfers034.q2 (1337812743) 1 (-31))
def d2Transfer279Hi : ℚ := (d2LitsNearTransfers034.q2 (41859077) 1 (-26))
def d2Transfer279Cap : ℚ := (d2LitsNearTransfers034.q2 (228036564400334149007) 1 (-76))
def d2Transfer279C0 : ℚ := (d2LitsNearTransfers034.q2 (1) 275 (-4))
def d2Transfer279S0 : ℚ := (d2LitsNearTransfers034.q2 (-1) 1 (0))
def d2Transfer279C1 : ℚ := (d2LitsNearTransfers034.q2 (-1) 55 (-3))
def d2Transfer279S1 : ℚ := (d2LitsNearTransfers034.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer279Arithmetic : weightedUpper d2Transfer279C0 d2Log139Lo d2Log139Hi + weightedUpper d2Transfer279C1 d2Log35Lo d2Log35Hi ≤ d2Transfer279Cap := by decide +kernel
theorem d2Transfer279Bound : ∀ x ∈ Set.Icc ((d2Transfer279Lo:ℚ):ℝ) ((d2Transfer279Hi:ℚ):ℝ), ((d2Transfer279C0:ℚ):ℝ)*Real.log |x-((d2Transfer279S0:ℚ):ℝ)| + ((d2Transfer279C1:ℚ):ℝ)*Real.log |x-((d2Transfer279S1:ℚ):ℝ)| ≤ ((d2Transfer279Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer279S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279S0,d2Transfer279Lo,d2Transfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer279C0 then |x-((d2Transfer279S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2Transfer279S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer279S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279S0,d2Transfer279Lo,d2Transfer279Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279C0,d2Log139Q,d2Transfer279S0,d2Transfer279Lo,d2Transfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer279C0 d2Transfer279S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2Transfer279S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279S1,d2Transfer279Lo,d2Transfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer279C1 then |x-((d2Transfer279S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2Transfer279S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer279S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279S1,d2Transfer279Lo,d2Transfer279Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers034.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2Transfer279C1,d2Log35Q,d2Transfer279S1,d2Transfer279Lo,d2Transfer279Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer279C1 d2Transfer279S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2Transfer279C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2Transfer279C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2Transfer279Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer279Arithmetic
  linarith
#print axioms d2Transfer279Arithmetic
#print axioms d2Transfer279Bound
end CatalanMeasure.GenD.Signed.Data.Cells

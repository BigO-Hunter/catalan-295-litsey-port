module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers021
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers021
open D72.LogTransfer
def d2WiderTransfer168Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (336550337) 1 (-29))
def d2WiderTransfer168Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer168Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (19238328556530536700837) 1 (-80))
def d2WiderTransfer168C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (-5))
def d2WiderTransfer168S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer168Arithmetic : weightedUpper d2WiderTransfer168C0 d2Log144Lo d2Log144Hi ≤ d2WiderTransfer168Cap := by decide +kernel
theorem d2WiderTransfer168Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer168Lo:ℚ):ℝ) ((d2WiderTransfer168Hi:ℚ):ℝ), ((d2WiderTransfer168C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer168S0:ℚ):ℝ)| ≤ ((d2WiderTransfer168Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer168S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer168S0,d2WiderTransfer168Lo,d2WiderTransfer168Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer168C0 then |x-((d2WiderTransfer168S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer168S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer168S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer168S0,d2WiderTransfer168Lo,d2WiderTransfer168Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer168C0,d2Log144Q,d2WiderTransfer168S0,d2WiderTransfer168Lo,d2WiderTransfer168Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer168C0 d2WiderTransfer168S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2WiderTransfer168C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer168Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer168Arithmetic
  linarith
#print axioms d2WiderTransfer168Arithmetic
#print axioms d2WiderTransfer168Bound
def d2WiderTransfer169Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (336550337) 1 (-29))
def d2WiderTransfer169Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer169Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (35603165878822044064677) 1 (-80))
def d2WiderTransfer169C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 11 (-5))
def d2WiderTransfer169S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
def d2WiderTransfer169C1 : ℚ := (d2LitsNearWiderTransfers021.q2 (-5) 11 (-4))
def d2WiderTransfer169S1 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer169Arithmetic : weightedUpper d2WiderTransfer169C0 d2Log144Lo d2Log144Hi + weightedUpper d2WiderTransfer169C1 d2Log30Lo d2Log30Hi ≤ d2WiderTransfer169Cap := by decide +kernel
theorem d2WiderTransfer169Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer169Lo:ℚ):ℝ) ((d2WiderTransfer169Hi:ℚ):ℝ), ((d2WiderTransfer169C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer169S0:ℚ):ℝ)| + ((d2WiderTransfer169C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer169S1:ℚ):ℝ)| ≤ ((d2WiderTransfer169Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer169S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169S0,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer169C0 then |x-((d2WiderTransfer169S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer169S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer169S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169S0,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169C0,d2Log144Q,d2WiderTransfer169S0,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer169C0 d2WiderTransfer169S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2WiderTransfer169S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169S1,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer169C1 then |x-((d2WiderTransfer169S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer169S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer169S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169S1,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer169C1,d2Log30Q,d2WiderTransfer169S1,d2WiderTransfer169Lo,d2WiderTransfer169Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer169C1 d2WiderTransfer169S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2WiderTransfer169C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer169C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer169Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer169Arithmetic
  linarith
#print axioms d2WiderTransfer169Arithmetic
#print axioms d2WiderTransfer169Bound
def d2WiderTransfer170Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer170Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer170Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (2838751284562214786385) 1 (-80))
def d2WiderTransfer170C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 25 (-4))
def d2WiderTransfer170S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer170Arithmetic : weightedUpper d2WiderTransfer170C0 d2Log145Lo d2Log145Hi ≤ d2WiderTransfer170Cap := by decide +kernel
theorem d2WiderTransfer170Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer170Lo:ℚ):ℝ) ((d2WiderTransfer170Hi:ℚ):ℝ), ((d2WiderTransfer170C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer170S0:ℚ):ℝ)| ≤ ((d2WiderTransfer170Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer170S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer170S0,d2WiderTransfer170Lo,d2WiderTransfer170Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer170C0 then |x-((d2WiderTransfer170S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer170S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer170S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer170S0,d2WiderTransfer170Lo,d2WiderTransfer170Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer170C0,d2Log145Q,d2WiderTransfer170S0,d2WiderTransfer170Lo,d2WiderTransfer170Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer170C0 d2WiderTransfer170S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2WiderTransfer170C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer170Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer170Arithmetic
  linarith
#print axioms d2WiderTransfer170Arithmetic
#print axioms d2WiderTransfer170Bound
def d2WiderTransfer171Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer171Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer171Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (4089051453197950129489) 1 (-80))
def d2WiderTransfer171C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 275 (-4))
def d2WiderTransfer171S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
def d2WiderTransfer171C1 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 55 (-3))
def d2WiderTransfer171S1 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer171Arithmetic : weightedUpper d2WiderTransfer171C0 d2Log145Lo d2Log145Hi + weightedUpper d2WiderTransfer171C1 d2Log29Lo d2Log29Hi ≤ d2WiderTransfer171Cap := by decide +kernel
theorem d2WiderTransfer171Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer171Lo:ℚ):ℝ) ((d2WiderTransfer171Hi:ℚ):ℝ), ((d2WiderTransfer171C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer171S0:ℚ):ℝ)| + ((d2WiderTransfer171C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer171S1:ℚ):ℝ)| ≤ ((d2WiderTransfer171Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer171S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171S0,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer171C0 then |x-((d2WiderTransfer171S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer171S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer171S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171S0,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171C0,d2Log145Q,d2WiderTransfer171S0,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer171C0 d2WiderTransfer171S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2WiderTransfer171S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171S1,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer171C1 then |x-((d2WiderTransfer171S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer171S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer171S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171S1,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer171C1,d2Log29Q,d2WiderTransfer171S1,d2WiderTransfer171Lo,d2WiderTransfer171Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer171C1 d2WiderTransfer171S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2WiderTransfer171C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer171C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer171Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer171Arithmetic
  linarith
#print axioms d2WiderTransfer171Arithmetic
#print axioms d2WiderTransfer171Bound
def d2WiderTransfer172Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer172Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer172Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (19312113543620910650705) 1 (-80))
def d2WiderTransfer172C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (-5))
def d2WiderTransfer172S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer172Arithmetic : weightedUpper d2WiderTransfer172C0 d2Log145Lo d2Log145Hi ≤ d2WiderTransfer172Cap := by decide +kernel
theorem d2WiderTransfer172Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer172Lo:ℚ):ℝ) ((d2WiderTransfer172Hi:ℚ):ℝ), ((d2WiderTransfer172C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer172S0:ℚ):ℝ)| ≤ ((d2WiderTransfer172Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer172S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer172S0,d2WiderTransfer172Lo,d2WiderTransfer172Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer172C0 then |x-((d2WiderTransfer172S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer172S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer172S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer172S0,d2WiderTransfer172Lo,d2WiderTransfer172Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer172C0,d2Log145Q,d2WiderTransfer172S0,d2WiderTransfer172Lo,d2WiderTransfer172Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer172C0 d2WiderTransfer172S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2WiderTransfer172C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer172Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer172Arithmetic
  linarith
#print axioms d2WiderTransfer172Arithmetic
#print axioms d2WiderTransfer172Bound
def d2WiderTransfer173Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (1347879069) 1 (-31))
def d2WiderTransfer173Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer173Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (35676950865912418014545) 1 (-80))
def d2WiderTransfer173C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 11 (-5))
def d2WiderTransfer173S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
def d2WiderTransfer173C1 : ℚ := (d2LitsNearWiderTransfers021.q2 (-5) 11 (-4))
def d2WiderTransfer173S1 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer173Arithmetic : weightedUpper d2WiderTransfer173C0 d2Log145Lo d2Log145Hi + weightedUpper d2WiderTransfer173C1 d2Log29Lo d2Log29Hi ≤ d2WiderTransfer173Cap := by decide +kernel
theorem d2WiderTransfer173Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer173Lo:ℚ):ℝ) ((d2WiderTransfer173Hi:ℚ):ℝ), ((d2WiderTransfer173C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer173S0:ℚ):ℝ)| + ((d2WiderTransfer173C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer173S1:ℚ):ℝ)| ≤ ((d2WiderTransfer173Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer173S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173S0,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer173C0 then |x-((d2WiderTransfer173S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer173S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer173S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173S0,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173C0,d2Log145Q,d2WiderTransfer173S0,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer173C0 d2WiderTransfer173S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2WiderTransfer173S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173S1,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer173C1 then |x-((d2WiderTransfer173S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer173S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer173S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173S1,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer173C1,d2Log29Q,d2WiderTransfer173S1,d2WiderTransfer173Lo,d2WiderTransfer173Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer173C1 d2WiderTransfer173S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2WiderTransfer173C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer173C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer173Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer173Arithmetic
  linarith
#print axioms d2WiderTransfer173Arithmetic
#print axioms d2WiderTransfer173Bound
def d2WiderTransfer174Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer174Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (1351234511) 1 (-31))
def d2WiderTransfer174Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (1456343657972225333883) 1 (-79))
def d2WiderTransfer174C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 25 (-4))
def d2WiderTransfer174S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer174Arithmetic : weightedUpper d2WiderTransfer174C0 d2Log146Lo d2Log146Hi ≤ d2WiderTransfer174Cap := by decide +kernel
theorem d2WiderTransfer174Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer174Lo:ℚ):ℝ) ((d2WiderTransfer174Hi:ℚ):ℝ), ((d2WiderTransfer174C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer174S0:ℚ):ℝ)| ≤ ((d2WiderTransfer174Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer174S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer174S0,d2WiderTransfer174Lo,d2WiderTransfer174Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer174C0 then |x-((d2WiderTransfer174S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer174S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer174S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer174S0,d2WiderTransfer174Lo,d2WiderTransfer174Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer174C0,d2Log146Q,d2WiderTransfer174S0,d2WiderTransfer174Lo,d2WiderTransfer174Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer174C0 d2WiderTransfer174S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2WiderTransfer174C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer174Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer174Arithmetic
  linarith
#print axioms d2WiderTransfer174Arithmetic
#print axioms d2WiderTransfer174Bound
def d2WiderTransfer175Lo : ℚ := (d2LitsNearWiderTransfers021.q2 (674778395) 1 (-30))
def d2WiderTransfer175Hi : ℚ := (d2LitsNearWiderTransfers021.q2 (1351234511) 1 (-31))
def d2WiderTransfer175Cap : ℚ := (d2LitsNearWiderTransfers021.q2 (2081493742290093005435) 1 (-79))
def d2WiderTransfer175C0 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 275 (-4))
def d2WiderTransfer175S0 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 1 (0))
def d2WiderTransfer175C1 : ℚ := (d2LitsNearWiderTransfers021.q2 (-1) 55 (-3))
def d2WiderTransfer175S1 : ℚ := (d2LitsNearWiderTransfers021.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer175Arithmetic : weightedUpper d2WiderTransfer175C0 d2Log146Lo d2Log146Hi + weightedUpper d2WiderTransfer175C1 d2Log28Lo d2Log28Hi ≤ d2WiderTransfer175Cap := by decide +kernel
theorem d2WiderTransfer175Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer175Lo:ℚ):ℝ) ((d2WiderTransfer175Hi:ℚ):ℝ), ((d2WiderTransfer175C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer175S0:ℚ):ℝ)| + ((d2WiderTransfer175C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer175S1:ℚ):ℝ)| ≤ ((d2WiderTransfer175Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer175S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175S0,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer175C0 then |x-((d2WiderTransfer175S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer175S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer175S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175S0,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175C0,d2Log146Q,d2WiderTransfer175S0,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer175C0 d2WiderTransfer175S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2WiderTransfer175S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175S1,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer175C1 then |x-((d2WiderTransfer175S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer175S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer175S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175S1,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers021.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer175C1,d2Log28Q,d2WiderTransfer175S1,d2WiderTransfer175Lo,d2WiderTransfer175Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer175C1 d2WiderTransfer175S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2WiderTransfer175C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer175C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer175Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer175Arithmetic
  linarith
#print axioms d2WiderTransfer175Arithmetic
#print axioms d2WiderTransfer175Bound
end CatalanMeasure.GenD.Signed.Data.Cells

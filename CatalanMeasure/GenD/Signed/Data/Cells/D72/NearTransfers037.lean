module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers037
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers037
open D72.LogTransfer
def d2Transfer296Lo : ℚ := (d2LitsNearTransfers037.q2 (1344523627) 1 (-31))
def d2Transfer296Hi : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer296Cap : ℚ := (d2LitsNearTransfers037.q2 (19164693976484106390377) 1 (-80))
def d2Transfer296C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (-5))
def d2Transfer296S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer296Arithmetic : weightedUpper d2Transfer296C0 d2Log143Lo d2Log143Hi ≤ d2Transfer296Cap := by decide +kernel
theorem d2Transfer296Bound : ∀ x ∈ Set.Icc ((d2Transfer296Lo:ℚ):ℝ) ((d2Transfer296Hi:ℚ):ℝ), ((d2Transfer296C0:ℚ):ℝ)*Real.log |x-((d2Transfer296S0:ℚ):ℝ)| ≤ ((d2Transfer296Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer296S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer296S0,d2Transfer296Lo,d2Transfer296Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer296C0 then |x-((d2Transfer296S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer296S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer296S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer296S0,d2Transfer296Lo,d2Transfer296Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer296C0,d2Log143Q,d2Transfer296S0,d2Transfer296Lo,d2Transfer296Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer296C0 d2Transfer296S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have har : (((weightedUpper d2Transfer296C0 d2Log143Lo d2Log143Hi:ℚ):ℝ)) ≤ ((d2Transfer296Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer296Arithmetic
  linarith
#print axioms d2Transfer296Arithmetic
#print axioms d2Transfer296Bound
def d2Transfer297Lo : ℚ := (d2LitsNearTransfers037.q2 (1344523627) 1 (-31))
def d2Transfer297Hi : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer297Cap : ℚ := (d2LitsNearTransfers037.q2 (35529531298775613754217) 1 (-80))
def d2Transfer297C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 11 (-5))
def d2Transfer297S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
def d2Transfer297C1 : ℚ := (d2LitsNearTransfers037.q2 (-5) 11 (-4))
def d2Transfer297S1 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer297Arithmetic : weightedUpper d2Transfer297C0 d2Log143Lo d2Log143Hi + weightedUpper d2Transfer297C1 d2Log31Lo d2Log31Hi ≤ d2Transfer297Cap := by decide +kernel
theorem d2Transfer297Bound : ∀ x ∈ Set.Icc ((d2Transfer297Lo:ℚ):ℝ) ((d2Transfer297Hi:ℚ):ℝ), ((d2Transfer297C0:ℚ):ℝ)*Real.log |x-((d2Transfer297S0:ℚ):ℝ)| + ((d2Transfer297C1:ℚ):ℝ)*Real.log |x-((d2Transfer297S1:ℚ):ℝ)| ≤ ((d2Transfer297Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer297S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297S0,d2Transfer297Lo,d2Transfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer297C0 then |x-((d2Transfer297S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer297S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer297S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297S0,d2Transfer297Lo,d2Transfer297Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297C0,d2Log143Q,d2Transfer297S0,d2Transfer297Lo,d2Transfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer297C0 d2Transfer297S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2Transfer297S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297S1,d2Transfer297Lo,d2Transfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer297C1 then |x-((d2Transfer297S1:ℚ):ℝ)| ≤ ((d2Log31Q:ℚ):ℝ) else ((d2Log31Q:ℚ):ℝ) ≤ |x-((d2Transfer297S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer297S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297S1,d2Transfer297Lo,d2Transfer297Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer297C1,d2Log31Q,d2Transfer297S1,d2Transfer297Lo,d2Transfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer297C1 d2Transfer297S1 d2Log31Q d2Log31Lo d2Log31Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log31Bounds
  have har : (((weightedUpper d2Transfer297C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2Transfer297C1 d2Log31Lo d2Log31Hi:ℚ):ℝ)) ≤ ((d2Transfer297Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer297Arithmetic
  linarith
#print axioms d2Transfer297Arithmetic
#print axioms d2Transfer297Bound
def d2Transfer298Lo : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer298Hi : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer298Cap : ℚ := (d2LitsNearTransfers037.q2 (2764966297471840836517) 1 (-80))
def d2Transfer298C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 25 (-4))
def d2Transfer298S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer298Arithmetic : weightedUpper d2Transfer298C0 d2Log144Lo d2Log144Hi ≤ d2Transfer298Cap := by decide +kernel
theorem d2Transfer298Bound : ∀ x ∈ Set.Icc ((d2Transfer298Lo:ℚ):ℝ) ((d2Transfer298Hi:ℚ):ℝ), ((d2Transfer298C0:ℚ):ℝ)*Real.log |x-((d2Transfer298S0:ℚ):ℝ)| ≤ ((d2Transfer298Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer298S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer298S0,d2Transfer298Lo,d2Transfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer298C0 then |x-((d2Transfer298S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer298S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer298S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer298S0,d2Transfer298Lo,d2Transfer298Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer298C0,d2Log144Q,d2Transfer298S0,d2Transfer298Lo,d2Transfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer298C0 d2Transfer298S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2Transfer298C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2Transfer298Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer298Arithmetic
  linarith
#print axioms d2Transfer298Arithmetic
#print axioms d2Transfer298Bound
def d2Transfer299Lo : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer299Hi : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer299Cap : ℚ := (d2LitsNearTransfers037.q2 (4015266466107576179621) 1 (-80))
def d2Transfer299C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 275 (-4))
def d2Transfer299S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
def d2Transfer299C1 : ℚ := (d2LitsNearTransfers037.q2 (-1) 55 (-3))
def d2Transfer299S1 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer299Arithmetic : weightedUpper d2Transfer299C0 d2Log144Lo d2Log144Hi + weightedUpper d2Transfer299C1 d2Log30Lo d2Log30Hi ≤ d2Transfer299Cap := by decide +kernel
theorem d2Transfer299Bound : ∀ x ∈ Set.Icc ((d2Transfer299Lo:ℚ):ℝ) ((d2Transfer299Hi:ℚ):ℝ), ((d2Transfer299C0:ℚ):ℝ)*Real.log |x-((d2Transfer299S0:ℚ):ℝ)| + ((d2Transfer299C1:ℚ):ℝ)*Real.log |x-((d2Transfer299S1:ℚ):ℝ)| ≤ ((d2Transfer299Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer299S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299S0,d2Transfer299Lo,d2Transfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer299C0 then |x-((d2Transfer299S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer299S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer299S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299S0,d2Transfer299Lo,d2Transfer299Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299C0,d2Log144Q,d2Transfer299S0,d2Transfer299Lo,d2Transfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer299C0 d2Transfer299S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2Transfer299S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299S1,d2Transfer299Lo,d2Transfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer299C1 then |x-((d2Transfer299S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2Transfer299S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer299S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299S1,d2Transfer299Lo,d2Transfer299Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer299C1,d2Log30Q,d2Transfer299S1,d2Transfer299Lo,d2Transfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer299C1 d2Transfer299S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2Transfer299C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2Transfer299C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2Transfer299Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer299Arithmetic
  linarith
#print axioms d2Transfer299Arithmetic
#print axioms d2Transfer299Bound
def d2Transfer300Lo : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer300Hi : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer300Cap : ℚ := (d2LitsNearTransfers037.q2 (19238328556530536700837) 1 (-80))
def d2Transfer300C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (-5))
def d2Transfer300S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer300Arithmetic : weightedUpper d2Transfer300C0 d2Log144Lo d2Log144Hi ≤ d2Transfer300Cap := by decide +kernel
theorem d2Transfer300Bound : ∀ x ∈ Set.Icc ((d2Transfer300Lo:ℚ):ℝ) ((d2Transfer300Hi:ℚ):ℝ), ((d2Transfer300C0:ℚ):ℝ)*Real.log |x-((d2Transfer300S0:ℚ):ℝ)| ≤ ((d2Transfer300Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer300S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer300S0,d2Transfer300Lo,d2Transfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer300C0 then |x-((d2Transfer300S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer300S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer300S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer300S0,d2Transfer300Lo,d2Transfer300Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer300C0,d2Log144Q,d2Transfer300S0,d2Transfer300Lo,d2Transfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer300C0 d2Transfer300S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2Transfer300C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2Transfer300Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer300Arithmetic
  linarith
#print axioms d2Transfer300Arithmetic
#print axioms d2Transfer300Bound
def d2Transfer301Lo : ℚ := (d2LitsNearTransfers037.q2 (336550337) 1 (-29))
def d2Transfer301Hi : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer301Cap : ℚ := (d2LitsNearTransfers037.q2 (35603165878822044064677) 1 (-80))
def d2Transfer301C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 11 (-5))
def d2Transfer301S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
def d2Transfer301C1 : ℚ := (d2LitsNearTransfers037.q2 (-5) 11 (-4))
def d2Transfer301S1 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer301Arithmetic : weightedUpper d2Transfer301C0 d2Log144Lo d2Log144Hi + weightedUpper d2Transfer301C1 d2Log30Lo d2Log30Hi ≤ d2Transfer301Cap := by decide +kernel
theorem d2Transfer301Bound : ∀ x ∈ Set.Icc ((d2Transfer301Lo:ℚ):ℝ) ((d2Transfer301Hi:ℚ):ℝ), ((d2Transfer301C0:ℚ):ℝ)*Real.log |x-((d2Transfer301S0:ℚ):ℝ)| + ((d2Transfer301C1:ℚ):ℝ)*Real.log |x-((d2Transfer301S1:ℚ):ℝ)| ≤ ((d2Transfer301Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer301S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301S0,d2Transfer301Lo,d2Transfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer301C0 then |x-((d2Transfer301S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer301S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer301S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301S0,d2Transfer301Lo,d2Transfer301Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301C0,d2Log144Q,d2Transfer301S0,d2Transfer301Lo,d2Transfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer301C0 d2Transfer301S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2Transfer301S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301S1,d2Transfer301Lo,d2Transfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer301C1 then |x-((d2Transfer301S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2Transfer301S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer301S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301S1,d2Transfer301Lo,d2Transfer301Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer301C1,d2Log30Q,d2Transfer301S1,d2Transfer301Lo,d2Transfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer301C1 d2Transfer301S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2Transfer301C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2Transfer301C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2Transfer301Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer301Arithmetic
  linarith
#print axioms d2Transfer301Arithmetic
#print axioms d2Transfer301Bound
def d2Transfer302Lo : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer302Hi : ℚ := (d2LitsNearTransfers037.q2 (674778395) 1 (-30))
def d2Transfer302Cap : ℚ := (d2LitsNearTransfers037.q2 (2838751284562214786385) 1 (-80))
def d2Transfer302C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 25 (-4))
def d2Transfer302S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer302Arithmetic : weightedUpper d2Transfer302C0 d2Log145Lo d2Log145Hi ≤ d2Transfer302Cap := by decide +kernel
theorem d2Transfer302Bound : ∀ x ∈ Set.Icc ((d2Transfer302Lo:ℚ):ℝ) ((d2Transfer302Hi:ℚ):ℝ), ((d2Transfer302C0:ℚ):ℝ)*Real.log |x-((d2Transfer302S0:ℚ):ℝ)| ≤ ((d2Transfer302Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer302S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer302S0,d2Transfer302Lo,d2Transfer302Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer302C0 then |x-((d2Transfer302S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer302S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer302S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer302S0,d2Transfer302Lo,d2Transfer302Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer302C0,d2Log145Q,d2Transfer302S0,d2Transfer302Lo,d2Transfer302Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer302C0 d2Transfer302S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2Transfer302C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2Transfer302Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer302Arithmetic
  linarith
#print axioms d2Transfer302Arithmetic
#print axioms d2Transfer302Bound
def d2Transfer303Lo : ℚ := (d2LitsNearTransfers037.q2 (1347879069) 1 (-31))
def d2Transfer303Hi : ℚ := (d2LitsNearTransfers037.q2 (674778395) 1 (-30))
def d2Transfer303Cap : ℚ := (d2LitsNearTransfers037.q2 (4089051453197950129489) 1 (-80))
def d2Transfer303C0 : ℚ := (d2LitsNearTransfers037.q2 (1) 275 (-4))
def d2Transfer303S0 : ℚ := (d2LitsNearTransfers037.q2 (-1) 1 (0))
def d2Transfer303C1 : ℚ := (d2LitsNearTransfers037.q2 (-1) 55 (-3))
def d2Transfer303S1 : ℚ := (d2LitsNearTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer303Arithmetic : weightedUpper d2Transfer303C0 d2Log145Lo d2Log145Hi + weightedUpper d2Transfer303C1 d2Log29Lo d2Log29Hi ≤ d2Transfer303Cap := by decide +kernel
theorem d2Transfer303Bound : ∀ x ∈ Set.Icc ((d2Transfer303Lo:ℚ):ℝ) ((d2Transfer303Hi:ℚ):ℝ), ((d2Transfer303C0:ℚ):ℝ)*Real.log |x-((d2Transfer303S0:ℚ):ℝ)| + ((d2Transfer303C1:ℚ):ℝ)*Real.log |x-((d2Transfer303S1:ℚ):ℝ)| ≤ ((d2Transfer303Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer303S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303S0,d2Transfer303Lo,d2Transfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer303C0 then |x-((d2Transfer303S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer303S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer303S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303S0,d2Transfer303Lo,d2Transfer303Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303C0,d2Log145Q,d2Transfer303S0,d2Transfer303Lo,d2Transfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer303C0 d2Transfer303S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2Transfer303S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303S1,d2Transfer303Lo,d2Transfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer303C1 then |x-((d2Transfer303S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2Transfer303S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer303S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303S1,d2Transfer303Lo,d2Transfer303Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers037.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer303C1,d2Log29Q,d2Transfer303S1,d2Transfer303Lo,d2Transfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer303C1 d2Transfer303S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2Transfer303C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2Transfer303C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2Transfer303Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer303Arithmetic
  linarith
#print axioms d2Transfer303Arithmetic
#print axioms d2Transfer303Bound
end CatalanMeasure.GenD.Signed.Data.Cells

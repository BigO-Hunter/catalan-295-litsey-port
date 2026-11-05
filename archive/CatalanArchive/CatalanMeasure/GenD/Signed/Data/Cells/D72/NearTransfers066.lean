module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers066
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers066
open D72.LogTransfer
def d2Transfer528Lo : ℚ := (d2LitsNearTransfers066.q2 (674778395) 1 (-30))
def d2Transfer528Hi : ℚ := (d2LitsNearTransfers066.q2 (1351234511) 1 (-31))
def d2Transfer528Cap : ℚ := (d2LitsNearTransfers066.q2 (17137847732989585535547) 1 (-79))
def d2Transfer528C0 : ℚ := (d2LitsNearTransfers066.q2 (3) 275 (-5))
def d2Transfer528S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer528C1 : ℚ := (d2LitsNearTransfers066.q2 (-5) 11 (-4))
def d2Transfer528S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer528Arithmetic : weightedUpper d2Transfer528C0 d2Log146Lo d2Log146Hi + weightedUpper d2Transfer528C1 d2Log28Lo d2Log28Hi ≤ d2Transfer528Cap := by decide +kernel
theorem d2Transfer528Bound : ∀ x ∈ Set.Icc ((d2Transfer528Lo:ℚ):ℝ) ((d2Transfer528Hi:ℚ):ℝ), ((d2Transfer528C0:ℚ):ℝ)*Real.log |x-((d2Transfer528S0:ℚ):ℝ)| + ((d2Transfer528C1:ℚ):ℝ)*Real.log |x-((d2Transfer528S1:ℚ):ℝ)| ≤ ((d2Transfer528Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer528S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528S0,d2Transfer528Lo,d2Transfer528Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer528C0 then |x-((d2Transfer528S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer528S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer528S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528S0,d2Transfer528Lo,d2Transfer528Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528C0,d2Log146Q,d2Transfer528S0,d2Transfer528Lo,d2Transfer528Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer528C0 d2Transfer528S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2Transfer528S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528S1,d2Transfer528Lo,d2Transfer528Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer528C1 then |x-((d2Transfer528S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2Transfer528S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer528S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528S1,d2Transfer528Lo,d2Transfer528Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer528C1,d2Log28Q,d2Transfer528S1,d2Transfer528Lo,d2Transfer528Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer528C1 d2Transfer528S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2Transfer528C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2Transfer528C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2Transfer528Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer528Arithmetic
  linarith
#print axioms d2Transfer528Arithmetic
#print axioms d2Transfer528Bound
def d2Transfer529Lo : ℚ := (d2LitsNearTransfers066.q2 (1351234511) 1 (-31))
def d2Transfer529Hi : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer529Cap : ℚ := (d2LitsNearTransfers066.q2 (2165550991296720462783) 1 (-80))
def d2Transfer529C0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer529S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer529C1 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer529S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer529Arithmetic : weightedUpper d2Transfer529C0 d2Log146Lo d2Log146Hi + weightedUpper d2Transfer529C1 d2Log27Lo d2Log27Hi ≤ d2Transfer529Cap := by decide +kernel
theorem d2Transfer529Bound : ∀ x ∈ Set.Icc ((d2Transfer529Lo:ℚ):ℝ) ((d2Transfer529Hi:ℚ):ℝ), ((d2Transfer529C0:ℚ):ℝ)*Real.log |x-((d2Transfer529S0:ℚ):ℝ)| + ((d2Transfer529C1:ℚ):ℝ)*Real.log |x-((d2Transfer529S1:ℚ):ℝ)| ≤ ((d2Transfer529Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer529S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529S0,d2Transfer529Lo,d2Transfer529Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer529C0 then |x-((d2Transfer529S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer529S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer529S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529S0,d2Transfer529Lo,d2Transfer529Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529C0,d2Log146Q,d2Transfer529S0,d2Transfer529Lo,d2Transfer529Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer529C0 d2Transfer529S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2Transfer529S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529S1,d2Transfer529Lo,d2Transfer529Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer529C1 then |x-((d2Transfer529S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2Transfer529S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer529S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529S1,d2Transfer529Lo,d2Transfer529Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer529C1,d2Log27Q,d2Transfer529S1,d2Transfer529Lo,d2Transfer529Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer529C1 d2Transfer529S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2Transfer529C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2Transfer529C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2Transfer529Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer529Arithmetic
  linarith
#print axioms d2Transfer529Arithmetic
#print axioms d2Transfer529Bound
def d2Transfer530Lo : ℚ := (d2LitsNearTransfers066.q2 (1351234511) 1 (-31))
def d2Transfer530Hi : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer530Cap : ℚ := (d2LitsNearTransfers066.q2 (17497346865223007396799) 1 (-80))
def d2Transfer530C0 : ℚ := (d2LitsNearTransfers066.q2 (23) 25 (-5))
def d2Transfer530S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer530Arithmetic : weightedUpper d2Transfer530C0 d2Log147Lo d2Log147Hi ≤ d2Transfer530Cap := by decide +kernel
theorem d2Transfer530Bound : ∀ x ∈ Set.Icc ((d2Transfer530Lo:ℚ):ℝ) ((d2Transfer530Hi:ℚ):ℝ), ((d2Transfer530C0:ℚ):ℝ)*Real.log |x-((d2Transfer530S0:ℚ):ℝ)| ≤ ((d2Transfer530Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer530S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer530S0,d2Transfer530Lo,d2Transfer530Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer530C0 then |x-((d2Transfer530S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer530S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer530S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer530S0,d2Transfer530Lo,d2Transfer530Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer530C0,d2Log147Q,d2Transfer530S0,d2Transfer530Lo,d2Transfer530Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer530C0 d2Transfer530S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2Transfer530C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2Transfer530Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer530Arithmetic
  linarith
#print axioms d2Transfer530Arithmetic
#print axioms d2Transfer530Bound
def d2Transfer531Lo : ℚ := (d2LitsNearTransfers066.q2 (1351234511) 1 (-31))
def d2Transfer531Hi : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer531Cap : ℚ := (d2LitsNearTransfers066.q2 (34348334256490277692351) 1 (-80))
def d2Transfer531C0 : ℚ := (d2LitsNearTransfers066.q2 (3) 275 (-5))
def d2Transfer531S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer531C1 : ℚ := (d2LitsNearTransfers066.q2 (-5) 11 (-4))
def d2Transfer531S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer531Arithmetic : weightedUpper d2Transfer531C0 d2Log147Lo d2Log147Hi + weightedUpper d2Transfer531C1 d2Log27Lo d2Log27Hi ≤ d2Transfer531Cap := by decide +kernel
theorem d2Transfer531Bound : ∀ x ∈ Set.Icc ((d2Transfer531Lo:ℚ):ℝ) ((d2Transfer531Hi:ℚ):ℝ), ((d2Transfer531C0:ℚ):ℝ)*Real.log |x-((d2Transfer531S0:ℚ):ℝ)| + ((d2Transfer531C1:ℚ):ℝ)*Real.log |x-((d2Transfer531S1:ℚ):ℝ)| ≤ ((d2Transfer531Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer531S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531S0,d2Transfer531Lo,d2Transfer531Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer531C0 then |x-((d2Transfer531S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer531S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer531S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531S0,d2Transfer531Lo,d2Transfer531Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531C0,d2Log147Q,d2Transfer531S0,d2Transfer531Lo,d2Transfer531Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer531C0 d2Transfer531S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2Transfer531S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531S1,d2Transfer531Lo,d2Transfer531Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer531C1 then |x-((d2Transfer531S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2Transfer531S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer531S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531S1,d2Transfer531Lo,d2Transfer531Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer531C1,d2Log27Q,d2Transfer531S1,d2Transfer531Lo,d2Transfer531Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer531C1 d2Transfer531S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2Transfer531C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2Transfer531C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2Transfer531Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer531Arithmetic
  linarith
#print axioms d2Transfer531Arithmetic
#print axioms d2Transfer531Bound
def d2Transfer532Lo : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer532Hi : ℚ := (d2LitsNearTransfers066.q2 (1354589953) 1 (-31))
def d2Transfer532Cap : ℚ := (d2LitsNearTransfers066.q2 (2238342807005286720359) 1 (-80))
def d2Transfer532C0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer532S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer532C1 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer532S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer532Arithmetic : weightedUpper d2Transfer532C0 d2Log147Lo d2Log147Hi + weightedUpper d2Transfer532C1 d2Log26Lo d2Log26Hi ≤ d2Transfer532Cap := by decide +kernel
theorem d2Transfer532Bound : ∀ x ∈ Set.Icc ((d2Transfer532Lo:ℚ):ℝ) ((d2Transfer532Hi:ℚ):ℝ), ((d2Transfer532C0:ℚ):ℝ)*Real.log |x-((d2Transfer532S0:ℚ):ℝ)| + ((d2Transfer532C1:ℚ):ℝ)*Real.log |x-((d2Transfer532S1:ℚ):ℝ)| ≤ ((d2Transfer532Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer532S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532S0,d2Transfer532Lo,d2Transfer532Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer532C0 then |x-((d2Transfer532S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2Transfer532S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer532S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532S0,d2Transfer532Lo,d2Transfer532Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532C0,d2Log147Q,d2Transfer532S0,d2Transfer532Lo,d2Transfer532Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer532C0 d2Transfer532S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2Transfer532S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532S1,d2Transfer532Lo,d2Transfer532Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer532C1 then |x-((d2Transfer532S1:ℚ):ℝ)| ≤ ((d2Log26Q:ℚ):ℝ) else ((d2Log26Q:ℚ):ℝ) ≤ |x-((d2Transfer532S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer532S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532S1,d2Transfer532Lo,d2Transfer532Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer532C1,d2Log26Q,d2Transfer532S1,d2Transfer532Lo,d2Transfer532Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer532C1 d2Transfer532S1 d2Log26Q d2Log26Lo d2Log26Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log26Bounds
  have har : (((weightedUpper d2Transfer532C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2Transfer532C1 d2Log26Lo d2Log26Hi:ℚ):ℝ)) ≤ ((d2Transfer532Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer532Arithmetic
  linarith
#print axioms d2Transfer532Arithmetic
#print axioms d2Transfer532Bound
def d2Transfer533Lo : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer533Hi : ℚ := (d2LitsNearTransfers066.q2 (1354589953) 1 (-31))
def d2Transfer533Cap : ℚ := (d2LitsNearTransfers066.q2 (17570138680931573654375) 1 (-80))
def d2Transfer533C0 : ℚ := (d2LitsNearTransfers066.q2 (23) 25 (-5))
def d2Transfer533S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer533Arithmetic : weightedUpper d2Transfer533C0 d2Log148Lo d2Log148Hi ≤ d2Transfer533Cap := by decide +kernel
theorem d2Transfer533Bound : ∀ x ∈ Set.Icc ((d2Transfer533Lo:ℚ):ℝ) ((d2Transfer533Hi:ℚ):ℝ), ((d2Transfer533C0:ℚ):ℝ)*Real.log |x-((d2Transfer533S0:ℚ):ℝ)| ≤ ((d2Transfer533Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer533S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer533S0,d2Transfer533Lo,d2Transfer533Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer533C0 then |x-((d2Transfer533S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2Transfer533S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer533S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer533S0,d2Transfer533Lo,d2Transfer533Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer533C0,d2Log148Q,d2Transfer533S0,d2Transfer533Lo,d2Transfer533Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer533C0 d2Transfer533S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have har : (((weightedUpper d2Transfer533C0 d2Log148Lo d2Log148Hi:ℚ):ℝ)) ≤ ((d2Transfer533Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer533Arithmetic
  linarith
#print axioms d2Transfer533Arithmetic
#print axioms d2Transfer533Bound
def d2Transfer534Lo : ℚ := (d2LitsNearTransfers066.q2 (169114029) 1 (-28))
def d2Transfer534Hi : ℚ := (d2LitsNearTransfers066.q2 (1354589953) 1 (-31))
def d2Transfer534Cap : ℚ := (d2LitsNearTransfers066.q2 (34421126072198843949927) 1 (-80))
def d2Transfer534C0 : ℚ := (d2LitsNearTransfers066.q2 (3) 275 (-5))
def d2Transfer534S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer534C1 : ℚ := (d2LitsNearTransfers066.q2 (-5) 11 (-4))
def d2Transfer534S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer534Arithmetic : weightedUpper d2Transfer534C0 d2Log148Lo d2Log148Hi + weightedUpper d2Transfer534C1 d2Log26Lo d2Log26Hi ≤ d2Transfer534Cap := by decide +kernel
theorem d2Transfer534Bound : ∀ x ∈ Set.Icc ((d2Transfer534Lo:ℚ):ℝ) ((d2Transfer534Hi:ℚ):ℝ), ((d2Transfer534C0:ℚ):ℝ)*Real.log |x-((d2Transfer534S0:ℚ):ℝ)| + ((d2Transfer534C1:ℚ):ℝ)*Real.log |x-((d2Transfer534S1:ℚ):ℝ)| ≤ ((d2Transfer534Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer534S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534S0,d2Transfer534Lo,d2Transfer534Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer534C0 then |x-((d2Transfer534S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2Transfer534S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer534S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534S0,d2Transfer534Lo,d2Transfer534Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534C0,d2Log148Q,d2Transfer534S0,d2Transfer534Lo,d2Transfer534Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer534C0 d2Transfer534S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have hn1 : x-((d2Transfer534S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534S1,d2Transfer534Lo,d2Transfer534Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer534C1 then |x-((d2Transfer534S1:ℚ):ℝ)| ≤ ((d2Log26Q:ℚ):ℝ) else ((d2Log26Q:ℚ):ℝ) ≤ |x-((d2Transfer534S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer534S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534S1,d2Transfer534Lo,d2Transfer534Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer534C1,d2Log26Q,d2Transfer534S1,d2Transfer534Lo,d2Transfer534Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer534C1 d2Transfer534S1 d2Log26Q d2Log26Lo d2Log26Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log26Bounds
  have har : (((weightedUpper d2Transfer534C0 d2Log148Lo d2Log148Hi:ℚ):ℝ) + ((weightedUpper d2Transfer534C1 d2Log26Lo d2Log26Hi:ℚ):ℝ)) ≤ ((d2Transfer534Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer534Arithmetic
  linarith
#print axioms d2Transfer534Arithmetic
#print axioms d2Transfer534Bound
def d2Transfer535Lo : ℚ := (d2LitsNearTransfers066.q2 (1354589953) 1 (-31))
def d2Transfer535Hi : ℚ := (d2LitsNearTransfers066.q2 (678133837) 1 (-30))
def d2Transfer535Cap : ℚ := (d2LitsNearTransfers066.q2 (1155644148338036120111) 1 (-79))
def d2Transfer535C0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer535S0 : ℚ := (d2LitsNearTransfers066.q2 (-1) 1 (0))
def d2Transfer535C1 : ℚ := (d2LitsNearTransfers066.q2 (-1) 55 (-3))
def d2Transfer535S1 : ℚ := (d2LitsNearTransfers066.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer535Arithmetic : weightedUpper d2Transfer535C0 d2Log148Lo d2Log148Hi + weightedUpper d2Transfer535C1 d2Log25Lo d2Log25Hi ≤ d2Transfer535Cap := by decide +kernel
theorem d2Transfer535Bound : ∀ x ∈ Set.Icc ((d2Transfer535Lo:ℚ):ℝ) ((d2Transfer535Hi:ℚ):ℝ), ((d2Transfer535C0:ℚ):ℝ)*Real.log |x-((d2Transfer535S0:ℚ):ℝ)| + ((d2Transfer535C1:ℚ):ℝ)*Real.log |x-((d2Transfer535S1:ℚ):ℝ)| ≤ ((d2Transfer535Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer535S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535S0,d2Transfer535Lo,d2Transfer535Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer535C0 then |x-((d2Transfer535S0:ℚ):ℝ)| ≤ ((d2Log148Q:ℚ):ℝ) else ((d2Log148Q:ℚ):ℝ) ≤ |x-((d2Transfer535S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer535S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535S0,d2Transfer535Lo,d2Transfer535Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535C0,d2Log148Q,d2Transfer535S0,d2Transfer535Lo,d2Transfer535Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer535C0 d2Transfer535S0 d2Log148Q d2Log148Lo d2Log148Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log148Bounds
  have hn1 : x-((d2Transfer535S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535S1,d2Transfer535Lo,d2Transfer535Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer535C1 then |x-((d2Transfer535S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2Transfer535S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer535S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535S1,d2Transfer535Lo,d2Transfer535Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers066.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2Transfer535C1,d2Log25Q,d2Transfer535S1,d2Transfer535Lo,d2Transfer535Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer535C1 d2Transfer535S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2Transfer535C0 d2Log148Lo d2Log148Hi:ℚ):ℝ) + ((weightedUpper d2Transfer535C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2Transfer535Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer535Arithmetic
  linarith
#print axioms d2Transfer535Arithmetic
#print axioms d2Transfer535Bound
end CatalanMeasure.GenD.Signed.Data.Cells

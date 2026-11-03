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
namespace d2LitsNearWiderTransfers022
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers022
open D72.LogTransfer
def d2WiderTransfer176Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (674778395) 1 (-30))
def d2WiderTransfer176Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer176Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (9693024787501573266043) 1 (-79))
def d2WiderTransfer176C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (-5))
def d2WiderTransfer176S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer176Arithmetic : weightedUpper d2WiderTransfer176C0 d2Log146Lo d2Log146Hi ≤ d2WiderTransfer176Cap := by decide +kernel
theorem d2WiderTransfer176Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer176Lo:ℚ):ℝ) ((d2WiderTransfer176Hi:ℚ):ℝ), ((d2WiderTransfer176C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer176S0:ℚ):ℝ)| ≤ ((d2WiderTransfer176Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer176S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer176S0,d2WiderTransfer176Lo,d2WiderTransfer176Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer176C0 then |x-((d2WiderTransfer176S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer176S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer176S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer176S0,d2WiderTransfer176Lo,d2WiderTransfer176Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer176C0,d2Log146Q,d2WiderTransfer176S0,d2WiderTransfer176Lo,d2WiderTransfer176Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer176C0 d2WiderTransfer176S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2WiderTransfer176C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer176Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer176Arithmetic
  linarith
#print axioms d2WiderTransfer176Arithmetic
#print axioms d2WiderTransfer176Bound
def d2WiderTransfer177Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (674778395) 1 (-30))
def d2WiderTransfer177Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer177Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (17875443448647326947963) 1 (-79))
def d2WiderTransfer177C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 11 (-5))
def d2WiderTransfer177S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
def d2WiderTransfer177C1 : ℚ := (d2LitsNearWiderTransfers022.q2 (-5) 11 (-4))
def d2WiderTransfer177S1 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer177Arithmetic : weightedUpper d2WiderTransfer177C0 d2Log146Lo d2Log146Hi + weightedUpper d2WiderTransfer177C1 d2Log28Lo d2Log28Hi ≤ d2WiderTransfer177Cap := by decide +kernel
theorem d2WiderTransfer177Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer177Lo:ℚ):ℝ) ((d2WiderTransfer177Hi:ℚ):ℝ), ((d2WiderTransfer177C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer177S0:ℚ):ℝ)| + ((d2WiderTransfer177C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer177S1:ℚ):ℝ)| ≤ ((d2WiderTransfer177Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer177S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177S0,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer177C0 then |x-((d2WiderTransfer177S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer177S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer177S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177S0,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177C0,d2Log146Q,d2WiderTransfer177S0,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer177C0 d2WiderTransfer177S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have hn1 : x-((d2WiderTransfer177S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177S1,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer177C1 then |x-((d2WiderTransfer177S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer177S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer177S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177S1,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer177C1,d2Log28Q,d2WiderTransfer177S1,d2WiderTransfer177Lo,d2WiderTransfer177Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer177C1 d2WiderTransfer177S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2WiderTransfer177C0 d2Log146Lo d2Log146Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer177C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer177Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer177Arithmetic
  linarith
#print axioms d2WiderTransfer177Arithmetic
#print axioms d2WiderTransfer177Bound
def d2WiderTransfer178Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer178Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer178Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (1493387516446464078587) 1 (-79))
def d2WiderTransfer178C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 25 (-4))
def d2WiderTransfer178S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer178Arithmetic : weightedUpper d2WiderTransfer178C0 d2Log147Lo d2Log147Hi ≤ d2WiderTransfer178Cap := by decide +kernel
theorem d2WiderTransfer178Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer178Lo:ℚ):ℝ) ((d2WiderTransfer178Hi:ℚ):ℝ), ((d2WiderTransfer178C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer178S0:ℚ):ℝ)| ≤ ((d2WiderTransfer178Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer178S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer178S0,d2WiderTransfer178Lo,d2WiderTransfer178Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer178C0 then |x-((d2WiderTransfer178S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer178S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer178S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer178S0,d2WiderTransfer178Lo,d2WiderTransfer178Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer178C0,d2Log147Q,d2WiderTransfer178S0,d2WiderTransfer178Lo,d2WiderTransfer178Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer178C0 d2WiderTransfer178S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2WiderTransfer178C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer178Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer178Arithmetic
  linarith
#print axioms d2WiderTransfer178Arithmetic
#print axioms d2WiderTransfer178Bound
def d2WiderTransfer179Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer179Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer179Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (2118537600764331750139) 1 (-79))
def d2WiderTransfer179C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 275 (-4))
def d2WiderTransfer179S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
def d2WiderTransfer179C1 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 55 (-3))
def d2WiderTransfer179S1 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer179Arithmetic : weightedUpper d2WiderTransfer179C0 d2Log147Lo d2Log147Hi + weightedUpper d2WiderTransfer179C1 d2Log27Lo d2Log27Hi ≤ d2WiderTransfer179Cap := by decide +kernel
theorem d2WiderTransfer179Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer179Lo:ℚ):ℝ) ((d2WiderTransfer179Hi:ℚ):ℝ), ((d2WiderTransfer179C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer179S0:ℚ):ℝ)| + ((d2WiderTransfer179C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer179S1:ℚ):ℝ)| ≤ ((d2WiderTransfer179Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer179S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179S0,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer179C0 then |x-((d2WiderTransfer179S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer179S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer179S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179S0,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179C0,d2Log147Q,d2WiderTransfer179S0,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer179C0 d2WiderTransfer179S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2WiderTransfer179S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179S1,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer179C1 then |x-((d2WiderTransfer179S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer179S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer179S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179S1,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer179C1,d2Log27Q,d2WiderTransfer179S1,d2WiderTransfer179Lo,d2WiderTransfer179Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer179C1 d2WiderTransfer179S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2WiderTransfer179C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer179C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer179Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer179Arithmetic
  linarith
#print axioms d2WiderTransfer179Arithmetic
#print axioms d2WiderTransfer179Bound
def d2WiderTransfer180Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer180Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer180Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (9730068645975812010747) 1 (-79))
def d2WiderTransfer180C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (-5))
def d2WiderTransfer180S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer180Arithmetic : weightedUpper d2WiderTransfer180C0 d2Log147Lo d2Log147Hi ≤ d2WiderTransfer180Cap := by decide +kernel
theorem d2WiderTransfer180Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer180Lo:ℚ):ℝ) ((d2WiderTransfer180Hi:ℚ):ℝ), ((d2WiderTransfer180C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer180S0:ℚ):ℝ)| ≤ ((d2WiderTransfer180Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer180S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer180S0,d2WiderTransfer180Lo,d2WiderTransfer180Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer180C0 then |x-((d2WiderTransfer180S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer180S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer180S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer180S0,d2WiderTransfer180Lo,d2WiderTransfer180Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer180C0,d2Log147Q,d2WiderTransfer180S0,d2WiderTransfer180Lo,d2WiderTransfer180Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer180C0 d2WiderTransfer180S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have har : (((weightedUpper d2WiderTransfer180C0 d2Log147Lo d2Log147Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer180Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer180Arithmetic
  linarith
#print axioms d2WiderTransfer180Arithmetic
#print axioms d2WiderTransfer180Bound
def d2WiderTransfer181Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (1351234511) 1 (-31))
def d2WiderTransfer181Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer181Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (17912487307121565692667) 1 (-79))
def d2WiderTransfer181C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 11 (-5))
def d2WiderTransfer181S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
def d2WiderTransfer181C1 : ℚ := (d2LitsNearWiderTransfers022.q2 (-5) 11 (-4))
def d2WiderTransfer181S1 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer181Arithmetic : weightedUpper d2WiderTransfer181C0 d2Log147Lo d2Log147Hi + weightedUpper d2WiderTransfer181C1 d2Log27Lo d2Log27Hi ≤ d2WiderTransfer181Cap := by decide +kernel
theorem d2WiderTransfer181Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer181Lo:ℚ):ℝ) ((d2WiderTransfer181Hi:ℚ):ℝ), ((d2WiderTransfer181C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer181S0:ℚ):ℝ)| + ((d2WiderTransfer181C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer181S1:ℚ):ℝ)| ≤ ((d2WiderTransfer181Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer181S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181S0,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer181C0 then |x-((d2WiderTransfer181S0:ℚ):ℝ)| ≤ ((d2Log147Q:ℚ):ℝ) else ((d2Log147Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer181S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer181S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181S0,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181C0,d2Log147Q,d2WiderTransfer181S0,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer181C0 d2WiderTransfer181S0 d2Log147Q d2Log147Lo d2Log147Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log147Bounds
  have hn1 : x-((d2WiderTransfer181S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181S1,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer181C1 then |x-((d2WiderTransfer181S1:ℚ):ℝ)| ≤ ((d2Log27Q:ℚ):ℝ) else ((d2Log27Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer181S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer181S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181S1,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer181C1,d2Log27Q,d2WiderTransfer181S1,d2WiderTransfer181Lo,d2WiderTransfer181Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer181C1 d2WiderTransfer181S1 d2Log27Q d2Log27Lo d2Log27Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log27Bounds
  have har : (((weightedUpper d2WiderTransfer181C0 d2Log147Lo d2Log147Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer181C1 d2Log27Lo d2Log27Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer181Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer181Arithmetic
  linarith
#print axioms d2WiderTransfer181Arithmetic
#print axioms d2WiderTransfer181Bound
def d2WiderTransfer182Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer182Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (678133837) 1 (-30))
def d2WiderTransfer182Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (1567704054461560565645) 1 (-79))
def d2WiderTransfer182C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 25 (-4))
def d2WiderTransfer182S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer182Arithmetic : weightedUpper d2WiderTransfer182C0 d2Log149Lo d2Log149Hi ≤ d2WiderTransfer182Cap := by decide +kernel
theorem d2WiderTransfer182Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer182Lo:ℚ):ℝ) ((d2WiderTransfer182Hi:ℚ):ℝ), ((d2WiderTransfer182C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer182S0:ℚ):ℝ)| ≤ ((d2WiderTransfer182Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer182S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer182S0,d2WiderTransfer182Lo,d2WiderTransfer182Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer182C0 then |x-((d2WiderTransfer182S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer182S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer182S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer182S0,d2WiderTransfer182Lo,d2WiderTransfer182Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer182C0,d2Log149Q,d2WiderTransfer182S0,d2WiderTransfer182Lo,d2WiderTransfer182Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer182C0 d2WiderTransfer182S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have har : (((weightedUpper d2WiderTransfer182C0 d2Log149Lo d2Log149Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer182Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer182Arithmetic
  linarith
#print axioms d2WiderTransfer182Arithmetic
#print axioms d2WiderTransfer182Bound
def d2WiderTransfer183Lo : ℚ := (d2LitsNearWiderTransfers022.q2 (169114029) 1 (-28))
def d2WiderTransfer183Hi : ℚ := (d2LitsNearWiderTransfers022.q2 (678133837) 1 (-30))
def d2WiderTransfer183Cap : ℚ := (d2LitsNearWiderTransfers022.q2 (2192854138779428237197) 1 (-79))
def d2WiderTransfer183C0 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 275 (-4))
def d2WiderTransfer183S0 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 1 (0))
def d2WiderTransfer183C1 : ℚ := (d2LitsNearWiderTransfers022.q2 (-1) 55 (-3))
def d2WiderTransfer183S1 : ℚ := (d2LitsNearWiderTransfers022.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer183Arithmetic : weightedUpper d2WiderTransfer183C0 d2Log149Lo d2Log149Hi + weightedUpper d2WiderTransfer183C1 d2Log25Lo d2Log25Hi ≤ d2WiderTransfer183Cap := by decide +kernel
theorem d2WiderTransfer183Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer183Lo:ℚ):ℝ) ((d2WiderTransfer183Hi:ℚ):ℝ), ((d2WiderTransfer183C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer183S0:ℚ):ℝ)| + ((d2WiderTransfer183C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer183S1:ℚ):ℝ)| ≤ ((d2WiderTransfer183Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer183S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183S0,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer183C0 then |x-((d2WiderTransfer183S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer183S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer183S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183S0,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183C0,d2Log149Q,d2WiderTransfer183S0,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer183C0 d2WiderTransfer183S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2WiderTransfer183S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183S1,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer183C1 then |x-((d2WiderTransfer183S1:ℚ):ℝ)| ≤ ((d2Log25Q:ℚ):ℝ) else ((d2Log25Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer183S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer183S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183S1,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers022.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer183C1,d2Log25Q,d2WiderTransfer183S1,d2WiderTransfer183Lo,d2WiderTransfer183Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer183C1 d2WiderTransfer183S1 d2Log25Q d2Log25Lo d2Log25Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log25Bounds
  have har : (((weightedUpper d2WiderTransfer183C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer183C1 d2Log25Lo d2Log25Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer183Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer183Arithmetic
  linarith
#print axioms d2WiderTransfer183Arithmetic
#print axioms d2WiderTransfer183Bound
end CatalanMeasure.GenD.Signed.Data.Cells

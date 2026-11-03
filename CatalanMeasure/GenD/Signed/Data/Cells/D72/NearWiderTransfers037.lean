module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers037
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers037
open D72.LogTransfer
def d2WiderTransfer296Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (333194895) 1 (-29))
def d2WiderTransfer296Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (668067511) 1 (-30))
def d2WiderTransfer296Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (16814377008084446589281) 1 (-80))
def d2WiderTransfer296C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (23) 25 (-5))
def d2WiderTransfer296S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer296Arithmetic : weightedUpper d2WiderTransfer296C0 d2Log137Lo d2Log137Hi ≤ d2WiderTransfer296Cap := by decide +kernel
theorem d2WiderTransfer296Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer296Lo:ℚ):ℝ) ((d2WiderTransfer296Hi:ℚ):ℝ), ((d2WiderTransfer296C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer296S0:ℚ):ℝ)| ≤ ((d2WiderTransfer296Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer296S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer296S0,d2WiderTransfer296Lo,d2WiderTransfer296Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer296C0 then |x-((d2WiderTransfer296S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer296S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer296S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer296S0,d2WiderTransfer296Lo,d2WiderTransfer296Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer296C0,d2Log137Q,d2WiderTransfer296S0,d2WiderTransfer296Lo,d2WiderTransfer296Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer296C0 d2WiderTransfer296S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have har : (((weightedUpper d2WiderTransfer296C0 d2Log137Lo d2Log137Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer296Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer296Arithmetic
  linarith
#print axioms d2WiderTransfer296Arithmetic
#print axioms d2WiderTransfer296Bound
def d2WiderTransfer297Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (333194895) 1 (-29))
def d2WiderTransfer297Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (668067511) 1 (-30))
def d2WiderTransfer297Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (33665364399351716884833) 1 (-80))
def d2WiderTransfer297C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (3) 275 (-5))
def d2WiderTransfer297S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
def d2WiderTransfer297C1 : ℚ := (d2LitsNearWiderTransfers037.q2 (-5) 11 (-4))
def d2WiderTransfer297S1 : ℚ := (d2LitsNearWiderTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer297Arithmetic : weightedUpper d2WiderTransfer297C0 d2Log137Lo d2Log137Hi + weightedUpper d2WiderTransfer297C1 d2Log37Lo d2Log37Hi ≤ d2WiderTransfer297Cap := by decide +kernel
theorem d2WiderTransfer297Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer297Lo:ℚ):ℝ) ((d2WiderTransfer297Hi:ℚ):ℝ), ((d2WiderTransfer297C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer297S0:ℚ):ℝ)| + ((d2WiderTransfer297C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer297S1:ℚ):ℝ)| ≤ ((d2WiderTransfer297Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer297S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297S0,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer297C0 then |x-((d2WiderTransfer297S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer297S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer297S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297S0,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297C0,d2Log137Q,d2WiderTransfer297S0,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer297C0 d2WiderTransfer297S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2WiderTransfer297S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297S1,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer297C1 then |x-((d2WiderTransfer297S1:ℚ):ℝ)| ≤ ((d2Log37Q:ℚ):ℝ) else ((d2Log37Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer297S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer297S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297S1,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer297C1,d2Log37Q,d2WiderTransfer297S1,d2WiderTransfer297Lo,d2WiderTransfer297Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer297C1 d2WiderTransfer297S1 d2Log37Q d2Log37Lo d2Log37Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log37Bounds
  have har : (((weightedUpper d2WiderTransfer297C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer297C1 d2Log37Lo d2Log37Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer297Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer297Arithmetic
  linarith
#print axioms d2WiderTransfer297Arithmetic
#print axioms d2WiderTransfer297Bound
def d2WiderTransfer298Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (668067511) 1 (-30))
def d2WiderTransfer298Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer298Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (1588671728036449488905) 1 (-80))
def d2WiderTransfer298C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 55 (-3))
def d2WiderTransfer298S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
def d2WiderTransfer298C1 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 55 (-3))
def d2WiderTransfer298S1 : ℚ := (d2LitsNearWiderTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer298Arithmetic : weightedUpper d2WiderTransfer298C0 d2Log137Lo d2Log137Hi + weightedUpper d2WiderTransfer298C1 d2Log35Lo d2Log35Hi ≤ d2WiderTransfer298Cap := by decide +kernel
theorem d2WiderTransfer298Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer298Lo:ℚ):ℝ) ((d2WiderTransfer298Hi:ℚ):ℝ), ((d2WiderTransfer298C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer298S0:ℚ):ℝ)| + ((d2WiderTransfer298C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer298S1:ℚ):ℝ)| ≤ ((d2WiderTransfer298Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer298S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298S0,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer298C0 then |x-((d2WiderTransfer298S0:ℚ):ℝ)| ≤ ((d2Log137Q:ℚ):ℝ) else ((d2Log137Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer298S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer298S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298S0,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298C0,d2Log137Q,d2WiderTransfer298S0,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer298C0 d2WiderTransfer298S0 d2Log137Q d2Log137Lo d2Log137Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log137Bounds
  have hn1 : x-((d2WiderTransfer298S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298S1,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer298C1 then |x-((d2WiderTransfer298S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer298S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer298S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298S1,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer298C1,d2Log35Q,d2WiderTransfer298S1,d2WiderTransfer298Lo,d2WiderTransfer298Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer298C1 d2WiderTransfer298S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2WiderTransfer298C0 d2Log137Lo d2Log137Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer298C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer298Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer298Arithmetic
  linarith
#print axioms d2WiderTransfer298Arithmetic
#print axioms d2WiderTransfer298Bound
def d2WiderTransfer299Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (668067511) 1 (-30))
def d2WiderTransfer299Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer299Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (16920467601962736422921) 1 (-80))
def d2WiderTransfer299C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (23) 25 (-5))
def d2WiderTransfer299S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer299Arithmetic : weightedUpper d2WiderTransfer299C0 d2Log139Lo d2Log139Hi ≤ d2WiderTransfer299Cap := by decide +kernel
theorem d2WiderTransfer299Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer299Lo:ℚ):ℝ) ((d2WiderTransfer299Hi:ℚ):ℝ), ((d2WiderTransfer299C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer299S0:ℚ):ℝ)| ≤ ((d2WiderTransfer299Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer299S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer299S0,d2WiderTransfer299Lo,d2WiderTransfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer299C0 then |x-((d2WiderTransfer299S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer299S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer299S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer299S0,d2WiderTransfer299Lo,d2WiderTransfer299Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer299C0,d2Log139Q,d2WiderTransfer299S0,d2WiderTransfer299Lo,d2WiderTransfer299Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer299C0 d2WiderTransfer299S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have har : (((weightedUpper d2WiderTransfer299C0 d2Log139Lo d2Log139Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer299Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer299Arithmetic
  linarith
#print axioms d2WiderTransfer299Arithmetic
#print axioms d2WiderTransfer299Bound
def d2WiderTransfer300Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (668067511) 1 (-30))
def d2WiderTransfer300Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer300Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (33771454993230006718473) 1 (-80))
def d2WiderTransfer300C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (3) 275 (-5))
def d2WiderTransfer300S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
def d2WiderTransfer300C1 : ℚ := (d2LitsNearWiderTransfers037.q2 (-5) 11 (-4))
def d2WiderTransfer300S1 : ℚ := (d2LitsNearWiderTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer300Arithmetic : weightedUpper d2WiderTransfer300C0 d2Log139Lo d2Log139Hi + weightedUpper d2WiderTransfer300C1 d2Log35Lo d2Log35Hi ≤ d2WiderTransfer300Cap := by decide +kernel
theorem d2WiderTransfer300Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer300Lo:ℚ):ℝ) ((d2WiderTransfer300Hi:ℚ):ℝ), ((d2WiderTransfer300C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer300S0:ℚ):ℝ)| + ((d2WiderTransfer300C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer300S1:ℚ):ℝ)| ≤ ((d2WiderTransfer300Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer300S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300S0,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer300C0 then |x-((d2WiderTransfer300S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer300S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer300S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300S0,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300C0,d2Log139Q,d2WiderTransfer300S0,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer300C0 d2WiderTransfer300S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2WiderTransfer300S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300S1,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer300C1 then |x-((d2WiderTransfer300S1:ℚ):ℝ)| ≤ ((d2Log35Q:ℚ):ℝ) else ((d2Log35Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer300S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer300S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300S1,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer300C1,d2Log35Q,d2WiderTransfer300S1,d2WiderTransfer300Lo,d2WiderTransfer300Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer300C1 d2WiderTransfer300S1 d2Log35Q d2Log35Lo d2Log35Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log35Bounds
  have har : (((weightedUpper d2WiderTransfer300C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer300C1 d2Log35Lo d2Log35Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer300Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer300Arithmetic
  linarith
#print axioms d2WiderTransfer300Arithmetic
#print axioms d2WiderTransfer300Bound
def d2WiderTransfer301Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer301Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (671422953) 1 (-30))
def d2WiderTransfer301Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (432997801055116030553) 1 (-78))
def d2WiderTransfer301C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 55 (-3))
def d2WiderTransfer301S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
def d2WiderTransfer301C1 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 55 (-3))
def d2WiderTransfer301S1 : ℚ := (d2LitsNearWiderTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer301Arithmetic : weightedUpper d2WiderTransfer301C0 d2Log139Lo d2Log139Hi + weightedUpper d2WiderTransfer301C1 d2Log33Lo d2Log33Hi ≤ d2WiderTransfer301Cap := by decide +kernel
theorem d2WiderTransfer301Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer301Lo:ℚ):ℝ) ((d2WiderTransfer301Hi:ℚ):ℝ), ((d2WiderTransfer301C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer301S0:ℚ):ℝ)| + ((d2WiderTransfer301C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer301S1:ℚ):ℝ)| ≤ ((d2WiderTransfer301Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer301S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301S0,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer301C0 then |x-((d2WiderTransfer301S0:ℚ):ℝ)| ≤ ((d2Log139Q:ℚ):ℝ) else ((d2Log139Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer301S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer301S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301S0,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301C0,d2Log139Q,d2WiderTransfer301S0,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer301C0 d2WiderTransfer301S0 d2Log139Q d2Log139Lo d2Log139Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log139Bounds
  have hn1 : x-((d2WiderTransfer301S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301S1,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer301C1 then |x-((d2WiderTransfer301S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer301S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer301S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301S1,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer301C1,d2Log33Q,d2WiderTransfer301S1,d2WiderTransfer301Lo,d2WiderTransfer301Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer301C1 d2WiderTransfer301S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2WiderTransfer301C0 d2Log139Lo d2Log139Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer301C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer301Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer301Arithmetic
  linarith
#print axioms d2WiderTransfer301Arithmetic
#print axioms d2WiderTransfer301Bound
def d2WiderTransfer302Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer302Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (671422953) 1 (-30))
def d2WiderTransfer302Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (4265946769536687764057) 1 (-78))
def d2WiderTransfer302C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (23) 25 (-5))
def d2WiderTransfer302S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer302Arithmetic : weightedUpper d2WiderTransfer302C0 d2Log141Lo d2Log141Hi ≤ d2WiderTransfer302Cap := by decide +kernel
theorem d2WiderTransfer302Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer302Lo:ℚ):ℝ) ((d2WiderTransfer302Hi:ℚ):ℝ), ((d2WiderTransfer302C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer302S0:ℚ):ℝ)| ≤ ((d2WiderTransfer302Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer302S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer302S0,d2WiderTransfer302Lo,d2WiderTransfer302Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer302C0 then |x-((d2WiderTransfer302S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer302S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer302S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer302S0,d2WiderTransfer302Lo,d2WiderTransfer302Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer302C0,d2Log141Q,d2WiderTransfer302S0,d2WiderTransfer302Lo,d2WiderTransfer302Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer302C0 d2WiderTransfer302S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have har : (((weightedUpper d2WiderTransfer302C0 d2Log141Lo d2Log141Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer302Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer302Arithmetic
  linarith
#print axioms d2WiderTransfer302Arithmetic
#print axioms d2WiderTransfer302Bound
def d2WiderTransfer303Lo : ℚ := (d2LitsNearWiderTransfers037.q2 (41859077) 1 (-26))
def d2WiderTransfer303Hi : ℚ := (d2LitsNearWiderTransfers037.q2 (671422953) 1 (-30))
def d2WiderTransfer303Cap : ℚ := (d2LitsNearWiderTransfers037.q2 (8478693617353505337945) 1 (-78))
def d2WiderTransfer303C0 : ℚ := (d2LitsNearWiderTransfers037.q2 (3) 275 (-5))
def d2WiderTransfer303S0 : ℚ := (d2LitsNearWiderTransfers037.q2 (-1) 1 (0))
def d2WiderTransfer303C1 : ℚ := (d2LitsNearWiderTransfers037.q2 (-5) 11 (-4))
def d2WiderTransfer303S1 : ℚ := (d2LitsNearWiderTransfers037.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer303Arithmetic : weightedUpper d2WiderTransfer303C0 d2Log141Lo d2Log141Hi + weightedUpper d2WiderTransfer303C1 d2Log33Lo d2Log33Hi ≤ d2WiderTransfer303Cap := by decide +kernel
theorem d2WiderTransfer303Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer303Lo:ℚ):ℝ) ((d2WiderTransfer303Hi:ℚ):ℝ), ((d2WiderTransfer303C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer303S0:ℚ):ℝ)| + ((d2WiderTransfer303C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer303S1:ℚ):ℝ)| ≤ ((d2WiderTransfer303Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer303S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303S0,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer303C0 then |x-((d2WiderTransfer303S0:ℚ):ℝ)| ≤ ((d2Log141Q:ℚ):ℝ) else ((d2Log141Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer303S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer303S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303S0,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303C0,d2Log141Q,d2WiderTransfer303S0,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer303C0 d2WiderTransfer303S0 d2Log141Q d2Log141Lo d2Log141Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log141Bounds
  have hn1 : x-((d2WiderTransfer303S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303S1,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer303C1 then |x-((d2WiderTransfer303S1:ℚ):ℝ)| ≤ ((d2Log33Q:ℚ):ℝ) else ((d2Log33Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer303S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer303S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303S1,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers037.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache008.q2, d2WiderTransfer303C1,d2Log33Q,d2WiderTransfer303S1,d2WiderTransfer303Lo,d2WiderTransfer303Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer303C1 d2WiderTransfer303S1 d2Log33Q d2Log33Lo d2Log33Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log33Bounds
  have har : (((weightedUpper d2WiderTransfer303C0 d2Log141Lo d2Log141Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer303C1 d2Log33Lo d2Log33Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer303Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer303Arithmetic
  linarith
#print axioms d2WiderTransfer303Arithmetic
#print axioms d2WiderTransfer303Bound
end CatalanMeasure.GenD.Signed.Data.Cells

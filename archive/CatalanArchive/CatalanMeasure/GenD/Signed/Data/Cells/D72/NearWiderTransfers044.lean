module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers044
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers044
open D72.LogTransfer
def d2WiderTransfer352Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (684844721) 1 (-30))
def d2WiderTransfer352Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer352Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (3049340988866887689691) 1 (-80))
def d2WiderTransfer352C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer352S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
def d2WiderTransfer352C1 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer352S1 : ℚ := (d2LitsNearWiderTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer352Arithmetic : weightedUpper d2WiderTransfer352C0 d2Log157Lo d2Log157Hi + weightedUpper d2WiderTransfer352C1 d2Log16Lo d2Log16Hi ≤ d2WiderTransfer352Cap := by decide +kernel
theorem d2WiderTransfer352Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer352Lo:ℚ):ℝ) ((d2WiderTransfer352Hi:ℚ):ℝ), ((d2WiderTransfer352C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer352S0:ℚ):ℝ)| + ((d2WiderTransfer352C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer352S1:ℚ):ℝ)| ≤ ((d2WiderTransfer352Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer352S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352S0,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer352C0 then |x-((d2WiderTransfer352S0:ℚ):ℝ)| ≤ ((d2Log157Q:ℚ):ℝ) else ((d2Log157Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer352S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer352S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352S0,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352C0,d2Log157Q,d2WiderTransfer352S0,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer352C0 d2WiderTransfer352S0 d2Log157Q d2Log157Lo d2Log157Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log157Bounds
  have hn1 : x-((d2WiderTransfer352S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352S1,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer352C1 then |x-((d2WiderTransfer352S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer352S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer352S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352S1,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer352C1,d2Log16Q,d2WiderTransfer352S1,d2WiderTransfer352Lo,d2WiderTransfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer352C1 d2WiderTransfer352S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2WiderTransfer352C0 d2Log157Lo d2Log157Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer352C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer352Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer352Arithmetic
  linarith
#print axioms d2WiderTransfer352Arithmetic
#print axioms d2WiderTransfer352Bound
def d2WiderTransfer353Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (684844721) 1 (-30))
def d2WiderTransfer353Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer353Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (18381136862793174623707) 1 (-80))
def d2WiderTransfer353C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (23) 25 (-5))
def d2WiderTransfer353S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer353Arithmetic : weightedUpper d2WiderTransfer353C0 d2Log158Lo d2Log158Hi ≤ d2WiderTransfer353Cap := by decide +kernel
theorem d2WiderTransfer353Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer353Lo:ℚ):ℝ) ((d2WiderTransfer353Hi:ℚ):ℝ), ((d2WiderTransfer353C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer353S0:ℚ):ℝ)| ≤ ((d2WiderTransfer353Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer353S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer353S0,d2WiderTransfer353Lo,d2WiderTransfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer353C0 then |x-((d2WiderTransfer353S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer353S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer353S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer353S0,d2WiderTransfer353Lo,d2WiderTransfer353Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer353C0,d2Log158Q,d2WiderTransfer353S0,d2WiderTransfer353Lo,d2WiderTransfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer353C0 d2WiderTransfer353S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2WiderTransfer353C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer353Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer353Arithmetic
  linarith
#print axioms d2WiderTransfer353Arithmetic
#print axioms d2WiderTransfer353Bound
def d2WiderTransfer354Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (684844721) 1 (-30))
def d2WiderTransfer354Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer354Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (35232124254060444919259) 1 (-80))
def d2WiderTransfer354C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (3) 275 (-5))
def d2WiderTransfer354S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
def d2WiderTransfer354C1 : ℚ := (d2LitsNearWiderTransfers044.q2 (-5) 11 (-4))
def d2WiderTransfer354S1 : ℚ := (d2LitsNearWiderTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer354Arithmetic : weightedUpper d2WiderTransfer354C0 d2Log158Lo d2Log158Hi + weightedUpper d2WiderTransfer354C1 d2Log16Lo d2Log16Hi ≤ d2WiderTransfer354Cap := by decide +kernel
theorem d2WiderTransfer354Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer354Lo:ℚ):ℝ) ((d2WiderTransfer354Hi:ℚ):ℝ), ((d2WiderTransfer354C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer354S0:ℚ):ℝ)| + ((d2WiderTransfer354C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer354S1:ℚ):ℝ)| ≤ ((d2WiderTransfer354Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer354S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354S0,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer354C0 then |x-((d2WiderTransfer354S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer354S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer354S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354S0,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354C0,d2Log158Q,d2WiderTransfer354S0,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer354C0 d2WiderTransfer354S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2WiderTransfer354S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354S1,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer354C1 then |x-((d2WiderTransfer354S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer354S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer354S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354S1,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer354C1,d2Log16Q,d2WiderTransfer354S1,d2WiderTransfer354Lo,d2WiderTransfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer354C1 d2WiderTransfer354S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2WiderTransfer354C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer354C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer354Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer354Arithmetic
  linarith
#print axioms d2WiderTransfer354Arithmetic
#print axioms d2WiderTransfer354Bound
def d2WiderTransfer355Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer355Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (688200163) 1 (-30))
def d2WiderTransfer355Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (1599431318984013064275) 1 (-79))
def d2WiderTransfer355C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer355S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
def d2WiderTransfer355C1 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer355S1 : ℚ := (d2LitsNearWiderTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer355Arithmetic : weightedUpper d2WiderTransfer355C0 d2Log158Lo d2Log158Hi + weightedUpper d2WiderTransfer355C1 d2Log15Lo d2Log15Hi ≤ d2WiderTransfer355Cap := by decide +kernel
theorem d2WiderTransfer355Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer355Lo:ℚ):ℝ) ((d2WiderTransfer355Hi:ℚ):ℝ), ((d2WiderTransfer355C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer355S0:ℚ):ℝ)| + ((d2WiderTransfer355C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer355S1:ℚ):ℝ)| ≤ ((d2WiderTransfer355Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer355S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355S0,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer355C0 then |x-((d2WiderTransfer355S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer355S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer355S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355S0,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355C0,d2Log158Q,d2WiderTransfer355S0,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer355C0 d2WiderTransfer355S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2WiderTransfer355S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355S1,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer355C1 then |x-((d2WiderTransfer355S1:ℚ):ℝ)| ≤ ((d2Log15Q:ℚ):ℝ) else ((d2Log15Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer355S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer355S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355S1,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer355C1,d2Log15Q,d2WiderTransfer355S1,d2WiderTransfer355Lo,d2WiderTransfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer355C1 d2WiderTransfer355S1 d2Log15Q d2Log15Lo d2Log15Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log15Bounds
  have har : (((weightedUpper d2WiderTransfer355C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer355C1 d2Log15Lo d2Log15Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer355Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer355Arithmetic
  linarith
#print axioms d2WiderTransfer355Arithmetic
#print axioms d2WiderTransfer355Bound
def d2WiderTransfer356Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer356Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (688200163) 1 (-30))
def d2WiderTransfer356Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (9265329255947156531283) 1 (-79))
def d2WiderTransfer356C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (23) 25 (-5))
def d2WiderTransfer356S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer356Arithmetic : weightedUpper d2WiderTransfer356C0 d2Log159Lo d2Log159Hi ≤ d2WiderTransfer356Cap := by decide +kernel
theorem d2WiderTransfer356Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer356Lo:ℚ):ℝ) ((d2WiderTransfer356Hi:ℚ):ℝ), ((d2WiderTransfer356C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer356S0:ℚ):ℝ)| ≤ ((d2WiderTransfer356Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer356S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer356S0,d2WiderTransfer356Lo,d2WiderTransfer356Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer356C0 then |x-((d2WiderTransfer356S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer356S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer356S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer356S0,d2WiderTransfer356Lo,d2WiderTransfer356Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer356C0,d2Log159Q,d2WiderTransfer356S0,d2WiderTransfer356Lo,d2WiderTransfer356Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer356C0 d2WiderTransfer356S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have har : (((weightedUpper d2WiderTransfer356C0 d2Log159Lo d2Log159Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer356Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer356Arithmetic
  linarith
#print axioms d2WiderTransfer356Arithmetic
#print axioms d2WiderTransfer356Bound
def d2WiderTransfer357Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (343261221) 1 (-29))
def d2WiderTransfer357Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (688200163) 1 (-30))
def d2WiderTransfer357Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (17690822951580791679059) 1 (-79))
def d2WiderTransfer357C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (3) 275 (-5))
def d2WiderTransfer357S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
def d2WiderTransfer357C1 : ℚ := (d2LitsNearWiderTransfers044.q2 (-5) 11 (-4))
def d2WiderTransfer357S1 : ℚ := (d2LitsNearWiderTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer357Arithmetic : weightedUpper d2WiderTransfer357C0 d2Log159Lo d2Log159Hi + weightedUpper d2WiderTransfer357C1 d2Log15Lo d2Log15Hi ≤ d2WiderTransfer357Cap := by decide +kernel
theorem d2WiderTransfer357Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer357Lo:ℚ):ℝ) ((d2WiderTransfer357Hi:ℚ):ℝ), ((d2WiderTransfer357C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer357S0:ℚ):ℝ)| + ((d2WiderTransfer357C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer357S1:ℚ):ℝ)| ≤ ((d2WiderTransfer357Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer357S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357S0,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer357C0 then |x-((d2WiderTransfer357S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer357S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer357S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357S0,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357C0,d2Log159Q,d2WiderTransfer357S0,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer357C0 d2WiderTransfer357S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have hn1 : x-((d2WiderTransfer357S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357S1,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer357C1 then |x-((d2WiderTransfer357S1:ℚ):ℝ)| ≤ ((d2Log15Q:ℚ):ℝ) else ((d2Log15Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer357S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer357S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357S1,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer357C1,d2Log15Q,d2WiderTransfer357S1,d2WiderTransfer357Lo,d2WiderTransfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer357C1 d2WiderTransfer357S1 d2Log15Q d2Log15Lo d2Log15Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log15Bounds
  have har : (((weightedUpper d2WiderTransfer357C0 d2Log159Lo d2Log159Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer357C1 d2Log15Lo d2Log15Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer357Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer357Arithmetic
  linarith
#print axioms d2WiderTransfer357Arithmetic
#print axioms d2WiderTransfer357Bound
def d2WiderTransfer358Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (688200163) 1 (-30))
def d2WiderTransfer358Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (172469471) 1 (-28))
def d2WiderTransfer358Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (837258569895468822063) 1 (-78))
def d2WiderTransfer358C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer358S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
def d2WiderTransfer358C1 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 55 (-3))
def d2WiderTransfer358S1 : ℚ := (d2LitsNearWiderTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer358Arithmetic : weightedUpper d2WiderTransfer358C0 d2Log159Lo d2Log159Hi + weightedUpper d2WiderTransfer358C1 d2Log14Lo d2Log14Hi ≤ d2WiderTransfer358Cap := by decide +kernel
theorem d2WiderTransfer358Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer358Lo:ℚ):ℝ) ((d2WiderTransfer358Hi:ℚ):ℝ), ((d2WiderTransfer358C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer358S0:ℚ):ℝ)| + ((d2WiderTransfer358C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer358S1:ℚ):ℝ)| ≤ ((d2WiderTransfer358Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer358S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358S0,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer358C0 then |x-((d2WiderTransfer358S0:ℚ):ℝ)| ≤ ((d2Log159Q:ℚ):ℝ) else ((d2Log159Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer358S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer358S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358S0,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358C0,d2Log159Q,d2WiderTransfer358S0,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer358C0 d2WiderTransfer358S0 d2Log159Q d2Log159Lo d2Log159Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log159Bounds
  have hn1 : x-((d2WiderTransfer358S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358S1,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer358C1 then |x-((d2WiderTransfer358S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer358S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer358S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358S1,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer358C1,d2Log14Q,d2WiderTransfer358S1,d2WiderTransfer358Lo,d2WiderTransfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer358C1 d2WiderTransfer358S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2WiderTransfer358C0 d2Log159Lo d2Log159Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer358C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer358Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer358Arithmetic
  linarith
#print axioms d2WiderTransfer358Arithmetic
#print axioms d2WiderTransfer358Bound
def d2WiderTransfer359Lo : ℚ := (d2LitsNearWiderTransfers044.q2 (688200163) 1 (-30))
def d2WiderTransfer359Hi : ℚ := (d2LitsNearWiderTransfers044.q2 (172469471) 1 (-28))
def d2WiderTransfer359Cap : ℚ := (d2LitsNearWiderTransfers044.q2 (4670207538377040555567) 1 (-78))
def d2WiderTransfer359C0 : ℚ := (d2LitsNearWiderTransfers044.q2 (23) 25 (-5))
def d2WiderTransfer359S0 : ℚ := (d2LitsNearWiderTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer359Arithmetic : weightedUpper d2WiderTransfer359C0 d2Log160Lo d2Log160Hi ≤ d2WiderTransfer359Cap := by decide +kernel
theorem d2WiderTransfer359Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer359Lo:ℚ):ℝ) ((d2WiderTransfer359Hi:ℚ):ℝ), ((d2WiderTransfer359C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer359S0:ℚ):ℝ)| ≤ ((d2WiderTransfer359Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer359S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer359S0,d2WiderTransfer359Lo,d2WiderTransfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer359C0 then |x-((d2WiderTransfer359S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer359S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer359S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer359S0,d2WiderTransfer359Lo,d2WiderTransfer359Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2WiderTransfer359C0,d2Log160Q,d2WiderTransfer359S0,d2WiderTransfer359Lo,d2WiderTransfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer359C0 d2WiderTransfer359S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2WiderTransfer359C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer359Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer359Arithmetic
  linarith
#print axioms d2WiderTransfer359Arithmetic
#print axioms d2WiderTransfer359Bound
end CatalanMeasure.GenD.Signed.Data.Cells

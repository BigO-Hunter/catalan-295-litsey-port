module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers044
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers044
open D72.LogTransfer
def d2Transfer352Lo : ℚ := (d2LitsNearTransfers044.q2 (2930765) 1 (-22))
def d2Transfer352Hi : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer352Cap : ℚ := (d2LitsNearTransfers044.q2 (8248696076668099390357) 1 (-78))
def d2Transfer352C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (-5))
def d2Transfer352S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer352Arithmetic : weightedUpper d2Transfer352C0 d2Log167Lo d2Log167Hi ≤ d2Transfer352Cap := by decide +kernel
theorem d2Transfer352Bound : ∀ x ∈ Set.Icc ((d2Transfer352Lo:ℚ):ℝ) ((d2Transfer352Hi:ℚ):ℝ), ((d2Transfer352C0:ℚ):ℝ)*Real.log |x-((d2Transfer352S0:ℚ):ℝ)| ≤ ((d2Transfer352Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer352S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer352S0,d2Transfer352Lo,d2Transfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer352C0 then |x-((d2Transfer352S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer352S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer352S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer352S0,d2Transfer352Lo,d2Transfer352Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer352C0,d2Log167Q,d2Transfer352S0,d2Transfer352Lo,d2Transfer352Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer352C0 d2Transfer352S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have har : (((weightedUpper d2Transfer352C0 d2Log167Lo d2Log167Hi:ℚ):ℝ)) ≤ ((d2Transfer352Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer352Arithmetic
  linarith
#print axioms d2Transfer352Arithmetic
#print axioms d2Transfer352Bound
def d2Transfer353Lo : ℚ := (d2LitsNearTransfers044.q2 (2930765) 1 (-22))
def d2Transfer353Hi : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer353Cap : ℚ := (d2LitsNearTransfers044.q2 (12339905407240976231317) 1 (-78))
def d2Transfer353C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 11 (-5))
def d2Transfer353S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
def d2Transfer353C1 : ℚ := (d2LitsNearTransfers044.q2 (-5) 11 (-4))
def d2Transfer353S1 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer353Arithmetic : weightedUpper d2Transfer353C0 d2Log167Lo d2Log167Hi + weightedUpper d2Transfer353C1 d2Log7Lo d2Log7Hi ≤ d2Transfer353Cap := by decide +kernel
theorem d2Transfer353Bound : ∀ x ∈ Set.Icc ((d2Transfer353Lo:ℚ):ℝ) ((d2Transfer353Hi:ℚ):ℝ), ((d2Transfer353C0:ℚ):ℝ)*Real.log |x-((d2Transfer353S0:ℚ):ℝ)| + ((d2Transfer353C1:ℚ):ℝ)*Real.log |x-((d2Transfer353S1:ℚ):ℝ)| ≤ ((d2Transfer353Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer353S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353S0,d2Transfer353Lo,d2Transfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer353C0 then |x-((d2Transfer353S0:ℚ):ℝ)| ≤ ((d2Log167Q:ℚ):ℝ) else ((d2Log167Q:ℚ):ℝ) ≤ |x-((d2Transfer353S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer353S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353S0,d2Transfer353Lo,d2Transfer353Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353C0,d2Log167Q,d2Transfer353S0,d2Transfer353Lo,d2Transfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer353C0 d2Transfer353S0 d2Log167Q d2Log167Lo d2Log167Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log167Bounds
  have hn1 : x-((d2Transfer353S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353S1,d2Transfer353Lo,d2Transfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer353C1 then |x-((d2Transfer353S1:ℚ):ℝ)| ≤ ((d2Log7Q:ℚ):ℝ) else ((d2Log7Q:ℚ):ℝ) ≤ |x-((d2Transfer353S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer353S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353S1,d2Transfer353Lo,d2Transfer353Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer353C1,d2Log7Q,d2Transfer353S1,d2Transfer353Lo,d2Transfer353Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer353C1 d2Transfer353S1 d2Log7Q d2Log7Lo d2Log7Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log7Bounds
  have har : (((weightedUpper d2Transfer353C0 d2Log167Lo d2Log167Hi:ℚ):ℝ) + ((weightedUpper d2Transfer353C1 d2Log7Lo d2Log7Hi:ℚ):ℝ)) ≤ ((d2Transfer353Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer353Arithmetic
  linarith
#print axioms d2Transfer353Arithmetic
#print axioms d2Transfer353Bound
def d2Transfer354Lo : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer354Hi : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer354Cap : ℚ := (d2LitsNearTransfers044.q2 (24239257739226882297541) 1 (-80))
def d2Transfer354C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 25 (-4))
def d2Transfer354S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer354Arithmetic : weightedUpper d2Transfer354C0 d2Log168Lo d2Log168Hi ≤ d2Transfer354Cap := by decide +kernel
theorem d2Transfer354Bound : ∀ x ∈ Set.Icc ((d2Transfer354Lo:ℚ):ℝ) ((d2Transfer354Hi:ℚ):ℝ), ((d2Transfer354C0:ℚ):ℝ)*Real.log |x-((d2Transfer354S0:ℚ):ℝ)| ≤ ((d2Transfer354Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer354S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer354S0,d2Transfer354Lo,d2Transfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer354C0 then |x-((d2Transfer354S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer354S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer354S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer354S0,d2Transfer354Lo,d2Transfer354Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer354C0,d2Log168Q,d2Transfer354S0,d2Transfer354Lo,d2Transfer354Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer354C0 d2Transfer354S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2Transfer354C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2Transfer354Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer354Arithmetic
  linarith
#print axioms d2Transfer354Arithmetic
#print axioms d2Transfer354Bound
def d2Transfer355Lo : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer355Hi : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer355Cap : ℚ := (d2LitsNearTransfers044.q2 (25489557907862617640645) 1 (-80))
def d2Transfer355C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 275 (-4))
def d2Transfer355S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
def d2Transfer355C1 : ℚ := (d2LitsNearTransfers044.q2 (-1) 55 (-3))
def d2Transfer355S1 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer355Arithmetic : weightedUpper d2Transfer355C0 d2Log168Lo d2Log168Hi + weightedUpper d2Transfer355C1 d2Log6Lo d2Log6Hi ≤ d2Transfer355Cap := by decide +kernel
theorem d2Transfer355Bound : ∀ x ∈ Set.Icc ((d2Transfer355Lo:ℚ):ℝ) ((d2Transfer355Hi:ℚ):ℝ), ((d2Transfer355C0:ℚ):ℝ)*Real.log |x-((d2Transfer355S0:ℚ):ℝ)| + ((d2Transfer355C1:ℚ):ℝ)*Real.log |x-((d2Transfer355S1:ℚ):ℝ)| ≤ ((d2Transfer355Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer355S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355S0,d2Transfer355Lo,d2Transfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer355C0 then |x-((d2Transfer355S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer355S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer355S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355S0,d2Transfer355Lo,d2Transfer355Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355C0,d2Log168Q,d2Transfer355S0,d2Transfer355Lo,d2Transfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer355C0 d2Transfer355S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2Transfer355S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355S1,d2Transfer355Lo,d2Transfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer355C1 then |x-((d2Transfer355S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2Transfer355S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer355S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355S1,d2Transfer355Lo,d2Transfer355Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer355C1,d2Log6Q,d2Transfer355S1,d2Transfer355Lo,d2Transfer355Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer355C1 d2Transfer355S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2Transfer355C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2Transfer355C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2Transfer355Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer355Arithmetic
  linarith
#print axioms d2Transfer355Arithmetic
#print axioms d2Transfer355Bound
def d2Transfer356Lo : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer356Hi : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer356Cap : ℚ := (d2LitsNearTransfers044.q2 (40712619998285578161861) 1 (-80))
def d2Transfer356C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (-5))
def d2Transfer356S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer356Arithmetic : weightedUpper d2Transfer356C0 d2Log168Lo d2Log168Hi ≤ d2Transfer356Cap := by decide +kernel
theorem d2Transfer356Bound : ∀ x ∈ Set.Icc ((d2Transfer356Lo:ℚ):ℝ) ((d2Transfer356Hi:ℚ):ℝ), ((d2Transfer356C0:ℚ):ℝ)*Real.log |x-((d2Transfer356S0:ℚ):ℝ)| ≤ ((d2Transfer356Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer356S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer356S0,d2Transfer356Lo,d2Transfer356Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer356C0 then |x-((d2Transfer356S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer356S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer356S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer356S0,d2Transfer356Lo,d2Transfer356Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer356C0,d2Log168Q,d2Transfer356S0,d2Transfer356Lo,d2Transfer356Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer356C0 d2Transfer356S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have har : (((weightedUpper d2Transfer356C0 d2Log168Lo d2Log168Hi:ℚ):ℝ)) ≤ ((d2Transfer356Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer356Arithmetic
  linarith
#print axioms d2Transfer356Arithmetic
#print axioms d2Transfer356Bound
def d2Transfer357Lo : ℚ := (d2LitsNearTransfers044.q2 (25123841) 1 (-25))
def d2Transfer357Hi : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer357Cap : ℚ := (d2LitsNearTransfers044.q2 (57077457320577085525701) 1 (-80))
def d2Transfer357C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 11 (-5))
def d2Transfer357S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
def d2Transfer357C1 : ℚ := (d2LitsNearTransfers044.q2 (-5) 11 (-4))
def d2Transfer357S1 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer357Arithmetic : weightedUpper d2Transfer357C0 d2Log168Lo d2Log168Hi + weightedUpper d2Transfer357C1 d2Log6Lo d2Log6Hi ≤ d2Transfer357Cap := by decide +kernel
theorem d2Transfer357Bound : ∀ x ∈ Set.Icc ((d2Transfer357Lo:ℚ):ℝ) ((d2Transfer357Hi:ℚ):ℝ), ((d2Transfer357C0:ℚ):ℝ)*Real.log |x-((d2Transfer357S0:ℚ):ℝ)| + ((d2Transfer357C1:ℚ):ℝ)*Real.log |x-((d2Transfer357S1:ℚ):ℝ)| ≤ ((d2Transfer357Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer357S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357S0,d2Transfer357Lo,d2Transfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer357C0 then |x-((d2Transfer357S0:ℚ):ℝ)| ≤ ((d2Log168Q:ℚ):ℝ) else ((d2Log168Q:ℚ):ℝ) ≤ |x-((d2Transfer357S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer357S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357S0,d2Transfer357Lo,d2Transfer357Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357C0,d2Log168Q,d2Transfer357S0,d2Transfer357Lo,d2Transfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer357C0 d2Transfer357S0 d2Log168Q d2Log168Lo d2Log168Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log168Bounds
  have hn1 : x-((d2Transfer357S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357S1,d2Transfer357Lo,d2Transfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer357C1 then |x-((d2Transfer357S1:ℚ):ℝ)| ≤ ((d2Log6Q:ℚ):ℝ) else ((d2Log6Q:ℚ):ℝ) ≤ |x-((d2Transfer357S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer357S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357S1,d2Transfer357Lo,d2Transfer357Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer357C1,d2Log6Q,d2Transfer357S1,d2Transfer357Lo,d2Transfer357Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer357C1 d2Transfer357S1 d2Log6Q d2Log6Lo d2Log6Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log6Bounds
  have har : (((weightedUpper d2Transfer357C0 d2Log168Lo d2Log168Hi:ℚ):ℝ) + ((weightedUpper d2Transfer357C1 d2Log6Lo d2Log6Hi:ℚ):ℝ)) ≤ ((d2Transfer357Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer357Arithmetic
  linarith
#print axioms d2Transfer357Arithmetic
#print axioms d2Transfer357Bound
def d2Transfer358Lo : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer358Hi : ℚ := (d2LitsNearTransfers044.q2 (7539251) 1 (-23))
def d2Transfer358Cap : ℚ := (d2LitsNearTransfers044.q2 (48017980514036806306389) 1 (-80))
def d2Transfer358C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 25 (-4))
def d2Transfer358S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer358Arithmetic : weightedUpper d2Transfer358C0 d2Log169Lo d2Log169Hi ≤ d2Transfer358Cap := by decide +kernel
theorem d2Transfer358Bound : ∀ x ∈ Set.Icc ((d2Transfer358Lo:ℚ):ℝ) ((d2Transfer358Hi:ℚ):ℝ), ((d2Transfer358C0:ℚ):ℝ)*Real.log |x-((d2Transfer358S0:ℚ):ℝ)| ≤ ((d2Transfer358Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer358S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer358S0,d2Transfer358Lo,d2Transfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer358C0 then |x-((d2Transfer358S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer358S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer358S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer358S0,d2Transfer358Lo,d2Transfer358Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer358C0,d2Log169Q,d2Transfer358S0,d2Transfer358Lo,d2Transfer358Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer358C0 d2Transfer358S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have har : (((weightedUpper d2Transfer358C0 d2Log169Lo d2Log169Hi:ℚ):ℝ)) ≤ ((d2Transfer358Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer358Arithmetic
  linarith
#print axioms d2Transfer358Arithmetic
#print axioms d2Transfer358Bound
def d2Transfer359Lo : ℚ := (d2LitsNearTransfers044.q2 (13400781) 1 (-24))
def d2Transfer359Hi : ℚ := (d2LitsNearTransfers044.q2 (7539251) 1 (-23))
def d2Transfer359Cap : ℚ := (d2LitsNearTransfers044.q2 (49268280682672541649493) 1 (-80))
def d2Transfer359C0 : ℚ := (d2LitsNearTransfers044.q2 (1) 275 (-4))
def d2Transfer359S0 : ℚ := (d2LitsNearTransfers044.q2 (-1) 1 (0))
def d2Transfer359C1 : ℚ := (d2LitsNearTransfers044.q2 (-1) 55 (-3))
def d2Transfer359S1 : ℚ := (d2LitsNearTransfers044.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer359Arithmetic : weightedUpper d2Transfer359C0 d2Log169Lo d2Log169Hi + weightedUpper d2Transfer359C1 d2Log5Lo d2Log5Hi ≤ d2Transfer359Cap := by decide +kernel
theorem d2Transfer359Bound : ∀ x ∈ Set.Icc ((d2Transfer359Lo:ℚ):ℝ) ((d2Transfer359Hi:ℚ):ℝ), ((d2Transfer359C0:ℚ):ℝ)*Real.log |x-((d2Transfer359S0:ℚ):ℝ)| + ((d2Transfer359C1:ℚ):ℝ)*Real.log |x-((d2Transfer359S1:ℚ):ℝ)| ≤ ((d2Transfer359Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer359S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359S0,d2Transfer359Lo,d2Transfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer359C0 then |x-((d2Transfer359S0:ℚ):ℝ)| ≤ ((d2Log169Q:ℚ):ℝ) else ((d2Log169Q:ℚ):ℝ) ≤ |x-((d2Transfer359S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer359S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359S0,d2Transfer359Lo,d2Transfer359Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359C0,d2Log169Q,d2Transfer359S0,d2Transfer359Lo,d2Transfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer359C0 d2Transfer359S0 d2Log169Q d2Log169Lo d2Log169Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log169Bounds
  have hn1 : x-((d2Transfer359S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359S1,d2Transfer359Lo,d2Transfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer359C1 then |x-((d2Transfer359S1:ℚ):ℝ)| ≤ ((d2Log5Q:ℚ):ℝ) else ((d2Log5Q:ℚ):ℝ) ≤ |x-((d2Transfer359S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer359S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359S1,d2Transfer359Lo,d2Transfer359Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers044.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache010.q2, d2Transfer359C1,d2Log5Q,d2Transfer359S1,d2Transfer359Lo,d2Transfer359Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer359C1 d2Transfer359S1 d2Log5Q d2Log5Lo d2Log5Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log5Bounds
  have har : (((weightedUpper d2Transfer359C0 d2Log169Lo d2Log169Hi:ℚ):ℝ) + ((weightedUpper d2Transfer359C1 d2Log5Lo d2Log5Hi:ℚ):ℝ)) ≤ ((d2Transfer359Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer359Arithmetic
  linarith
#print axioms d2Transfer359Arithmetic
#print axioms d2Transfer359Bound
end CatalanMeasure.GenD.Signed.Data.Cells

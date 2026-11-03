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
namespace d2LitsNearTransfers065
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers065
open D72.LogTransfer
def d2Transfer520Lo : ℚ := (d2LitsNearTransfers065.q2 (336550337) 1 (-29))
def d2Transfer520Hi : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer520Cap : ℚ := (d2LitsNearTransfers065.q2 (1948091120741767569807) 1 (-80))
def d2Transfer520C0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer520S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
def d2Transfer520C1 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer520S1 : ℚ := (d2LitsNearTransfers065.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer520Arithmetic : weightedUpper d2Transfer520C0 d2Log143Lo d2Log143Hi + weightedUpper d2Transfer520C1 d2Log30Lo d2Log30Hi ≤ d2Transfer520Cap := by decide +kernel
theorem d2Transfer520Bound : ∀ x ∈ Set.Icc ((d2Transfer520Lo:ℚ):ℝ) ((d2Transfer520Hi:ℚ):ℝ), ((d2Transfer520C0:ℚ):ℝ)*Real.log |x-((d2Transfer520S0:ℚ):ℝ)| + ((d2Transfer520C1:ℚ):ℝ)*Real.log |x-((d2Transfer520S1:ℚ):ℝ)| ≤ ((d2Transfer520Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer520S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520S0,d2Transfer520Lo,d2Transfer520Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer520C0 then |x-((d2Transfer520S0:ℚ):ℝ)| ≤ ((d2Log143Q:ℚ):ℝ) else ((d2Log143Q:ℚ):ℝ) ≤ |x-((d2Transfer520S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer520S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520S0,d2Transfer520Lo,d2Transfer520Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520C0,d2Log143Q,d2Transfer520S0,d2Transfer520Lo,d2Transfer520Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer520C0 d2Transfer520S0 d2Log143Q d2Log143Lo d2Log143Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log143Bounds
  have hn1 : x-((d2Transfer520S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520S1,d2Transfer520Lo,d2Transfer520Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer520C1 then |x-((d2Transfer520S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2Transfer520S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer520S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520S1,d2Transfer520Lo,d2Transfer520Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer520C1,d2Log30Q,d2Transfer520S1,d2Transfer520Lo,d2Transfer520Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer520C1 d2Transfer520S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2Transfer520C0 d2Log143Lo d2Log143Hi:ℚ):ℝ) + ((weightedUpper d2Transfer520C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2Transfer520Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer520Arithmetic
  linarith
#print axioms d2Transfer520Arithmetic
#print axioms d2Transfer520Bound
def d2Transfer521Lo : ℚ := (d2LitsNearTransfers065.q2 (336550337) 1 (-29))
def d2Transfer521Hi : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer521Cap : ℚ := (d2LitsNearTransfers065.q2 (17279886994668054503823) 1 (-80))
def d2Transfer521C0 : ℚ := (d2LitsNearTransfers065.q2 (23) 25 (-5))
def d2Transfer521S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer521Arithmetic : weightedUpper d2Transfer521C0 d2Log144Lo d2Log144Hi ≤ d2Transfer521Cap := by decide +kernel
theorem d2Transfer521Bound : ∀ x ∈ Set.Icc ((d2Transfer521Lo:ℚ):ℝ) ((d2Transfer521Hi:ℚ):ℝ), ((d2Transfer521C0:ℚ):ℝ)*Real.log |x-((d2Transfer521S0:ℚ):ℝ)| ≤ ((d2Transfer521Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer521S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer521S0,d2Transfer521Lo,d2Transfer521Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer521C0 then |x-((d2Transfer521S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer521S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer521S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer521S0,d2Transfer521Lo,d2Transfer521Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer521C0,d2Log144Q,d2Transfer521S0,d2Transfer521Lo,d2Transfer521Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer521C0 d2Transfer521S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have har : (((weightedUpper d2Transfer521C0 d2Log144Lo d2Log144Hi:ℚ):ℝ)) ≤ ((d2Transfer521Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer521Arithmetic
  linarith
#print axioms d2Transfer521Arithmetic
#print axioms d2Transfer521Bound
def d2Transfer522Lo : ℚ := (d2LitsNearTransfers065.q2 (336550337) 1 (-29))
def d2Transfer522Hi : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer522Cap : ℚ := (d2LitsNearTransfers065.q2 (34130874385935324799375) 1 (-80))
def d2Transfer522C0 : ℚ := (d2LitsNearTransfers065.q2 (3) 275 (-5))
def d2Transfer522S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
def d2Transfer522C1 : ℚ := (d2LitsNearTransfers065.q2 (-5) 11 (-4))
def d2Transfer522S1 : ℚ := (d2LitsNearTransfers065.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer522Arithmetic : weightedUpper d2Transfer522C0 d2Log144Lo d2Log144Hi + weightedUpper d2Transfer522C1 d2Log30Lo d2Log30Hi ≤ d2Transfer522Cap := by decide +kernel
theorem d2Transfer522Bound : ∀ x ∈ Set.Icc ((d2Transfer522Lo:ℚ):ℝ) ((d2Transfer522Hi:ℚ):ℝ), ((d2Transfer522C0:ℚ):ℝ)*Real.log |x-((d2Transfer522S0:ℚ):ℝ)| + ((d2Transfer522C1:ℚ):ℝ)*Real.log |x-((d2Transfer522S1:ℚ):ℝ)| ≤ ((d2Transfer522Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer522S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522S0,d2Transfer522Lo,d2Transfer522Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer522C0 then |x-((d2Transfer522S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer522S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer522S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522S0,d2Transfer522Lo,d2Transfer522Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522C0,d2Log144Q,d2Transfer522S0,d2Transfer522Lo,d2Transfer522Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer522C0 d2Transfer522S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2Transfer522S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522S1,d2Transfer522Lo,d2Transfer522Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer522C1 then |x-((d2Transfer522S1:ℚ):ℝ)| ≤ ((d2Log30Q:ℚ):ℝ) else ((d2Log30Q:ℚ):ℝ) ≤ |x-((d2Transfer522S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer522S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522S1,d2Transfer522Lo,d2Transfer522Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer522C1,d2Log30Q,d2Transfer522S1,d2Transfer522Lo,d2Transfer522Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer522C1 d2Transfer522S1 d2Log30Q d2Log30Lo d2Log30Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log30Bounds
  have har : (((weightedUpper d2Transfer522C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2Transfer522C1 d2Log30Lo d2Log30Hi:ℚ):ℝ)) ≤ ((d2Transfer522Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer522Arithmetic
  linarith
#print axioms d2Transfer522Arithmetic
#print axioms d2Transfer522Bound
def d2Transfer523Lo : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer523Hi : ℚ := (d2LitsNearTransfers065.q2 (674778395) 1 (-30))
def d2Transfer523Cap : ℚ := (d2LitsNearTransfers065.q2 (2020425790803095201589) 1 (-80))
def d2Transfer523C0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer523S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
def d2Transfer523C1 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer523S1 : ℚ := (d2LitsNearTransfers065.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer523Arithmetic : weightedUpper d2Transfer523C0 d2Log144Lo d2Log144Hi + weightedUpper d2Transfer523C1 d2Log29Lo d2Log29Hi ≤ d2Transfer523Cap := by decide +kernel
theorem d2Transfer523Bound : ∀ x ∈ Set.Icc ((d2Transfer523Lo:ℚ):ℝ) ((d2Transfer523Hi:ℚ):ℝ), ((d2Transfer523C0:ℚ):ℝ)*Real.log |x-((d2Transfer523S0:ℚ):ℝ)| + ((d2Transfer523C1:ℚ):ℝ)*Real.log |x-((d2Transfer523S1:ℚ):ℝ)| ≤ ((d2Transfer523Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer523S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523S0,d2Transfer523Lo,d2Transfer523Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer523C0 then |x-((d2Transfer523S0:ℚ):ℝ)| ≤ ((d2Log144Q:ℚ):ℝ) else ((d2Log144Q:ℚ):ℝ) ≤ |x-((d2Transfer523S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer523S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523S0,d2Transfer523Lo,d2Transfer523Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523C0,d2Log144Q,d2Transfer523S0,d2Transfer523Lo,d2Transfer523Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer523C0 d2Transfer523S0 d2Log144Q d2Log144Lo d2Log144Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log144Bounds
  have hn1 : x-((d2Transfer523S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523S1,d2Transfer523Lo,d2Transfer523Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer523C1 then |x-((d2Transfer523S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2Transfer523S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer523S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523S1,d2Transfer523Lo,d2Transfer523Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer523C1,d2Log29Q,d2Transfer523S1,d2Transfer523Lo,d2Transfer523Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer523C1 d2Transfer523S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2Transfer523C0 d2Log144Lo d2Log144Hi:ℚ):ℝ) + ((weightedUpper d2Transfer523C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2Transfer523Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer523Arithmetic
  linarith
#print axioms d2Transfer523Arithmetic
#print axioms d2Transfer523Bound
def d2Transfer524Lo : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer524Hi : ℚ := (d2LitsNearTransfers065.q2 (674778395) 1 (-30))
def d2Transfer524Cap : ℚ := (d2LitsNearTransfers065.q2 (17352221664729382135605) 1 (-80))
def d2Transfer524C0 : ℚ := (d2LitsNearTransfers065.q2 (23) 25 (-5))
def d2Transfer524S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer524Arithmetic : weightedUpper d2Transfer524C0 d2Log145Lo d2Log145Hi ≤ d2Transfer524Cap := by decide +kernel
theorem d2Transfer524Bound : ∀ x ∈ Set.Icc ((d2Transfer524Lo:ℚ):ℝ) ((d2Transfer524Hi:ℚ):ℝ), ((d2Transfer524C0:ℚ):ℝ)*Real.log |x-((d2Transfer524S0:ℚ):ℝ)| ≤ ((d2Transfer524Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer524S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer524S0,d2Transfer524Lo,d2Transfer524Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer524C0 then |x-((d2Transfer524S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer524S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer524S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer524S0,d2Transfer524Lo,d2Transfer524Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer524C0,d2Log145Q,d2Transfer524S0,d2Transfer524Lo,d2Transfer524Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer524C0 d2Transfer524S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have har : (((weightedUpper d2Transfer524C0 d2Log145Lo d2Log145Hi:ℚ):ℝ)) ≤ ((d2Transfer524Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer524Arithmetic
  linarith
#print axioms d2Transfer524Arithmetic
#print axioms d2Transfer524Bound
def d2Transfer525Lo : ℚ := (d2LitsNearTransfers065.q2 (1347879069) 1 (-31))
def d2Transfer525Hi : ℚ := (d2LitsNearTransfers065.q2 (674778395) 1 (-30))
def d2Transfer525Cap : ℚ := (d2LitsNearTransfers065.q2 (34203209055996652431157) 1 (-80))
def d2Transfer525C0 : ℚ := (d2LitsNearTransfers065.q2 (3) 275 (-5))
def d2Transfer525S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
def d2Transfer525C1 : ℚ := (d2LitsNearTransfers065.q2 (-5) 11 (-4))
def d2Transfer525S1 : ℚ := (d2LitsNearTransfers065.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer525Arithmetic : weightedUpper d2Transfer525C0 d2Log145Lo d2Log145Hi + weightedUpper d2Transfer525C1 d2Log29Lo d2Log29Hi ≤ d2Transfer525Cap := by decide +kernel
theorem d2Transfer525Bound : ∀ x ∈ Set.Icc ((d2Transfer525Lo:ℚ):ℝ) ((d2Transfer525Hi:ℚ):ℝ), ((d2Transfer525C0:ℚ):ℝ)*Real.log |x-((d2Transfer525S0:ℚ):ℝ)| + ((d2Transfer525C1:ℚ):ℝ)*Real.log |x-((d2Transfer525S1:ℚ):ℝ)| ≤ ((d2Transfer525Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer525S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525S0,d2Transfer525Lo,d2Transfer525Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer525C0 then |x-((d2Transfer525S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer525S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer525S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525S0,d2Transfer525Lo,d2Transfer525Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525C0,d2Log145Q,d2Transfer525S0,d2Transfer525Lo,d2Transfer525Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer525C0 d2Transfer525S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2Transfer525S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525S1,d2Transfer525Lo,d2Transfer525Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer525C1 then |x-((d2Transfer525S1:ℚ):ℝ)| ≤ ((d2Log29Q:ℚ):ℝ) else ((d2Log29Q:ℚ):ℝ) ≤ |x-((d2Transfer525S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer525S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525S1,d2Transfer525Lo,d2Transfer525Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer525C1,d2Log29Q,d2Transfer525S1,d2Transfer525Lo,d2Transfer525Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer525C1 d2Transfer525S1 d2Log29Q d2Log29Lo d2Log29Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log29Bounds
  have har : (((weightedUpper d2Transfer525C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2Transfer525C1 d2Log29Lo d2Log29Hi:ℚ):ℝ)) ≤ ((d2Transfer525Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer525Arithmetic
  linarith
#print axioms d2Transfer525Arithmetic
#print axioms d2Transfer525Bound
def d2Transfer526Lo : ℚ := (d2LitsNearTransfers065.q2 (674778395) 1 (-30))
def d2Transfer526Hi : ℚ := (d2LitsNearTransfers065.q2 (1351234511) 1 (-31))
def d2Transfer526Cap : ℚ := (d2LitsNearTransfers065.q2 (1046456100392806920763) 1 (-79))
def d2Transfer526C0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer526S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
def d2Transfer526C1 : ℚ := (d2LitsNearTransfers065.q2 (-1) 55 (-3))
def d2Transfer526S1 : ℚ := (d2LitsNearTransfers065.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer526Arithmetic : weightedUpper d2Transfer526C0 d2Log145Lo d2Log145Hi + weightedUpper d2Transfer526C1 d2Log28Lo d2Log28Hi ≤ d2Transfer526Cap := by decide +kernel
theorem d2Transfer526Bound : ∀ x ∈ Set.Icc ((d2Transfer526Lo:ℚ):ℝ) ((d2Transfer526Hi:ℚ):ℝ), ((d2Transfer526C0:ℚ):ℝ)*Real.log |x-((d2Transfer526S0:ℚ):ℝ)| + ((d2Transfer526C1:ℚ):ℝ)*Real.log |x-((d2Transfer526S1:ℚ):ℝ)| ≤ ((d2Transfer526Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer526S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526S0,d2Transfer526Lo,d2Transfer526Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer526C0 then |x-((d2Transfer526S0:ℚ):ℝ)| ≤ ((d2Log145Q:ℚ):ℝ) else ((d2Log145Q:ℚ):ℝ) ≤ |x-((d2Transfer526S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer526S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526S0,d2Transfer526Lo,d2Transfer526Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526C0,d2Log145Q,d2Transfer526S0,d2Transfer526Lo,d2Transfer526Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer526C0 d2Transfer526S0 d2Log145Q d2Log145Lo d2Log145Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log145Bounds
  have hn1 : x-((d2Transfer526S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526S1,d2Transfer526Lo,d2Transfer526Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer526C1 then |x-((d2Transfer526S1:ℚ):ℝ)| ≤ ((d2Log28Q:ℚ):ℝ) else ((d2Log28Q:ℚ):ℝ) ≤ |x-((d2Transfer526S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer526S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526S1,d2Transfer526Lo,d2Transfer526Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer526C1,d2Log28Q,d2Transfer526S1,d2Transfer526Lo,d2Transfer526Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer526C1 d2Transfer526S1 d2Log28Q d2Log28Lo d2Log28Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log28Bounds
  have har : (((weightedUpper d2Transfer526C0 d2Log145Lo d2Log145Hi:ℚ):ℝ) + ((weightedUpper d2Transfer526C1 d2Log28Lo d2Log28Hi:ℚ):ℝ)) ≤ ((d2Transfer526Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer526Arithmetic
  linarith
#print axioms d2Transfer526Arithmetic
#print axioms d2Transfer526Bound
def d2Transfer527Lo : ℚ := (d2LitsNearTransfers065.q2 (674778395) 1 (-30))
def d2Transfer527Hi : ℚ := (d2LitsNearTransfers065.q2 (1351234511) 1 (-31))
def d2Transfer527Cap : ℚ := (d2LitsNearTransfers065.q2 (8712354037355950387771) 1 (-79))
def d2Transfer527C0 : ℚ := (d2LitsNearTransfers065.q2 (23) 25 (-5))
def d2Transfer527S0 : ℚ := (d2LitsNearTransfers065.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer527Arithmetic : weightedUpper d2Transfer527C0 d2Log146Lo d2Log146Hi ≤ d2Transfer527Cap := by decide +kernel
theorem d2Transfer527Bound : ∀ x ∈ Set.Icc ((d2Transfer527Lo:ℚ):ℝ) ((d2Transfer527Hi:ℚ):ℝ), ((d2Transfer527C0:ℚ):ℝ)*Real.log |x-((d2Transfer527S0:ℚ):ℝ)| ≤ ((d2Transfer527Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer527S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer527S0,d2Transfer527Lo,d2Transfer527Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer527C0 then |x-((d2Transfer527S0:ℚ):ℝ)| ≤ ((d2Log146Q:ℚ):ℝ) else ((d2Log146Q:ℚ):ℝ) ≤ |x-((d2Transfer527S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer527S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer527S0,d2Transfer527Lo,d2Transfer527Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers065.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache008.q2, d2LitsNearLogCache009.q2, d2Transfer527C0,d2Log146Q,d2Transfer527S0,d2Transfer527Lo,d2Transfer527Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer527C0 d2Transfer527S0 d2Log146Q d2Log146Lo d2Log146Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log146Bounds
  have har : (((weightedUpper d2Transfer527C0 d2Log146Lo d2Log146Hi:ℚ):ℝ)) ≤ ((d2Transfer527Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer527Arithmetic
  linarith
#print axioms d2Transfer527Arithmetic
#print axioms d2Transfer527Bound
end CatalanMeasure.GenD.Signed.Data.Cells

module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache002
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache008
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers012
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers012
open D72.LogTransfer
def d2WiderTransfer96Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (162403145) 1 (-28))
def d2WiderTransfer96Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer96Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (17947568960646277009121) 1 (-80))
def d2WiderTransfer96C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (-5))
def d2WiderTransfer96S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer96Arithmetic : weightedUpper d2WiderTransfer96C0 d2Log126Lo d2Log126Hi ≤ d2WiderTransfer96Cap := by decide +kernel
theorem d2WiderTransfer96Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer96Lo:ℚ):ℝ) ((d2WiderTransfer96Hi:ℚ):ℝ), ((d2WiderTransfer96C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer96S0:ℚ):ℝ)| ≤ ((d2WiderTransfer96Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer96S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer96S0,d2WiderTransfer96Lo,d2WiderTransfer96Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer96C0 then |x-((d2WiderTransfer96S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer96S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer96S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer96S0,d2WiderTransfer96Lo,d2WiderTransfer96Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer96C0,d2Log126Q,d2WiderTransfer96S0,d2WiderTransfer96Lo,d2WiderTransfer96Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer96C0 d2WiderTransfer96S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have har : (((weightedUpper d2WiderTransfer96C0 d2Log126Lo d2Log126Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer96Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer96Arithmetic
  linarith
#print axioms d2WiderTransfer96Arithmetic
#print axioms d2WiderTransfer96Bound
def d2WiderTransfer97Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (162403145) 1 (-28))
def d2WiderTransfer97Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer97Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (34312406282937784372961) 1 (-80))
def d2WiderTransfer97C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 11 (-5))
def d2WiderTransfer97S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
def d2WiderTransfer97C1 : ℚ := (d2LitsNearWiderTransfers012.q2 (-5) 11 (-4))
def d2WiderTransfer97S1 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer97Arithmetic : weightedUpper d2WiderTransfer97C0 d2Log126Lo d2Log126Hi + weightedUpper d2WiderTransfer97C1 d2Log48Lo d2Log48Hi ≤ d2WiderTransfer97Cap := by decide +kernel
theorem d2WiderTransfer97Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer97Lo:ℚ):ℝ) ((d2WiderTransfer97Hi:ℚ):ℝ), ((d2WiderTransfer97C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer97S0:ℚ):ℝ)| + ((d2WiderTransfer97C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer97S1:ℚ):ℝ)| ≤ ((d2WiderTransfer97Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer97S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97S0,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer97C0 then |x-((d2WiderTransfer97S0:ℚ):ℝ)| ≤ ((d2Log126Q:ℚ):ℝ) else ((d2Log126Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer97S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer97S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97S0,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97C0,d2Log126Q,d2WiderTransfer97S0,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer97C0 d2WiderTransfer97S0 d2Log126Q d2Log126Lo d2Log126Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log126Bounds
  have hn1 : x-((d2WiderTransfer97S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97S1,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer97C1 then |x-((d2WiderTransfer97S1:ℚ):ℝ)| ≤ ((d2Log48Q:ℚ):ℝ) else ((d2Log48Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer97S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer97S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97S1,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer97C1,d2Log48Q,d2WiderTransfer97S1,d2WiderTransfer97Lo,d2WiderTransfer97Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer97C1 d2WiderTransfer97S1 d2Log48Q d2Log48Lo d2Log48Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log48Bounds
  have har : (((weightedUpper d2WiderTransfer97C0 d2Log126Lo d2Log126Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer97C1 d2Log48Lo d2Log48Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer97Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer97Arithmetic
  linarith
#print axioms d2WiderTransfer97Arithmetic
#print axioms d2WiderTransfer97Bound
def d2WiderTransfer98Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer98Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer98Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (188861997272932581765) 1 (-77))
def d2WiderTransfer98C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 25 (-4))
def d2WiderTransfer98S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer98Arithmetic : weightedUpper d2WiderTransfer98C0 d2Log127Lo d2Log127Hi ≤ d2WiderTransfer98Cap := by decide +kernel
theorem d2WiderTransfer98Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer98Lo:ℚ):ℝ) ((d2WiderTransfer98Hi:ℚ):ℝ), ((d2WiderTransfer98C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer98S0:ℚ):ℝ)| ≤ ((d2WiderTransfer98Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer98S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer98S0,d2WiderTransfer98Lo,d2WiderTransfer98Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer98C0 then |x-((d2WiderTransfer98S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer98S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer98S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer98S0,d2WiderTransfer98Lo,d2WiderTransfer98Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer98C0,d2Log127Q,d2WiderTransfer98S0,d2WiderTransfer98Lo,d2WiderTransfer98Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer98C0 d2WiderTransfer98S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have har : (((weightedUpper d2WiderTransfer98C0 d2Log127Lo d2Log127Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer98Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer98Arithmetic
  linarith
#print axioms d2WiderTransfer98Arithmetic
#print axioms d2WiderTransfer98Bound
def d2WiderTransfer99Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer99Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer99Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (345149518352399499653) 1 (-77))
def d2WiderTransfer99C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 275 (-4))
def d2WiderTransfer99S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
def d2WiderTransfer99C1 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 55 (-3))
def d2WiderTransfer99S1 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer99Arithmetic : weightedUpper d2WiderTransfer99C0 d2Log127Lo d2Log127Hi + weightedUpper d2WiderTransfer99C1 d2Log47Lo d2Log47Hi ≤ d2WiderTransfer99Cap := by decide +kernel
theorem d2WiderTransfer99Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer99Lo:ℚ):ℝ) ((d2WiderTransfer99Hi:ℚ):ℝ), ((d2WiderTransfer99C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer99S0:ℚ):ℝ)| + ((d2WiderTransfer99C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer99S1:ℚ):ℝ)| ≤ ((d2WiderTransfer99Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer99S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99S0,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer99C0 then |x-((d2WiderTransfer99S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer99S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer99S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99S0,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99C0,d2Log127Q,d2WiderTransfer99S0,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer99C0 d2WiderTransfer99S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have hn1 : x-((d2WiderTransfer99S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99S1,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer99C1 then |x-((d2WiderTransfer99S1:ℚ):ℝ)| ≤ ((d2Log47Q:ℚ):ℝ) else ((d2Log47Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer99S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer99S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99S1,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer99C1,d2Log47Q,d2WiderTransfer99S1,d2WiderTransfer99Lo,d2WiderTransfer99Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer99C1 d2WiderTransfer99S1 d2Log47Q d2Log47Lo d2Log47Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log47Bounds
  have har : (((weightedUpper d2WiderTransfer99C0 d2Log127Lo d2Log127Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer99C1 d2Log47Lo d2Log47Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer99Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer99Arithmetic
  linarith
#print axioms d2WiderTransfer99Arithmetic
#print axioms d2WiderTransfer99Bound
def d2WiderTransfer100Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer100Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer100Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (2248032279655269564805) 1 (-77))
def d2WiderTransfer100C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (-5))
def d2WiderTransfer100S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer100Arithmetic : weightedUpper d2WiderTransfer100C0 d2Log127Lo d2Log127Hi ≤ d2WiderTransfer100Cap := by decide +kernel
theorem d2WiderTransfer100Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer100Lo:ℚ):ℝ) ((d2WiderTransfer100Hi:ℚ):ℝ), ((d2WiderTransfer100C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer100S0:ℚ):ℝ)| ≤ ((d2WiderTransfer100Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer100S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer100S0,d2WiderTransfer100Lo,d2WiderTransfer100Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer100C0 then |x-((d2WiderTransfer100S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer100S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer100S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer100S0,d2WiderTransfer100Lo,d2WiderTransfer100Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer100C0,d2Log127Q,d2WiderTransfer100S0,d2WiderTransfer100Lo,d2WiderTransfer100Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer100C0 d2WiderTransfer100S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have har : (((weightedUpper d2WiderTransfer100C0 d2Log127Lo d2Log127Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer100Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer100Arithmetic
  linarith
#print axioms d2WiderTransfer100Arithmetic
#print axioms d2WiderTransfer100Bound
def d2WiderTransfer101Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (326484011) 1 (-29))
def d2WiderTransfer101Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer101Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (4293636944941707985285) 1 (-77))
def d2WiderTransfer101C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 11 (-5))
def d2WiderTransfer101S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
def d2WiderTransfer101C1 : ℚ := (d2LitsNearWiderTransfers012.q2 (-5) 11 (-4))
def d2WiderTransfer101S1 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer101Arithmetic : weightedUpper d2WiderTransfer101C0 d2Log127Lo d2Log127Hi + weightedUpper d2WiderTransfer101C1 d2Log47Lo d2Log47Hi ≤ d2WiderTransfer101Cap := by decide +kernel
theorem d2WiderTransfer101Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer101Lo:ℚ):ℝ) ((d2WiderTransfer101Hi:ℚ):ℝ), ((d2WiderTransfer101C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer101S0:ℚ):ℝ)| + ((d2WiderTransfer101C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer101S1:ℚ):ℝ)| ≤ ((d2WiderTransfer101Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer101S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101S0,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer101C0 then |x-((d2WiderTransfer101S0:ℚ):ℝ)| ≤ ((d2Log127Q:ℚ):ℝ) else ((d2Log127Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer101S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer101S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101S0,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101C0,d2Log127Q,d2WiderTransfer101S0,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer101C0 d2WiderTransfer101S0 d2Log127Q d2Log127Lo d2Log127Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log127Bounds
  have hn1 : x-((d2WiderTransfer101S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101S1,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer101C1 then |x-((d2WiderTransfer101S1:ℚ):ℝ)| ≤ ((d2Log47Q:ℚ):ℝ) else ((d2Log47Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer101S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer101S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101S1,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer101C1,d2Log47Q,d2WiderTransfer101S1,d2WiderTransfer101Lo,d2WiderTransfer101Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer101C1 d2WiderTransfer101S1 d2Log47Q d2Log47Lo d2Log47Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log47Bounds
  have har : (((weightedUpper d2WiderTransfer101C0 d2Log127Lo d2Log127Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer101C1 d2Log47Lo d2Log47Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer101Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer101Arithmetic
  linarith
#print axioms d2WiderTransfer101Arithmetic
#print axioms d2WiderTransfer101Bound
def d2WiderTransfer102Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer102Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (82040433) 1 (-27))
def d2WiderTransfer102Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (773774829148068366265) 1 (-79))
def d2WiderTransfer102C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 25 (-4))
def d2WiderTransfer102S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer102Arithmetic : weightedUpper d2WiderTransfer102C0 d2Log128Lo d2Log128Hi ≤ d2WiderTransfer102Cap := by decide +kernel
theorem d2WiderTransfer102Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer102Lo:ℚ):ℝ) ((d2WiderTransfer102Hi:ℚ):ℝ), ((d2WiderTransfer102C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer102S0:ℚ):ℝ)| ≤ ((d2WiderTransfer102Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer102S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer102S0,d2WiderTransfer102Lo,d2WiderTransfer102Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer102C0 then |x-((d2WiderTransfer102S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer102S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer102S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer102S0,d2WiderTransfer102Lo,d2WiderTransfer102Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer102C0,d2Log128Q,d2WiderTransfer102S0,d2WiderTransfer102Lo,d2WiderTransfer102Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer102C0 d2WiderTransfer102S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have har : (((weightedUpper d2WiderTransfer102C0 d2Log128Lo d2Log128Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer102Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer102Arithmetic
  linarith
#print axioms d2WiderTransfer102Arithmetic
#print axioms d2WiderTransfer102Bound
def d2WiderTransfer103Lo : ℚ := (d2LitsNearWiderTransfers012.q2 (654645743) 1 (-30))
def d2WiderTransfer103Hi : ℚ := (d2LitsNearWiderTransfers012.q2 (82040433) 1 (-27))
def d2WiderTransfer103Cap : ℚ := (d2LitsNearWiderTransfers012.q2 (1398924913465936037817) 1 (-79))
def d2WiderTransfer103C0 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 275 (-4))
def d2WiderTransfer103S0 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 1 (0))
def d2WiderTransfer103C1 : ℚ := (d2LitsNearWiderTransfers012.q2 (-1) 55 (-3))
def d2WiderTransfer103S1 : ℚ := (d2LitsNearWiderTransfers012.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer103Arithmetic : weightedUpper d2WiderTransfer103C0 d2Log128Lo d2Log128Hi + weightedUpper d2WiderTransfer103C1 d2Log46Lo d2Log46Hi ≤ d2WiderTransfer103Cap := by decide +kernel
theorem d2WiderTransfer103Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer103Lo:ℚ):ℝ) ((d2WiderTransfer103Hi:ℚ):ℝ), ((d2WiderTransfer103C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer103S0:ℚ):ℝ)| + ((d2WiderTransfer103C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer103S1:ℚ):ℝ)| ≤ ((d2WiderTransfer103Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer103S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103S0,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer103C0 then |x-((d2WiderTransfer103S0:ℚ):ℝ)| ≤ ((d2Log128Q:ℚ):ℝ) else ((d2Log128Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer103S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer103S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103S0,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103C0,d2Log128Q,d2WiderTransfer103S0,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer103C0 d2WiderTransfer103S0 d2Log128Q d2Log128Lo d2Log128Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log128Bounds
  have hn1 : x-((d2WiderTransfer103S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103S1,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer103C1 then |x-((d2WiderTransfer103S1:ℚ):ℝ)| ≤ ((d2Log46Q:ℚ):ℝ) else ((d2Log46Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer103S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer103S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103S1,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers012.q2, d2LitsNearLogCache002.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2LitsNearLogCache008.q2, d2WiderTransfer103C1,d2Log46Q,d2WiderTransfer103S1,d2WiderTransfer103Lo,d2WiderTransfer103Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer103C1 d2WiderTransfer103S1 d2Log46Q d2Log46Lo d2Log46Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log46Bounds
  have har : (((weightedUpper d2WiderTransfer103C0 d2Log128Lo d2Log128Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer103C1 d2Log46Lo d2Log46Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer103Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer103Arithmetic
  linarith
#print axioms d2WiderTransfer103Arithmetic
#print axioms d2WiderTransfer103Bound
end CatalanMeasure.GenD.Signed.Data.Cells

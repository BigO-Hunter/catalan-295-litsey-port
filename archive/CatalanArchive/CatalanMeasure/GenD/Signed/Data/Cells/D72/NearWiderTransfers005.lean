module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers005
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers005
open D72.LogTransfer
def d2WiderTransfer40Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (31834725) 1 (-25))
def d2WiderTransfer40Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (16756223) 1 (-24))
def d2WiderTransfer40Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (17306181503079751321725) 1 (-80))
def d2WiderTransfer40C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 25 (-4))
def d2WiderTransfer40S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer40Arithmetic : weightedUpper d2WiderTransfer40C0 d2Log172Lo d2Log172Hi ≤ d2WiderTransfer40Cap := by decide +kernel
theorem d2WiderTransfer40Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer40Lo:ℚ):ℝ) ((d2WiderTransfer40Hi:ℚ):ℝ), ((d2WiderTransfer40C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer40S0:ℚ):ℝ)| ≤ ((d2WiderTransfer40Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer40S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer40S0,d2WiderTransfer40Lo,d2WiderTransfer40Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer40C0 then |x-((d2WiderTransfer40S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer40S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer40S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer40S0,d2WiderTransfer40Lo,d2WiderTransfer40Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer40C0,d2Log172Q,d2WiderTransfer40S0,d2WiderTransfer40Lo,d2WiderTransfer40Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer40C0 d2WiderTransfer40S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have har : (((weightedUpper d2WiderTransfer40C0 d2Log172Lo d2Log172Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer40Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer40Arithmetic
  linarith
#print axioms d2WiderTransfer40Arithmetic
#print axioms d2WiderTransfer40Bound
def d2WiderTransfer41Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (31834725) 1 (-25))
def d2WiderTransfer41Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (16756223) 1 (-24))
def d2WiderTransfer41Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (18553824547935338072189) 1 (-80))
def d2WiderTransfer41C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 275 (-4))
def d2WiderTransfer41S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
def d2WiderTransfer41C1 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 55 (-3))
def d2WiderTransfer41S1 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer41Arithmetic : weightedUpper d2WiderTransfer41C0 d2Log172Lo d2Log172Hi + weightedUpper d2WiderTransfer41C1 d2Log2Lo d2Log2Hi ≤ d2WiderTransfer41Cap := by decide +kernel
theorem d2WiderTransfer41Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer41Lo:ℚ):ℝ) ((d2WiderTransfer41Hi:ℚ):ℝ), ((d2WiderTransfer41C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer41S0:ℚ):ℝ)| + ((d2WiderTransfer41C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer41S1:ℚ):ℝ)| ≤ ((d2WiderTransfer41Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer41S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41S0,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer41C0 then |x-((d2WiderTransfer41S0:ℚ):ℝ)| ≤ ((d2Log172Q:ℚ):ℝ) else ((d2Log172Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer41S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer41S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41S0,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41C0,d2Log172Q,d2WiderTransfer41S0,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer41C0 d2WiderTransfer41S0 d2Log172Q d2Log172Lo d2Log172Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log172Bounds
  have hn1 : x-((d2WiderTransfer41S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41S1,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer41C1 then |x-((d2WiderTransfer41S1:ℚ):ℝ)| ≤ ((d2Log2Q:ℚ):ℝ) else ((d2Log2Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer41S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer41S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41S1,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer41C1,d2Log2Q,d2WiderTransfer41S1,d2WiderTransfer41Lo,d2WiderTransfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer41C1 d2WiderTransfer41S1 d2Log2Q d2Log2Lo d2Log2Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log2Bounds
  have har : (((weightedUpper d2WiderTransfer41C0 d2Log172Lo d2Log172Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer41C1 d2Log2Lo d2Log2Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer41Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer41Arithmetic
  linarith
#print axioms d2WiderTransfer41Arithmetic
#print axioms d2WiderTransfer41Bound
def d2WiderTransfer42Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (16756223) 1 (-24))
def d2WiderTransfer42Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (8380219) 1 (-23))
def d2WiderTransfer42Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (4480500095951157354537) 1 (-78))
def d2WiderTransfer42C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 25 (-4))
def d2WiderTransfer42S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer42Arithmetic : weightedUpper d2WiderTransfer42C0 d2Log173Lo d2Log173Hi ≤ d2WiderTransfer42Cap := by decide +kernel
theorem d2WiderTransfer42Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer42Lo:ℚ):ℝ) ((d2WiderTransfer42Hi:ℚ):ℝ), ((d2WiderTransfer42C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer42S0:ℚ):ℝ)| ≤ ((d2WiderTransfer42Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer42S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer42S0,d2WiderTransfer42Lo,d2WiderTransfer42Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer42C0 then |x-((d2WiderTransfer42S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer42S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer42S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer42S0,d2WiderTransfer42Lo,d2WiderTransfer42Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer42C0,d2Log173Q,d2WiderTransfer42S0,d2WiderTransfer42Lo,d2WiderTransfer42Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer42C0 d2WiderTransfer42S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have har : (((weightedUpper d2WiderTransfer42C0 d2Log173Lo d2Log173Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer42Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer42Arithmetic
  linarith
#print axioms d2WiderTransfer42Arithmetic
#print axioms d2WiderTransfer42Bound
def d2WiderTransfer43Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (16756223) 1 (-24))
def d2WiderTransfer43Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (8380219) 1 (-23))
def d2WiderTransfer43Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (4792410857165054042153) 1 (-78))
def d2WiderTransfer43C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 275 (-4))
def d2WiderTransfer43S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
def d2WiderTransfer43C1 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 55 (-3))
def d2WiderTransfer43S1 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer43Arithmetic : weightedUpper d2WiderTransfer43C0 d2Log173Lo d2Log173Hi + weightedUpper d2WiderTransfer43C1 d2Log1Lo d2Log1Hi ≤ d2WiderTransfer43Cap := by decide +kernel
theorem d2WiderTransfer43Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer43Lo:ℚ):ℝ) ((d2WiderTransfer43Hi:ℚ):ℝ), ((d2WiderTransfer43C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer43S0:ℚ):ℝ)| + ((d2WiderTransfer43C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer43S1:ℚ):ℝ)| ≤ ((d2WiderTransfer43Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer43S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43S0,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer43C0 then |x-((d2WiderTransfer43S0:ℚ):ℝ)| ≤ ((d2Log173Q:ℚ):ℝ) else ((d2Log173Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer43S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer43S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43S0,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43C0,d2Log173Q,d2WiderTransfer43S0,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer43C0 d2WiderTransfer43S0 d2Log173Q d2Log173Lo d2Log173Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log173Bounds
  have hn1 : x-((d2WiderTransfer43S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43S1,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer43C1 then |x-((d2WiderTransfer43S1:ℚ):ℝ)| ≤ ((d2Log1Q:ℚ):ℝ) else ((d2Log1Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer43S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer43S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43S1,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer43C1,d2Log1Q,d2WiderTransfer43S1,d2WiderTransfer43Lo,d2WiderTransfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer43C1 d2WiderTransfer43S1 d2Log1Q d2Log1Lo d2Log1Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log1Bounds
  have har : (((weightedUpper d2WiderTransfer43C0 d2Log173Lo d2Log173Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer43C1 d2Log1Lo d2Log1Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer43Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer43Arithmetic
  linarith
#print axioms d2WiderTransfer43Arithmetic
#print axioms d2WiderTransfer43Bound
def d2WiderTransfer44Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (8380219) 1 (-23))
def d2WiderTransfer44Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (999) 125 (-3))
def d2WiderTransfer44Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (17922128780758888283833) 1 (-80))
def d2WiderTransfer44C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 25 (-4))
def d2WiderTransfer44S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer44Arithmetic : weightedUpper d2WiderTransfer44C0 d2Log174Lo d2Log174Hi ≤ d2WiderTransfer44Cap := by decide +kernel
theorem d2WiderTransfer44Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer44Lo:ℚ):ℝ) ((d2WiderTransfer44Hi:ℚ):ℝ), ((d2WiderTransfer44C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer44S0:ℚ):ℝ)| ≤ ((d2WiderTransfer44Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer44S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer44S0,d2WiderTransfer44Lo,d2WiderTransfer44Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer44C0 then |x-((d2WiderTransfer44S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer44S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer44S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer44S0,d2WiderTransfer44Lo,d2WiderTransfer44Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer44C0,d2Log174Q,d2WiderTransfer44S0,d2WiderTransfer44Lo,d2WiderTransfer44Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer44C0 d2WiderTransfer44S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have har : (((weightedUpper d2WiderTransfer44C0 d2Log174Lo d2Log174Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer44Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer44Arithmetic
  linarith
#print axioms d2WiderTransfer44Arithmetic
#print axioms d2WiderTransfer44Bound
def d2WiderTransfer45Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (8380219) 1 (-23))
def d2WiderTransfer45Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (999) 125 (-3))
def d2WiderTransfer45Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (19169771825614475034297) 1 (-80))
def d2WiderTransfer45C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 275 (-4))
def d2WiderTransfer45S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
def d2WiderTransfer45C1 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 55 (-3))
def d2WiderTransfer45S1 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer45Arithmetic : weightedUpper d2WiderTransfer45C0 d2Log174Lo d2Log174Hi + weightedUpper d2WiderTransfer45C1 d2Log0Lo d2Log0Hi ≤ d2WiderTransfer45Cap := by decide +kernel
theorem d2WiderTransfer45Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer45Lo:ℚ):ℝ) ((d2WiderTransfer45Hi:ℚ):ℝ), ((d2WiderTransfer45C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer45S0:ℚ):ℝ)| + ((d2WiderTransfer45C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer45S1:ℚ):ℝ)| ≤ ((d2WiderTransfer45Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer45S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45S0,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer45C0 then |x-((d2WiderTransfer45S0:ℚ):ℝ)| ≤ ((d2Log174Q:ℚ):ℝ) else ((d2Log174Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer45S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer45S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45S0,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45C0,d2Log174Q,d2WiderTransfer45S0,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer45C0 d2WiderTransfer45S0 d2Log174Q d2Log174Lo d2Log174Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log174Bounds
  have hn1 : x-((d2WiderTransfer45S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45S1,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer45C1 then |x-((d2WiderTransfer45S1:ℚ):ℝ)| ≤ ((d2Log0Q:ℚ):ℝ) else ((d2Log0Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer45S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer45S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45S1,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer45C1,d2Log0Q,d2WiderTransfer45S1,d2WiderTransfer45Lo,d2WiderTransfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer45C1 d2WiderTransfer45S1 d2Log0Q d2Log0Lo d2Log0Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log0Bounds
  have har : (((weightedUpper d2WiderTransfer45C0 d2Log174Lo d2Log174Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer45C1 d2Log0Lo d2Log0Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer45Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer45Arithmetic
  linarith
#print axioms d2WiderTransfer45Arithmetic
#print axioms d2WiderTransfer45Bound
def d2WiderTransfer46Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (98749) 15625 (-6))
def d2WiderTransfer46Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (828367) 1 (-23))
def d2WiderTransfer46Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (649441385) 1 (-39))
def d2WiderTransfer46C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 25 (-4))
def d2WiderTransfer46S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer46Arithmetic : weightedUpper d2WiderTransfer46C0 d2Log88Lo d2Log88Hi ≤ d2WiderTransfer46Cap := by decide +kernel
theorem d2WiderTransfer46Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer46Lo:ℚ):ℝ) ((d2WiderTransfer46Hi:ℚ):ℝ), ((d2WiderTransfer46C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer46S0:ℚ):ℝ)| ≤ ((d2WiderTransfer46Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer46S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer46S0,d2WiderTransfer46Lo,d2WiderTransfer46Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer46C0 then |x-((d2WiderTransfer46S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer46S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer46S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer46S0,d2WiderTransfer46Lo,d2WiderTransfer46Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer46C0,d2Log88Q,d2WiderTransfer46S0,d2WiderTransfer46Lo,d2WiderTransfer46Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer46C0 d2WiderTransfer46S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2WiderTransfer46C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer46Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer46Arithmetic
  linarith
#print axioms d2WiderTransfer46Arithmetic
#print axioms d2WiderTransfer46Bound
def d2WiderTransfer47Lo : ℚ := (d2LitsNearWiderTransfers005.q2 (98749) 15625 (-6))
def d2WiderTransfer47Hi : ℚ := (d2LitsNearWiderTransfers005.q2 (828367) 1 (-23))
def d2WiderTransfer47Cap : ℚ := (d2LitsNearWiderTransfers005.q2 (2436024149) 1 (-40))
def d2WiderTransfer47C0 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 275 (-4))
def d2WiderTransfer47S0 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 1 (0))
def d2WiderTransfer47C1 : ℚ := (d2LitsNearWiderTransfers005.q2 (-1) 55 (-3))
def d2WiderTransfer47S1 : ℚ := (d2LitsNearWiderTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer47Arithmetic : weightedUpper d2WiderTransfer47C0 d2Log88Lo d2Log88Hi + weightedUpper d2WiderTransfer47C1 d2Log86Lo d2Log86Hi ≤ d2WiderTransfer47Cap := by decide +kernel
theorem d2WiderTransfer47Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer47Lo:ℚ):ℝ) ((d2WiderTransfer47Hi:ℚ):ℝ), ((d2WiderTransfer47C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer47S0:ℚ):ℝ)| + ((d2WiderTransfer47C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer47S1:ℚ):ℝ)| ≤ ((d2WiderTransfer47Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer47S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47S0,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer47C0 then |x-((d2WiderTransfer47S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer47S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer47S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47S0,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47C0,d2Log88Q,d2WiderTransfer47S0,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer47C0 d2WiderTransfer47S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2WiderTransfer47S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47S1,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer47C1 then |x-((d2WiderTransfer47S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer47S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer47S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47S1,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers005.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache005.q2, d2LitsNearLogCache010.q2, d2WiderTransfer47C1,d2Log86Q,d2WiderTransfer47S1,d2WiderTransfer47Lo,d2WiderTransfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer47C1 d2WiderTransfer47S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2WiderTransfer47C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer47C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer47Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer47Arithmetic
  linarith
#print axioms d2WiderTransfer47Arithmetic
#print axioms d2WiderTransfer47Bound
end CatalanMeasure.GenD.Signed.Data.Cells

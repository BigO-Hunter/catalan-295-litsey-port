module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache003
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache007
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers005
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers005
open D72.LogTransfer
def d2Transfer40Lo : ℚ := (d2LitsNearTransfers005.q2 (18370983) 1 (-26))
def d2Transfer40Hi : ℚ := (d2LitsNearTransfers005.q2 (313261) 1 (-20))
def d2Transfer40Cap : ℚ := (d2LitsNearTransfers005.q2 (648894057) 1 (-39))
def d2Transfer40C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 25 (-4))
def d2Transfer40S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer40Arithmetic : weightedUpper d2Transfer40C0 d2Log113Lo d2Log113Hi ≤ d2Transfer40Cap := by decide +kernel
theorem d2Transfer40Bound : ∀ x ∈ Set.Icc ((d2Transfer40Lo:ℚ):ℝ) ((d2Transfer40Hi:ℚ):ℝ), ((d2Transfer40C0:ℚ):ℝ)*Real.log |x-((d2Transfer40S0:ℚ):ℝ)| ≤ ((d2Transfer40Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer40S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer40S0,d2Transfer40Lo,d2Transfer40Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer40C0 then |x-((d2Transfer40S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer40S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer40S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer40S0,d2Transfer40Lo,d2Transfer40Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer40C0,d2Log113Q,d2Transfer40S0,d2Transfer40Lo,d2Transfer40Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer40C0 d2Transfer40S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have har : (((weightedUpper d2Transfer40C0 d2Log113Lo d2Log113Hi:ℚ):ℝ)) ≤ ((d2Transfer40Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer40Arithmetic
  linarith
#print axioms d2Transfer40Arithmetic
#print axioms d2Transfer40Bound
def d2Transfer41Lo : ℚ := (d2LitsNearTransfers005.q2 (18370983) 1 (-26))
def d2Transfer41Hi : ℚ := (d2LitsNearTransfers005.q2 (313261) 1 (-20))
def d2Transfer41Cap : ℚ := (d2LitsNearTransfers005.q2 (2432512853) 1 (-40))
def d2Transfer41C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 275 (-4))
def d2Transfer41S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
def d2Transfer41C1 : ℚ := (d2LitsNearTransfers005.q2 (-1) 55 (-3))
def d2Transfer41S1 : ℚ := (d2LitsNearTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer41Arithmetic : weightedUpper d2Transfer41C0 d2Log113Lo d2Log113Hi + weightedUpper d2Transfer41C1 d2Log61Lo d2Log61Hi ≤ d2Transfer41Cap := by decide +kernel
theorem d2Transfer41Bound : ∀ x ∈ Set.Icc ((d2Transfer41Lo:ℚ):ℝ) ((d2Transfer41Hi:ℚ):ℝ), ((d2Transfer41C0:ℚ):ℝ)*Real.log |x-((d2Transfer41S0:ℚ):ℝ)| + ((d2Transfer41C1:ℚ):ℝ)*Real.log |x-((d2Transfer41S1:ℚ):ℝ)| ≤ ((d2Transfer41Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer41S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41S0,d2Transfer41Lo,d2Transfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer41C0 then |x-((d2Transfer41S0:ℚ):ℝ)| ≤ ((d2Log113Q:ℚ):ℝ) else ((d2Log113Q:ℚ):ℝ) ≤ |x-((d2Transfer41S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer41S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41S0,d2Transfer41Lo,d2Transfer41Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41C0,d2Log113Q,d2Transfer41S0,d2Transfer41Lo,d2Transfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer41C0 d2Transfer41S0 d2Log113Q d2Log113Lo d2Log113Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log113Bounds
  have hn1 : x-((d2Transfer41S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41S1,d2Transfer41Lo,d2Transfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer41C1 then |x-((d2Transfer41S1:ℚ):ℝ)| ≤ ((d2Log61Q:ℚ):ℝ) else ((d2Log61Q:ℚ):ℝ) ≤ |x-((d2Transfer41S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer41S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41S1,d2Transfer41Lo,d2Transfer41Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer41C1,d2Log61Q,d2Transfer41S1,d2Transfer41Lo,d2Transfer41Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer41C1 d2Transfer41S1 d2Log61Q d2Log61Lo d2Log61Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log61Bounds
  have har : (((weightedUpper d2Transfer41C0 d2Log113Lo d2Log113Hi:ℚ):ℝ) + ((weightedUpper d2Transfer41C1 d2Log61Lo d2Log61Hi:ℚ):ℝ)) ≤ ((d2Transfer41Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer41Arithmetic
  linarith
#print axioms d2Transfer41Arithmetic
#print axioms d2Transfer41Bound
def d2Transfer42Lo : ℚ := (d2LitsNearTransfers005.q2 (313261) 1 (-20))
def d2Transfer42Hi : ℚ := (d2LitsNearTransfers005.q2 (21726425) 1 (-26))
def d2Transfer42Cap : ℚ := (d2LitsNearTransfers005.q2 (648894057) 1 (-39))
def d2Transfer42C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 25 (-4))
def d2Transfer42S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer42Arithmetic : weightedUpper d2Transfer42C0 d2Log114Lo d2Log114Hi ≤ d2Transfer42Cap := by decide +kernel
theorem d2Transfer42Bound : ∀ x ∈ Set.Icc ((d2Transfer42Lo:ℚ):ℝ) ((d2Transfer42Hi:ℚ):ℝ), ((d2Transfer42C0:ℚ):ℝ)*Real.log |x-((d2Transfer42S0:ℚ):ℝ)| ≤ ((d2Transfer42Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer42S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer42S0,d2Transfer42Lo,d2Transfer42Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer42C0 then |x-((d2Transfer42S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer42S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer42S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer42S0,d2Transfer42Lo,d2Transfer42Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer42C0,d2Log114Q,d2Transfer42S0,d2Transfer42Lo,d2Transfer42Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer42C0 d2Transfer42S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have har : (((weightedUpper d2Transfer42C0 d2Log114Lo d2Log114Hi:ℚ):ℝ)) ≤ ((d2Transfer42Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer42Arithmetic
  linarith
#print axioms d2Transfer42Arithmetic
#print axioms d2Transfer42Bound
def d2Transfer43Lo : ℚ := (d2LitsNearTransfers005.q2 (313261) 1 (-20))
def d2Transfer43Hi : ℚ := (d2LitsNearTransfers005.q2 (21726425) 1 (-26))
def d2Transfer43Cap : ℚ := (d2LitsNearTransfers005.q2 (2432512853) 1 (-40))
def d2Transfer43C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 275 (-4))
def d2Transfer43S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
def d2Transfer43C1 : ℚ := (d2LitsNearTransfers005.q2 (-1) 55 (-3))
def d2Transfer43S1 : ℚ := (d2LitsNearTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer43Arithmetic : weightedUpper d2Transfer43C0 d2Log114Lo d2Log114Hi + weightedUpper d2Transfer43C1 d2Log60Lo d2Log60Hi ≤ d2Transfer43Cap := by decide +kernel
theorem d2Transfer43Bound : ∀ x ∈ Set.Icc ((d2Transfer43Lo:ℚ):ℝ) ((d2Transfer43Hi:ℚ):ℝ), ((d2Transfer43C0:ℚ):ℝ)*Real.log |x-((d2Transfer43S0:ℚ):ℝ)| + ((d2Transfer43C1:ℚ):ℝ)*Real.log |x-((d2Transfer43S1:ℚ):ℝ)| ≤ ((d2Transfer43Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer43S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43S0,d2Transfer43Lo,d2Transfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer43C0 then |x-((d2Transfer43S0:ℚ):ℝ)| ≤ ((d2Log114Q:ℚ):ℝ) else ((d2Log114Q:ℚ):ℝ) ≤ |x-((d2Transfer43S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer43S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43S0,d2Transfer43Lo,d2Transfer43Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43C0,d2Log114Q,d2Transfer43S0,d2Transfer43Lo,d2Transfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer43C0 d2Transfer43S0 d2Log114Q d2Log114Lo d2Log114Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log114Bounds
  have hn1 : x-((d2Transfer43S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43S1,d2Transfer43Lo,d2Transfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer43C1 then |x-((d2Transfer43S1:ℚ):ℝ)| ≤ ((d2Log60Q:ℚ):ℝ) else ((d2Log60Q:ℚ):ℝ) ≤ |x-((d2Transfer43S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer43S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43S1,d2Transfer43Lo,d2Transfer43Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer43C1,d2Log60Q,d2Transfer43S1,d2Transfer43Lo,d2Transfer43Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer43C1 d2Transfer43S1 d2Log60Q d2Log60Lo d2Log60Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log60Bounds
  have har : (((weightedUpper d2Transfer43C0 d2Log114Lo d2Log114Hi:ℚ):ℝ) + ((weightedUpper d2Transfer43C1 d2Log60Lo d2Log60Hi:ℚ):ℝ)) ≤ ((d2Transfer43Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer43Arithmetic
  linarith
#print axioms d2Transfer43Arithmetic
#print axioms d2Transfer43Bound
def d2Transfer44Lo : ℚ := (d2LitsNearTransfers005.q2 (21726425) 1 (-26))
def d2Transfer44Hi : ℚ := (d2LitsNearTransfers005.q2 (11702073) 1 (-25))
def d2Transfer44Cap : ℚ := (d2LitsNearTransfers005.q2 (648894057) 1 (-39))
def d2Transfer44C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 25 (-4))
def d2Transfer44S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer44Arithmetic : weightedUpper d2Transfer44C0 d2Log115Lo d2Log115Hi ≤ d2Transfer44Cap := by decide +kernel
theorem d2Transfer44Bound : ∀ x ∈ Set.Icc ((d2Transfer44Lo:ℚ):ℝ) ((d2Transfer44Hi:ℚ):ℝ), ((d2Transfer44C0:ℚ):ℝ)*Real.log |x-((d2Transfer44S0:ℚ):ℝ)| ≤ ((d2Transfer44Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer44S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer44S0,d2Transfer44Lo,d2Transfer44Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer44C0 then |x-((d2Transfer44S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer44S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer44S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer44S0,d2Transfer44Lo,d2Transfer44Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer44C0,d2Log115Q,d2Transfer44S0,d2Transfer44Lo,d2Transfer44Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer44C0 d2Transfer44S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have har : (((weightedUpper d2Transfer44C0 d2Log115Lo d2Log115Hi:ℚ):ℝ)) ≤ ((d2Transfer44Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer44Arithmetic
  linarith
#print axioms d2Transfer44Arithmetic
#print axioms d2Transfer44Bound
def d2Transfer45Lo : ℚ := (d2LitsNearTransfers005.q2 (21726425) 1 (-26))
def d2Transfer45Hi : ℚ := (d2LitsNearTransfers005.q2 (11702073) 1 (-25))
def d2Transfer45Cap : ℚ := (d2LitsNearTransfers005.q2 (2432512853) 1 (-40))
def d2Transfer45C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 275 (-4))
def d2Transfer45S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
def d2Transfer45C1 : ℚ := (d2LitsNearTransfers005.q2 (-1) 55 (-3))
def d2Transfer45S1 : ℚ := (d2LitsNearTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer45Arithmetic : weightedUpper d2Transfer45C0 d2Log115Lo d2Log115Hi + weightedUpper d2Transfer45C1 d2Log59Lo d2Log59Hi ≤ d2Transfer45Cap := by decide +kernel
theorem d2Transfer45Bound : ∀ x ∈ Set.Icc ((d2Transfer45Lo:ℚ):ℝ) ((d2Transfer45Hi:ℚ):ℝ), ((d2Transfer45C0:ℚ):ℝ)*Real.log |x-((d2Transfer45S0:ℚ):ℝ)| + ((d2Transfer45C1:ℚ):ℝ)*Real.log |x-((d2Transfer45S1:ℚ):ℝ)| ≤ ((d2Transfer45Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer45S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45S0,d2Transfer45Lo,d2Transfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer45C0 then |x-((d2Transfer45S0:ℚ):ℝ)| ≤ ((d2Log115Q:ℚ):ℝ) else ((d2Log115Q:ℚ):ℝ) ≤ |x-((d2Transfer45S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer45S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45S0,d2Transfer45Lo,d2Transfer45Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45C0,d2Log115Q,d2Transfer45S0,d2Transfer45Lo,d2Transfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer45C0 d2Transfer45S0 d2Log115Q d2Log115Lo d2Log115Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log115Bounds
  have hn1 : x-((d2Transfer45S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45S1,d2Transfer45Lo,d2Transfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer45C1 then |x-((d2Transfer45S1:ℚ):ℝ)| ≤ ((d2Log59Q:ℚ):ℝ) else ((d2Log59Q:ℚ):ℝ) ≤ |x-((d2Transfer45S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer45S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45S1,d2Transfer45Lo,d2Transfer45Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer45C1,d2Log59Q,d2Transfer45S1,d2Transfer45Lo,d2Transfer45Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer45C1 d2Transfer45S1 d2Log59Q d2Log59Lo d2Log59Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log59Bounds
  have har : (((weightedUpper d2Transfer45C0 d2Log115Lo d2Log115Hi:ℚ):ℝ) + ((weightedUpper d2Transfer45C1 d2Log59Lo d2Log59Hi:ℚ):ℝ)) ≤ ((d2Transfer45Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer45Arithmetic
  linarith
#print axioms d2Transfer45Arithmetic
#print axioms d2Transfer45Bound
def d2Transfer46Lo : ℚ := (d2LitsNearTransfers005.q2 (11702073) 1 (-25))
def d2Transfer46Hi : ℚ := (d2LitsNearTransfers005.q2 (25081867) 1 (-26))
def d2Transfer46Cap : ℚ := (d2LitsNearTransfers005.q2 (648894057) 1 (-39))
def d2Transfer46C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 25 (-4))
def d2Transfer46S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer46Arithmetic : weightedUpper d2Transfer46C0 d2Log116Lo d2Log116Hi ≤ d2Transfer46Cap := by decide +kernel
theorem d2Transfer46Bound : ∀ x ∈ Set.Icc ((d2Transfer46Lo:ℚ):ℝ) ((d2Transfer46Hi:ℚ):ℝ), ((d2Transfer46C0:ℚ):ℝ)*Real.log |x-((d2Transfer46S0:ℚ):ℝ)| ≤ ((d2Transfer46Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer46S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer46S0,d2Transfer46Lo,d2Transfer46Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer46C0 then |x-((d2Transfer46S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer46S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer46S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer46S0,d2Transfer46Lo,d2Transfer46Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer46C0,d2Log116Q,d2Transfer46S0,d2Transfer46Lo,d2Transfer46Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer46C0 d2Transfer46S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have har : (((weightedUpper d2Transfer46C0 d2Log116Lo d2Log116Hi:ℚ):ℝ)) ≤ ((d2Transfer46Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer46Arithmetic
  linarith
#print axioms d2Transfer46Arithmetic
#print axioms d2Transfer46Bound
def d2Transfer47Lo : ℚ := (d2LitsNearTransfers005.q2 (11702073) 1 (-25))
def d2Transfer47Hi : ℚ := (d2LitsNearTransfers005.q2 (25081867) 1 (-26))
def d2Transfer47Cap : ℚ := (d2LitsNearTransfers005.q2 (2432512853) 1 (-40))
def d2Transfer47C0 : ℚ := (d2LitsNearTransfers005.q2 (1) 275 (-4))
def d2Transfer47S0 : ℚ := (d2LitsNearTransfers005.q2 (-1) 1 (0))
def d2Transfer47C1 : ℚ := (d2LitsNearTransfers005.q2 (-1) 55 (-3))
def d2Transfer47S1 : ℚ := (d2LitsNearTransfers005.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer47Arithmetic : weightedUpper d2Transfer47C0 d2Log116Lo d2Log116Hi + weightedUpper d2Transfer47C1 d2Log58Lo d2Log58Hi ≤ d2Transfer47Cap := by decide +kernel
theorem d2Transfer47Bound : ∀ x ∈ Set.Icc ((d2Transfer47Lo:ℚ):ℝ) ((d2Transfer47Hi:ℚ):ℝ), ((d2Transfer47C0:ℚ):ℝ)*Real.log |x-((d2Transfer47S0:ℚ):ℝ)| + ((d2Transfer47C1:ℚ):ℝ)*Real.log |x-((d2Transfer47S1:ℚ):ℝ)| ≤ ((d2Transfer47Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer47S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47S0,d2Transfer47Lo,d2Transfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer47C0 then |x-((d2Transfer47S0:ℚ):ℝ)| ≤ ((d2Log116Q:ℚ):ℝ) else ((d2Log116Q:ℚ):ℝ) ≤ |x-((d2Transfer47S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer47S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47S0,d2Transfer47Lo,d2Transfer47Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47C0,d2Log116Q,d2Transfer47S0,d2Transfer47Lo,d2Transfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer47C0 d2Transfer47S0 d2Log116Q d2Log116Lo d2Log116Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log116Bounds
  have hn1 : x-((d2Transfer47S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47S1,d2Transfer47Lo,d2Transfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer47C1 then |x-((d2Transfer47S1:ℚ):ℝ)| ≤ ((d2Log58Q:ℚ):ℝ) else ((d2Log58Q:ℚ):ℝ) ≤ |x-((d2Transfer47S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer47S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47S1,d2Transfer47Lo,d2Transfer47Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers005.q2, d2LitsNearLogCache003.q2, d2LitsNearLogCache007.q2, d2Transfer47C1,d2Log58Q,d2Transfer47S1,d2Transfer47Lo,d2Transfer47Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer47C1 d2Transfer47S1 d2Log58Q d2Log58Lo d2Log58Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log58Bounds
  have har : (((weightedUpper d2Transfer47C0 d2Log116Lo d2Log116Hi:ℚ):ℝ) + ((weightedUpper d2Transfer47C1 d2Log58Lo d2Log58Hi:ℚ):ℝ)) ≤ ((d2Transfer47Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer47Arithmetic
  linarith
#print axioms d2Transfer47Arithmetic
#print axioms d2Transfer47Bound
end CatalanMeasure.GenD.Signed.Data.Cells

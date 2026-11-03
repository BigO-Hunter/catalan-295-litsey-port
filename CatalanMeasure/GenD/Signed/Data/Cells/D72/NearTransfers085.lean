module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache011
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers085
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers085
open D72.LogTransfer
def d2Transfer680Lo : ℚ := (d2LitsNearTransfers085.q2 (1023) 1 (-10))
def d2Transfer680Hi : ℚ := (d2LitsNearTransfers085.q2 (2047) 1 (-11))
def d2Transfer680Cap : ℚ := (d2LitsNearTransfers085.q2 (24082965488750313183221) 1 (-80))
def d2Transfer680C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer680S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer680Arithmetic : weightedUpper d2Transfer680C0 d2Log177Lo d2Log177Hi ≤ d2Transfer680Cap := by decide +kernel
theorem d2Transfer680Bound : ∀ x ∈ Set.Icc ((d2Transfer680Lo:ℚ):ℝ) ((d2Transfer680Hi:ℚ):ℝ), ((d2Transfer680C0:ℚ):ℝ)*Real.log |x-((d2Transfer680S0:ℚ):ℝ)| ≤ ((d2Transfer680Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer680S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer680S0,d2Transfer680Lo,d2Transfer680Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer680C0 then |x-((d2Transfer680S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer680S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer680S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer680S0,d2Transfer680Lo,d2Transfer680Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer680C0,d2Log177Q,d2Transfer680S0,d2Transfer680Lo,d2Transfer680Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer680C0 d2Transfer680S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer680C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer680Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer680Arithmetic
  linarith
#print axioms d2Transfer680Arithmetic
#print axioms d2Transfer680Bound
def d2Transfer681Lo : ℚ := (d2LitsNearTransfers085.q2 (1023) 1 (-10))
def d2Transfer681Hi : ℚ := (d2LitsNearTransfers085.q2 (2047) 1 (-11))
def d2Transfer681Cap : ℚ := (d2LitsNearTransfers085.q2 (24082964758674592339957) 1 (-80))
def d2Transfer681C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer681S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer681Arithmetic : weightedUpper d2Transfer681C0 d2Log177Lo d2Log177Hi ≤ d2Transfer681Cap := by decide +kernel
theorem d2Transfer681Bound : ∀ x ∈ Set.Icc ((d2Transfer681Lo:ℚ):ℝ) ((d2Transfer681Hi:ℚ):ℝ), ((d2Transfer681C0:ℚ):ℝ)*Real.log |x-((d2Transfer681S0:ℚ):ℝ)| ≤ ((d2Transfer681Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer681S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer681S0,d2Transfer681Lo,d2Transfer681Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer681C0 then |x-((d2Transfer681S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer681S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer681S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer681S0,d2Transfer681Lo,d2Transfer681Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer681C0,d2Log177Q,d2Transfer681S0,d2Transfer681Lo,d2Transfer681Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer681C0 d2Transfer681S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer681C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer681Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer681Arithmetic
  linarith
#print axioms d2Transfer681Arithmetic
#print axioms d2Transfer681Bound
def d2Transfer682Lo : ℚ := (d2LitsNearTransfers085.q2 (2047) 1 (-11))
def d2Transfer682Hi : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer682Cap : ℚ := (d2LitsNearTransfers085.q2 (13140388118353036535) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer682Arithmetic : (0 : ℚ) ≤ d2Transfer682Cap := by decide +kernel
theorem d2Transfer682Bound : ∀ x ∈ Set.Icc ((d2Transfer682Lo:ℚ):ℝ) ((d2Transfer682Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer682Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer682Arithmetic
#print axioms d2Transfer682Arithmetic
#print axioms d2Transfer682Bound
def d2Transfer683Lo : ℚ := (d2LitsNearTransfers085.q2 (2047) 1 (-11))
def d2Transfer683Hi : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer683Cap : ℚ := (d2LitsNearTransfers085.q2 (24087209016905748858103) 1 (-80))
def d2Transfer683C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer683S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer683Arithmetic : weightedUpper d2Transfer683C0 d2Log178Lo d2Log178Hi ≤ d2Transfer683Cap := by decide +kernel
theorem d2Transfer683Bound : ∀ x ∈ Set.Icc ((d2Transfer683Lo:ℚ):ℝ) ((d2Transfer683Hi:ℚ):ℝ), ((d2Transfer683C0:ℚ):ℝ)*Real.log |x-((d2Transfer683S0:ℚ):ℝ)| ≤ ((d2Transfer683Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer683S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer683S0,d2Transfer683Lo,d2Transfer683Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer683C0 then |x-((d2Transfer683S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer683S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer683S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer683S0,d2Transfer683Lo,d2Transfer683Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer683C0,d2Log178Q,d2Transfer683S0,d2Transfer683Lo,d2Transfer683Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer683C0 d2Transfer683S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer683C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer683Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer683Arithmetic
  linarith
#print axioms d2Transfer683Arithmetic
#print axioms d2Transfer683Bound
def d2Transfer684Lo : ℚ := (d2LitsNearTransfers085.q2 (2047) 1 (-11))
def d2Transfer684Hi : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer684Cap : ℚ := (d2LitsNearTransfers085.q2 (24087208286830028014839) 1 (-80))
def d2Transfer684C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer684S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer684Arithmetic : weightedUpper d2Transfer684C0 d2Log178Lo d2Log178Hi ≤ d2Transfer684Cap := by decide +kernel
theorem d2Transfer684Bound : ∀ x ∈ Set.Icc ((d2Transfer684Lo:ℚ):ℝ) ((d2Transfer684Hi:ℚ):ℝ), ((d2Transfer684C0:ℚ):ℝ)*Real.log |x-((d2Transfer684S0:ℚ):ℝ)| ≤ ((d2Transfer684Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer684S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer684S0,d2Transfer684Lo,d2Transfer684Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer684C0 then |x-((d2Transfer684S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer684S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer684S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer684S0,d2Transfer684Lo,d2Transfer684Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer684C0,d2Log178Q,d2Transfer684S0,d2Transfer684Lo,d2Transfer684Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer684C0 d2Transfer684S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer684C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer684Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer684Arithmetic
  linarith
#print axioms d2Transfer684Arithmetic
#print axioms d2Transfer684Bound
def d2Transfer685Lo : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer685Hi : ℚ := (d2LitsNearTransfers085.q2 (8191) 1 (-13))
def d2Transfer685Cap : ℚ := (d2LitsNearTransfers085.q2 (15261957923005100557) 1 (-80))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer685Arithmetic : (0 : ℚ) ≤ d2Transfer685Cap := by decide +kernel
theorem d2Transfer685Bound : ∀ x ∈ Set.Icc ((d2Transfer685Lo:ℚ):ℝ) ((d2Transfer685Hi:ℚ):ℝ), (0 : ℝ) ≤ ((d2Transfer685Cap:ℚ):ℝ) := by
  intro x hx
  exact_mod_cast d2Transfer685Arithmetic
#print axioms d2Transfer685Arithmetic
#print axioms d2Transfer685Bound
def d2Transfer686Lo : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer686Hi : ℚ := (d2LitsNearTransfers085.q2 (8191) 1 (-13))
def d2Transfer686Cap : ℚ := (d2LitsNearTransfers085.q2 (24089330586710400922125) 1 (-80))
def d2Transfer686C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer686S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer686Arithmetic : weightedUpper d2Transfer686C0 d2Log179Lo d2Log179Hi ≤ d2Transfer686Cap := by decide +kernel
theorem d2Transfer686Bound : ∀ x ∈ Set.Icc ((d2Transfer686Lo:ℚ):ℝ) ((d2Transfer686Hi:ℚ):ℝ), ((d2Transfer686C0:ℚ):ℝ)*Real.log |x-((d2Transfer686S0:ℚ):ℝ)| ≤ ((d2Transfer686Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer686S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer686S0,d2Transfer686Lo,d2Transfer686Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer686C0 then |x-((d2Transfer686S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer686S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer686S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer686S0,d2Transfer686Lo,d2Transfer686Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer686C0,d2Log179Q,d2Transfer686S0,d2Transfer686Lo,d2Transfer686Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer686C0 d2Transfer686S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer686C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer686Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer686Arithmetic
  linarith
#print axioms d2Transfer686Arithmetic
#print axioms d2Transfer686Bound
def d2Transfer687Lo : ℚ := (d2LitsNearTransfers085.q2 (4095) 1 (-12))
def d2Transfer687Hi : ℚ := (d2LitsNearTransfers085.q2 (8191) 1 (-13))
def d2Transfer687Cap : ℚ := (d2LitsNearTransfers085.q2 (24089329856634680078861) 1 (-80))
def d2Transfer687C0 : ℚ := (d2LitsNearTransfers085.q2 (23) 25 (-5))
def d2Transfer687S0 : ℚ := (d2LitsNearTransfers085.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer687Arithmetic : weightedUpper d2Transfer687C0 d2Log179Lo d2Log179Hi ≤ d2Transfer687Cap := by decide +kernel
theorem d2Transfer687Bound : ∀ x ∈ Set.Icc ((d2Transfer687Lo:ℚ):ℝ) ((d2Transfer687Hi:ℚ):ℝ), ((d2Transfer687C0:ℚ):ℝ)*Real.log |x-((d2Transfer687S0:ℚ):ℝ)| ≤ ((d2Transfer687Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer687S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer687S0,d2Transfer687Lo,d2Transfer687Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer687C0 then |x-((d2Transfer687S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer687S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer687S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer687S0,d2Transfer687Lo,d2Transfer687Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers085.q2, d2LitsNearLogCache011.q2, d2Transfer687C0,d2Log179Q,d2Transfer687S0,d2Transfer687Lo,d2Transfer687Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer687C0 d2Transfer687S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer687C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer687Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer687Arithmetic
  linarith
#print axioms d2Transfer687Arithmetic
#print axioms d2Transfer687Bound
end CatalanMeasure.GenD.Signed.Data.Cells

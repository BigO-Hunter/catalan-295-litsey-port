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
namespace d2LitsNearTransfers081
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers081
open D72.LogTransfer
def d2Transfer648Lo : ℚ := (d2LitsNearTransfers081.q2 (1023) 1 (-10))
def d2Transfer648Hi : ℚ := (d2LitsNearTransfers081.q2 (2047) 1 (-11))
def d2Transfer648Cap : ℚ := (d2LitsNearTransfers081.q2 (13088568001539588836613) 1 (-79))
def d2Transfer648C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 1 (-5))
def d2Transfer648S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer648Arithmetic : weightedUpper d2Transfer648C0 d2Log177Lo d2Log177Hi ≤ d2Transfer648Cap := by decide +kernel
theorem d2Transfer648Bound : ∀ x ∈ Set.Icc ((d2Transfer648Lo:ℚ):ℝ) ((d2Transfer648Hi:ℚ):ℝ), ((d2Transfer648C0:ℚ):ℝ)*Real.log |x-((d2Transfer648S0:ℚ):ℝ)| ≤ ((d2Transfer648Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer648S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer648S0,d2Transfer648Lo,d2Transfer648Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer648C0 then |x-((d2Transfer648S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer648S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer648S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer648S0,d2Transfer648Lo,d2Transfer648Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer648C0,d2Log177Q,d2Transfer648S0,d2Transfer648Lo,d2Transfer648Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer648C0 d2Transfer648S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer648C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer648Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer648Arithmetic
  linarith
#print axioms d2Transfer648Arithmetic
#print axioms d2Transfer648Bound
def d2Transfer649Lo : ℚ := (d2LitsNearTransfers081.q2 (2047) 1 (-11))
def d2Transfer649Hi : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer649Cap : ℚ := (d2LitsNearTransfers081.q2 (2107679927985260464173) 1 (-80))
def d2Transfer649C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 25 (-4))
def d2Transfer649S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer649Arithmetic : weightedUpper d2Transfer649C0 d2Log178Lo d2Log178Hi ≤ d2Transfer649Cap := by decide +kernel
theorem d2Transfer649Bound : ∀ x ∈ Set.Icc ((d2Transfer649Lo:ℚ):ℝ) ((d2Transfer649Hi:ℚ):ℝ), ((d2Transfer649C0:ℚ):ℝ)*Real.log |x-((d2Transfer649S0:ℚ):ℝ)| ≤ ((d2Transfer649Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer649S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer649S0,d2Transfer649Lo,d2Transfer649Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer649C0 then |x-((d2Transfer649S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer649S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer649S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer649S0,d2Transfer649Lo,d2Transfer649Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer649C0,d2Log178Q,d2Transfer649S0,d2Transfer649Lo,d2Transfer649Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer649C0 d2Transfer649S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer649C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer649Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer649Arithmetic
  linarith
#print axioms d2Transfer649Arithmetic
#print axioms d2Transfer649Bound
def d2Transfer650Lo : ℚ := (d2LitsNearTransfers081.q2 (2047) 1 (-11))
def d2Transfer650Hi : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer650Cap : ℚ := (d2LitsNearTransfers081.q2 (2107679509071330281517) 1 (-80))
def d2Transfer650C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 25 (-4))
def d2Transfer650S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer650Arithmetic : weightedUpper d2Transfer650C0 d2Log178Lo d2Log178Hi ≤ d2Transfer650Cap := by decide +kernel
theorem d2Transfer650Bound : ∀ x ∈ Set.Icc ((d2Transfer650Lo:ℚ):ℝ) ((d2Transfer650Hi:ℚ):ℝ), ((d2Transfer650C0:ℚ):ℝ)*Real.log |x-((d2Transfer650S0:ℚ):ℝ)| ≤ ((d2Transfer650Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer650S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer650S0,d2Transfer650Lo,d2Transfer650Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer650C0 then |x-((d2Transfer650S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer650S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer650S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer650S0,d2Transfer650Lo,d2Transfer650Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer650C0,d2Log178Q,d2Transfer650S0,d2Transfer650Lo,d2Transfer650Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer650C0 d2Transfer650S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer650C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer650Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer650Arithmetic
  linarith
#print axioms d2Transfer650Arithmetic
#print axioms d2Transfer650Bound
def d2Transfer651Lo : ℚ := (d2LitsNearTransfers081.q2 (2047) 1 (-11))
def d2Transfer651Hi : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer651Cap : ℚ := (d2LitsNearTransfers081.q2 (26181748137858726103085) 1 (-80))
def d2Transfer651C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 1 (-5))
def d2Transfer651S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer651Arithmetic : weightedUpper d2Transfer651C0 d2Log178Lo d2Log178Hi ≤ d2Transfer651Cap := by decide +kernel
theorem d2Transfer651Bound : ∀ x ∈ Set.Icc ((d2Transfer651Lo:ℚ):ℝ) ((d2Transfer651Hi:ℚ):ℝ), ((d2Transfer651C0:ℚ):ℝ)*Real.log |x-((d2Transfer651S0:ℚ):ℝ)| ≤ ((d2Transfer651Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer651S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer651S0,d2Transfer651Lo,d2Transfer651Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer651C0 then |x-((d2Transfer651S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer651S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer651S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer651S0,d2Transfer651Lo,d2Transfer651Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer651C0,d2Log178Q,d2Transfer651S0,d2Transfer651Lo,d2Transfer651Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer651C0 d2Transfer651S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer651C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer651Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer651Arithmetic
  linarith
#print axioms d2Transfer651Arithmetic
#print axioms d2Transfer651Bound
def d2Transfer652Lo : ℚ := (d2LitsNearTransfers081.q2 (2047) 1 (-11))
def d2Transfer652Hi : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer652Cap : ℚ := (d2LitsNearTransfers081.q2 (26181748533682912102445) 1 (-80))
def d2Transfer652C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 1 (-5))
def d2Transfer652S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer652Arithmetic : weightedUpper d2Transfer652C0 d2Log178Lo d2Log178Hi ≤ d2Transfer652Cap := by decide +kernel
theorem d2Transfer652Bound : ∀ x ∈ Set.Icc ((d2Transfer652Lo:ℚ):ℝ) ((d2Transfer652Hi:ℚ):ℝ), ((d2Transfer652C0:ℚ):ℝ)*Real.log |x-((d2Transfer652S0:ℚ):ℝ)| ≤ ((d2Transfer652Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer652S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer652S0,d2Transfer652Lo,d2Transfer652Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer652C0 then |x-((d2Transfer652S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer652S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer652S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer652S0,d2Transfer652Lo,d2Transfer652Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer652C0,d2Log178Q,d2Transfer652S0,d2Transfer652Lo,d2Transfer652Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer652C0 d2Transfer652S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer652C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer652Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer652Arithmetic
  linarith
#print axioms d2Transfer652Arithmetic
#print axioms d2Transfer652Bound
def d2Transfer653Lo : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer653Hi : ℚ := (d2LitsNearTransfers081.q2 (8191) 1 (-13))
def d2Transfer653Cap : ℚ := (d2LitsNearTransfers081.q2 (2109985982120751838111) 1 (-80))
def d2Transfer653C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 25 (-4))
def d2Transfer653S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer653Arithmetic : weightedUpper d2Transfer653C0 d2Log179Lo d2Log179Hi ≤ d2Transfer653Cap := by decide +kernel
theorem d2Transfer653Bound : ∀ x ∈ Set.Icc ((d2Transfer653Lo:ℚ):ℝ) ((d2Transfer653Hi:ℚ):ℝ), ((d2Transfer653C0:ℚ):ℝ)*Real.log |x-((d2Transfer653S0:ℚ):ℝ)| ≤ ((d2Transfer653Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer653S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer653S0,d2Transfer653Lo,d2Transfer653Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer653C0 then |x-((d2Transfer653S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer653S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer653S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer653S0,d2Transfer653Lo,d2Transfer653Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer653C0,d2Log179Q,d2Transfer653S0,d2Transfer653Lo,d2Transfer653Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer653C0 d2Transfer653S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer653C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer653Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer653Arithmetic
  linarith
#print axioms d2Transfer653Arithmetic
#print axioms d2Transfer653Bound
def d2Transfer654Lo : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer654Hi : ℚ := (d2LitsNearTransfers081.q2 (8191) 1 (-13))
def d2Transfer654Cap : ℚ := (d2LitsNearTransfers081.q2 (2109985563206821655455) 1 (-80))
def d2Transfer654C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 25 (-4))
def d2Transfer654S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer654Arithmetic : weightedUpper d2Transfer654C0 d2Log179Lo d2Log179Hi ≤ d2Transfer654Cap := by decide +kernel
theorem d2Transfer654Bound : ∀ x ∈ Set.Icc ((d2Transfer654Lo:ℚ):ℝ) ((d2Transfer654Hi:ℚ):ℝ), ((d2Transfer654C0:ℚ):ℝ)*Real.log |x-((d2Transfer654S0:ℚ):ℝ)| ≤ ((d2Transfer654Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer654S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer654S0,d2Transfer654Lo,d2Transfer654Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer654C0 then |x-((d2Transfer654S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer654S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer654S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer654S0,d2Transfer654Lo,d2Transfer654Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer654C0,d2Log179Q,d2Transfer654S0,d2Transfer654Lo,d2Transfer654Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer654C0 d2Transfer654S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer654C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer654Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer654Arithmetic
  linarith
#print axioms d2Transfer654Arithmetic
#print axioms d2Transfer654Bound
def d2Transfer655Lo : ℚ := (d2LitsNearTransfers081.q2 (4095) 1 (-12))
def d2Transfer655Hi : ℚ := (d2LitsNearTransfers081.q2 (8191) 1 (-13))
def d2Transfer655Cap : ℚ := (d2LitsNearTransfers081.q2 (26184054191994217477023) 1 (-80))
def d2Transfer655C0 : ℚ := (d2LitsNearTransfers081.q2 (1) 1 (-5))
def d2Transfer655S0 : ℚ := (d2LitsNearTransfers081.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer655Arithmetic : weightedUpper d2Transfer655C0 d2Log179Lo d2Log179Hi ≤ d2Transfer655Cap := by decide +kernel
theorem d2Transfer655Bound : ∀ x ∈ Set.Icc ((d2Transfer655Lo:ℚ):ℝ) ((d2Transfer655Hi:ℚ):ℝ), ((d2Transfer655C0:ℚ):ℝ)*Real.log |x-((d2Transfer655S0:ℚ):ℝ)| ≤ ((d2Transfer655Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer655S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer655S0,d2Transfer655Lo,d2Transfer655Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer655C0 then |x-((d2Transfer655S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer655S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer655S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer655S0,d2Transfer655Lo,d2Transfer655Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers081.q2, d2LitsNearLogCache011.q2, d2Transfer655C0,d2Log179Q,d2Transfer655S0,d2Transfer655Lo,d2Transfer655Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer655C0 d2Transfer655S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer655C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer655Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer655Arithmetic
  linarith
#print axioms d2Transfer655Arithmetic
#print axioms d2Transfer655Bound
end CatalanMeasure.GenD.Signed.Data.Cells

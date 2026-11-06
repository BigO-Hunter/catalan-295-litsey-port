module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
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
namespace d2LitsNearWiderTransfers055
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers055
open D72.LogTransfer
def d2WiderTransfer440Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (2047) 1 (-11))
def d2WiderTransfer440Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer440Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (2107679509071330281517) 1 (-80))
def d2WiderTransfer440C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 25 (-4))
def d2WiderTransfer440S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer440Arithmetic : weightedUpper d2WiderTransfer440C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer440Cap := by decide +kernel
theorem d2WiderTransfer440Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer440Lo:ℚ):ℝ) ((d2WiderTransfer440Hi:ℚ):ℝ), ((d2WiderTransfer440C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer440S0:ℚ):ℝ)| ≤ ((d2WiderTransfer440Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer440S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer440S0,d2WiderTransfer440Lo,d2WiderTransfer440Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer440C0 then |x-((d2WiderTransfer440S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer440S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer440S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer440S0,d2WiderTransfer440Lo,d2WiderTransfer440Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer440C0,d2Log178Q,d2WiderTransfer440S0,d2WiderTransfer440Lo,d2WiderTransfer440Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer440C0 d2WiderTransfer440S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer440C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer440Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer440Arithmetic
  linarith
#print axioms d2WiderTransfer440Arithmetic
#print axioms d2WiderTransfer440Bound
def d2WiderTransfer441Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (2047) 1 (-11))
def d2WiderTransfer441Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer441Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (26181748137858726103085) 1 (-80))
def d2WiderTransfer441C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 1 (-5))
def d2WiderTransfer441S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer441Arithmetic : weightedUpper d2WiderTransfer441C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer441Cap := by decide +kernel
theorem d2WiderTransfer441Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer441Lo:ℚ):ℝ) ((d2WiderTransfer441Hi:ℚ):ℝ), ((d2WiderTransfer441C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer441S0:ℚ):ℝ)| ≤ ((d2WiderTransfer441Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer441S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer441S0,d2WiderTransfer441Lo,d2WiderTransfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer441C0 then |x-((d2WiderTransfer441S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer441S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer441S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer441S0,d2WiderTransfer441Lo,d2WiderTransfer441Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer441C0,d2Log178Q,d2WiderTransfer441S0,d2WiderTransfer441Lo,d2WiderTransfer441Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer441C0 d2WiderTransfer441S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer441C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer441Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer441Arithmetic
  linarith
#print axioms d2WiderTransfer441Arithmetic
#print axioms d2WiderTransfer441Bound
def d2WiderTransfer442Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (2047) 1 (-11))
def d2WiderTransfer442Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer442Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (26181748533682912102445) 1 (-80))
def d2WiderTransfer442C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 1 (-5))
def d2WiderTransfer442S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer442Arithmetic : weightedUpper d2WiderTransfer442C0 d2Log178Lo d2Log178Hi ≤ d2WiderTransfer442Cap := by decide +kernel
theorem d2WiderTransfer442Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer442Lo:ℚ):ℝ) ((d2WiderTransfer442Hi:ℚ):ℝ), ((d2WiderTransfer442C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer442S0:ℚ):ℝ)| ≤ ((d2WiderTransfer442Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer442S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer442S0,d2WiderTransfer442Lo,d2WiderTransfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer442C0 then |x-((d2WiderTransfer442S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer442S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer442S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer442S0,d2WiderTransfer442Lo,d2WiderTransfer442Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer442C0,d2Log178Q,d2WiderTransfer442S0,d2WiderTransfer442Lo,d2WiderTransfer442Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer442C0 d2WiderTransfer442S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2WiderTransfer442C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer442Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer442Arithmetic
  linarith
#print axioms d2WiderTransfer442Arithmetic
#print axioms d2WiderTransfer442Bound
def d2WiderTransfer443Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer443Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (8191) 1 (-13))
def d2WiderTransfer443Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (2109985982120751838111) 1 (-80))
def d2WiderTransfer443C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 25 (-4))
def d2WiderTransfer443S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer443Arithmetic : weightedUpper d2WiderTransfer443C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer443Cap := by decide +kernel
theorem d2WiderTransfer443Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer443Lo:ℚ):ℝ) ((d2WiderTransfer443Hi:ℚ):ℝ), ((d2WiderTransfer443C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer443S0:ℚ):ℝ)| ≤ ((d2WiderTransfer443Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer443S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer443S0,d2WiderTransfer443Lo,d2WiderTransfer443Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer443C0 then |x-((d2WiderTransfer443S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer443S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer443S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer443S0,d2WiderTransfer443Lo,d2WiderTransfer443Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer443C0,d2Log179Q,d2WiderTransfer443S0,d2WiderTransfer443Lo,d2WiderTransfer443Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer443C0 d2WiderTransfer443S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer443C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer443Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer443Arithmetic
  linarith
#print axioms d2WiderTransfer443Arithmetic
#print axioms d2WiderTransfer443Bound
def d2WiderTransfer444Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer444Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (8191) 1 (-13))
def d2WiderTransfer444Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (2109985563206821655455) 1 (-80))
def d2WiderTransfer444C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 25 (-4))
def d2WiderTransfer444S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer444Arithmetic : weightedUpper d2WiderTransfer444C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer444Cap := by decide +kernel
theorem d2WiderTransfer444Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer444Lo:ℚ):ℝ) ((d2WiderTransfer444Hi:ℚ):ℝ), ((d2WiderTransfer444C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer444S0:ℚ):ℝ)| ≤ ((d2WiderTransfer444Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer444S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer444S0,d2WiderTransfer444Lo,d2WiderTransfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer444C0 then |x-((d2WiderTransfer444S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer444S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer444S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer444S0,d2WiderTransfer444Lo,d2WiderTransfer444Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer444C0,d2Log179Q,d2WiderTransfer444S0,d2WiderTransfer444Lo,d2WiderTransfer444Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer444C0 d2WiderTransfer444S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer444C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer444Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer444Arithmetic
  linarith
#print axioms d2WiderTransfer444Arithmetic
#print axioms d2WiderTransfer444Bound
def d2WiderTransfer445Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer445Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (8191) 1 (-13))
def d2WiderTransfer445Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (26184054191994217477023) 1 (-80))
def d2WiderTransfer445C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 1 (-5))
def d2WiderTransfer445S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer445Arithmetic : weightedUpper d2WiderTransfer445C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer445Cap := by decide +kernel
theorem d2WiderTransfer445Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer445Lo:ℚ):ℝ) ((d2WiderTransfer445Hi:ℚ):ℝ), ((d2WiderTransfer445C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer445S0:ℚ):ℝ)| ≤ ((d2WiderTransfer445Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer445S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer445S0,d2WiderTransfer445Lo,d2WiderTransfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer445C0 then |x-((d2WiderTransfer445S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer445S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer445S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer445S0,d2WiderTransfer445Lo,d2WiderTransfer445Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer445C0,d2Log179Q,d2WiderTransfer445S0,d2WiderTransfer445Lo,d2WiderTransfer445Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer445C0 d2WiderTransfer445S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer445C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer445Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer445Arithmetic
  linarith
#print axioms d2WiderTransfer445Arithmetic
#print axioms d2WiderTransfer445Bound
def d2WiderTransfer446Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (4095) 1 (-12))
def d2WiderTransfer446Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (8191) 1 (-13))
def d2WiderTransfer446Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (26184054587818403476383) 1 (-80))
def d2WiderTransfer446C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 1 (-5))
def d2WiderTransfer446S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer446Arithmetic : weightedUpper d2WiderTransfer446C0 d2Log179Lo d2Log179Hi ≤ d2WiderTransfer446Cap := by decide +kernel
theorem d2WiderTransfer446Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer446Lo:ℚ):ℝ) ((d2WiderTransfer446Hi:ℚ):ℝ), ((d2WiderTransfer446C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer446S0:ℚ):ℝ)| ≤ ((d2WiderTransfer446Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer446S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer446S0,d2WiderTransfer446Lo,d2WiderTransfer446Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer446C0 then |x-((d2WiderTransfer446S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer446S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer446S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer446S0,d2WiderTransfer446Lo,d2WiderTransfer446Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer446C0,d2Log179Q,d2WiderTransfer446S0,d2WiderTransfer446Lo,d2WiderTransfer446Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer446C0 d2WiderTransfer446S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2WiderTransfer446C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer446Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer446Arithmetic
  linarith
#print axioms d2WiderTransfer446Arithmetic
#print axioms d2WiderTransfer446Bound
def d2WiderTransfer447Lo : ℚ := (d2LitsNearWiderTransfers055.q2 (8191) 1 (-13))
def d2WiderTransfer447Hi : ℚ := (d2LitsNearWiderTransfers055.q2 (16383) 1 (-14))
def d2WiderTransfer447Cap : ℚ := (d2LitsNearWiderTransfers055.q2 (1055569478202211169405) 1 (-79))
def d2WiderTransfer447C0 : ℚ := (d2LitsNearWiderTransfers055.q2 (1) 25 (-4))
def d2WiderTransfer447S0 : ℚ := (d2LitsNearWiderTransfers055.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer447Arithmetic : weightedUpper d2WiderTransfer447C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer447Cap := by decide +kernel
theorem d2WiderTransfer447Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer447Lo:ℚ):ℝ) ((d2WiderTransfer447Hi:ℚ):ℝ), ((d2WiderTransfer447C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer447S0:ℚ):ℝ)| ≤ ((d2WiderTransfer447Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer447S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer447S0,d2WiderTransfer447Lo,d2WiderTransfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer447C0 then |x-((d2WiderTransfer447S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer447S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer447S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer447S0,d2WiderTransfer447Lo,d2WiderTransfer447Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers055.q2, d2LitsNearLogCache011.q2, d2WiderTransfer447C0,d2Log180Q,d2WiderTransfer447S0,d2WiderTransfer447Lo,d2WiderTransfer447Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer447C0 d2WiderTransfer447S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer447C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer447Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer447Arithmetic
  linarith
#print axioms d2WiderTransfer447Arithmetic
#print axioms d2WiderTransfer447Bound
end CatalanMeasure.GenD.Signed.Data.Cells

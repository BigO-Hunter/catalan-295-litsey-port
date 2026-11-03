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
namespace d2LitsNearTransfers077
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers077
open D72.LogTransfer
def d2Transfer616Lo : ℚ := (d2LitsNearTransfers077.q2 (16760439) 1 (-24))
def d2Transfer616Hi : ℚ := (d2LitsNearTransfers077.q2 (1023) 1 (-10))
def d2Transfer616Cap : ℚ := (d2LitsNearTransfers077.q2 (1046716354249405971389) 1 (-79))
def d2Transfer616C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer616S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer616Arithmetic : weightedUpper d2Transfer616C0 d2Log176Lo d2Log176Hi ≤ d2Transfer616Cap := by decide +kernel
theorem d2Transfer616Bound : ∀ x ∈ Set.Icc ((d2Transfer616Lo:ℚ):ℝ) ((d2Transfer616Hi:ℚ):ℝ), ((d2Transfer616C0:ℚ):ℝ)*Real.log |x-((d2Transfer616S0:ℚ):ℝ)| ≤ ((d2Transfer616Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer616S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer616S0,d2Transfer616Lo,d2Transfer616Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer616C0 then |x-((d2Transfer616S0:ℚ):ℝ)| ≤ ((d2Log176Q:ℚ):ℝ) else ((d2Log176Q:ℚ):ℝ) ≤ |x-((d2Transfer616S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer616S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer616S0,d2Transfer616Lo,d2Transfer616Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer616C0,d2Log176Q,d2Transfer616S0,d2Transfer616Lo,d2Transfer616Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer616C0 d2Transfer616S0 d2Log176Q d2Log176Lo d2Log176Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log176Bounds
  have har : (((weightedUpper d2Transfer616C0 d2Log176Lo d2Log176Hi:ℚ):ℝ)) ≤ ((d2Transfer616Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer616Arithmetic
  linarith
#print axioms d2Transfer616Arithmetic
#print axioms d2Transfer616Bound
def d2Transfer617Lo : ℚ := (d2LitsNearTransfers077.q2 (1023) 1 (-10))
def d2Transfer617Hi : ℚ := (d2LitsNearTransfers077.q2 (2047) 1 (-11))
def d2Transfer617Cap : ℚ := (d2LitsNearTransfers077.q2 (1047085633747164758283) 1 (-79))
def d2Transfer617C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer617S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer617Arithmetic : weightedUpper d2Transfer617C0 d2Log177Lo d2Log177Hi ≤ d2Transfer617Cap := by decide +kernel
theorem d2Transfer617Bound : ∀ x ∈ Set.Icc ((d2Transfer617Lo:ℚ):ℝ) ((d2Transfer617Hi:ℚ):ℝ), ((d2Transfer617C0:ℚ):ℝ)*Real.log |x-((d2Transfer617S0:ℚ):ℝ)| ≤ ((d2Transfer617Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer617S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer617S0,d2Transfer617Lo,d2Transfer617Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer617C0 then |x-((d2Transfer617S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer617S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer617S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer617S0,d2Transfer617Lo,d2Transfer617Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer617C0,d2Log177Q,d2Transfer617S0,d2Transfer617Lo,d2Transfer617Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer617C0 d2Transfer617S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer617C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer617Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer617Arithmetic
  linarith
#print axioms d2Transfer617Arithmetic
#print axioms d2Transfer617Bound
def d2Transfer618Lo : ℚ := (d2LitsNearTransfers077.q2 (1023) 1 (-10))
def d2Transfer618Hi : ℚ := (d2LitsNearTransfers077.q2 (2047) 1 (-11))
def d2Transfer618Cap : ℚ := (d2LitsNearTransfers077.q2 (1047085424290199666955) 1 (-79))
def d2Transfer618C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer618S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer618Arithmetic : weightedUpper d2Transfer618C0 d2Log177Lo d2Log177Hi ≤ d2Transfer618Cap := by decide +kernel
theorem d2Transfer618Bound : ∀ x ∈ Set.Icc ((d2Transfer618Lo:ℚ):ℝ) ((d2Transfer618Hi:ℚ):ℝ), ((d2Transfer618C0:ℚ):ℝ)*Real.log |x-((d2Transfer618S0:ℚ):ℝ)| ≤ ((d2Transfer618Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer618S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer618S0,d2Transfer618Lo,d2Transfer618Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer618C0 then |x-((d2Transfer618S0:ℚ):ℝ)| ≤ ((d2Log177Q:ℚ):ℝ) else ((d2Log177Q:ℚ):ℝ) ≤ |x-((d2Transfer618S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer618S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer618S0,d2Transfer618Lo,d2Transfer618Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer618C0,d2Log177Q,d2Transfer618S0,d2Transfer618Lo,d2Transfer618Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer618C0 d2Transfer618S0 d2Log177Q d2Log177Lo d2Log177Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log177Bounds
  have har : (((weightedUpper d2Transfer618C0 d2Log177Lo d2Log177Hi:ℚ):ℝ)) ≤ ((d2Transfer618Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer618Arithmetic
  linarith
#print axioms d2Transfer618Arithmetic
#print axioms d2Transfer618Bound
def d2Transfer619Lo : ℚ := (d2LitsNearTransfers077.q2 (2047) 1 (-11))
def d2Transfer619Hi : ℚ := (d2LitsNearTransfers077.q2 (4095) 1 (-12))
def d2Transfer619Cap : ℚ := (d2LitsNearTransfers077.q2 (2094540269942628270903) 1 (-80))
def d2Transfer619C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer619S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer619Arithmetic : weightedUpper d2Transfer619C0 d2Log178Lo d2Log178Hi ≤ d2Transfer619Cap := by decide +kernel
theorem d2Transfer619Bound : ∀ x ∈ Set.Icc ((d2Transfer619Lo:ℚ):ℝ) ((d2Transfer619Hi:ℚ):ℝ), ((d2Transfer619C0:ℚ):ℝ)*Real.log |x-((d2Transfer619S0:ℚ):ℝ)| ≤ ((d2Transfer619Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer619S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer619S0,d2Transfer619Lo,d2Transfer619Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer619C0 then |x-((d2Transfer619S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer619S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer619S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer619S0,d2Transfer619Lo,d2Transfer619Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer619C0,d2Log178Q,d2Transfer619S0,d2Transfer619Lo,d2Transfer619Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer619C0 d2Transfer619S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer619C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer619Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer619Arithmetic
  linarith
#print axioms d2Transfer619Arithmetic
#print axioms d2Transfer619Bound
def d2Transfer620Lo : ℚ := (d2LitsNearTransfers077.q2 (2047) 1 (-11))
def d2Transfer620Hi : ℚ := (d2LitsNearTransfers077.q2 (4095) 1 (-12))
def d2Transfer620Cap : ℚ := (d2LitsNearTransfers077.q2 (2094539851028698088247) 1 (-80))
def d2Transfer620C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer620S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer620Arithmetic : weightedUpper d2Transfer620C0 d2Log178Lo d2Log178Hi ≤ d2Transfer620Cap := by decide +kernel
theorem d2Transfer620Bound : ∀ x ∈ Set.Icc ((d2Transfer620Lo:ℚ):ℝ) ((d2Transfer620Hi:ℚ):ℝ), ((d2Transfer620C0:ℚ):ℝ)*Real.log |x-((d2Transfer620S0:ℚ):ℝ)| ≤ ((d2Transfer620Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer620S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer620S0,d2Transfer620Lo,d2Transfer620Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer620C0 then |x-((d2Transfer620S0:ℚ):ℝ)| ≤ ((d2Log178Q:ℚ):ℝ) else ((d2Log178Q:ℚ):ℝ) ≤ |x-((d2Transfer620S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer620S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer620S0,d2Transfer620Lo,d2Transfer620Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer620C0,d2Log178Q,d2Transfer620S0,d2Transfer620Lo,d2Transfer620Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer620C0 d2Transfer620S0 d2Log178Q d2Log178Lo d2Log178Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log178Bounds
  have har : (((weightedUpper d2Transfer620C0 d2Log178Lo d2Log178Hi:ℚ):ℝ)) ≤ ((d2Transfer620Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer620Arithmetic
  linarith
#print axioms d2Transfer620Arithmetic
#print axioms d2Transfer620Bound
def d2Transfer621Lo : ℚ := (d2LitsNearTransfers077.q2 (4095) 1 (-12))
def d2Transfer621Hi : ℚ := (d2LitsNearTransfers077.q2 (8191) 1 (-13))
def d2Transfer621Cap : ℚ := (d2LitsNearTransfers077.q2 (1047362377136733790409) 1 (-79))
def d2Transfer621C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer621S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer621Arithmetic : weightedUpper d2Transfer621C0 d2Log179Lo d2Log179Hi ≤ d2Transfer621Cap := by decide +kernel
theorem d2Transfer621Bound : ∀ x ∈ Set.Icc ((d2Transfer621Lo:ℚ):ℝ) ((d2Transfer621Hi:ℚ):ℝ), ((d2Transfer621C0:ℚ):ℝ)*Real.log |x-((d2Transfer621S0:ℚ):ℝ)| ≤ ((d2Transfer621Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer621S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer621S0,d2Transfer621Lo,d2Transfer621Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer621C0 then |x-((d2Transfer621S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer621S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer621S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer621S0,d2Transfer621Lo,d2Transfer621Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer621C0,d2Log179Q,d2Transfer621S0,d2Transfer621Lo,d2Transfer621Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer621C0 d2Transfer621S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer621C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer621Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer621Arithmetic
  linarith
#print axioms d2Transfer621Arithmetic
#print axioms d2Transfer621Bound
def d2Transfer622Lo : ℚ := (d2LitsNearTransfers077.q2 (4095) 1 (-12))
def d2Transfer622Hi : ℚ := (d2LitsNearTransfers077.q2 (8191) 1 (-13))
def d2Transfer622Cap : ℚ := (d2LitsNearTransfers077.q2 (1047362167679768699081) 1 (-79))
def d2Transfer622C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer622S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer622Arithmetic : weightedUpper d2Transfer622C0 d2Log179Lo d2Log179Hi ≤ d2Transfer622Cap := by decide +kernel
theorem d2Transfer622Bound : ∀ x ∈ Set.Icc ((d2Transfer622Lo:ℚ):ℝ) ((d2Transfer622Hi:ℚ):ℝ), ((d2Transfer622C0:ℚ):ℝ)*Real.log |x-((d2Transfer622S0:ℚ):ℝ)| ≤ ((d2Transfer622Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer622S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer622S0,d2Transfer622Lo,d2Transfer622Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer622C0 then |x-((d2Transfer622S0:ℚ):ℝ)| ≤ ((d2Log179Q:ℚ):ℝ) else ((d2Log179Q:ℚ):ℝ) ≤ |x-((d2Transfer622S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer622S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer622S0,d2Transfer622Lo,d2Transfer622Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer622C0,d2Log179Q,d2Transfer622S0,d2Transfer622Lo,d2Transfer622Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer622C0 d2Transfer622S0 d2Log179Q d2Log179Lo d2Log179Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log179Bounds
  have har : (((weightedUpper d2Transfer622C0 d2Log179Lo d2Log179Hi:ℚ):ℝ)) ≤ ((d2Transfer622Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer622Arithmetic
  linarith
#print axioms d2Transfer622Arithmetic
#print axioms d2Transfer622Bound
def d2Transfer623Lo : ℚ := (d2LitsNearTransfers077.q2 (8191) 1 (-13))
def d2Transfer623Hi : ℚ := (d2LitsNearTransfers077.q2 (16383) 1 (-14))
def d2Transfer623Cap : ℚ := (d2LitsNearTransfers077.q2 (1047408496108080610437) 1 (-79))
def d2Transfer623C0 : ℚ := (d2LitsNearTransfers077.q2 (1) 25 (-4))
def d2Transfer623S0 : ℚ := (d2LitsNearTransfers077.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer623Arithmetic : weightedUpper d2Transfer623C0 d2Log180Lo d2Log180Hi ≤ d2Transfer623Cap := by decide +kernel
theorem d2Transfer623Bound : ∀ x ∈ Set.Icc ((d2Transfer623Lo:ℚ):ℝ) ((d2Transfer623Hi:ℚ):ℝ), ((d2Transfer623C0:ℚ):ℝ)*Real.log |x-((d2Transfer623S0:ℚ):ℝ)| ≤ ((d2Transfer623Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer623S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer623S0,d2Transfer623Lo,d2Transfer623Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer623C0 then |x-((d2Transfer623S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2Transfer623S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer623S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer623S0,d2Transfer623Lo,d2Transfer623Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers077.q2, d2LitsNearLogCache011.q2, d2Transfer623C0,d2Log180Q,d2Transfer623S0,d2Transfer623Lo,d2Transfer623Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer623C0 d2Transfer623S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2Transfer623C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2Transfer623Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer623Arithmetic
  linarith
#print axioms d2Transfer623Arithmetic
#print axioms d2Transfer623Bound
end CatalanMeasure.GenD.Signed.Data.Cells

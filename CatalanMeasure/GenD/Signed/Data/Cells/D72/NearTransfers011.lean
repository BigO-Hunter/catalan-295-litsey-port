module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache005
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers011
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers011
open D72.LogTransfer
def d2Transfer88Lo : ℚ := (d2LitsNearTransfers011.q2 (98749) 15625 (-6))
def d2Transfer88Hi : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer88Cap : ℚ := (d2LitsNearTransfers011.q2 (16281318465) 1 (-40))
def d2Transfer88C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (-5))
def d2Transfer88S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer88Arithmetic : weightedUpper d2Transfer88C0 d2Log88Lo d2Log88Hi ≤ d2Transfer88Cap := by decide +kernel
theorem d2Transfer88Bound : ∀ x ∈ Set.Icc ((d2Transfer88Lo:ℚ):ℝ) ((d2Transfer88Hi:ℚ):ℝ), ((d2Transfer88C0:ℚ):ℝ)*Real.log |x-((d2Transfer88S0:ℚ):ℝ)| ≤ ((d2Transfer88Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer88S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer88S0,d2Transfer88Lo,d2Transfer88Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer88C0 then |x-((d2Transfer88S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer88S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer88S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer88S0,d2Transfer88Lo,d2Transfer88Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer88C0,d2Log88Q,d2Transfer88S0,d2Transfer88Lo,d2Transfer88Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer88C0 d2Transfer88S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have har : (((weightedUpper d2Transfer88C0 d2Log88Lo d2Log88Hi:ℚ):ℝ)) ≤ ((d2Transfer88Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer88Arithmetic
  linarith
#print axioms d2Transfer88Arithmetic
#print axioms d2Transfer88Bound
def d2Transfer89Lo : ℚ := (d2LitsNearTransfers011.q2 (98749) 15625 (-6))
def d2Transfer89Hi : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer89Cap : ℚ := (d2LitsNearTransfers011.q2 (31165051305) 1 (-40))
def d2Transfer89C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 11 (-5))
def d2Transfer89S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
def d2Transfer89C1 : ℚ := (d2LitsNearTransfers011.q2 (-5) 11 (-4))
def d2Transfer89S1 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer89Arithmetic : weightedUpper d2Transfer89C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer89C1 d2Log86Lo d2Log86Hi ≤ d2Transfer89Cap := by decide +kernel
theorem d2Transfer89Bound : ∀ x ∈ Set.Icc ((d2Transfer89Lo:ℚ):ℝ) ((d2Transfer89Hi:ℚ):ℝ), ((d2Transfer89C0:ℚ):ℝ)*Real.log |x-((d2Transfer89S0:ℚ):ℝ)| + ((d2Transfer89C1:ℚ):ℝ)*Real.log |x-((d2Transfer89S1:ℚ):ℝ)| ≤ ((d2Transfer89Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer89S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89S0,d2Transfer89Lo,d2Transfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer89C0 then |x-((d2Transfer89S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer89S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer89S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89S0,d2Transfer89Lo,d2Transfer89Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89C0,d2Log88Q,d2Transfer89S0,d2Transfer89Lo,d2Transfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer89C0 d2Transfer89S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer89S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89S1,d2Transfer89Lo,d2Transfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer89C1 then |x-((d2Transfer89S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer89S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer89S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89S1,d2Transfer89Lo,d2Transfer89Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer89C1,d2Log86Q,d2Transfer89S1,d2Transfer89Lo,d2Transfer89Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer89C1 d2Transfer89S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer89C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer89C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer89Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer89Arithmetic
  linarith
#print axioms d2Transfer89Arithmetic
#print axioms d2Transfer89Bound
def d2Transfer90Lo : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer90Hi : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer90Cap : ℚ := (d2LitsNearTransfers011.q2 (649441385) 1 (-39))
def d2Transfer90C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 25 (-4))
def d2Transfer90S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer90Arithmetic : weightedUpper d2Transfer90C0 d2Log89Lo d2Log89Hi ≤ d2Transfer90Cap := by decide +kernel
theorem d2Transfer90Bound : ∀ x ∈ Set.Icc ((d2Transfer90Lo:ℚ):ℝ) ((d2Transfer90Hi:ℚ):ℝ), ((d2Transfer90C0:ℚ):ℝ)*Real.log |x-((d2Transfer90S0:ℚ):ℝ)| ≤ ((d2Transfer90Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer90S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer90S0,d2Transfer90Lo,d2Transfer90Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer90C0 then |x-((d2Transfer90S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer90S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer90S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer90S0,d2Transfer90Lo,d2Transfer90Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer90C0,d2Log89Q,d2Transfer90S0,d2Transfer90Lo,d2Transfer90Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer90C0 d2Transfer90S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have har : (((weightedUpper d2Transfer90C0 d2Log89Lo d2Log89Hi:ℚ):ℝ)) ≤ ((d2Transfer90Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer90Arithmetic
  linarith
#print axioms d2Transfer90Arithmetic
#print axioms d2Transfer90Bound
def d2Transfer91Lo : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer91Hi : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer91Cap : ℚ := (d2LitsNearTransfers011.q2 (2436024149) 1 (-40))
def d2Transfer91C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 275 (-4))
def d2Transfer91S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
def d2Transfer91C1 : ℚ := (d2LitsNearTransfers011.q2 (-1) 55 (-3))
def d2Transfer91S1 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer91Arithmetic : weightedUpper d2Transfer91C0 d2Log89Lo d2Log89Hi + weightedUpper d2Transfer91C1 d2Log85Lo d2Log85Hi ≤ d2Transfer91Cap := by decide +kernel
theorem d2Transfer91Bound : ∀ x ∈ Set.Icc ((d2Transfer91Lo:ℚ):ℝ) ((d2Transfer91Hi:ℚ):ℝ), ((d2Transfer91C0:ℚ):ℝ)*Real.log |x-((d2Transfer91S0:ℚ):ℝ)| + ((d2Transfer91C1:ℚ):ℝ)*Real.log |x-((d2Transfer91S1:ℚ):ℝ)| ≤ ((d2Transfer91Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer91S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91S0,d2Transfer91Lo,d2Transfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer91C0 then |x-((d2Transfer91S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer91S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer91S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91S0,d2Transfer91Lo,d2Transfer91Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91C0,d2Log89Q,d2Transfer91S0,d2Transfer91Lo,d2Transfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer91C0 d2Transfer91S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have hn1 : x-((d2Transfer91S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91S1,d2Transfer91Lo,d2Transfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer91C1 then |x-((d2Transfer91S1:ℚ):ℝ)| ≤ ((d2Log85Q:ℚ):ℝ) else ((d2Log85Q:ℚ):ℝ) ≤ |x-((d2Transfer91S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer91S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91S1,d2Transfer91Lo,d2Transfer91Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer91C1,d2Log85Q,d2Transfer91S1,d2Transfer91Lo,d2Transfer91Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer91C1 d2Transfer91S1 d2Log85Q d2Log85Lo d2Log85Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log85Bounds
  have har : (((weightedUpper d2Transfer91C0 d2Log89Lo d2Log89Hi:ℚ):ℝ) + ((weightedUpper d2Transfer91C1 d2Log85Lo d2Log85Hi:ℚ):ℝ)) ≤ ((d2Transfer91Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer91Arithmetic
  linarith
#print axioms d2Transfer91Arithmetic
#print axioms d2Transfer91Bound
def d2Transfer92Lo : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer92Hi : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer92Cap : ℚ := (d2LitsNearTransfers011.q2 (16281318465) 1 (-40))
def d2Transfer92C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (-5))
def d2Transfer92S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer92Arithmetic : weightedUpper d2Transfer92C0 d2Log89Lo d2Log89Hi ≤ d2Transfer92Cap := by decide +kernel
theorem d2Transfer92Bound : ∀ x ∈ Set.Icc ((d2Transfer92Lo:ℚ):ℝ) ((d2Transfer92Hi:ℚ):ℝ), ((d2Transfer92C0:ℚ):ℝ)*Real.log |x-((d2Transfer92S0:ℚ):ℝ)| ≤ ((d2Transfer92Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer92S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer92S0,d2Transfer92Lo,d2Transfer92Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer92C0 then |x-((d2Transfer92S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer92S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer92S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer92S0,d2Transfer92Lo,d2Transfer92Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer92C0,d2Log89Q,d2Transfer92S0,d2Transfer92Lo,d2Transfer92Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer92C0 d2Transfer92S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have har : (((weightedUpper d2Transfer92C0 d2Log89Lo d2Log89Hi:ℚ):ℝ)) ≤ ((d2Transfer92Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer92Arithmetic
  linarith
#print axioms d2Transfer92Arithmetic
#print axioms d2Transfer92Bound
def d2Transfer93Lo : ℚ := (d2LitsNearTransfers011.q2 (828367) 1 (-23))
def d2Transfer93Hi : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer93Cap : ℚ := (d2LitsNearTransfers011.q2 (31165051305) 1 (-40))
def d2Transfer93C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 11 (-5))
def d2Transfer93S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
def d2Transfer93C1 : ℚ := (d2LitsNearTransfers011.q2 (-5) 11 (-4))
def d2Transfer93S1 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer93Arithmetic : weightedUpper d2Transfer93C0 d2Log89Lo d2Log89Hi + weightedUpper d2Transfer93C1 d2Log85Lo d2Log85Hi ≤ d2Transfer93Cap := by decide +kernel
theorem d2Transfer93Bound : ∀ x ∈ Set.Icc ((d2Transfer93Lo:ℚ):ℝ) ((d2Transfer93Hi:ℚ):ℝ), ((d2Transfer93C0:ℚ):ℝ)*Real.log |x-((d2Transfer93S0:ℚ):ℝ)| + ((d2Transfer93C1:ℚ):ℝ)*Real.log |x-((d2Transfer93S1:ℚ):ℝ)| ≤ ((d2Transfer93Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer93S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93S0,d2Transfer93Lo,d2Transfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer93C0 then |x-((d2Transfer93S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer93S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer93S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93S0,d2Transfer93Lo,d2Transfer93Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93C0,d2Log89Q,d2Transfer93S0,d2Transfer93Lo,d2Transfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer93C0 d2Transfer93S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have hn1 : x-((d2Transfer93S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93S1,d2Transfer93Lo,d2Transfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer93C1 then |x-((d2Transfer93S1:ℚ):ℝ)| ≤ ((d2Log85Q:ℚ):ℝ) else ((d2Log85Q:ℚ):ℝ) ≤ |x-((d2Transfer93S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer93S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93S1,d2Transfer93Lo,d2Transfer93Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer93C1,d2Log85Q,d2Transfer93S1,d2Transfer93Lo,d2Transfer93Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer93C1 d2Transfer93S1 d2Log85Q d2Log85Lo d2Log85Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log85Bounds
  have har : (((weightedUpper d2Transfer93C0 d2Log89Lo d2Log89Hi:ℚ):ℝ) + ((weightedUpper d2Transfer93C1 d2Log85Lo d2Log85Hi:ℚ):ℝ)) ≤ ((d2Transfer93Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer93Arithmetic
  linarith
#print axioms d2Transfer93Arithmetic
#print axioms d2Transfer93Bound
def d2Transfer94Lo : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer94Hi : ℚ := (d2LitsNearTransfers011.q2 (28185465) 1 (-28))
def d2Transfer94Cap : ℚ := (d2LitsNearTransfers011.q2 (649441385) 1 (-39))
def d2Transfer94C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 25 (-4))
def d2Transfer94S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer94Arithmetic : weightedUpper d2Transfer94C0 d2Log90Lo d2Log90Hi ≤ d2Transfer94Cap := by decide +kernel
theorem d2Transfer94Bound : ∀ x ∈ Set.Icc ((d2Transfer94Lo:ℚ):ℝ) ((d2Transfer94Hi:ℚ):ℝ), ((d2Transfer94C0:ℚ):ℝ)*Real.log |x-((d2Transfer94S0:ℚ):ℝ)| ≤ ((d2Transfer94Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer94S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer94S0,d2Transfer94Lo,d2Transfer94Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer94C0 then |x-((d2Transfer94S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer94S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer94S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer94S0,d2Transfer94Lo,d2Transfer94Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer94C0,d2Log90Q,d2Transfer94S0,d2Transfer94Lo,d2Transfer94Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer94C0 d2Transfer94S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have har : (((weightedUpper d2Transfer94C0 d2Log90Lo d2Log90Hi:ℚ):ℝ)) ≤ ((d2Transfer94Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer94Arithmetic
  linarith
#print axioms d2Transfer94Arithmetic
#print axioms d2Transfer94Bound
def d2Transfer95Lo : ℚ := (d2LitsNearTransfers011.q2 (54693209) 1 (-29))
def d2Transfer95Hi : ℚ := (d2LitsNearTransfers011.q2 (28185465) 1 (-28))
def d2Transfer95Cap : ℚ := (d2LitsNearTransfers011.q2 (2436024149) 1 (-40))
def d2Transfer95C0 : ℚ := (d2LitsNearTransfers011.q2 (1) 275 (-4))
def d2Transfer95S0 : ℚ := (d2LitsNearTransfers011.q2 (-1) 1 (0))
def d2Transfer95C1 : ℚ := (d2LitsNearTransfers011.q2 (-1) 55 (-3))
def d2Transfer95S1 : ℚ := (d2LitsNearTransfers011.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer95Arithmetic : weightedUpper d2Transfer95C0 d2Log90Lo d2Log90Hi + weightedUpper d2Transfer95C1 d2Log84Lo d2Log84Hi ≤ d2Transfer95Cap := by decide +kernel
theorem d2Transfer95Bound : ∀ x ∈ Set.Icc ((d2Transfer95Lo:ℚ):ℝ) ((d2Transfer95Hi:ℚ):ℝ), ((d2Transfer95C0:ℚ):ℝ)*Real.log |x-((d2Transfer95S0:ℚ):ℝ)| + ((d2Transfer95C1:ℚ):ℝ)*Real.log |x-((d2Transfer95S1:ℚ):ℝ)| ≤ ((d2Transfer95Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer95S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95S0,d2Transfer95Lo,d2Transfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer95C0 then |x-((d2Transfer95S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer95S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer95S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95S0,d2Transfer95Lo,d2Transfer95Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95C0,d2Log90Q,d2Transfer95S0,d2Transfer95Lo,d2Transfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer95C0 d2Transfer95S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have hn1 : x-((d2Transfer95S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95S1,d2Transfer95Lo,d2Transfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer95C1 then |x-((d2Transfer95S1:ℚ):ℝ)| ≤ ((d2Log84Q:ℚ):ℝ) else ((d2Log84Q:ℚ):ℝ) ≤ |x-((d2Transfer95S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer95S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95S1,d2Transfer95Lo,d2Transfer95Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers011.q2, d2LitsNearLogCache005.q2, d2Transfer95C1,d2Log84Q,d2Transfer95S1,d2Transfer95Lo,d2Transfer95Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer95C1 d2Transfer95S1 d2Log84Q d2Log84Lo d2Log84Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log84Bounds
  have har : (((weightedUpper d2Transfer95C0 d2Log90Lo d2Log90Hi:ℚ):ℝ) + ((weightedUpper d2Transfer95C1 d2Log84Lo d2Log84Hi:ℚ):ℝ)) ≤ ((d2Transfer95Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer95Arithmetic
  linarith
#print axioms d2Transfer95Arithmetic
#print axioms d2Transfer95Bound
end CatalanMeasure.GenD.Signed.Data.Cells

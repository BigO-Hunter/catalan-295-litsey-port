module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
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
namespace d2LitsNearTransfers048
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers048
open D72.LogTransfer
def d2Transfer384Lo : ℚ := (d2LitsNearTransfers048.q2 (98749) 15625 (-6))
def d2Transfer384Hi : ℚ := (d2LitsNearTransfers048.q2 (828367) 1 (-23))
def d2Transfer384Cap : ℚ := (d2LitsNearTransfers048.q2 (30439539927) 1 (-40))
def d2Transfer384C0 : ℚ := (d2LitsNearTransfers048.q2 (3) 275 (-5))
def d2Transfer384S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer384C1 : ℚ := (d2LitsNearTransfers048.q2 (-5) 11 (-4))
def d2Transfer384S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer384Arithmetic : weightedUpper d2Transfer384C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer384C1 d2Log86Lo d2Log86Hi ≤ d2Transfer384Cap := by decide +kernel
theorem d2Transfer384Bound : ∀ x ∈ Set.Icc ((d2Transfer384Lo:ℚ):ℝ) ((d2Transfer384Hi:ℚ):ℝ), ((d2Transfer384C0:ℚ):ℝ)*Real.log |x-((d2Transfer384S0:ℚ):ℝ)| + ((d2Transfer384C1:ℚ):ℝ)*Real.log |x-((d2Transfer384S1:ℚ):ℝ)| ≤ ((d2Transfer384Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer384S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384S0,d2Transfer384Lo,d2Transfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer384C0 then |x-((d2Transfer384S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer384S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer384S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384S0,d2Transfer384Lo,d2Transfer384Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384C0,d2Log88Q,d2Transfer384S0,d2Transfer384Lo,d2Transfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer384C0 d2Transfer384S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer384S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384S1,d2Transfer384Lo,d2Transfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer384C1 then |x-((d2Transfer384S1:ℚ):ℝ)| ≤ ((d2Log86Q:ℚ):ℝ) else ((d2Log86Q:ℚ):ℝ) ≤ |x-((d2Transfer384S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer384S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384S1,d2Transfer384Lo,d2Transfer384Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer384C1,d2Log86Q,d2Transfer384S1,d2Transfer384Lo,d2Transfer384Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer384C1 d2Transfer384S1 d2Log86Q d2Log86Lo d2Log86Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log86Bounds
  have har : (((weightedUpper d2Transfer384C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer384C1 d2Log86Lo d2Log86Hi:ℚ):ℝ)) ≤ ((d2Transfer384Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer384Arithmetic
  linarith
#print axioms d2Transfer384Arithmetic
#print axioms d2Transfer384Bound
def d2Transfer385Lo : ℚ := (d2LitsNearTransfers048.q2 (828367) 1 (-23))
def d2Transfer385Hi : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer385Cap : ℚ := (d2LitsNearTransfers048.q2 (1169469059) 1 (-40))
def d2Transfer385C0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer385S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer385C1 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer385S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer385Arithmetic : weightedUpper d2Transfer385C0 d2Log88Lo d2Log88Hi + weightedUpper d2Transfer385C1 d2Log85Lo d2Log85Hi ≤ d2Transfer385Cap := by decide +kernel
theorem d2Transfer385Bound : ∀ x ∈ Set.Icc ((d2Transfer385Lo:ℚ):ℝ) ((d2Transfer385Hi:ℚ):ℝ), ((d2Transfer385C0:ℚ):ℝ)*Real.log |x-((d2Transfer385S0:ℚ):ℝ)| + ((d2Transfer385C1:ℚ):ℝ)*Real.log |x-((d2Transfer385S1:ℚ):ℝ)| ≤ ((d2Transfer385Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer385S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385S0,d2Transfer385Lo,d2Transfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer385C0 then |x-((d2Transfer385S0:ℚ):ℝ)| ≤ ((d2Log88Q:ℚ):ℝ) else ((d2Log88Q:ℚ):ℝ) ≤ |x-((d2Transfer385S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer385S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385S0,d2Transfer385Lo,d2Transfer385Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385C0,d2Log88Q,d2Transfer385S0,d2Transfer385Lo,d2Transfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer385C0 d2Transfer385S0 d2Log88Q d2Log88Lo d2Log88Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log88Bounds
  have hn1 : x-((d2Transfer385S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385S1,d2Transfer385Lo,d2Transfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer385C1 then |x-((d2Transfer385S1:ℚ):ℝ)| ≤ ((d2Log85Q:ℚ):ℝ) else ((d2Log85Q:ℚ):ℝ) ≤ |x-((d2Transfer385S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer385S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385S1,d2Transfer385Lo,d2Transfer385Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer385C1,d2Log85Q,d2Transfer385S1,d2Transfer385Lo,d2Transfer385Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer385C1 d2Transfer385S1 d2Log85Q d2Log85Lo d2Log85Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log85Bounds
  have har : (((weightedUpper d2Transfer385C0 d2Log88Lo d2Log88Hi:ℚ):ℝ) + ((weightedUpper d2Transfer385C1 d2Log85Lo d2Log85Hi:ℚ):ℝ)) ≤ ((d2Transfer385Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer385Arithmetic
  linarith
#print axioms d2Transfer385Arithmetic
#print axioms d2Transfer385Bound
def d2Transfer386Lo : ℚ := (d2LitsNearTransfers048.q2 (828367) 1 (-23))
def d2Transfer386Hi : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer386Cap : ℚ := (d2LitsNearTransfers048.q2 (15113656175) 1 (-40))
def d2Transfer386C0 : ℚ := (d2LitsNearTransfers048.q2 (23) 25 (-5))
def d2Transfer386S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer386Arithmetic : weightedUpper d2Transfer386C0 d2Log89Lo d2Log89Hi ≤ d2Transfer386Cap := by decide +kernel
theorem d2Transfer386Bound : ∀ x ∈ Set.Icc ((d2Transfer386Lo:ℚ):ℝ) ((d2Transfer386Hi:ℚ):ℝ), ((d2Transfer386C0:ℚ):ℝ)*Real.log |x-((d2Transfer386S0:ℚ):ℝ)| ≤ ((d2Transfer386Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer386S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer386S0,d2Transfer386Lo,d2Transfer386Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer386C0 then |x-((d2Transfer386S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer386S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer386S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer386S0,d2Transfer386Lo,d2Transfer386Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer386C0,d2Log89Q,d2Transfer386S0,d2Transfer386Lo,d2Transfer386Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer386C0 d2Transfer386S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have har : (((weightedUpper d2Transfer386C0 d2Log89Lo d2Log89Hi:ℚ):ℝ)) ≤ ((d2Transfer386Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer386Arithmetic
  linarith
#print axioms d2Transfer386Arithmetic
#print axioms d2Transfer386Bound
def d2Transfer387Lo : ℚ := (d2LitsNearTransfers048.q2 (828367) 1 (-23))
def d2Transfer387Hi : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer387Cap : ℚ := (d2LitsNearTransfers048.q2 (30439539927) 1 (-40))
def d2Transfer387C0 : ℚ := (d2LitsNearTransfers048.q2 (3) 275 (-5))
def d2Transfer387S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer387C1 : ℚ := (d2LitsNearTransfers048.q2 (-5) 11 (-4))
def d2Transfer387S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer387Arithmetic : weightedUpper d2Transfer387C0 d2Log89Lo d2Log89Hi + weightedUpper d2Transfer387C1 d2Log85Lo d2Log85Hi ≤ d2Transfer387Cap := by decide +kernel
theorem d2Transfer387Bound : ∀ x ∈ Set.Icc ((d2Transfer387Lo:ℚ):ℝ) ((d2Transfer387Hi:ℚ):ℝ), ((d2Transfer387C0:ℚ):ℝ)*Real.log |x-((d2Transfer387S0:ℚ):ℝ)| + ((d2Transfer387C1:ℚ):ℝ)*Real.log |x-((d2Transfer387S1:ℚ):ℝ)| ≤ ((d2Transfer387Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer387S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387S0,d2Transfer387Lo,d2Transfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer387C0 then |x-((d2Transfer387S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer387S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer387S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387S0,d2Transfer387Lo,d2Transfer387Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387C0,d2Log89Q,d2Transfer387S0,d2Transfer387Lo,d2Transfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer387C0 d2Transfer387S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have hn1 : x-((d2Transfer387S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387S1,d2Transfer387Lo,d2Transfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer387C1 then |x-((d2Transfer387S1:ℚ):ℝ)| ≤ ((d2Log85Q:ℚ):ℝ) else ((d2Log85Q:ℚ):ℝ) ≤ |x-((d2Transfer387S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer387S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387S1,d2Transfer387Lo,d2Transfer387Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer387C1,d2Log85Q,d2Transfer387S1,d2Transfer387Lo,d2Transfer387Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer387C1 d2Transfer387S1 d2Log85Q d2Log85Lo d2Log85Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log85Bounds
  have har : (((weightedUpper d2Transfer387C0 d2Log89Lo d2Log89Hi:ℚ):ℝ) + ((weightedUpper d2Transfer387C1 d2Log85Lo d2Log85Hi:ℚ):ℝ)) ≤ ((d2Transfer387Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer387Arithmetic
  linarith
#print axioms d2Transfer387Arithmetic
#print axioms d2Transfer387Bound
def d2Transfer388Lo : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer388Hi : ℚ := (d2LitsNearTransfers048.q2 (28185465) 1 (-28))
def d2Transfer388Cap : ℚ := (d2LitsNearTransfers048.q2 (1169469059) 1 (-40))
def d2Transfer388C0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer388S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer388C1 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer388S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer388Arithmetic : weightedUpper d2Transfer388C0 d2Log89Lo d2Log89Hi + weightedUpper d2Transfer388C1 d2Log84Lo d2Log84Hi ≤ d2Transfer388Cap := by decide +kernel
theorem d2Transfer388Bound : ∀ x ∈ Set.Icc ((d2Transfer388Lo:ℚ):ℝ) ((d2Transfer388Hi:ℚ):ℝ), ((d2Transfer388C0:ℚ):ℝ)*Real.log |x-((d2Transfer388S0:ℚ):ℝ)| + ((d2Transfer388C1:ℚ):ℝ)*Real.log |x-((d2Transfer388S1:ℚ):ℝ)| ≤ ((d2Transfer388Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer388S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388S0,d2Transfer388Lo,d2Transfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer388C0 then |x-((d2Transfer388S0:ℚ):ℝ)| ≤ ((d2Log89Q:ℚ):ℝ) else ((d2Log89Q:ℚ):ℝ) ≤ |x-((d2Transfer388S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer388S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388S0,d2Transfer388Lo,d2Transfer388Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388C0,d2Log89Q,d2Transfer388S0,d2Transfer388Lo,d2Transfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer388C0 d2Transfer388S0 d2Log89Q d2Log89Lo d2Log89Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log89Bounds
  have hn1 : x-((d2Transfer388S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388S1,d2Transfer388Lo,d2Transfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer388C1 then |x-((d2Transfer388S1:ℚ):ℝ)| ≤ ((d2Log84Q:ℚ):ℝ) else ((d2Log84Q:ℚ):ℝ) ≤ |x-((d2Transfer388S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer388S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388S1,d2Transfer388Lo,d2Transfer388Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer388C1,d2Log84Q,d2Transfer388S1,d2Transfer388Lo,d2Transfer388Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer388C1 d2Transfer388S1 d2Log84Q d2Log84Lo d2Log84Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log84Bounds
  have har : (((weightedUpper d2Transfer388C0 d2Log89Lo d2Log89Hi:ℚ):ℝ) + ((weightedUpper d2Transfer388C1 d2Log84Lo d2Log84Hi:ℚ):ℝ)) ≤ ((d2Transfer388Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer388Arithmetic
  linarith
#print axioms d2Transfer388Arithmetic
#print axioms d2Transfer388Bound
def d2Transfer389Lo : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer389Hi : ℚ := (d2LitsNearTransfers048.q2 (28185465) 1 (-28))
def d2Transfer389Cap : ℚ := (d2LitsNearTransfers048.q2 (15113656175) 1 (-40))
def d2Transfer389C0 : ℚ := (d2LitsNearTransfers048.q2 (23) 25 (-5))
def d2Transfer389S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer389Arithmetic : weightedUpper d2Transfer389C0 d2Log90Lo d2Log90Hi ≤ d2Transfer389Cap := by decide +kernel
theorem d2Transfer389Bound : ∀ x ∈ Set.Icc ((d2Transfer389Lo:ℚ):ℝ) ((d2Transfer389Hi:ℚ):ℝ), ((d2Transfer389C0:ℚ):ℝ)*Real.log |x-((d2Transfer389S0:ℚ):ℝ)| ≤ ((d2Transfer389Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer389S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer389S0,d2Transfer389Lo,d2Transfer389Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer389C0 then |x-((d2Transfer389S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer389S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer389S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer389S0,d2Transfer389Lo,d2Transfer389Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer389C0,d2Log90Q,d2Transfer389S0,d2Transfer389Lo,d2Transfer389Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer389C0 d2Transfer389S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have har : (((weightedUpper d2Transfer389C0 d2Log90Lo d2Log90Hi:ℚ):ℝ)) ≤ ((d2Transfer389Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer389Arithmetic
  linarith
#print axioms d2Transfer389Arithmetic
#print axioms d2Transfer389Bound
def d2Transfer390Lo : ℚ := (d2LitsNearTransfers048.q2 (54693209) 1 (-29))
def d2Transfer390Hi : ℚ := (d2LitsNearTransfers048.q2 (28185465) 1 (-28))
def d2Transfer390Cap : ℚ := (d2LitsNearTransfers048.q2 (30439539927) 1 (-40))
def d2Transfer390C0 : ℚ := (d2LitsNearTransfers048.q2 (3) 275 (-5))
def d2Transfer390S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer390C1 : ℚ := (d2LitsNearTransfers048.q2 (-5) 11 (-4))
def d2Transfer390S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer390Arithmetic : weightedUpper d2Transfer390C0 d2Log90Lo d2Log90Hi + weightedUpper d2Transfer390C1 d2Log84Lo d2Log84Hi ≤ d2Transfer390Cap := by decide +kernel
theorem d2Transfer390Bound : ∀ x ∈ Set.Icc ((d2Transfer390Lo:ℚ):ℝ) ((d2Transfer390Hi:ℚ):ℝ), ((d2Transfer390C0:ℚ):ℝ)*Real.log |x-((d2Transfer390S0:ℚ):ℝ)| + ((d2Transfer390C1:ℚ):ℝ)*Real.log |x-((d2Transfer390S1:ℚ):ℝ)| ≤ ((d2Transfer390Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer390S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390S0,d2Transfer390Lo,d2Transfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer390C0 then |x-((d2Transfer390S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer390S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer390S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390S0,d2Transfer390Lo,d2Transfer390Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390C0,d2Log90Q,d2Transfer390S0,d2Transfer390Lo,d2Transfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer390C0 d2Transfer390S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have hn1 : x-((d2Transfer390S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390S1,d2Transfer390Lo,d2Transfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer390C1 then |x-((d2Transfer390S1:ℚ):ℝ)| ≤ ((d2Log84Q:ℚ):ℝ) else ((d2Log84Q:ℚ):ℝ) ≤ |x-((d2Transfer390S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer390S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390S1,d2Transfer390Lo,d2Transfer390Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer390C1,d2Log84Q,d2Transfer390S1,d2Transfer390Lo,d2Transfer390Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer390C1 d2Transfer390S1 d2Log84Q d2Log84Lo d2Log84Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log84Bounds
  have har : (((weightedUpper d2Transfer390C0 d2Log90Lo d2Log90Hi:ℚ):ℝ) + ((weightedUpper d2Transfer390C1 d2Log84Lo d2Log84Hi:ℚ):ℝ)) ≤ ((d2Transfer390Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer390Arithmetic
  linarith
#print axioms d2Transfer390Arithmetic
#print axioms d2Transfer390Bound
def d2Transfer391Lo : ℚ := (d2LitsNearTransfers048.q2 (28185465) 1 (-28))
def d2Transfer391Hi : ℚ := (d2LitsNearTransfers048.q2 (58048651) 1 (-29))
def d2Transfer391Cap : ℚ := (d2LitsNearTransfers048.q2 (1169469059) 1 (-40))
def d2Transfer391C0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer391S0 : ℚ := (d2LitsNearTransfers048.q2 (-1) 1 (0))
def d2Transfer391C1 : ℚ := (d2LitsNearTransfers048.q2 (-1) 55 (-3))
def d2Transfer391S1 : ℚ := (d2LitsNearTransfers048.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer391Arithmetic : weightedUpper d2Transfer391C0 d2Log90Lo d2Log90Hi + weightedUpper d2Transfer391C1 d2Log83Lo d2Log83Hi ≤ d2Transfer391Cap := by decide +kernel
theorem d2Transfer391Bound : ∀ x ∈ Set.Icc ((d2Transfer391Lo:ℚ):ℝ) ((d2Transfer391Hi:ℚ):ℝ), ((d2Transfer391C0:ℚ):ℝ)*Real.log |x-((d2Transfer391S0:ℚ):ℝ)| + ((d2Transfer391C1:ℚ):ℝ)*Real.log |x-((d2Transfer391S1:ℚ):ℝ)| ≤ ((d2Transfer391Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer391S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391S0,d2Transfer391Lo,d2Transfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer391C0 then |x-((d2Transfer391S0:ℚ):ℝ)| ≤ ((d2Log90Q:ℚ):ℝ) else ((d2Log90Q:ℚ):ℝ) ≤ |x-((d2Transfer391S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer391S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391S0,d2Transfer391Lo,d2Transfer391Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391C0,d2Log90Q,d2Transfer391S0,d2Transfer391Lo,d2Transfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer391C0 d2Transfer391S0 d2Log90Q d2Log90Lo d2Log90Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log90Bounds
  have hn1 : x-((d2Transfer391S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391S1,d2Transfer391Lo,d2Transfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer391C1 then |x-((d2Transfer391S1:ℚ):ℝ)| ≤ ((d2Log83Q:ℚ):ℝ) else ((d2Log83Q:ℚ):ℝ) ≤ |x-((d2Transfer391S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer391S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391S1,d2Transfer391Lo,d2Transfer391Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers048.q2, d2LitsNearLogCache005.q2, d2Transfer391C1,d2Log83Q,d2Transfer391S1,d2Transfer391Lo,d2Transfer391Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer391C1 d2Transfer391S1 d2Log83Q d2Log83Lo d2Log83Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log83Bounds
  have har : (((weightedUpper d2Transfer391C0 d2Log90Lo d2Log90Hi:ℚ):ℝ) + ((weightedUpper d2Transfer391C1 d2Log83Lo d2Log83Hi:ℚ):ℝ)) ≤ ((d2Transfer391Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer391Arithmetic
  linarith
#print axioms d2Transfer391Arithmetic
#print axioms d2Transfer391Bound
end CatalanMeasure.GenD.Signed.Data.Cells

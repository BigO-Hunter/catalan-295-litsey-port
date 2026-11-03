module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache004
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache006
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers051
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers051
open D72.LogTransfer
def d2Transfer408Lo : ℚ := (d2LitsNearTransfers051.q2 (8304657) 1 (-26))
def d2Transfer408Hi : ℚ := (d2LitsNearTransfers051.q2 (34896349) 1 (-28))
def d2Transfer408Cap : ℚ := (d2LitsNearTransfers051.q2 (30439539927) 1 (-40))
def d2Transfer408C0 : ℚ := (d2LitsNearTransfers051.q2 (3) 275 (-5))
def d2Transfer408S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer408C1 : ℚ := (d2LitsNearTransfers051.q2 (-5) 11 (-4))
def d2Transfer408S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer408Arithmetic : weightedUpper d2Transfer408C0 d2Log96Lo d2Log96Hi + weightedUpper d2Transfer408C1 d2Log78Lo d2Log78Hi ≤ d2Transfer408Cap := by decide +kernel
theorem d2Transfer408Bound : ∀ x ∈ Set.Icc ((d2Transfer408Lo:ℚ):ℝ) ((d2Transfer408Hi:ℚ):ℝ), ((d2Transfer408C0:ℚ):ℝ)*Real.log |x-((d2Transfer408S0:ℚ):ℝ)| + ((d2Transfer408C1:ℚ):ℝ)*Real.log |x-((d2Transfer408S1:ℚ):ℝ)| ≤ ((d2Transfer408Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer408S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408S0,d2Transfer408Lo,d2Transfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer408C0 then |x-((d2Transfer408S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer408S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer408S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408S0,d2Transfer408Lo,d2Transfer408Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408C0,d2Log96Q,d2Transfer408S0,d2Transfer408Lo,d2Transfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer408C0 d2Transfer408S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have hn1 : x-((d2Transfer408S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408S1,d2Transfer408Lo,d2Transfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer408C1 then |x-((d2Transfer408S1:ℚ):ℝ)| ≤ ((d2Log78Q:ℚ):ℝ) else ((d2Log78Q:ℚ):ℝ) ≤ |x-((d2Transfer408S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer408S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408S1,d2Transfer408Lo,d2Transfer408Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer408C1,d2Log78Q,d2Transfer408S1,d2Transfer408Lo,d2Transfer408Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer408C1 d2Transfer408S1 d2Log78Q d2Log78Lo d2Log78Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log78Bounds
  have har : (((weightedUpper d2Transfer408C0 d2Log96Lo d2Log96Hi:ℚ):ℝ) + ((weightedUpper d2Transfer408C1 d2Log78Lo d2Log78Hi:ℚ):ℝ)) ≤ ((d2Transfer408Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer408Arithmetic
  linarith
#print axioms d2Transfer408Arithmetic
#print axioms d2Transfer408Bound
def d2Transfer409Lo : ℚ := (d2LitsNearTransfers051.q2 (34896349) 1 (-28))
def d2Transfer409Hi : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer409Cap : ℚ := (d2LitsNearTransfers051.q2 (1169469059) 1 (-40))
def d2Transfer409C0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer409S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer409C1 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer409S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer409Arithmetic : weightedUpper d2Transfer409C0 d2Log96Lo d2Log96Hi + weightedUpper d2Transfer409C1 d2Log77Lo d2Log77Hi ≤ d2Transfer409Cap := by decide +kernel
theorem d2Transfer409Bound : ∀ x ∈ Set.Icc ((d2Transfer409Lo:ℚ):ℝ) ((d2Transfer409Hi:ℚ):ℝ), ((d2Transfer409C0:ℚ):ℝ)*Real.log |x-((d2Transfer409S0:ℚ):ℝ)| + ((d2Transfer409C1:ℚ):ℝ)*Real.log |x-((d2Transfer409S1:ℚ):ℝ)| ≤ ((d2Transfer409Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer409S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409S0,d2Transfer409Lo,d2Transfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer409C0 then |x-((d2Transfer409S0:ℚ):ℝ)| ≤ ((d2Log96Q:ℚ):ℝ) else ((d2Log96Q:ℚ):ℝ) ≤ |x-((d2Transfer409S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer409S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409S0,d2Transfer409Lo,d2Transfer409Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409C0,d2Log96Q,d2Transfer409S0,d2Transfer409Lo,d2Transfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer409C0 d2Transfer409S0 d2Log96Q d2Log96Lo d2Log96Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log96Bounds
  have hn1 : x-((d2Transfer409S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409S1,d2Transfer409Lo,d2Transfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer409C1 then |x-((d2Transfer409S1:ℚ):ℝ)| ≤ ((d2Log77Q:ℚ):ℝ) else ((d2Log77Q:ℚ):ℝ) ≤ |x-((d2Transfer409S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer409S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409S1,d2Transfer409Lo,d2Transfer409Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer409C1,d2Log77Q,d2Transfer409S1,d2Transfer409Lo,d2Transfer409Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer409C1 d2Transfer409S1 d2Log77Q d2Log77Lo d2Log77Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log77Bounds
  have har : (((weightedUpper d2Transfer409C0 d2Log96Lo d2Log96Hi:ℚ):ℝ) + ((weightedUpper d2Transfer409C1 d2Log77Lo d2Log77Hi:ℚ):ℝ)) ≤ ((d2Transfer409Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer409Arithmetic
  linarith
#print axioms d2Transfer409Arithmetic
#print axioms d2Transfer409Bound
def d2Transfer410Lo : ℚ := (d2LitsNearTransfers051.q2 (34896349) 1 (-28))
def d2Transfer410Hi : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer410Cap : ℚ := (d2LitsNearTransfers051.q2 (15113656175) 1 (-40))
def d2Transfer410C0 : ℚ := (d2LitsNearTransfers051.q2 (23) 25 (-5))
def d2Transfer410S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer410Arithmetic : weightedUpper d2Transfer410C0 d2Log97Lo d2Log97Hi ≤ d2Transfer410Cap := by decide +kernel
theorem d2Transfer410Bound : ∀ x ∈ Set.Icc ((d2Transfer410Lo:ℚ):ℝ) ((d2Transfer410Hi:ℚ):ℝ), ((d2Transfer410C0:ℚ):ℝ)*Real.log |x-((d2Transfer410S0:ℚ):ℝ)| ≤ ((d2Transfer410Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer410S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer410S0,d2Transfer410Lo,d2Transfer410Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer410C0 then |x-((d2Transfer410S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer410S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer410S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer410S0,d2Transfer410Lo,d2Transfer410Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer410C0,d2Log97Q,d2Transfer410S0,d2Transfer410Lo,d2Transfer410Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer410C0 d2Transfer410S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have har : (((weightedUpper d2Transfer410C0 d2Log97Lo d2Log97Hi:ℚ):ℝ)) ≤ ((d2Transfer410Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer410Arithmetic
  linarith
#print axioms d2Transfer410Arithmetic
#print axioms d2Transfer410Bound
def d2Transfer411Lo : ℚ := (d2LitsNearTransfers051.q2 (34896349) 1 (-28))
def d2Transfer411Hi : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer411Cap : ℚ := (d2LitsNearTransfers051.q2 (30439539927) 1 (-40))
def d2Transfer411C0 : ℚ := (d2LitsNearTransfers051.q2 (3) 275 (-5))
def d2Transfer411S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer411C1 : ℚ := (d2LitsNearTransfers051.q2 (-5) 11 (-4))
def d2Transfer411S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer411Arithmetic : weightedUpper d2Transfer411C0 d2Log97Lo d2Log97Hi + weightedUpper d2Transfer411C1 d2Log77Lo d2Log77Hi ≤ d2Transfer411Cap := by decide +kernel
theorem d2Transfer411Bound : ∀ x ∈ Set.Icc ((d2Transfer411Lo:ℚ):ℝ) ((d2Transfer411Hi:ℚ):ℝ), ((d2Transfer411C0:ℚ):ℝ)*Real.log |x-((d2Transfer411S0:ℚ):ℝ)| + ((d2Transfer411C1:ℚ):ℝ)*Real.log |x-((d2Transfer411S1:ℚ):ℝ)| ≤ ((d2Transfer411Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer411S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411S0,d2Transfer411Lo,d2Transfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer411C0 then |x-((d2Transfer411S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer411S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer411S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411S0,d2Transfer411Lo,d2Transfer411Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411C0,d2Log97Q,d2Transfer411S0,d2Transfer411Lo,d2Transfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer411C0 d2Transfer411S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have hn1 : x-((d2Transfer411S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411S1,d2Transfer411Lo,d2Transfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer411C1 then |x-((d2Transfer411S1:ℚ):ℝ)| ≤ ((d2Log77Q:ℚ):ℝ) else ((d2Log77Q:ℚ):ℝ) ≤ |x-((d2Transfer411S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer411S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411S1,d2Transfer411Lo,d2Transfer411Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer411C1,d2Log77Q,d2Transfer411S1,d2Transfer411Lo,d2Transfer411Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer411C1 d2Transfer411S1 d2Log77Q d2Log77Lo d2Log77Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log77Bounds
  have har : (((weightedUpper d2Transfer411C0 d2Log97Lo d2Log97Hi:ℚ):ℝ) + ((weightedUpper d2Transfer411C1 d2Log77Lo d2Log77Hi:ℚ):ℝ)) ≤ ((d2Transfer411Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer411Arithmetic
  linarith
#print axioms d2Transfer411Arithmetic
#print axioms d2Transfer411Bound
def d2Transfer412Lo : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer412Hi : ℚ := (d2LitsNearTransfers051.q2 (38251791) 1 (-28))
def d2Transfer412Cap : ℚ := (d2LitsNearTransfers051.q2 (1169469059) 1 (-40))
def d2Transfer412C0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer412S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer412C1 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer412S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer412Arithmetic : weightedUpper d2Transfer412C0 d2Log97Lo d2Log97Hi + weightedUpper d2Transfer412C1 d2Log76Lo d2Log76Hi ≤ d2Transfer412Cap := by decide +kernel
theorem d2Transfer412Bound : ∀ x ∈ Set.Icc ((d2Transfer412Lo:ℚ):ℝ) ((d2Transfer412Hi:ℚ):ℝ), ((d2Transfer412C0:ℚ):ℝ)*Real.log |x-((d2Transfer412S0:ℚ):ℝ)| + ((d2Transfer412C1:ℚ):ℝ)*Real.log |x-((d2Transfer412S1:ℚ):ℝ)| ≤ ((d2Transfer412Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer412S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412S0,d2Transfer412Lo,d2Transfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer412C0 then |x-((d2Transfer412S0:ℚ):ℝ)| ≤ ((d2Log97Q:ℚ):ℝ) else ((d2Log97Q:ℚ):ℝ) ≤ |x-((d2Transfer412S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer412S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412S0,d2Transfer412Lo,d2Transfer412Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412C0,d2Log97Q,d2Transfer412S0,d2Transfer412Lo,d2Transfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer412C0 d2Transfer412S0 d2Log97Q d2Log97Lo d2Log97Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log97Bounds
  have hn1 : x-((d2Transfer412S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412S1,d2Transfer412Lo,d2Transfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer412C1 then |x-((d2Transfer412S1:ℚ):ℝ)| ≤ ((d2Log76Q:ℚ):ℝ) else ((d2Log76Q:ℚ):ℝ) ≤ |x-((d2Transfer412S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer412S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412S1,d2Transfer412Lo,d2Transfer412Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer412C1,d2Log76Q,d2Transfer412S1,d2Transfer412Lo,d2Transfer412Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer412C1 d2Transfer412S1 d2Log76Q d2Log76Lo d2Log76Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log76Bounds
  have har : (((weightedUpper d2Transfer412C0 d2Log97Lo d2Log97Hi:ℚ):ℝ) + ((weightedUpper d2Transfer412C1 d2Log76Lo d2Log76Hi:ℚ):ℝ)) ≤ ((d2Transfer412Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer412Arithmetic
  linarith
#print axioms d2Transfer412Arithmetic
#print axioms d2Transfer412Bound
def d2Transfer413Lo : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer413Hi : ℚ := (d2LitsNearTransfers051.q2 (38251791) 1 (-28))
def d2Transfer413Cap : ℚ := (d2LitsNearTransfers051.q2 (15113656175) 1 (-40))
def d2Transfer413C0 : ℚ := (d2LitsNearTransfers051.q2 (23) 25 (-5))
def d2Transfer413S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer413Arithmetic : weightedUpper d2Transfer413C0 d2Log98Lo d2Log98Hi ≤ d2Transfer413Cap := by decide +kernel
theorem d2Transfer413Bound : ∀ x ∈ Set.Icc ((d2Transfer413Lo:ℚ):ℝ) ((d2Transfer413Hi:ℚ):ℝ), ((d2Transfer413C0:ℚ):ℝ)*Real.log |x-((d2Transfer413S0:ℚ):ℝ)| ≤ ((d2Transfer413Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer413S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer413S0,d2Transfer413Lo,d2Transfer413Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer413C0 then |x-((d2Transfer413S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer413S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer413S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer413S0,d2Transfer413Lo,d2Transfer413Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer413C0,d2Log98Q,d2Transfer413S0,d2Transfer413Lo,d2Transfer413Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer413C0 d2Transfer413S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have har : (((weightedUpper d2Transfer413C0 d2Log98Lo d2Log98Hi:ℚ):ℝ)) ≤ ((d2Transfer413Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer413Arithmetic
  linarith
#print axioms d2Transfer413Arithmetic
#print axioms d2Transfer413Bound
def d2Transfer414Lo : ℚ := (d2LitsNearTransfers051.q2 (18287035) 1 (-27))
def d2Transfer414Hi : ℚ := (d2LitsNearTransfers051.q2 (38251791) 1 (-28))
def d2Transfer414Cap : ℚ := (d2LitsNearTransfers051.q2 (30439539927) 1 (-40))
def d2Transfer414C0 : ℚ := (d2LitsNearTransfers051.q2 (3) 275 (-5))
def d2Transfer414S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer414C1 : ℚ := (d2LitsNearTransfers051.q2 (-5) 11 (-4))
def d2Transfer414S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer414Arithmetic : weightedUpper d2Transfer414C0 d2Log98Lo d2Log98Hi + weightedUpper d2Transfer414C1 d2Log76Lo d2Log76Hi ≤ d2Transfer414Cap := by decide +kernel
theorem d2Transfer414Bound : ∀ x ∈ Set.Icc ((d2Transfer414Lo:ℚ):ℝ) ((d2Transfer414Hi:ℚ):ℝ), ((d2Transfer414C0:ℚ):ℝ)*Real.log |x-((d2Transfer414S0:ℚ):ℝ)| + ((d2Transfer414C1:ℚ):ℝ)*Real.log |x-((d2Transfer414S1:ℚ):ℝ)| ≤ ((d2Transfer414Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer414S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414S0,d2Transfer414Lo,d2Transfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer414C0 then |x-((d2Transfer414S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer414S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer414S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414S0,d2Transfer414Lo,d2Transfer414Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414C0,d2Log98Q,d2Transfer414S0,d2Transfer414Lo,d2Transfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer414C0 d2Transfer414S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have hn1 : x-((d2Transfer414S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414S1,d2Transfer414Lo,d2Transfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer414C1 then |x-((d2Transfer414S1:ℚ):ℝ)| ≤ ((d2Log76Q:ℚ):ℝ) else ((d2Log76Q:ℚ):ℝ) ≤ |x-((d2Transfer414S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer414S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414S1,d2Transfer414Lo,d2Transfer414Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer414C1,d2Log76Q,d2Transfer414S1,d2Transfer414Lo,d2Transfer414Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer414C1 d2Transfer414S1 d2Log76Q d2Log76Lo d2Log76Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log76Bounds
  have har : (((weightedUpper d2Transfer414C0 d2Log98Lo d2Log98Hi:ℚ):ℝ) + ((weightedUpper d2Transfer414C1 d2Log76Lo d2Log76Hi:ℚ):ℝ)) ≤ ((d2Transfer414Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer414Arithmetic
  linarith
#print axioms d2Transfer414Arithmetic
#print axioms d2Transfer414Bound
def d2Transfer415Lo : ℚ := (d2LitsNearTransfers051.q2 (38251791) 1 (-28))
def d2Transfer415Hi : ℚ := (d2LitsNearTransfers051.q2 (4991189) 1 (-25))
def d2Transfer415Cap : ℚ := (d2LitsNearTransfers051.q2 (1169469059) 1 (-40))
def d2Transfer415C0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer415S0 : ℚ := (d2LitsNearTransfers051.q2 (-1) 1 (0))
def d2Transfer415C1 : ℚ := (d2LitsNearTransfers051.q2 (-1) 55 (-3))
def d2Transfer415S1 : ℚ := (d2LitsNearTransfers051.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer415Arithmetic : weightedUpper d2Transfer415C0 d2Log98Lo d2Log98Hi + weightedUpper d2Transfer415C1 d2Log75Lo d2Log75Hi ≤ d2Transfer415Cap := by decide +kernel
theorem d2Transfer415Bound : ∀ x ∈ Set.Icc ((d2Transfer415Lo:ℚ):ℝ) ((d2Transfer415Hi:ℚ):ℝ), ((d2Transfer415C0:ℚ):ℝ)*Real.log |x-((d2Transfer415S0:ℚ):ℝ)| + ((d2Transfer415C1:ℚ):ℝ)*Real.log |x-((d2Transfer415S1:ℚ):ℝ)| ≤ ((d2Transfer415Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer415S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415S0,d2Transfer415Lo,d2Transfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer415C0 then |x-((d2Transfer415S0:ℚ):ℝ)| ≤ ((d2Log98Q:ℚ):ℝ) else ((d2Log98Q:ℚ):ℝ) ≤ |x-((d2Transfer415S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer415S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415S0,d2Transfer415Lo,d2Transfer415Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415C0,d2Log98Q,d2Transfer415S0,d2Transfer415Lo,d2Transfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer415C0 d2Transfer415S0 d2Log98Q d2Log98Lo d2Log98Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log98Bounds
  have hn1 : x-((d2Transfer415S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415S1,d2Transfer415Lo,d2Transfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer415C1 then |x-((d2Transfer415S1:ℚ):ℝ)| ≤ ((d2Log75Q:ℚ):ℝ) else ((d2Log75Q:ℚ):ℝ) ≤ |x-((d2Transfer415S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer415S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415S1,d2Transfer415Lo,d2Transfer415Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers051.q2, d2LitsNearLogCache004.q2, d2LitsNearLogCache006.q2, d2Transfer415C1,d2Log75Q,d2Transfer415S1,d2Transfer415Lo,d2Transfer415Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer415C1 d2Transfer415S1 d2Log75Q d2Log75Lo d2Log75Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log75Bounds
  have har : (((weightedUpper d2Transfer415C0 d2Log98Lo d2Log98Hi:ℚ):ℝ) + ((weightedUpper d2Transfer415C1 d2Log75Lo d2Log75Hi:ℚ):ℝ)) ≤ ((d2Transfer415Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer415Arithmetic
  linarith
#print axioms d2Transfer415Arithmetic
#print axioms d2Transfer415Bound
end CatalanMeasure.GenD.Signed.Data.Cells

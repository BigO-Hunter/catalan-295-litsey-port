module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.ZeroLaurent
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearWiderTransfers041
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers041
open D72.LogTransfer
def d2WiderTransfer328Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (678133837) 1 (-30))
def d2WiderTransfer328Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer328Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (1192194056602251574363) 1 (-79))
def d2WiderTransfer328C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer328S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
def d2WiderTransfer328C1 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer328S1 : ℚ := (d2LitsNearWiderTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer328Arithmetic : weightedUpper d2WiderTransfer328C0 d2Log149Lo d2Log149Hi + weightedUpper d2WiderTransfer328C1 d2Log24Lo d2Log24Hi ≤ d2WiderTransfer328Cap := by decide +kernel
theorem d2WiderTransfer328Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer328Lo:ℚ):ℝ) ((d2WiderTransfer328Hi:ℚ):ℝ), ((d2WiderTransfer328C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer328S0:ℚ):ℝ)| + ((d2WiderTransfer328C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer328S1:ℚ):ℝ)| ≤ ((d2WiderTransfer328Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer328S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328S0,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer328C0 then |x-((d2WiderTransfer328S0:ℚ):ℝ)| ≤ ((d2Log149Q:ℚ):ℝ) else ((d2Log149Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer328S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer328S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328S0,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328C0,d2Log149Q,d2WiderTransfer328S0,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer328C0 d2WiderTransfer328S0 d2Log149Q d2Log149Lo d2Log149Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log149Bounds
  have hn1 : x-((d2WiderTransfer328S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328S1,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer328C1 then |x-((d2WiderTransfer328S1:ℚ):ℝ)| ≤ ((d2Log24Q:ℚ):ℝ) else ((d2Log24Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer328S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer328S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328S1,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer328C1,d2Log24Q,d2WiderTransfer328S1,d2WiderTransfer328Lo,d2WiderTransfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer328C1 d2WiderTransfer328S1 d2Log24Q d2Log24Lo d2Log24Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log24Bounds
  have har : (((weightedUpper d2WiderTransfer328C0 d2Log149Lo d2Log149Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer328C1 d2Log24Lo d2Log24Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer328Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer328Arithmetic
  linarith
#print axioms d2WiderTransfer328Arithmetic
#print axioms d2WiderTransfer328Bound
def d2WiderTransfer329Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (678133837) 1 (-30))
def d2WiderTransfer329Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer329Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (8858091993565395041371) 1 (-79))
def d2WiderTransfer329C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (23) 25 (-5))
def d2WiderTransfer329S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer329Arithmetic : weightedUpper d2WiderTransfer329C0 d2Log150Lo d2Log150Hi ≤ d2WiderTransfer329Cap := by decide +kernel
theorem d2WiderTransfer329Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer329Lo:ℚ):ℝ) ((d2WiderTransfer329Hi:ℚ):ℝ), ((d2WiderTransfer329C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer329S0:ℚ):ℝ)| ≤ ((d2WiderTransfer329Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer329S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer329S0,d2WiderTransfer329Lo,d2WiderTransfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer329C0 then |x-((d2WiderTransfer329S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer329S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer329S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer329S0,d2WiderTransfer329Lo,d2WiderTransfer329Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer329C0,d2Log150Q,d2WiderTransfer329S0,d2WiderTransfer329Lo,d2WiderTransfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer329C0 d2WiderTransfer329S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have har : (((weightedUpper d2WiderTransfer329C0 d2Log150Lo d2Log150Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer329Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer329Arithmetic
  linarith
#print axioms d2WiderTransfer329Arithmetic
#print axioms d2WiderTransfer329Bound
def d2WiderTransfer330Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (678133837) 1 (-30))
def d2WiderTransfer330Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer330Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (17283585689199030189147) 1 (-79))
def d2WiderTransfer330C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (3) 275 (-5))
def d2WiderTransfer330S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
def d2WiderTransfer330C1 : ℚ := (d2LitsNearWiderTransfers041.q2 (-5) 11 (-4))
def d2WiderTransfer330S1 : ℚ := (d2LitsNearWiderTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer330Arithmetic : weightedUpper d2WiderTransfer330C0 d2Log150Lo d2Log150Hi + weightedUpper d2WiderTransfer330C1 d2Log24Lo d2Log24Hi ≤ d2WiderTransfer330Cap := by decide +kernel
theorem d2WiderTransfer330Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer330Lo:ℚ):ℝ) ((d2WiderTransfer330Hi:ℚ):ℝ), ((d2WiderTransfer330C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer330S0:ℚ):ℝ)| + ((d2WiderTransfer330C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer330S1:ℚ):ℝ)| ≤ ((d2WiderTransfer330Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer330S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330S0,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer330C0 then |x-((d2WiderTransfer330S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer330S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer330S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330S0,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330C0,d2Log150Q,d2WiderTransfer330S0,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer330C0 d2WiderTransfer330S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have hn1 : x-((d2WiderTransfer330S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330S1,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer330C1 then |x-((d2WiderTransfer330S1:ℚ):ℝ)| ≤ ((d2Log24Q:ℚ):ℝ) else ((d2Log24Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer330S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer330S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330S1,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer330C1,d2Log24Q,d2WiderTransfer330S1,d2WiderTransfer330Lo,d2WiderTransfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer330C1 d2WiderTransfer330S1 d2Log24Q d2Log24Lo d2Log24Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log24Bounds
  have har : (((weightedUpper d2WiderTransfer330C0 d2Log150Lo d2Log150Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer330C1 d2Log24Lo d2Log24Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer330Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer330Arithmetic
  linarith
#print axioms d2WiderTransfer330Arithmetic
#print axioms d2WiderTransfer330Bound
def d2WiderTransfer331Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer331Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (339905779) 1 (-29))
def d2WiderTransfer331Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (1228821456825910251985) 1 (-79))
def d2WiderTransfer331C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer331S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
def d2WiderTransfer331C1 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer331S1 : ℚ := (d2LitsNearWiderTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer331Arithmetic : weightedUpper d2WiderTransfer331C0 d2Log150Lo d2Log150Hi + weightedUpper d2WiderTransfer331C1 d2Log23Lo d2Log23Hi ≤ d2WiderTransfer331Cap := by decide +kernel
theorem d2WiderTransfer331Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer331Lo:ℚ):ℝ) ((d2WiderTransfer331Hi:ℚ):ℝ), ((d2WiderTransfer331C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer331S0:ℚ):ℝ)| + ((d2WiderTransfer331C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer331S1:ℚ):ℝ)| ≤ ((d2WiderTransfer331Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer331S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331S0,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer331C0 then |x-((d2WiderTransfer331S0:ℚ):ℝ)| ≤ ((d2Log150Q:ℚ):ℝ) else ((d2Log150Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer331S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer331S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331S0,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331C0,d2Log150Q,d2WiderTransfer331S0,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer331C0 d2WiderTransfer331S0 d2Log150Q d2Log150Lo d2Log150Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log150Bounds
  have hn1 : x-((d2WiderTransfer331S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331S1,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer331C1 then |x-((d2WiderTransfer331S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer331S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer331S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331S1,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer331C1,d2Log23Q,d2WiderTransfer331S1,d2WiderTransfer331Lo,d2WiderTransfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer331C1 d2WiderTransfer331S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2WiderTransfer331C0 d2Log150Lo d2Log150Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer331C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer331Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer331Arithmetic
  linarith
#print axioms d2WiderTransfer331Arithmetic
#print axioms d2WiderTransfer331Bound
def d2WiderTransfer332Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer332Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (339905779) 1 (-29))
def d2WiderTransfer332Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (8894719393789053718993) 1 (-79))
def d2WiderTransfer332C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (23) 25 (-5))
def d2WiderTransfer332S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer332Arithmetic : weightedUpper d2WiderTransfer332C0 d2Log151Lo d2Log151Hi ≤ d2WiderTransfer332Cap := by decide +kernel
theorem d2WiderTransfer332Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer332Lo:ℚ):ℝ) ((d2WiderTransfer332Hi:ℚ):ℝ), ((d2WiderTransfer332C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer332S0:ℚ):ℝ)| ≤ ((d2WiderTransfer332Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer332S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer332S0,d2WiderTransfer332Lo,d2WiderTransfer332Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer332C0 then |x-((d2WiderTransfer332S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer332S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer332S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer332S0,d2WiderTransfer332Lo,d2WiderTransfer332Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer332C0,d2Log151Q,d2WiderTransfer332S0,d2WiderTransfer332Lo,d2WiderTransfer332Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer332C0 d2WiderTransfer332S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have har : (((weightedUpper d2WiderTransfer332C0 d2Log151Lo d2Log151Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer332Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer332Arithmetic
  linarith
#print axioms d2WiderTransfer332Arithmetic
#print axioms d2WiderTransfer332Bound
def d2WiderTransfer333Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (1357945395) 1 (-31))
def d2WiderTransfer333Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (339905779) 1 (-29))
def d2WiderTransfer333Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (17320213089422688866769) 1 (-79))
def d2WiderTransfer333C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (3) 275 (-5))
def d2WiderTransfer333S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
def d2WiderTransfer333C1 : ℚ := (d2LitsNearWiderTransfers041.q2 (-5) 11 (-4))
def d2WiderTransfer333S1 : ℚ := (d2LitsNearWiderTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer333Arithmetic : weightedUpper d2WiderTransfer333C0 d2Log151Lo d2Log151Hi + weightedUpper d2WiderTransfer333C1 d2Log23Lo d2Log23Hi ≤ d2WiderTransfer333Cap := by decide +kernel
theorem d2WiderTransfer333Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer333Lo:ℚ):ℝ) ((d2WiderTransfer333Hi:ℚ):ℝ), ((d2WiderTransfer333C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer333S0:ℚ):ℝ)| + ((d2WiderTransfer333C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer333S1:ℚ):ℝ)| ≤ ((d2WiderTransfer333Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer333S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333S0,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer333C0 then |x-((d2WiderTransfer333S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer333S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer333S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333S0,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333C0,d2Log151Q,d2WiderTransfer333S0,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer333C0 d2WiderTransfer333S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2WiderTransfer333S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333S1,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer333C1 then |x-((d2WiderTransfer333S1:ℚ):ℝ)| ≤ ((d2Log23Q:ℚ):ℝ) else ((d2Log23Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer333S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer333S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333S1,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer333C1,d2Log23Q,d2WiderTransfer333S1,d2WiderTransfer333Lo,d2WiderTransfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer333C1 d2WiderTransfer333S1 d2Log23Q d2Log23Lo d2Log23Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log23Bounds
  have har : (((weightedUpper d2WiderTransfer333C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer333C1 d2Log23Lo d2Log23Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer333Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer333Arithmetic
  linarith
#print axioms d2WiderTransfer333Arithmetic
#print axioms d2WiderTransfer333Bound
def d2WiderTransfer334Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (339905779) 1 (-29))
def d2WiderTransfer334Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (1361300837) 1 (-31))
def d2WiderTransfer334Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (2531053359280603360305) 1 (-80))
def d2WiderTransfer334C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer334S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
def d2WiderTransfer334C1 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 55 (-3))
def d2WiderTransfer334S1 : ℚ := (d2LitsNearWiderTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer334Arithmetic : weightedUpper d2WiderTransfer334C0 d2Log151Lo d2Log151Hi + weightedUpper d2WiderTransfer334C1 d2Log22Lo d2Log22Hi ≤ d2WiderTransfer334Cap := by decide +kernel
theorem d2WiderTransfer334Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer334Lo:ℚ):ℝ) ((d2WiderTransfer334Hi:ℚ):ℝ), ((d2WiderTransfer334C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer334S0:ℚ):ℝ)| + ((d2WiderTransfer334C1:ℚ):ℝ)*Real.log |x-((d2WiderTransfer334S1:ℚ):ℝ)| ≤ ((d2WiderTransfer334Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer334S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334S0,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer334C0 then |x-((d2WiderTransfer334S0:ℚ):ℝ)| ≤ ((d2Log151Q:ℚ):ℝ) else ((d2Log151Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer334S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer334S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334S0,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334C0,d2Log151Q,d2WiderTransfer334S0,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer334C0 d2WiderTransfer334S0 d2Log151Q d2Log151Lo d2Log151Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log151Bounds
  have hn1 : x-((d2WiderTransfer334S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334S1,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2WiderTransfer334C1 then |x-((d2WiderTransfer334S1:ℚ):ℝ)| ≤ ((d2Log22Q:ℚ):ℝ) else ((d2Log22Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer334S1:ℚ):ℝ)|) := by
    have ha : x-((d2WiderTransfer334S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334S1,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer334C1,d2Log22Q,d2WiderTransfer334S1,d2WiderTransfer334Lo,d2WiderTransfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2WiderTransfer334C1 d2WiderTransfer334S1 d2Log22Q d2Log22Lo d2Log22Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log22Bounds
  have har : (((weightedUpper d2WiderTransfer334C0 d2Log151Lo d2Log151Hi:ℚ):ℝ) + ((weightedUpper d2WiderTransfer334C1 d2Log22Lo d2Log22Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer334Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer334Arithmetic
  linarith
#print axioms d2WiderTransfer334Arithmetic
#print axioms d2WiderTransfer334Bound
def d2WiderTransfer335Lo : ℚ := (d2LitsNearWiderTransfers041.q2 (339905779) 1 (-29))
def d2WiderTransfer335Hi : ℚ := (d2LitsNearWiderTransfers041.q2 (1361300837) 1 (-31))
def d2WiderTransfer335Cap : ℚ := (d2LitsNearWiderTransfers041.q2 (17862849233206890294321) 1 (-80))
def d2WiderTransfer335C0 : ℚ := (d2LitsNearWiderTransfers041.q2 (23) 25 (-5))
def d2WiderTransfer335S0 : ℚ := (d2LitsNearWiderTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer335Arithmetic : weightedUpper d2WiderTransfer335C0 d2Log152Lo d2Log152Hi ≤ d2WiderTransfer335Cap := by decide +kernel
theorem d2WiderTransfer335Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer335Lo:ℚ):ℝ) ((d2WiderTransfer335Hi:ℚ):ℝ), ((d2WiderTransfer335C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer335S0:ℚ):ℝ)| ≤ ((d2WiderTransfer335Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer335S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer335S0,d2WiderTransfer335Lo,d2WiderTransfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer335C0 then |x-((d2WiderTransfer335S0:ℚ):ℝ)| ≤ ((d2Log152Q:ℚ):ℝ) else ((d2Log152Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer335S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer335S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer335S0,d2WiderTransfer335Lo,d2WiderTransfer335Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers041.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2WiderTransfer335C0,d2Log152Q,d2WiderTransfer335S0,d2WiderTransfer335Lo,d2WiderTransfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer335C0 d2WiderTransfer335S0 d2Log152Q d2Log152Lo d2Log152Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log152Bounds
  have har : (((weightedUpper d2WiderTransfer335C0 d2Log152Lo d2Log152Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer335Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer335Arithmetic
  linarith
#print axioms d2WiderTransfer335Arithmetic
#print axioms d2WiderTransfer335Bound
end CatalanMeasure.GenD.Signed.Data.Cells

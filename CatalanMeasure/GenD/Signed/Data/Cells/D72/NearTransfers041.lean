module

public import CatalanMeasure.GenD.Signed.Data.Cells.ChebPieceL
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LaurentCache
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.RootScale
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.LogTransfer
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache000
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache001
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache009
public import CatalanMeasure.GenD.Signed.Data.Cells.D72.NearLogCache010
public import CatalanMeasure.GenD.Signed.Data.Cells.Lits
public import CatalanMeasure.CellCert.RawInts

@[expose] public section

namespace CatalanMeasure.GenD.Signed.Data.Cells
open Set CatalanMeasure.CellCert CatalanMeasure.GenD.Signed.TaylorCell CatalanMeasure.GenD.Signed.LogEval
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace d2LitsNearTransfers041
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearTransfers041
open D72.LogTransfer
def d2Transfer328Lo : ℚ := (d2LitsNearTransfers041.q2 (85395875) 1 (-27))
def d2Transfer328Hi : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer328Cap : ℚ := (d2LitsNearTransfers041.q2 (20361260441185641722871) 1 (-80))
def d2Transfer328C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (-5))
def d2Transfer328S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer328Arithmetic : weightedUpper d2Transfer328C0 d2Log158Lo d2Log158Hi ≤ d2Transfer328Cap := by decide +kernel
theorem d2Transfer328Bound : ∀ x ∈ Set.Icc ((d2Transfer328Lo:ℚ):ℝ) ((d2Transfer328Hi:ℚ):ℝ), ((d2Transfer328C0:ℚ):ℝ)*Real.log |x-((d2Transfer328S0:ℚ):ℝ)| ≤ ((d2Transfer328Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer328S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer328S0,d2Transfer328Lo,d2Transfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer328C0 then |x-((d2Transfer328S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer328S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer328S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer328S0,d2Transfer328Lo,d2Transfer328Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer328C0,d2Log158Q,d2Transfer328S0,d2Transfer328Lo,d2Transfer328Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer328C0 d2Transfer328S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have har : (((weightedUpper d2Transfer328C0 d2Log158Lo d2Log158Hi:ℚ):ℝ)) ≤ ((d2Transfer328Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer328Arithmetic
  linarith
#print axioms d2Transfer328Arithmetic
#print axioms d2Transfer328Bound
def d2Transfer329Lo : ℚ := (d2LitsNearTransfers041.q2 (85395875) 1 (-27))
def d2Transfer329Hi : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer329Cap : ℚ := (d2LitsNearTransfers041.q2 (36726097763477149086711) 1 (-80))
def d2Transfer329C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 11 (-5))
def d2Transfer329S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
def d2Transfer329C1 : ℚ := (d2LitsNearTransfers041.q2 (-5) 11 (-4))
def d2Transfer329S1 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer329Arithmetic : weightedUpper d2Transfer329C0 d2Log158Lo d2Log158Hi + weightedUpper d2Transfer329C1 d2Log16Lo d2Log16Hi ≤ d2Transfer329Cap := by decide +kernel
theorem d2Transfer329Bound : ∀ x ∈ Set.Icc ((d2Transfer329Lo:ℚ):ℝ) ((d2Transfer329Hi:ℚ):ℝ), ((d2Transfer329C0:ℚ):ℝ)*Real.log |x-((d2Transfer329S0:ℚ):ℝ)| + ((d2Transfer329C1:ℚ):ℝ)*Real.log |x-((d2Transfer329S1:ℚ):ℝ)| ≤ ((d2Transfer329Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer329S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329S0,d2Transfer329Lo,d2Transfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer329C0 then |x-((d2Transfer329S0:ℚ):ℝ)| ≤ ((d2Log158Q:ℚ):ℝ) else ((d2Log158Q:ℚ):ℝ) ≤ |x-((d2Transfer329S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer329S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329S0,d2Transfer329Lo,d2Transfer329Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329C0,d2Log158Q,d2Transfer329S0,d2Transfer329Lo,d2Transfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer329C0 d2Transfer329S0 d2Log158Q d2Log158Lo d2Log158Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log158Bounds
  have hn1 : x-((d2Transfer329S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329S1,d2Transfer329Lo,d2Transfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer329C1 then |x-((d2Transfer329S1:ℚ):ℝ)| ≤ ((d2Log16Q:ℚ):ℝ) else ((d2Log16Q:ℚ):ℝ) ≤ |x-((d2Transfer329S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer329S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329S1,d2Transfer329Lo,d2Transfer329Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer329C1,d2Log16Q,d2Transfer329S1,d2Transfer329Lo,d2Transfer329Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer329C1 d2Transfer329S1 d2Log16Q d2Log16Lo d2Log16Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log16Bounds
  have har : (((weightedUpper d2Transfer329C0 d2Log158Lo d2Log158Hi:ℚ):ℝ) + ((weightedUpper d2Transfer329C1 d2Log16Lo d2Log16Hi:ℚ):ℝ)) ≤ ((d2Transfer329Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer329Arithmetic
  linarith
#print axioms d2Transfer329Arithmetic
#print axioms d2Transfer329Bound
def d2Transfer330Lo : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer330Hi : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer330Cap : ℚ := (d2LitsNearTransfers041.q2 (4193347169859673716761) 1 (-80))
def d2Transfer330C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 25 (-4))
def d2Transfer330S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer330Arithmetic : weightedUpper d2Transfer330C0 d2Log160Lo d2Log160Hi ≤ d2Transfer330Cap := by decide +kernel
theorem d2Transfer330Bound : ∀ x ∈ Set.Icc ((d2Transfer330Lo:ℚ):ℝ) ((d2Transfer330Hi:ℚ):ℝ), ((d2Transfer330C0:ℚ):ℝ)*Real.log |x-((d2Transfer330S0:ℚ):ℝ)| ≤ ((d2Transfer330Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer330S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer330S0,d2Transfer330Lo,d2Transfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer330C0 then |x-((d2Transfer330S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer330S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer330S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer330S0,d2Transfer330Lo,d2Transfer330Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer330C0,d2Log160Q,d2Transfer330S0,d2Transfer330Lo,d2Transfer330Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer330C0 d2Transfer330S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2Transfer330C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2Transfer330Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer330Arithmetic
  linarith
#print axioms d2Transfer330Arithmetic
#print axioms d2Transfer330Bound
def d2Transfer331Lo : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer331Hi : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer331Cap : ℚ := (d2LitsNearTransfers041.q2 (5443647338495409059865) 1 (-80))
def d2Transfer331C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 275 (-4))
def d2Transfer331S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
def d2Transfer331C1 : ℚ := (d2LitsNearTransfers041.q2 (-1) 55 (-3))
def d2Transfer331S1 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer331Arithmetic : weightedUpper d2Transfer331C0 d2Log160Lo d2Log160Hi + weightedUpper d2Transfer331C1 d2Log14Lo d2Log14Hi ≤ d2Transfer331Cap := by decide +kernel
theorem d2Transfer331Bound : ∀ x ∈ Set.Icc ((d2Transfer331Lo:ℚ):ℝ) ((d2Transfer331Hi:ℚ):ℝ), ((d2Transfer331C0:ℚ):ℝ)*Real.log |x-((d2Transfer331S0:ℚ):ℝ)| + ((d2Transfer331C1:ℚ):ℝ)*Real.log |x-((d2Transfer331S1:ℚ):ℝ)| ≤ ((d2Transfer331Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer331S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331S0,d2Transfer331Lo,d2Transfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer331C0 then |x-((d2Transfer331S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer331S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer331S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331S0,d2Transfer331Lo,d2Transfer331Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331C0,d2Log160Q,d2Transfer331S0,d2Transfer331Lo,d2Transfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer331C0 d2Transfer331S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2Transfer331S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331S1,d2Transfer331Lo,d2Transfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer331C1 then |x-((d2Transfer331S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2Transfer331S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer331S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331S1,d2Transfer331Lo,d2Transfer331Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer331C1,d2Log14Q,d2Transfer331S1,d2Transfer331Lo,d2Transfer331Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer331C1 d2Transfer331S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2Transfer331C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2Transfer331C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2Transfer331Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer331Arithmetic
  linarith
#print axioms d2Transfer331Arithmetic
#print axioms d2Transfer331Bound
def d2Transfer332Lo : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer332Hi : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer332Cap : ℚ := (d2LitsNearTransfers041.q2 (20666709428918369581081) 1 (-80))
def d2Transfer332C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (-5))
def d2Transfer332S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer332Arithmetic : weightedUpper d2Transfer332C0 d2Log160Lo d2Log160Hi ≤ d2Transfer332Cap := by decide +kernel
theorem d2Transfer332Bound : ∀ x ∈ Set.Icc ((d2Transfer332Lo:ℚ):ℝ) ((d2Transfer332Hi:ℚ):ℝ), ((d2Transfer332C0:ℚ):ℝ)*Real.log |x-((d2Transfer332S0:ℚ):ℝ)| ≤ ((d2Transfer332Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer332S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer332S0,d2Transfer332Lo,d2Transfer332Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer332C0 then |x-((d2Transfer332S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer332S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer332S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer332S0,d2Transfer332Lo,d2Transfer332Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer332C0,d2Log160Q,d2Transfer332S0,d2Transfer332Lo,d2Transfer332Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer332C0 d2Transfer332S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have har : (((weightedUpper d2Transfer332C0 d2Log160Lo d2Log160Hi:ℚ):ℝ)) ≤ ((d2Transfer332Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer332Arithmetic
  linarith
#print axioms d2Transfer332Arithmetic
#print axioms d2Transfer332Bound
def d2Transfer333Lo : ℚ := (d2LitsNearTransfers041.q2 (343261221) 1 (-29))
def d2Transfer333Hi : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer333Cap : ℚ := (d2LitsNearTransfers041.q2 (37031546751209876944921) 1 (-80))
def d2Transfer333C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 11 (-5))
def d2Transfer333S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
def d2Transfer333C1 : ℚ := (d2LitsNearTransfers041.q2 (-5) 11 (-4))
def d2Transfer333S1 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer333Arithmetic : weightedUpper d2Transfer333C0 d2Log160Lo d2Log160Hi + weightedUpper d2Transfer333C1 d2Log14Lo d2Log14Hi ≤ d2Transfer333Cap := by decide +kernel
theorem d2Transfer333Bound : ∀ x ∈ Set.Icc ((d2Transfer333Lo:ℚ):ℝ) ((d2Transfer333Hi:ℚ):ℝ), ((d2Transfer333C0:ℚ):ℝ)*Real.log |x-((d2Transfer333S0:ℚ):ℝ)| + ((d2Transfer333C1:ℚ):ℝ)*Real.log |x-((d2Transfer333S1:ℚ):ℝ)| ≤ ((d2Transfer333Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer333S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333S0,d2Transfer333Lo,d2Transfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer333C0 then |x-((d2Transfer333S0:ℚ):ℝ)| ≤ ((d2Log160Q:ℚ):ℝ) else ((d2Log160Q:ℚ):ℝ) ≤ |x-((d2Transfer333S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer333S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333S0,d2Transfer333Lo,d2Transfer333Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333C0,d2Log160Q,d2Transfer333S0,d2Transfer333Lo,d2Transfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer333C0 d2Transfer333S0 d2Log160Q d2Log160Lo d2Log160Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log160Bounds
  have hn1 : x-((d2Transfer333S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333S1,d2Transfer333Lo,d2Transfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer333C1 then |x-((d2Transfer333S1:ℚ):ℝ)| ≤ ((d2Log14Q:ℚ):ℝ) else ((d2Log14Q:ℚ):ℝ) ≤ |x-((d2Transfer333S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer333S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333S1,d2Transfer333Lo,d2Transfer333Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer333C1,d2Log14Q,d2Transfer333S1,d2Transfer333Lo,d2Transfer333Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer333C1 d2Transfer333S1 d2Log14Q d2Log14Lo d2Log14Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log14Bounds
  have har : (((weightedUpper d2Transfer333C0 d2Log160Lo d2Log160Hi:ℚ):ℝ) + ((weightedUpper d2Transfer333C1 d2Log14Lo d2Log14Hi:ℚ):ℝ)) ≤ ((d2Transfer333Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer333Arithmetic
  linarith
#print axioms d2Transfer333Arithmetic
#print axioms d2Transfer333Bound
def d2Transfer334Lo : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer334Hi : ℚ := (d2LitsNearTransfers041.q2 (21768399) 1 (-25))
def d2Transfer334Cap : ℚ := (d2LitsNearTransfers041.q2 (4812127375716014614645) 1 (-80))
def d2Transfer334C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 25 (-4))
def d2Transfer334S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer334Arithmetic : weightedUpper d2Transfer334C0 d2Log162Lo d2Log162Hi ≤ d2Transfer334Cap := by decide +kernel
theorem d2Transfer334Bound : ∀ x ∈ Set.Icc ((d2Transfer334Lo:ℚ):ℝ) ((d2Transfer334Hi:ℚ):ℝ), ((d2Transfer334C0:ℚ):ℝ)*Real.log |x-((d2Transfer334S0:ℚ):ℝ)| ≤ ((d2Transfer334Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer334S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer334S0,d2Transfer334Lo,d2Transfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer334C0 then |x-((d2Transfer334S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer334S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer334S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer334S0,d2Transfer334Lo,d2Transfer334Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer334C0,d2Log162Q,d2Transfer334S0,d2Transfer334Lo,d2Transfer334Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer334C0 d2Transfer334S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have har : (((weightedUpper d2Transfer334C0 d2Log162Lo d2Log162Hi:ℚ):ℝ)) ≤ ((d2Transfer334Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer334Arithmetic
  linarith
#print axioms d2Transfer334Arithmetic
#print axioms d2Transfer334Bound
def d2Transfer335Lo : ℚ := (d2LitsNearTransfers041.q2 (172469471) 1 (-28))
def d2Transfer335Hi : ℚ := (d2LitsNearTransfers041.q2 (21768399) 1 (-25))
def d2Transfer335Cap : ℚ := (d2LitsNearTransfers041.q2 (6062427544351749957749) 1 (-80))
def d2Transfer335C0 : ℚ := (d2LitsNearTransfers041.q2 (1) 275 (-4))
def d2Transfer335S0 : ℚ := (d2LitsNearTransfers041.q2 (-1) 1 (0))
def d2Transfer335C1 : ℚ := (d2LitsNearTransfers041.q2 (-1) 55 (-3))
def d2Transfer335S1 : ℚ := (d2LitsNearTransfers041.q2 (1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2Transfer335Arithmetic : weightedUpper d2Transfer335C0 d2Log162Lo d2Log162Hi + weightedUpper d2Transfer335C1 d2Log12Lo d2Log12Hi ≤ d2Transfer335Cap := by decide +kernel
theorem d2Transfer335Bound : ∀ x ∈ Set.Icc ((d2Transfer335Lo:ℚ):ℝ) ((d2Transfer335Hi:ℚ):ℝ), ((d2Transfer335C0:ℚ):ℝ)*Real.log |x-((d2Transfer335S0:ℚ):ℝ)| + ((d2Transfer335C1:ℚ):ℝ)*Real.log |x-((d2Transfer335S1:ℚ):ℝ)| ≤ ((d2Transfer335Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2Transfer335S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335S0,d2Transfer335Lo,d2Transfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2Transfer335C0 then |x-((d2Transfer335S0:ℚ):ℝ)| ≤ ((d2Log162Q:ℚ):ℝ) else ((d2Log162Q:ℚ):ℝ) ≤ |x-((d2Transfer335S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2Transfer335S0:ℚ):ℝ) := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335S0,d2Transfer335Lo,d2Transfer335Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335C0,d2Log162Q,d2Transfer335S0,d2Transfer335Lo,d2Transfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2Transfer335C0 d2Transfer335S0 d2Log162Q d2Log162Lo d2Log162Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log162Bounds
  have hn1 : x-((d2Transfer335S1:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335S1,d2Transfer335Lo,d2Transfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd1 : (if (0:ℚ) ≤ d2Transfer335C1 then |x-((d2Transfer335S1:ℚ):ℝ)| ≤ ((d2Log12Q:ℚ):ℝ) else ((d2Log12Q:ℚ):ℝ) ≤ |x-((d2Transfer335S1:ℚ):ℝ)|) := by
    have ha : x-((d2Transfer335S1:ℚ):ℝ) ≤ 0 := by
      norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335S1,d2Transfer335Lo,d2Transfer335Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonpos ha]
    norm_num [d2LitsNearTransfers041.q2, d2LitsNearLogCache000.q2, d2LitsNearLogCache001.q2, d2LitsNearLogCache009.q2, d2LitsNearLogCache010.q2, d2Transfer335C1,d2Log12Q,d2Transfer335S1,d2Transfer335Lo,d2Transfer335Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h1 := weighted_site_upper d2Transfer335C1 d2Transfer335S1 d2Log12Q d2Log12Lo d2Log12Hi x (by decide +kernel) (abs_pos.mpr hn1) hd1 d2Log12Bounds
  have har : (((weightedUpper d2Transfer335C0 d2Log162Lo d2Log162Hi:ℚ):ℝ) + ((weightedUpper d2Transfer335C1 d2Log12Lo d2Log12Hi:ℚ):ℝ)) ≤ ((d2Transfer335Cap:ℚ):ℝ) := by exact_mod_cast d2Transfer335Arithmetic
  linarith
#print axioms d2Transfer335Arithmetic
#print axioms d2Transfer335Bound
end CatalanMeasure.GenD.Signed.Data.Cells

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
namespace d2LitsNearWiderTransfers056
def q2 (n d e : Int) : ℚ := (n : ℚ)/(d : ℚ) *
  if 0 ≤ e then (2 : ℚ)^e.toNat else 1/(2 : ℚ)^(-e).toNat
def q2listC : List Int → List ℚ
  | n :: d :: e :: xs => q2 n d e :: q2listC xs
  | _ => []
end d2LitsNearWiderTransfers056
open D72.LogTransfer
def d2WiderTransfer448Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (8191) 1 (-13))
def d2WiderTransfer448Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer448Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (1055569268745246078077) 1 (-79))
def d2WiderTransfer448C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 25 (-4))
def d2WiderTransfer448S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer448Arithmetic : weightedUpper d2WiderTransfer448C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer448Cap := by decide +kernel
theorem d2WiderTransfer448Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer448Lo:ℚ):ℝ) ((d2WiderTransfer448Hi:ℚ):ℝ), ((d2WiderTransfer448C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer448S0:ℚ):ℝ)| ≤ ((d2WiderTransfer448Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer448S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer448S0,d2WiderTransfer448Lo,d2WiderTransfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer448C0 then |x-((d2WiderTransfer448S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer448S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer448S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer448S0,d2WiderTransfer448Lo,d2WiderTransfer448Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer448C0,d2Log180Q,d2WiderTransfer448S0,d2WiderTransfer448Lo,d2WiderTransfer448Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer448C0 d2WiderTransfer448S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer448C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer448Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer448Arithmetic
  linarith
#print axioms d2WiderTransfer448Arithmetic
#print axioms d2WiderTransfer448Bound
def d2WiderTransfer449Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (8191) 1 (-13))
def d2WiderTransfer449Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer449Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (13092603583138943988861) 1 (-79))
def d2WiderTransfer449C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 1 (-5))
def d2WiderTransfer449S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer449Arithmetic : weightedUpper d2WiderTransfer449C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer449Cap := by decide +kernel
theorem d2WiderTransfer449Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer449Lo:ℚ):ℝ) ((d2WiderTransfer449Hi:ℚ):ℝ), ((d2WiderTransfer449C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer449S0:ℚ):ℝ)| ≤ ((d2WiderTransfer449Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer449S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer449S0,d2WiderTransfer449Lo,d2WiderTransfer449Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer449C0 then |x-((d2WiderTransfer449S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer449S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer449S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer449S0,d2WiderTransfer449Lo,d2WiderTransfer449Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer449C0,d2Log180Q,d2WiderTransfer449S0,d2WiderTransfer449Lo,d2WiderTransfer449Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer449C0 d2WiderTransfer449S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer449C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer449Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer449Arithmetic
  linarith
#print axioms d2WiderTransfer449Arithmetic
#print axioms d2WiderTransfer449Bound
def d2WiderTransfer450Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (8191) 1 (-13))
def d2WiderTransfer450Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer450Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (13092603781051036988541) 1 (-79))
def d2WiderTransfer450C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 1 (-5))
def d2WiderTransfer450S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer450Arithmetic : weightedUpper d2WiderTransfer450C0 d2Log180Lo d2Log180Hi ≤ d2WiderTransfer450Cap := by decide +kernel
theorem d2WiderTransfer450Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer450Lo:ℚ):ℝ) ((d2WiderTransfer450Hi:ℚ):ℝ), ((d2WiderTransfer450C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer450S0:ℚ):ℝ)| ≤ ((d2WiderTransfer450Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer450S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer450S0,d2WiderTransfer450Lo,d2WiderTransfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer450C0 then |x-((d2WiderTransfer450S0:ℚ):ℝ)| ≤ ((d2Log180Q:ℚ):ℝ) else ((d2Log180Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer450S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer450S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer450S0,d2WiderTransfer450Lo,d2WiderTransfer450Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer450C0,d2Log180Q,d2WiderTransfer450S0,d2WiderTransfer450Lo,d2WiderTransfer450Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer450C0 d2WiderTransfer450S0 d2Log180Q d2Log180Lo d2Log180Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log180Bounds
  have har : (((weightedUpper d2WiderTransfer450C0 d2Log180Lo d2Log180Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer450Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer450Arithmetic
  linarith
#print axioms d2WiderTransfer450Arithmetic
#print axioms d2WiderTransfer450Bound
def d2WiderTransfer451Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer451Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (32767) 1 (-15))
def d2WiderTransfer451Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (2111715430351178477989) 1 (-80))
def d2WiderTransfer451C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 25 (-4))
def d2WiderTransfer451S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer451Arithmetic : weightedUpper d2WiderTransfer451C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer451Cap := by decide +kernel
theorem d2WiderTransfer451Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer451Lo:ℚ):ℝ) ((d2WiderTransfer451Hi:ℚ):ℝ), ((d2WiderTransfer451C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer451S0:ℚ):ℝ)| ≤ ((d2WiderTransfer451Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer451S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer451S0,d2WiderTransfer451Lo,d2WiderTransfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer451C0 then |x-((d2WiderTransfer451S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer451S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer451S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer451S0,d2WiderTransfer451Lo,d2WiderTransfer451Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer451C0,d2Log181Q,d2WiderTransfer451S0,d2WiderTransfer451Lo,d2WiderTransfer451Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer451C0 d2WiderTransfer451S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer451C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer451Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer451Arithmetic
  linarith
#print axioms d2WiderTransfer451Arithmetic
#print axioms d2WiderTransfer451Bound
def d2WiderTransfer452Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer452Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (32767) 1 (-15))
def d2WiderTransfer452Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (2111715011437248295333) 1 (-80))
def d2WiderTransfer452C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 25 (-4))
def d2WiderTransfer452S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer452Arithmetic : weightedUpper d2WiderTransfer452C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer452Cap := by decide +kernel
theorem d2WiderTransfer452Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer452Lo:ℚ):ℝ) ((d2WiderTransfer452Hi:ℚ):ℝ), ((d2WiderTransfer452C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer452S0:ℚ):ℝ)| ≤ ((d2WiderTransfer452Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer452S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer452S0,d2WiderTransfer452Lo,d2WiderTransfer452Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer452C0 then |x-((d2WiderTransfer452S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer452S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer452S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer452S0,d2WiderTransfer452Lo,d2WiderTransfer452Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer452C0,d2Log181Q,d2WiderTransfer452S0,d2WiderTransfer452Lo,d2WiderTransfer452Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer452C0 d2WiderTransfer452S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer452C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer452Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer452Arithmetic
  linarith
#print axioms d2WiderTransfer452Arithmetic
#print axioms d2WiderTransfer452Bound
def d2WiderTransfer453Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer453Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (32767) 1 (-15))
def d2WiderTransfer453Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (26185783640224644116901) 1 (-80))
def d2WiderTransfer453C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 1 (-5))
def d2WiderTransfer453S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer453Arithmetic : weightedUpper d2WiderTransfer453C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer453Cap := by decide +kernel
theorem d2WiderTransfer453Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer453Lo:ℚ):ℝ) ((d2WiderTransfer453Hi:ℚ):ℝ), ((d2WiderTransfer453C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer453S0:ℚ):ℝ)| ≤ ((d2WiderTransfer453Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer453S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer453S0,d2WiderTransfer453Lo,d2WiderTransfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer453C0 then |x-((d2WiderTransfer453S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer453S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer453S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer453S0,d2WiderTransfer453Lo,d2WiderTransfer453Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer453C0,d2Log181Q,d2WiderTransfer453S0,d2WiderTransfer453Lo,d2WiderTransfer453Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer453C0 d2WiderTransfer453S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer453C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer453Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer453Arithmetic
  linarith
#print axioms d2WiderTransfer453Arithmetic
#print axioms d2WiderTransfer453Bound
def d2WiderTransfer454Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (16383) 1 (-14))
def d2WiderTransfer454Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (32767) 1 (-15))
def d2WiderTransfer454Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (26185784036048830116261) 1 (-80))
def d2WiderTransfer454C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 1 (-5))
def d2WiderTransfer454S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer454Arithmetic : weightedUpper d2WiderTransfer454C0 d2Log181Lo d2Log181Hi ≤ d2WiderTransfer454Cap := by decide +kernel
theorem d2WiderTransfer454Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer454Lo:ℚ):ℝ) ((d2WiderTransfer454Hi:ℚ):ℝ), ((d2WiderTransfer454C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer454S0:ℚ):ℝ)| ≤ ((d2WiderTransfer454Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer454S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer454S0,d2WiderTransfer454Lo,d2WiderTransfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer454C0 then |x-((d2WiderTransfer454S0:ℚ):ℝ)| ≤ ((d2Log181Q:ℚ):ℝ) else ((d2Log181Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer454S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer454S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer454S0,d2WiderTransfer454Lo,d2WiderTransfer454Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer454C0,d2Log181Q,d2WiderTransfer454S0,d2WiderTransfer454Lo,d2WiderTransfer454Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer454C0 d2WiderTransfer454S0 d2Log181Q d2Log181Lo d2Log181Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log181Bounds
  have har : (((weightedUpper d2WiderTransfer454C0 d2Log181Lo d2Log181Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer454Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer454Arithmetic
  linarith
#print axioms d2WiderTransfer454Arithmetic
#print axioms d2WiderTransfer454Bound
def d2WiderTransfer455Lo : ℚ := (d2LitsNearWiderTransfers056.q2 (32767) 1 (-15))
def d2WiderTransfer455Hi : ℚ := (d2LitsNearWiderTransfers056.q2 (65535) 1 (-16))
def d2WiderTransfer455Cap : ℚ := (d2LitsNearWiderTransfers056.q2 (1056001832012952110189) 1 (-79))
def d2WiderTransfer455C0 : ℚ := (d2LitsNearWiderTransfers056.q2 (1) 25 (-4))
def d2WiderTransfer455S0 : ℚ := (d2LitsNearWiderTransfers056.q2 (-1) 1 (0))
-- kcost: at most2cached weighted endpoints, 3rational additions/comparisons; log evaluations imported once.
theorem d2WiderTransfer455Arithmetic : weightedUpper d2WiderTransfer455C0 d2Log182Lo d2Log182Hi ≤ d2WiderTransfer455Cap := by decide +kernel
theorem d2WiderTransfer455Bound : ∀ x ∈ Set.Icc ((d2WiderTransfer455Lo:ℚ):ℝ) ((d2WiderTransfer455Hi:ℚ):ℝ), ((d2WiderTransfer455C0:ℚ):ℝ)*Real.log |x-((d2WiderTransfer455S0:ℚ):ℝ)| ≤ ((d2WiderTransfer455Cap:ℚ):ℝ) := by
  intro x hx
  have hn0 : x-((d2WiderTransfer455S0:ℚ):ℝ) ≠ 0 := by
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer455S0,d2WiderTransfer455Lo,d2WiderTransfer455Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have hd0 : (if (0:ℚ) ≤ d2WiderTransfer455C0 then |x-((d2WiderTransfer455S0:ℚ):ℝ)| ≤ ((d2Log182Q:ℚ):ℝ) else ((d2Log182Q:ℚ):ℝ) ≤ |x-((d2WiderTransfer455S0:ℚ):ℝ)|) := by
    have ha : 0 ≤ x-((d2WiderTransfer455S0:ℚ):ℝ) := by
      norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer455S0,d2WiderTransfer455Lo,d2WiderTransfer455Hi] at *
      rcases hx with ⟨hl,hu⟩
      linarith
    rw [abs_of_nonneg ha]
    norm_num [d2LitsNearWiderTransfers056.q2, d2LitsNearLogCache011.q2, d2WiderTransfer455C0,d2Log182Q,d2WiderTransfer455S0,d2WiderTransfer455Lo,d2WiderTransfer455Hi] at *
    rcases hx with ⟨hl,hu⟩
    linarith
  have h0 := weighted_site_upper d2WiderTransfer455C0 d2WiderTransfer455S0 d2Log182Q d2Log182Lo d2Log182Hi x (by decide +kernel) (abs_pos.mpr hn0) hd0 d2Log182Bounds
  have har : (((weightedUpper d2WiderTransfer455C0 d2Log182Lo d2Log182Hi:ℚ):ℝ)) ≤ ((d2WiderTransfer455Cap:ℚ):ℝ) := by exact_mod_cast d2WiderTransfer455Arithmetic
  linarith
#print axioms d2WiderTransfer455Arithmetic
#print axioms d2WiderTransfer455Bound
end CatalanMeasure.GenD.Signed.Data.Cells
